//! Type checking context.
//!
//! This module provides `TypeContext`, the core context for type checking.
//! It replaces the global state from the OCaml implementation with explicit,
//! per-compilation state.
//!
//! # Design
//!
//! The `TypeContext` owns all type expressions through a `TypeArena`.
//! It maintains the type checking state including:
//! - Current generalization level
//! - Type variable tracking
//! - Unification state
//!
//! # Concurrency
//!
//! `TypeContext` is NOT thread-safe - it uses `RefCell` internally.
//! However, multiple `TypeContext` instances can exist concurrently,
//! one per compilation unit.

use super::asttypes::{ArgLabel, PrivateFlag};
use super::env::{Env, EnvId, ScopeId};
use super::path::Path;
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, FieldMutability, GENERIC_LEVEL, MutabilityRef, PackageLidsRef,
    RowDesc, RowDescRef, RowField, RowFieldRef, TypeArg, TypeArgList, TypeArgSlice, TypeArgs,
    TypeDesc, TypeExprRef, TypeRefList, TypeRefs, TypeSlice,
};
use super::typedtree::EnvRef;
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::parser::longident::Longident;
use crate::types::path::PathView;
use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

/// Append-only store of type nodes (OCaml `type_expr` records,
/// `compiler/ml/types.ml:22-26`) with `Copy` descriptor, level and id
/// fields. Nodes live in chunks that double in size and are never moved, so
/// allocation does not copy earlier nodes and reads take no borrow flag; a
/// node's position is its `TypeExprRef` index.
pub(crate) struct TypeNodes {
    /// Leased for this store's lifetime; only initialized slots below `len`
    /// may be read. Reusing an array does not clear its previous contents.
    first: Rc<[TypeNode; Self::FIRST_LEN]>,
    /// FIRST_LEN normally, zero while a store build must observe local reads.
    fast_limit: Cell<u32>,
    chunks: [std::cell::OnceCell<Box<[TypeNode]>>; TypeNodes::CHUNKS],
    /// One past the last node's index.
    len: Cell<usize>,
    /// Index of the first node: 0, or `FIRST_LEN` for a ladder-only store.
    start: usize,
}

/// One node of [`TypeNodes`]. A node's descriptor and level are usually
/// read together, so they share a cache line.
struct TypeNode {
    desc: Cell<TypeDesc>,
    level: Cell<i32>,
    id: Cell<i32>,
}

thread_local! {
    // The list retains one owner. A second owner leases the array exclusively.
    static FIRST_NODE_ARRAYS: RefCell<Vec<Rc<[TypeNode; TypeNodes::FIRST_LEN]>>> = const { RefCell::new(Vec::new()) };
    #[cfg(test)]
    static FIRST_ARRAY_LEASE_PROBES: Cell<usize> = const { Cell::new(0) };
    #[cfg(test)]
    static FIRST_ARRAY_INITIALIZATIONS: Cell<usize> = const { Cell::new(0) };
}

/// Lease one array: at most one reference-count probe per retained array,
/// no initialization on reuse, or exactly N initializations and one amortized
/// O(1) list append on a new allocation. Called once per pool, not per lookup.
pub(crate) fn lease_first_array<T, const N: usize>(
    arrays: &RefCell<Vec<Rc<[T; N]>>>,
    mut init: impl FnMut() -> T,
) -> Rc<[T; N]> {
    let mut arrays = arrays.borrow_mut();
    #[cfg(test)]
    let mut probes = 0;
    let free = arrays.iter().find(|array| {
        #[cfg(test)]
        {
            probes += 1;
        }
        Rc::strong_count(array) == 1
    });
    #[cfg(test)]
    {
        FIRST_ARRAY_LEASE_PROBES.with(|count| count.set(probes));
        FIRST_ARRAY_INITIALIZATIONS.with(|count| count.set(0));
    }
    if let Some(free) = free {
        return Rc::clone(free);
    }
    // Collect on the heap rather than constructing a large stack array.
    #[cfg(test)]
    let mut initialized = 0;
    let array: Rc<[T]> = (0..N)
        .map(|_| {
            #[cfg(test)]
            {
                initialized += 1;
            }
            init()
        })
        .collect();
    #[cfg(test)]
    FIRST_ARRAY_INITIALIZATIONS.with(|count| count.set(initialized));
    let array: Rc<[T; N]> = match array.try_into() {
        Ok(array) => array,
        Err(_) => unreachable!("first array has N elements"),
    };
    arrays.push(Rc::clone(&array));
    array
}

/// The first retained array of the thread, shared and never read or written
/// by the caller: a pool that keeps everything in its ladder still has to
/// hold an array of the type. Only a thread that has none yet creates one
/// (a later exclusive lease then takes it). One list read.
pub(crate) fn placeholder_first_array<T, const N: usize>(
    arrays: &RefCell<Vec<Rc<[T; N]>>>,
    init: impl FnMut() -> T,
) -> Rc<[T; N]> {
    if let Some(array) = arrays.borrow().first() {
        return Rc::clone(array);
    }
    lease_first_array(arrays, init)
}

impl TypeNodes {
    // Smaller measured arrays exceed the 0.2% instruction budget versus 65536.
    const FIRST_LEN: usize = 1 << 16;
    const FIRST_CHUNK_BITS: u32 = 8;
    /// Chunk `k` holds `1 << (FIRST_CHUNK_BITS + k)` nodes; together the
    /// chunks cover every index a `TypeExprRef` can hold.
    const CHUNKS: usize = 32 - Self::FIRST_CHUNK_BITS as usize;

    /// One thread-local acquisition and at most one reference-count probe per
    /// retained array. Reuse initializes no nodes; a fresh lease initializes
    /// FIRST_LEN nodes and appends one Rc to the list (amortized O(1)).
    pub(crate) fn new() -> Self {
        let first = FIRST_NODE_ARRAYS.with(|arrays| {
            lease_first_array(arrays, || TypeNode {
                desc: Cell::new(TypeDesc::Tnil),
                level: Cell::new(0),
                id: Cell::new(0),
            })
        });
        TypeNodes {
            first,
            fast_limit: Cell::new(Self::FIRST_LEN as u32),
            chunks: std::array::from_fn(|_| std::cell::OnceCell::new()),
            len: Cell::new(0),
            start: 0,
        }
    }

    /// A store whose nodes are all in the ladder, which grows from 256
    /// nodes: for a short-lived context that creates few nodes (a view
    /// build's scratch context), where a first array of its own would be
    /// 2 MB initialised per thread and kept. Its indices start at
    /// `FIRST_LEN`, so every read takes the far path and the first array it
    /// holds is never touched. One list read; initialises no node.
    pub(crate) fn ladder_only() -> Self {
        let first = FIRST_NODE_ARRAYS.with(|arrays| {
            placeholder_first_array(arrays, || TypeNode {
                desc: Cell::new(TypeDesc::Tnil),
                level: Cell::new(0),
                id: Cell::new(0),
            })
        });
        TypeNodes {
            first,
            fast_limit: Cell::new(Self::FIRST_LEN as u32),
            chunks: std::array::from_fn(|_| std::cell::OnceCell::new()),
            len: Cell::new(Self::FIRST_LEN),
            start: Self::FIRST_LEN,
        }
    }

    /// Chunk and offset of node `idx`.
    #[inline(always)]
    fn locate(idx: usize) -> (usize, usize) {
        let biased = idx + (1 << Self::FIRST_CHUNK_BITS);
        let bit = (usize::BITS - 1 - biased.leading_zeros()) as usize;
        (bit - Self::FIRST_CHUNK_BITS as usize, biased - (1 << bit))
    }

    /// One comparison excludes tagged handles, far nodes and active store builds.
    /// The mask makes the array bound explicit without a second runtime check.
    /// Cost: O(1), one limit comparison and, on success, one indexed address;
    /// no allocation, reference-count update or thread-local access.
    #[inline(always)]
    fn direct(&self, raw: u32) -> Option<&TypeNode> {
        if raw < self.fast_limit.get() {
            Some(&self.first[raw as usize & (Self::FIRST_LEN - 1)])
        } else {
            None
        }
    }

    /// Cost: O(1), select the limit and write one Cell; no node traversal.
    fn set_direct(&self, on: bool) {
        self.fast_limit.set(if on { Self::FIRST_LEN as u32 } else { 0 });
    }

    /// Node `idx` (a local index or a store index with the tag stripped).
    #[inline(always)]
    fn node(&self, idx: usize) -> &TypeNode {
        if idx < Self::FIRST_LEN {
            return &self.first[idx];
        }
        self.node_far(idx)
    }

    /// Cost: O(1), one chunk calculation and two indexed loads, no traversal
    /// or allocation. Kept out of line because first-array reads dominate.
    #[cold]
    #[inline(never)]
    fn node_far(&self, idx: usize) -> &TypeNode {
        let (chunk, offset) = Self::locate(idx - Self::FIRST_LEN);
        &self.chunks[chunk]
            .get()
            .expect("type node index refers to an unallocated chunk")[offset]
    }

    #[inline]
    pub(crate) fn desc(&self, idx: usize) -> TypeDesc {
        self.node(idx).desc.get()
    }

    #[inline]
    pub(crate) fn set_desc(&self, idx: usize, desc: TypeDesc) {
        self.node(idx).desc.set(desc);
    }

    #[inline]
    pub(crate) fn level(&self, idx: usize) -> i32 {
        self.node(idx).level.get()
    }

    #[inline]
    pub(crate) fn set_level(&self, idx: usize, level: i32) {
        self.node(idx).level.set(level);
    }

    #[cfg(test)]
    fn id(&self, idx: usize) -> i32 {
        self.node(idx).id.get()
    }

    /// Append a node and return its index.
    pub(crate) fn push(&self, desc: TypeDesc, level: i32, id: i32) -> usize {
        let idx = self.len.get();
        let node = if idx < Self::FIRST_LEN {
            &self.first[idx]
        } else {
            let (chunk, offset) = Self::locate(idx - Self::FIRST_LEN);
            &self.chunks[chunk].get_or_init(|| {
                (0..1usize << (Self::FIRST_CHUNK_BITS as usize + chunk))
                    .map(|_| TypeNode {
                        desc: Cell::new(TypeDesc::Tnil),
                        level: Cell::new(0),
                        id: Cell::new(0),
                    })
                    .collect()
            })[offset]
        };
        node.desc.set(desc);
        node.level.set(level);
        node.id.set(id);
        self.len.set(idx + 1);
        idx
    }

    /// One past the last node's index.
    pub(crate) fn len(&self) -> usize {
        self.len.get()
    }

    /// Number of nodes.
    pub(crate) fn count(&self) -> usize {
        self.len.get() - self.start
    }
}

/// A compilation's own type nodes. With the compiler counters on, their
/// number is reported when the compilation is dropped.
struct OwnTypeNodes(TypeNodes, Cell<bool>);

impl Deref for OwnTypeNodes {
    type Target = TypeNodes;
    fn deref(&self) -> &TypeNodes {
        &self.0
    }
}

impl Drop for OwnTypeNodes {
    fn drop(&mut self) {
        if self.1.get() && crate::perf_counters::enabled() {
            crate::perf_counters::record_local_type_nodes(self.0.count());
        }
    }
}

/// The compiler counters of a context's probes (see
/// [`crate::perf_counters::AttemptCounters`]): allocated on the first probe
/// with the counters enabled, never otherwise. A context that is not a
/// deferred unit attempt publishes them when flushed or dropped; a deferred
/// one publishes them only when kept, so a discarded attempt publishes
/// nothing.
#[derive(Default)]
struct ContextCounters {
    local: RefCell<Option<Box<crate::perf_counters::AttemptCounters>>>,
    deferred: Cell<bool>,
}

impl ContextCounters {
    /// Add the held counts to the process totals and start again from
    /// zero. O(size of the counts' maps); nothing when no probe ran.
    fn publish(&self) {
        if let Some(counts) = self.local.borrow_mut().take() {
            counts.publish();
        }
    }
}

impl Drop for ContextCounters {
    fn drop(&mut self) {
        if !self.deferred.get() {
            self.publish();
        }
    }
}

/// A type descriptor read by value. `TypeDesc` is `Copy`, so a reader never
/// holds a borrow of the node store; the lifetime only ties the copy to the
/// context it was read from.
pub struct TypeDescRef<'a>(TypeDesc, std::marker::PhantomData<&'a ()>);

impl Deref for TypeDescRef<'_> {
    type Target = TypeDesc;
    #[inline]
    fn deref(&self) -> &TypeDesc {
        &self.0
    }
}

/// `Cmt_utils.deprecated_used_context`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeprecatedContext {
    /// The deprecated function is called.
    FunctionCall,
    /// The deprecated item is referenced without a call.
    Reference,
}

/// `Cmt_utils.deprecated_used`: a use of a deprecated item, saved in the
/// `.cmt` for `rescript-tools migrate`.
#[derive(Debug, Clone)]
pub struct DeprecatedUse {
    /// Where the item is used.
    pub source_loc: crate::location::Location,
    /// The deprecation message.
    pub text: String,
    /// The `migrate` template expression, marshalled.
    pub migrate: Option<crate::binary_ast::marshal::MarshalFragment>,
    /// The `migrateInPipeChain` template expression, marshalled.
    pub migrate_in_pipe_chain: Option<crate::binary_ast::marshal::MarshalFragment>,
    /// How the item is used, when that matters for migration.
    pub context: Option<DeprecatedContext>,
}

/// Cloned snapshot of a type descriptor, for cases where the caller
/// needs to hold the desc while also mutating the same type node.
pub struct TypeDescSnapshot(TypeDesc);

impl TypeDescSnapshot {
    /// The copied descriptor itself.
    #[inline]
    pub fn into_desc(self) -> TypeDesc {
        self.0
    }
}

impl Deref for TypeDescSnapshot {
    type Target = TypeDesc;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Cursor into the OCaml-style type mutation trail.
pub(crate) struct TypeMutationSnapshot<'a> {
    journal: &'a RefCell<TypeMutationJournal>,
    logging: &'a TrailLogging,
    cursor: usize,
    id: u64,
    restored: bool,
}

impl Drop for TypeMutationSnapshot<'_> {
    /// Commit this snapshot's mutations. Entries remain available to any
    /// enclosing snapshot and are discarded once no snapshots are active.
    fn drop(&mut self) {
        if self.restored {
            return;
        }
        let mut journal = self.journal.borrow_mut();
        journal.finish(self.id);
        self.logging.update(&journal);
    }
}

/// Which mutations the trail logs, derived from the live snapshots.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum TrailMode {
    /// No snapshot lives.
    #[default]
    Off,
    /// Only `undo_compress` snapshots live: log path compressions.
    CompressOnly,
    /// A full snapshot lives: log every change, path compressions included.
    Full,
}

#[derive(Default)]
struct TrailLogging(Cell<TrailMode>);

impl TrailLogging {
    fn update(&self, journal: &TypeMutationJournal) {
        self.0.set(if journal.active.iter().any(|snapshot| snapshot.full) {
            TrailMode::Full
        } else if journal.active.is_empty() {
            TrailMode::Off
        } else {
            TrailMode::CompressOnly
        });
    }

    /// Every change is logged.
    fn full(&self) -> bool {
        self.0.get() == TrailMode::Full
    }

    /// Path compressions are logged.
    fn compress(&self) -> bool {
        self.0.get() != TrailMode::Off
    }
}

#[derive(Clone, Copy)]
struct ActiveTypeSnapshot {
    id: u64,
    /// `false` for a snapshot only used by `undo_compress`, which reads the
    /// path compressions logged since it.
    full: bool,
    type_len: usize,
    row_field_len: usize,
}

impl ActiveTypeSnapshot {
    /// Nodes allocated since the snapshot are dropped with it; worker-store
    /// and shared nodes always predate it.
    fn records_type(self, ty: TypeExprRef) -> bool {
        ty.is_store() || ty.index() < self.type_len
    }

    fn records_row_field(self, row: RowFieldRef) -> bool {
        row.is_store() || row.index() < self.row_field_len
    }
}

/// btype.ml `type_copy_session`: temporary writes a graph copy makes to the
/// source mutability cells, restored when the session ends. (`Tsubst` marks
/// are kept in the Rust copiers' caches instead of on the source nodes.)
#[derive(Default)]
struct CopySession {
    saved_mutabilities: Vec<(MutabilityRef, Option<FieldMutability>)>,
    new_mutabilities: Vec<MutabilityRef>,
    copy_policy_memo: crate::fast_hash::AHashMap<TypeExprRef, bool>,
}

/// A cell in the immutable graph whose value this compilation replaced.
#[derive(Clone, Copy)]
enum FrozenCell {
    Desc(TypeExprRef),
    Level(TypeExprRef),
    Memo(AbbrevMemoRef),
    RowField(RowFieldRef),
    Mutability(MutabilityRef),
}

#[derive(Default)]
struct FrozenWrites {
    any: Cell<bool>,
    descs: RefCell<crate::fast_hash::AHashMap<TypeExprRef, TypeDesc>>,
    levels: RefCell<crate::fast_hash::AHashMap<TypeExprRef, i32>>,
    memos: RefCell<crate::fast_hash::AHashMap<AbbrevMemoRef, AbbrevMemo>>,
    row_fields: RefCell<crate::fast_hash::AHashMap<RowFieldRef, Option<RowField>>>,
    mutabilities: RefCell<crate::fast_hash::AHashMap<MutabilityRef, FieldMutability>>,
    #[cfg(test)]
    probes: Cell<usize>,
}

impl FrozenWrites {
    #[inline]
    fn probe(&self) {
        #[cfg(test)]
        self.probes.set(self.probes.get() + 1);
    }

    fn contains(&self, cell: FrozenCell) -> bool {
        if !self.any.get() {
            return false;
        }
        match cell {
            FrozenCell::Desc(r) => self.descs.borrow().contains_key(&r),
            FrozenCell::Level(r) => self.levels.borrow().contains_key(&r),
            FrozenCell::Memo(r) => self.memos.borrow().contains_key(&r),
            FrozenCell::RowField(r) => self.row_fields.borrow().contains_key(&r),
            FrozenCell::Mutability(r) => self.mutabilities.borrow().contains_key(&r),
        }
    }

    fn is_empty(&self) -> bool {
        self.descs.borrow().is_empty() && self.levels.borrow().is_empty()
            && self.memos.borrow().is_empty() && self.row_fields.borrow().is_empty()
            && self.mutabilities.borrow().is_empty()
    }

    fn remove(&self, cell: FrozenCell) {
        match cell {
            FrozenCell::Desc(r) => { self.descs.borrow_mut().remove(&r); }
            FrozenCell::Level(r) => { self.levels.borrow_mut().remove(&r); }
            FrozenCell::Memo(r) => { self.memos.borrow_mut().remove(&r); }
            FrozenCell::RowField(r) => { self.row_fields.borrow_mut().remove(&r); }
            FrozenCell::Mutability(r) => { self.mutabilities.borrow_mut().remove(&r); }
        }
        self.any.set(!self.is_empty());
    }
}

enum TypeMutation {
    FrozenAbsent(FrozenCell),
    TypeDesc(TypeExprRef, TypeDesc),
    /// btype.ml `Ccompress (ty, old_desc, Tlink target)`: path compression by
    /// `repr`, logged whatever the node's age.
    Compress(TypeExprRef, TypeDesc, TypeExprRef),
    TypeLevel(TypeExprRef, i32),
    RowField(RowFieldRef, Option<RowField>),
    /// btype.ml `Cmutability (r, old)`.
    Mutability(MutabilityRef, FieldMutability),
    CurrentAbbreviations(AbbrevMemoRef),
    CurrentLevel(i32),
    NongenLevel(i32),
    GlobalLevel(i32),
    SavedLevels(Vec<(i32, i32)>),
}


#[derive(Default)]
struct TypeMutationJournal {
    entries: Vec<TypeMutation>,
    active: Vec<ActiveTypeSnapshot>,
    next_id: u64,
    #[cfg(test)]
    logged_writes: usize,
}

impl TypeMutationJournal {
    /// Amortized O(1): append one mutation to the existing journal buffer.
    #[inline]
    fn push(&mut self, mutation: TypeMutation) {
        #[cfg(test)]
        {
            self.logged_writes += 1;
        }
        self.entries.push(mutation);
    }

    fn finish(&mut self, id: u64) {
        if let Some(index) = self.active.iter().position(|snapshot| snapshot.id == id) {
            self.active.remove(index);
        }
        if self.active.is_empty() {
            self.entries.clear();
        }
    }

    fn records_type(&self, ty: TypeExprRef) -> bool {
        self.active
            .last()
            .is_some_and(|snapshot| snapshot.records_type(ty))
    }

    fn records_row_field(&self, row: RowFieldRef) -> bool {
        self.active
            .last()
            .is_some_and(|snapshot| snapshot.records_row_field(row))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct QualifiedModuleComponentsCacheKey {
    // OCaml compiler/ml/path.ml:20-24 ignores `Pdot` positions in
    // `Path.same`; component lookup in env.ml:781-793 keys module identity by
    // that path equality while still carrying positions in the selected access
    // path. `SamePathKey` compares and hashes with that equality directly.
    path: SamePathKey,
    env_id: Option<ScopeId>,
}

impl QualifiedModuleComponentsCacheKey {
    pub(crate) fn new(path: Path, env_id: Option<ScopeId>) -> Self {
        Self {
            path: SamePathKey(path),
            env_id,
        }
    }

    /// Whether the view for this key is the same in every compilation: a
    /// path rooted at a persistent unit, not scoped to one environment.
    pub(crate) fn is_worker_shareable(&self) -> bool {
        fn persistent_root(path: &Path) -> bool {
            match path.view() {
                PathView::Pident(id) => id.is_persistent(),
                PathView::Pdot(parent, _, _) => persistent_root(parent),
                PathView::Papply(_, _) => false,
            }
        }
        self.env_id.is_none() && persistent_root(&self.path.0)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RecordLabelDescriptionSummary {
    label_positions: Arc<crate::fast_hash::AHashMap<crate::name::Name, usize>>,
    pub(crate) mandatory_count: usize,
    pub(crate) has_optional: bool,
}

impl RecordLabelDescriptionSummary {
    pub(crate) fn from_labels(labels: &[super::decl::LabelDescription]) -> Self {
        let mut label_positions = crate::fast_hash::AHashMap::with_capacity(labels.len());
        let mut mandatory_count = 0;
        let mut has_optional = false;

        for (idx, label) in labels.iter().enumerate() {
            label_positions.insert(label.lbl_name, idx);
            if label.lbl_optional {
                has_optional = true;
            } else {
                mandatory_count += 1;
            }
        }

        Self {
            label_positions: Arc::new(label_positions),
            mandatory_count,
            has_optional,
        }
    }

    #[inline]
    pub(crate) fn label_index(&self, name: impl crate::name::NameKey) -> Option<usize> {
        self.label_positions.get(&name.name_key()?).copied()
    }

    #[inline]
    pub(crate) fn contains_label(&self, name: impl crate::name::NameKey) -> bool {
        name.name_key()
            .is_some_and(|name| self.label_positions.contains_key(&name))
    }
}

/// The refs captured by an `Env.open_signature` `using` callback.
#[derive(Debug, Clone)]
pub(crate) struct OpenSlotState {
    /// The open's location (warnings 44/45 are reported there).
    pub loc: crate::parse_arena::LocIdx,
    /// `used_slot`.
    pub used: bool,
    /// `shadowed`: the `(kind, name)` pairs already reported.
    pub shadowed: Vec<(&'static str, String)>,
}

#[derive(Debug, Clone)]
/// A side effect of an `Env` lookup that OCaml performs during the lookup
/// itself and Rust replays, in call order, when the lookup events drain.
pub(crate) enum LookupEvent {
    /// A `using name shadowed` call of an open's slot (env.ml:1847-1861).
    OpenSlot(OpenSlotEvent),
    /// `report_deprecated ?loc p deprecated` (env.ml:989-994).
    ModuleDeprecated(ModuleDeprecation),
}

#[derive(Debug, Clone)]
/// The module whose `deprecated` flag `report_deprecated` checks.
pub(crate) enum ModuleDeprecation {
    /// A module resolved in the lookup environment: `Path.name p` and the
    /// `deprecated_of_attrs md_attributes` of its declaration.
    Resolved {
        loc: crate::parse_arena::LocIdx,
        name: String,
        deprecated: String,
    },
    /// A module inside a persistent unit, reached through the submodules of
    /// `target` (none for the unit itself, whose flag is `ps_comps`'
    /// `Deprecated` persistence flag). Resolved once the lookup has loaded
    /// the unit, without forcing a load.
    Persistent {
        loc: crate::parse_arena::LocIdx,
        /// The path whose `Path.name` reports the module.
        name: crate::types::path::Path,
        /// The module's path from the unit's persistent identifier.
        target: crate::types::path::Path,
    },
}

/// One `using name shadowed` call.
#[derive(Debug, Clone)]
pub(crate) struct OpenSlotEvent {
    pub slot: u32,
    /// The `Env.check_shadowing` kind.
    pub kind: &'static str,
    pub name: String,
    /// Whether `check_shadowing` returns `Some kind`.
    pub shadowed: bool,
}

/// A saved position: resolved file name (or raw handle), line, bol, cnum.
type PositionKey = (Result<u32, String>, i32, i32, i32);

/// A compilation-local signature and its component-table name index.
type IndexedSignature = (
    Arc<super::decl::Signature>,
    Arc<super::env_lazy::SignatureIndex>,
);

/// A module's values by name: each value's path and declaration.
type ResolvedModuleValues =
    crate::fast_hash::AHashMap<String, (Path, Arc<super::decl::ValueDescription>)>;

/// A module's types by name: each type's path, identifier and declaration.
type ResolvedModuleTypes =
    crate::fast_hash::AHashMap<String, (Path, Ident, Arc<super::decl::TypeDeclaration>)>;

/// A module's submodules by name: each one's identifier and declaration.
type ModuleDeclarations =
    crate::fast_hash::AHashMap<String, (Ident, Arc<super::decl::ModuleDeclaration>)>;

/// A dotted type path resolved to its identifier and declaration.
type ResolvedTypeItem = (Ident, Arc<super::decl::TypeDeclaration>);

/// Resolved signatures keyed by their spelling and optional module scope.
type ResolvedModuleSignatures = hashbrown::HashMap<
    (String, Option<ScopeId>),
    (Path, Arc<super::decl::Signature>),
    crate::fast_hash::FastState,
>;

/// `raw_lambda::typeopt` answers by environment, type and query.
type TypeoptAnswers = crate::fast_hash::AHashMap<(EnvId, TypeExprRef, u8), bool>;

/// OCaml `Ctype.reified_var_counter_key`: the next index for each base
/// name, and the names already given.
#[derive(Default)]
pub(crate) struct ReifiedNames {
    counters: crate::fast_hash::AHashMap<String, usize>,
    used: crate::fast_hash::AHashSet<String>,
}

/// Diagnostic preparation policy, fixed for one whole-unit check attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum CheckMode {
    /// Skip diagnostic-only snapshots outside live speculation.
    Success,
    /// Preserve the original diagnostic preparation for every unification.
    Explain,
}

/// Type checking context.
///
/// This context is created for each type checking session (typically one
/// per source file). It owns all type expressions and maintains the state
/// needed for type inference.
///
/// # Example
///
/// ```rust,ignore
/// use rescript_compiler::types::TypeContext;
/// use rescript_compiler::context::IdGenerator;
///
/// let id_gen = IdGenerator::new();
/// let mut ctx = TypeContext::new(std::sync::Arc::new(id_gen));
///
/// // Create a type variable
/// let tvar = ctx.new_var(None);
///
/// // Create an arrow type
/// let int_type = ctx.new_constr(path_int, vec![]);
/// let func_type = ctx.new_arrow_simple(tvar, int_type);
/// ```
pub struct TypeContext {
    /// ID generator for type IDs.
    /// Owned by `Arc` so the context can outlive its caller and live in
    /// thread-local worker storage (where a borrow can't be expressed).
    id_gen: Arc<IdGenerator>,
    /// Current generalization level
    current_level: Cell<i32>,

    /// Non-generalizable level
    nongen_level: Cell<i32>,

    /// Global level
    global_level: Cell<i32>,

    /// Saved levels stack
    saved_levels: RefCell<Vec<(i32, i32)>>,

    /// GADT instance tracking flag
    trace_gadt_instances: Cell<bool>,
    /// `Ctype.passive_variants` (ctype.ml:2060).
    passive_variants: Cell<bool>,
    /// `Ctype.rigid_variants` (ctype.ml:2013), set by `expand_head_rigid`.
    rigid_variants: Cell<bool>,

    /// Dedicated memo ref for OCaml's simple_abbrevs (nullary, non-object
    /// abbreviations). This points to a mutable AbbrevMemo cell.
    simple_abbrevs: Cell<AbbrevMemoRef>,
    /// OCaml `Ctype.reified_var_counter_key`, for `get_new_abstract_name`
    /// when reifying local GADT constraint variables.
    reified_var_counters: RefCell<ReifiedNames>,
    /// OCaml `Ctype.existential_constructors_key` (ctype.ml:936-944): the
    /// constructor binding each existential type `instance_constructor`
    /// created in this compilation, by the stamp of its identifier.
    existential_constructors: RefCell<crate::fast_hash::AHashMap<i32, crate::name::Name>>,
    /// Previous env ID for check_abbrev_env (OCaml ctype.ml:1272)
    previous_env_id: Cell<Option<EnvId>>,

    /// Current abbreviation context during subst (OCaml: abbreviations = ref (ref Mnil)).
    /// Set during subst_with_memo so copy_type_cached can use find_repr to detect
    /// previously-expanded types and create Tlink sharing.
    current_abbreviations: Cell<AbbrevMemoRef>,

    /// Type expression storage. Uses UnsafeCell-based arena for zero-copy access.
    types: OwnTypeNodes,

    /// Exclusive lease of the worker's persistent arena for this compilation.
    /// Returned on drop; overlapping contexts get independent stores.
    store: super::thread_store::StoreLease,
    /// Type lists (`TypeRefList`) allocated by this compilation.
    type_lists: super::type_expr::TypePayloadPool,
    frozen_writes: FrozenWrites,
    /// Direct handle to the shared pool's page table for node reads. Never
    /// borrowed mutably: the `RefCell` only lets shared descriptor borrows be
    /// `Ref`s like local ones (`Ref::map`), so callers see one borrow type.
    shared_pages: super::shared_store::SharedPages,

    /// Nesting depth of `build_in_store`; allocations go to the worker store
    /// while it is non-zero.
    store_build_depth: Cell<u32>,
    /// Store arena lengths when the outermost store build started: nodes and
    /// row fields at or above these are still being built and are written in
    /// place.
    store_build_type_start: Cell<usize>,
    store_build_row_start: Cell<usize>,
    /// Memo ownership boundary used only by the frozen-write counters.
    store_build_abbrev_start: Cell<usize>,
    /// The current store build read compilation-local state, so its result
    /// must stay private to this compilation.
    store_build_poisoned: Cell<bool>,
    /// Effects of the current store build on this compilation.
    store_build_effects: RefCell<Vec<StoreEffect>>,
    /// Guards of the current store build (see `StorePiece::guards`).
    store_build_guards: RefCell<Vec<(Path, bool)>>,
    /// Shared pieces whose effects this compilation has already applied.
    touched_store_pieces: RefCell<crate::fast_hash::AHashSet<u64>>,
    /// Component tables of store-resident modules whose build read state
    /// private to this compilation, so they could not be published to the
    /// worker store. Keyed by `StoredModuleComponents` id; reused for the rest
    /// of this compilation instead of being rebuilt on every lookup.
    local_stored_components:
        RefCell<crate::fast_hash::AHashMap<u64, Rc<super::env_lazy::QualifiedModuleComponents>>>,
    /// OCaml-shaped mutation trail. Logging is dormant unless a snapshot lives.
    mutation_journal: RefCell<TypeMutationJournal>,
    mutation_logging: TrailLogging,
    /// The diagnostic policy fixed when preparing this unit.
    explain_mode: Cell<CheckMode>,
    /// A unification failed on the success path without its snapshot: the
    /// unit must be checked again in the explaining mode.
    unexplained_unify_failure: Cell<bool>,

    /// Cached value of `RESCRIPT_COMPILER_COUNTERS` for hot-path probes.
    compiler_counters_enabled: bool,
    attempt_counters: ContextCounters,

    /// Abbreviation memo storage
    abbrevs: RefCell<Vec<RefCell<AbbrevMemo>>>,
    /// Refs that have been written via memorize_abbrev_expansion since the
    /// last cleanup. Mirrors OCaml btype.ml `memo` list used by cleanup_abbrev.
    memoized_abbrev_refs: RefCell<Vec<AbbrevMemoRef>>,

    /// `full_expand` results recorded when a top-level unification fails,
    /// OCaml's `expand_trace` (ctype.ml:1601-1605, 2589-2594). Error reports
    /// print "(defined as ...)" from these.
    trace_expansions: RefCell<crate::fast_hash::AHashMap<TypeExprRef, TypeExprRef>>,

    /// State of the `used_slot`/`shadowed` refs captured by
    /// `Env.open_signature`'s `using` callbacks (env.ml:1835-1864), indexed
    /// by the slot id stored in opened environment layers.
    open_slots: RefCell<Vec<OpenSlotState>>,

    /// `using` calls made by lookups, processed by the type checker with the
    /// warning state current at the lookup.
    open_slot_events: RefCell<Vec<LookupEvent>>,

    /// OCaml `Env`'s usage tables (env.ml:27-53).
    usage: RefCell<super::usage::UsageTables>,

    /// Effects that signatures of this compilation require of the values
    /// matched against them (`crate::verify::purity`). Empty unless a
    /// signature declares `@pure` or `@mutates`.
    effect_obligations: RefCell<Vec<crate::verify::purity::Obligation>>,

    /// Locations of declarations and type labels this compilation built with
    /// coordinates (`DeclLocKind::Local` handles; see `types::decl_loc`).
    /// Empty for a location-free compilation, whose locations fit in their
    /// handles.
    decl_locs: super::decl_loc::OwnedDeclLocs,
    decl_loc_owner: u32,
    next_identity_scope: Cell<u32>,
    location_namespace: Cell<Option<u64>>,

    /// Parser warnings of the snippets error reports re-parse
    /// (`Error_message_utils.Parser.parse_source`), printed before the error
    /// like OCaml's immediate `Location.prerr_warning`.
    reparse_warnings: RefCell<Vec<crate::parser::ParserWarning>>,
    /// The warning state outside the implementation's structure, which is
    /// current when an error is reported (`Typemod.type_structure`'s
    /// `warning_scope` has been left).
    report_warning_config: RefCell<Option<crate::diagnostics::WarningConfig>>,

    /// Stable forward references for canonical variant layouts. Entries are
    /// allocated before translating a recursive declaration group and completed
    /// exactly once after the group is available in the environment.
    variant_layouts: RefCell<Vec<RefCell<super::variant_runtime::LayoutState>>>,

    /// Row field storage
    row_fields: RefCell<Vec<RefCell<Option<RowField>>>>,

    /// Object-field mutability cells of this compilation's graph.
    mutabilities: RefCell<Vec<Cell<FieldMutability>>>,
    /// btype.ml `type_copy_sessions`: the active graph-copy sessions,
    /// innermost last.
    copy_sessions: RefCell<Vec<CopySession>>,
    /// With the compiler counters on: the type nodes already counted as
    /// copied for some cause (see `counted_copy`).
    counted_copy_nodes: Cell<usize>,
    /// With the compiler counters on: the next call of a counted function
    /// is the counting code calling it again (see `counts_this_call`).
    counted_call_reentered: Cell<bool>,

    /// Cache for resolved module signatures. Keyed by module path name.
    /// OCaml `compiler/ml/env.ml:1513-1514,1516-1588` stores forced module
    /// components behind lazy cells; cache hits share the already-substituted
    /// signature snapshot instead of cloning every `SignatureItem`.
    resolved_module_sig_cache: RefCell<ResolvedModuleSignatures>,

    /// Cached qualified module-component views keyed by access-path semantics.
    /// This is the Rust analogue of OCaml's lazy `components_of_module_maker`.
    qualified_module_components_cache: RefCell<
        crate::fast_hash::AHashMap<
            QualifiedModuleComponentsCacheKey,
            super::env_lazy::HeldComponents,
        >,
    >,
    /// By view id, the child modules (by signature item, one bit each) whose
    /// forced declaration this compilation has registered
    /// (`note_forced_view_module`).
    noted_view_modules: RefCell<Vec<Vec<u64>>>,
    /// Views this compilation adopted (`adopt_view` calls that were not
    /// already answered by the component cache).
    #[cfg(test)]
    pub(crate) view_adoptions: Cell<u64>,

    /// Module alias source paths discovered while building component tables.
    ///
    /// OCaml compiler/ml/env.ml:1517 scrapes `Mty_alias`/`Mty_ident` through
    /// `find_module`, and env.ml:1530-1578 stores component thunks under the
    /// selected path returned by `prefix_idents`. This relation keeps that
    /// declaration-derived source path available when Rust later reaches a
    /// cached component view without `PersistentEnv`; it must not be inferred
    /// from flattened module-name spelling.
    component_alias_sources: RefCell<crate::fast_hash::AHashMap<SamePathKey, AliasPaths>>,
    /// Component-table name indexes of the signatures this compilation has
    /// indexed (a unit's comes from the world), keyed by address; the entry
    /// keeps the signature alive so the key stays unique.
    signature_indexes: RefCell<crate::fast_hash::AHashMap<usize, IndexedSignature>>,
    component_paths_by_alias_source: RefCell<crate::fast_hash::AHashMap<SamePathKey, AliasPaths>>,

    /// Cached dotted value lookups keyed by resolved module access path.
    resolved_module_value_cache: RefCell<crate::fast_hash::AHashMap<Path, ResolvedModuleValues>>,

    /// Cached dotted type lookups keyed by resolved module access path.
    /// Keyed by env id as well: OCaml's Env is persistent, so a binding can
    /// never change under an existing path, but Rust's Env is mutated in
    /// place (`add_module`) and must invalidate these derived entries.
    resolved_module_type_cache: RefCell<ScopedPathMap<ResolvedModuleTypes>>,

    /// Cached child-module access paths keyed by resolved parent access path.
    resolved_child_module_path_cache:
        RefCell<crate::fast_hash::AHashMap<Path, crate::fast_hash::AHashMap<String, Path>>>,

    /// Forced declarations shared by persistent/global alias component views.
    /// Local component views keep their own thunk state in StructureComponentTables.
    qualified_module_decl_cache: RefCell<crate::fast_hash::AHashMap<Path, ModuleDeclarations>>,

    /// Resolved dotted type paths keyed by `Env::scope_id`, path, and whether
    /// alias targets were strengthened (see `ctype::resolve_type_item_through_env`).
    resolved_type_item_cache: RefCell<
        hashbrown::HashMap<(ScopeId, Path, bool), ResolvedTypeItem, crate::fast_hash::FastState>,
    >,

    /// Cached full normalize_path results keyed by environment identity.
    normalized_path_full_cache: RefCell<ScopedPathMap<Arc<super::ctype::NormRecipe>>>,
    /// Answers of `raw_lambda::typeopt` queries while the finished typed tree
    /// is lowered (`None` outside that phase): the types no longer change.
    typeopt_answers: RefCell<Option<TypeoptAnswers>>,
    /// Outcome of expanding a `Pdot`-headed constructor, per module scope
    /// (see `ctype::PdotExpansion`).
    pdot_expansions: RefCell<
        hashbrown::HashMap<
            PdotExpansionKey,
            super::ctype::PdotExpansion,
            crate::fast_hash::FastState,
        >,
    >,

    /// Cached forward-only (unification) normalize_path results, keyed like
    /// `normalized_path_full_cache`.
    normalized_path_forward_cache: RefCell<ScopedPathMap<Arc<super::ctype::NormRecipe>>>,

    /// `occur_univar` argument masks per (scope, constructor path): bit `i`
    /// is set when argument `i` has a may-positive or may-negative variance;
    /// `None` when the declaration is not found (every argument is visited).
    occur_variance_masks: RefCell<ScopedPathMap<Option<u64>>>,

    /// `Ctype.get_level` declaration levels per (scope, type path): the
    /// `type_newtype_level` of the declaration `Env.find_type` returns.
    type_newtype_levels: RefCell<ScopedPathMap<Option<i32>>>,

    /// Cached side-effectful normalize_path results keyed by environment identity.
    forced_normalized_path_full_cache: RefCell<ScopedPathMap<Arc<super::ctype::NormRecipe>>>,

    /// Cached side-effectful type-path comparisons keyed by environment identity.
    forced_type_path_compare_cache:
        RefCell<hashbrown::HashMap<(ScopeId, Path, Path), bool, crate::fast_hash::FastState>>,

    /// Load paths for resolving CMI files during type alias expansion.
    load_paths: RefCell<Arc<Vec<std::path::PathBuf>>>,

    /// In-process persistent environment used by abbreviation expansion when a
    /// persistent module root is not present in the local Env. OCaml resolves
    /// persistent Pident module heads through Env.find_module_descr before
    /// reading lazy components (compiler/ml/env.ml:800-808,
    /// compiler/ml/env.ml:865-906); this gives Rust ctype the same lookup
    /// source without falling back to disk in in-process builds.
    persistent_env: RefCell<Option<crate::cmi::persistent_env::PersistentEnv>>,

    /// Cache of renamed module signatures.
    /// Matches OCaml's lazy ps_sig = Subst.signature Subst.identity sign.
    /// Populated by PersistentEnv::get_renamed_sig, consumed by normalize_path.
    pub(crate) renamed_module_sigs:
        RefCell<crate::fast_hash::AHashMap<String, Arc<DeferredRenamedSig>>>,

    /// Raw (un-renamed) module signatures for persistent modules.
    /// Used by trigger_module_sig_rename to lazily rename on first access
    /// from normalize_path, matching OCaml's lazy ps_sig forcing.
    raw_module_sigs: RefCell<crate::fast_hash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// Raw signature copies used only by GenType's CMT-shaped alias scraping.
    ///
    /// OCaml GenType reads CMT data and then calls Env.scrape_alias at
    /// compiler/gentype/TranslateStructure.ml:174-183. In-process Rust crosses
    /// TypeContext boundaries through PortablePersStruct, so keep those raw
    /// copied signatures separate from `raw_module_sigs`; typechecking lookup
    /// paths expect the normal component/rename caches, not this CMT view.
    gentype_raw_module_sigs:
        RefCell<crate::fast_hash::AHashMap<String, Arc<super::decl::Signature>>>,
    gentype_portable_raw_module_sigs: RefCell<
        crate::fast_hash::AHashMap<String, Arc<crate::cmi::portable_types::PortablePersStruct>>,
    >,

    /// Raw signatures loaded only for persistent component lookup.
    ///
    /// OCaml keeps `ps_comps` separate from `ps_sig`; this cache gives Rust the
    /// same one-shot component backing store without making the `ps_sig`
    /// rename see modules that were only touched by descriptor lookup.
    raw_component_module_sigs:
        RefCell<crate::fast_hash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// String table for CMI-decoded Longident components.
    /// CMI decoding happens without a ParseArena, so we allocate synthetic
    /// StrIdx values here and resolve them later when needed.
    cmi_longident_names: RefCell<crate::fast_hash::AHashMap<u32, String>>,

    /// String table for ParseArena Longident components whose StrIdx values are
    /// intentionally unique per source occurrence for marshal identity.
    /// Registered arenas' strings in registration order; the first arena
    /// that has an index names it.
    arena_longident_names: RefCell<Vec<crate::intern::InternedStrings>>,

    /// Next synthetic StrIdx raw value for CMI longident strings.
    next_cmi_longident_idx: Cell<u32>,

    /// Cached predef type singletons at generic_level.
    /// Matches OCaml's Predef.type_int etc. which are module-level singletons
    /// created via newgenty at generic_level. Lazily initialized on first use.
    predef_int: Cell<Option<TypeExprRef>>,
    predef_char: Cell<Option<TypeExprRef>>,
    predef_string: Cell<Option<TypeExprRef>>,
    predef_float: Cell<Option<TypeExprRef>>,
    predef_bool: Cell<Option<TypeExprRef>>,
    predef_unit: Cell<Option<TypeExprRef>>,
    predef_exn: Cell<Option<TypeExprRef>>,
    predef_bigint: Cell<Option<TypeExprRef>>,
    predef_option_inner: Cell<Option<TypeExprRef>>,
    predef_option_type: Cell<Option<TypeExprRef>>,
    predef_option_layout: Cell<Option<super::variant_runtime::LayoutRef>>,

    /// Arity update aliases: maps arity-updated TypeExprRef → original TypeExprRef.
    /// OCaml's `{t with desc = Tarrow(..., Some newarity)}` creates a new record
    /// sharing `t.id`, so the sexp serializer deduplicates them. In Rust, we create
    /// separate TypeExprRef nodes but record the alias here so the sexp serializer
    /// can use the original's dedup key.
    arity_aliases: RefCell<crate::fast_hash::AHashMap<TypeExprRef, TypeExprRef>>,


    /// `RecordLabelDescriptionSummary` of each label array, a memo derived
    /// from the array: name positions and optional/mandatory counts used by
    /// record disambiguation.
    label_family_summaries: RefCell<
        crate::fast_hash::AHashMap<super::decl::LabelArrayRef, Arc<RecordLabelDescriptionSummary>>,
    >,


    /// The `lbl_all` arrays of this compilation: `LabelArrayRef(n)` for
    /// `n >= 1` is entry `n - 1`. `Datarepr.label_descrs` allocates one per
    /// described record declaration, and `Dict_pattern.labels_of_keys` one per
    /// dict pattern. Families built in the worker store live in its pool and
    /// are shared with later compilations, hence the `Arc` element.
    label_families: RefCell<Vec<Arc<Vec<super::decl::LabelDescription>>>>,
    /// Set on the scratch context of a view build: binders take store-range
    /// stamps (see `new_scratch`).
    world_scratch: Cell<bool>,

    /// Stored typedtree environment snapshots, keyed by EnvRef.
    typed_envs: RefCell<Vec<Rc<Env>>>,

    /// Reuse EnvRefs for identical logical environments.
    typed_envs_by_id: RefCell<crate::fast_hash::AHashMap<EnvId, EnvRef>>,
    /// `Cmt_format.value_deps` (compiler/ml/cmt_format_common.ml:149-183):
    /// implementation/specification value pairs matched by inclusion checks.
    value_deps: RefCell<Vec<(super::decl::ValueDescription, super::decl::ValueDescription)>>,
    /// `Cmt_format.deprecated_used` (cmt_format_common.ml:152-178).
    deprecated_used: RefCell<Vec<DeprecatedUse>>,
    /// The most recently stored (env id, EnvRef): consecutive typed nodes
    /// usually share their environment.
    last_typed_env: Cell<Option<(EnvId, EnvRef)>>,
}

/// Effect of building shared store data on the state of the compilation that
/// built it. Another compilation that reuses the data replays these effects
/// the first time it touches the data, so its own tables (prepared units,
/// forced renames, alias sources) hold what they would if it had built the
/// data itself. Identifier stamps are not among the effects: binders of
/// store data take stamps of the process-wide store range and leave the
/// compilation's counter alone.
#[derive(Debug, Clone)]
pub(crate) enum StoreEffect {
    /// A shared piece forced while building this one.
    Piece(Rc<StorePiece>),
    /// `PersistentEnv::find_pers_struct` for this unit, which prepares the
    /// module for the compilation on first use.
    PreparePers(smol_str::SmolStr),
}

/// Replay record of one piece of shared store data (see
/// `TypeContext::build_in_store`).
#[derive(Debug)]
pub(crate) struct StorePiece {
    id: u64,
    effects: Vec<StoreEffect>,
    /// Answers the build read from this compilation's alias-source table
    /// (`has_component_paths_for_alias_source`): the alias source and
    /// whether it had registered component paths. A compilation may reuse
    /// the piece only when it gives the same answers
    /// (`TypeContext::store_guards_hold`).
    guards: Vec<(Path, bool)>,
}

pub(crate) fn store_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_STORE_DEBUG").is_some())
}

static NEXT_STORE_PIECE_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

thread_local! {
    /// The piece of every store build with no effects and no guards (id 0;
    /// built pieces count from 1). Pieces stay on their worker thread.
    static EMPTY_STORE_PIECE: Rc<StorePiece> = Rc::new(StorePiece {
        id: 0,
        effects: Vec::new(),
        guards: Vec::new(),
    });
}

/// A map key that compares paths with `Path::same` (ignoring `Pdot`
/// positions and comparing identifiers by stamp, or by name when persistent).
#[derive(Clone, Debug)]
pub(crate) struct SamePathKey(Path);

impl SamePathKey {
    pub(crate) fn new(path: Path) -> Self {
        SamePathKey(path)
    }
}

impl PartialEq for SamePathKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.same(&other.0)
    }
}

impl Eq for SamePathKey {}

impl std::hash::Hash for SamePathKey {
    /// The hash every interned path carries for `Path::same` (`Pdot`
    /// positions ignored): one word, no walk of the path.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.same_hash());
    }
}

/// Key of `TypeContext::pdot_expansions`.
#[derive(PartialEq, Eq, Hash)]
struct PdotExpansionKey {
    scope_id: ScopeId,
    mode: u8,
    arity: usize,
    path: Path,
}

/// Borrowed form of [`PdotExpansionKey`], so lookups do not clone the path.
/// Field order and hashing match the owned key.
#[derive(Hash)]
struct PdotExpansionKeyRef<'a> {
    scope_id: ScopeId,
    mode: u8,
    arity: usize,
    path: &'a Path,
}

impl hashbrown::Equivalent<PdotExpansionKey> for PdotExpansionKeyRef<'_> {
    fn equivalent(&self, key: &PdotExpansionKey) -> bool {
        self.scope_id == key.scope_id
            && self.mode == key.mode
            && self.arity == key.arity
            && *self.path == key.path
    }
}

/// Borrowed signature key; hashing matches the owned tuple without allocating.
#[derive(Hash)]
struct ModuleSignatureKeyRef<'a>(&'a str, Option<ScopeId>);

impl hashbrown::Equivalent<(String, Option<ScopeId>)> for ModuleSignatureKeyRef<'_> {
    fn equivalent(&self, key: &(String, Option<ScopeId>)) -> bool {
        self.0 == key.0 && self.1 == key.1
    }
}

/// Cache keyed by a scope identity and a path, probed without cloning the path.
type ScopedPathMap<V> = hashbrown::HashMap<(ScopeId, Path), V, crate::fast_hash::FastState>;

/// Borrowed form of a `(ScopeId, Path)` key. A tuple struct hashes its fields in
/// order exactly like the owned tuple.
#[derive(Hash)]
struct ScopedPathRef<'a>(ScopeId, &'a Path);

impl hashbrown::Equivalent<(ScopeId, Path)> for ScopedPathRef<'_> {
    fn equivalent(&self, key: &(ScopeId, Path)) -> bool {
        self.0 == key.0 && *self.1 == key.1
    }
}

/// Borrowed form of a `(ScopeId, Path, bool)` key.
#[derive(Hash)]
struct ScopedPathFlagRef<'a>(ScopeId, &'a Path, bool);

impl hashbrown::Equivalent<(ScopeId, Path, bool)> for ScopedPathFlagRef<'_> {
    fn equivalent(&self, key: &(ScopeId, Path, bool)) -> bool {
        self.0 == key.0 && self.2 == key.2 && *self.1 == key.1
    }
}

/// Borrowed form of a `(ScopeId, Path, Path)` key.
#[derive(Hash)]
struct ScopedPathPairRef<'a>(ScopeId, &'a Path, &'a Path);

impl hashbrown::Equivalent<(ScopeId, Path, Path)> for ScopedPathPairRef<'_> {
    fn equivalent(&self, key: &(ScopeId, Path, Path)) -> bool {
        self.0 == key.0 && *self.1 == key.1 && *self.2 == key.2
    }
}

/// The paths related to one path by an alias: almost always one, so kept
/// inline.
type AliasPaths = smallvec::SmallVec<[Path; 2]>;

fn push_unique_path(paths: &mut AliasPaths, path: Path) {
    if !paths.iter().any(|existing| existing.same(&path)) {
        paths.push(path);
    }
}

/// A forced persistent-signature rename whose copy is built on first read.
/// See [`TypeContext::defer_renamed_sig`].
#[derive(Debug)]
pub(crate) struct DeferredRenamedSig {
    kind: &'static str,
    source: Arc<super::decl::Signature>,
    renamed: std::sync::OnceLock<Arc<super::decl::Signature>>,
}

impl super::decl_loc::DeclLocs for TypeContext {
    fn resolve_loc(&self, loc: super::DeclLoc) -> crate::location::Location {
        TypeContext::resolve_loc(self, loc)
    }
}

impl TypeContext {
    /// Create a new type context.
    pub fn new(id_gen: Arc<IdGenerator>) -> Self {
        Self::with_storage(
            id_gen,
            super::thread_store::current(),
            TypeNodes::new(),
            Default::default(),
        )
    }

    /// The scratch context of a view build (`world::ViewScratch`): its
    /// nodes, its lists and its private store are all ladder-only, so
    /// creating one initialises no first array, and its binders take stamps
    /// of the process-wide store range. The private store is dropped with
    /// the context.
    pub(crate) fn new_scratch(id_gen: Arc<IdGenerator>) -> Self {
        let ctx = Self::with_storage(
            id_gen,
            super::thread_store::scratch(),
            TypeNodes::ladder_only(),
            super::type_expr::TypePayloadPool::ladder_only(0),
        );
        ctx.world_scratch.set(true);
        ctx
    }

    fn with_storage(
        id_gen: Arc<IdGenerator>,
        store: super::thread_store::StoreLease,
        types: TypeNodes,
        type_lists: super::type_expr::TypePayloadPool,
    ) -> Self {
        let shared_pages = store.shared_pool().pages();
        TypeContext {
            id_gen,
            current_level: Cell::new(0),
            nongen_level: Cell::new(0),
            global_level: Cell::new(1),
            saved_levels: RefCell::new(Vec::new()),
            trace_gadt_instances: Cell::new(false),
            passive_variants: Cell::new(false),
            rigid_variants: Cell::new(false),
            simple_abbrevs: Cell::new(AbbrevMemoRef(1)),
            reified_var_counters: RefCell::new(ReifiedNames::default()),
            existential_constructors: RefCell::new(crate::fast_hash::AHashMap::new()),
            previous_env_id: Cell::new(None),
            current_abbreviations: Cell::new(AbbrevMemoRef::nil()),
            types: OwnTypeNodes(types, Cell::new(true)),
            frozen_writes: FrozenWrites::default(),
            store,
            type_lists,
            shared_pages,
            store_build_depth: Cell::new(0),
            store_build_type_start: Cell::new(0),
            store_build_row_start: Cell::new(0),
            store_build_abbrev_start: Cell::new(0),
            store_build_poisoned: Cell::new(false),
            store_build_effects: RefCell::new(Vec::new()),
            store_build_guards: RefCell::new(Vec::new()),
            touched_store_pieces: RefCell::new(crate::fast_hash::AHashSet::new()),
            local_stored_components: RefCell::new(crate::fast_hash::AHashMap::new()),
            mutation_journal: RefCell::new(TypeMutationJournal::default()),
            mutation_logging: TrailLogging::default(),
            explain_mode: Cell::new(CheckMode::Explain),
            unexplained_unify_failure: Cell::new(false),
            compiler_counters_enabled: crate::perf_counters::context_enabled(),
            attempt_counters: ContextCounters::default(),
            // Index 0 is reserved as canonical Mnil; index 1 is the dedicated
            // simple_abbrevs memo ref.
            abbrevs: RefCell::new(vec![
                RefCell::new(AbbrevMemo::Mnil),
                RefCell::new(AbbrevMemo::Mnil),
            ]),
            memoized_abbrev_refs: RefCell::new(Vec::new()),
            trace_expansions: RefCell::new(crate::fast_hash::AHashMap::new()),
            open_slots: RefCell::new(Vec::new()),
            open_slot_events: RefCell::new(Vec::new()),
            usage: RefCell::new(super::usage::UsageTables::default()),
            effect_obligations: RefCell::new(Vec::new()),
            decl_locs: Default::default(),
            decl_loc_owner: super::decl_loc::next_table_owner(),
            next_identity_scope: Cell::new(1),
            location_namespace: Cell::new(None),
            reparse_warnings: RefCell::new(Vec::new()),
            report_warning_config: RefCell::new(None),
            variant_layouts: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            mutabilities: RefCell::new(Vec::new()),
            copy_sessions: RefCell::new(Vec::new()),
            counted_copy_nodes: Cell::new(0),
            counted_call_reentered: Cell::new(false),
            resolved_module_sig_cache: RefCell::new(hashbrown::HashMap::default()),
            qualified_module_components_cache: RefCell::new(crate::fast_hash::AHashMap::new()),
            noted_view_modules: RefCell::new(Vec::new()),
            #[cfg(test)]
            view_adoptions: Cell::new(0),
            component_alias_sources: RefCell::new(crate::fast_hash::AHashMap::new()),
            signature_indexes: RefCell::new(crate::fast_hash::AHashMap::new()),
            component_paths_by_alias_source: RefCell::new(crate::fast_hash::AHashMap::new()),
            resolved_module_value_cache: RefCell::new(crate::fast_hash::AHashMap::new()),
            resolved_module_type_cache: RefCell::new(ScopedPathMap::default()),
            resolved_child_module_path_cache: RefCell::new(crate::fast_hash::AHashMap::new()),
            qualified_module_decl_cache: RefCell::new(crate::fast_hash::AHashMap::new()),
            resolved_type_item_cache: RefCell::new(hashbrown::HashMap::default()),
            normalized_path_full_cache: RefCell::new(ScopedPathMap::default()),
            pdot_expansions: RefCell::new(hashbrown::HashMap::default()),
            typeopt_answers: RefCell::new(None),
            normalized_path_forward_cache: RefCell::new(ScopedPathMap::default()),
            occur_variance_masks: RefCell::new(ScopedPathMap::default()),
            type_newtype_levels: RefCell::new(ScopedPathMap::default()),
            forced_normalized_path_full_cache: RefCell::new(ScopedPathMap::default()),
            forced_type_path_compare_cache: RefCell::new(hashbrown::HashMap::default()),
            load_paths: RefCell::new(Arc::new(Vec::new())),
            persistent_env: RefCell::new(None),
            renamed_module_sigs: RefCell::new(crate::fast_hash::AHashMap::new()),
            raw_module_sigs: RefCell::new(crate::fast_hash::AHashMap::new()),
            gentype_raw_module_sigs: RefCell::new(crate::fast_hash::AHashMap::new()),
            gentype_portable_raw_module_sigs: RefCell::new(crate::fast_hash::AHashMap::new()),
            raw_component_module_sigs: RefCell::new(crate::fast_hash::AHashMap::new()),
            cmi_longident_names: RefCell::new(crate::fast_hash::AHashMap::new()),
            arena_longident_names: RefCell::new(Vec::new()),
            next_cmi_longident_idx: Cell::new(0xF000_0000),
            predef_int: Cell::new(None),
            predef_char: Cell::new(None),
            predef_string: Cell::new(None),
            predef_float: Cell::new(None),
            predef_bool: Cell::new(None),
            predef_unit: Cell::new(None),
            predef_exn: Cell::new(None),
            predef_bigint: Cell::new(None),
            predef_option_inner: Cell::new(None),
            predef_option_type: Cell::new(None),
            predef_option_layout: Cell::new(None),
            arity_aliases: RefCell::new(crate::fast_hash::AHashMap::new()),
            label_family_summaries: RefCell::new(crate::fast_hash::AHashMap::new()),
            label_families: RefCell::new(Vec::new()),
            world_scratch: Cell::new(false),
            typed_envs: RefCell::new(Vec::new()),
            typed_envs_by_id: RefCell::new(crate::fast_hash::AHashMap::new()),
            last_typed_env: Cell::new(None),
            value_deps: RefCell::new(Vec::new()),
            deprecated_used: RefCell::new(Vec::new()),
        }
    }

    /// Allocate a layout to be completed later, for a variant of a recursive
    /// declaration group.
    pub fn pending_variant_layout(&self) -> super::variant_runtime::LayoutRef {
        // A pending layout is completed later by this compilation.
        self.poison_store_build();
        let mut layouts = self.variant_layouts.borrow_mut();
        let layout_ref = super::variant_runtime::LayoutRef::from_usize(layouts.len());
        layouts.push(RefCell::new(super::variant_runtime::LayoutState::Pending));
        layout_ref
    }

    /// Allocate a completed layout.
    pub fn alloc_complete_variant_layout(
        &self,
        layout: super::variant_runtime::Layout,
    ) -> super::variant_runtime::LayoutRef {
        // Like `alloc_type`: a store build allocates in the worker store, where
        // layouts are complete on allocation.
        if self.in_store_build() {
            return self.store.alloc_complete_variant_layout(layout);
        }
        let layout_ref = self.pending_variant_layout();
        self.complete_variant_layout(layout_ref, layout);
        layout_ref
    }

    /// Complete a layout allocated with [`Self::pending_variant_layout`].
    pub fn complete_variant_layout(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
        layout: super::variant_runtime::Layout,
    ) {
        assert!(
            !layout_ref.is_store(),
            "variant layouts in the thread store are complete on allocation"
        );
        let layouts = self.variant_layouts.borrow();
        let Some(state) = layouts.get(layout_ref.index()) else {
            panic!("variant layout reference belongs to another TypeContext")
        };
        let mut state = state.borrow_mut();
        match &*state {
            super::variant_runtime::LayoutState::Pending => {
                *state = super::variant_runtime::LayoutState::Complete(layout)
            }
            super::variant_runtime::LayoutState::Complete(_) => {
                panic!("variant layout completed twice")
            }
        }
    }

    /// Read a completed variant layout without copying its constructor table.
    pub fn with_variant_layout<R>(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
        read: impl FnOnce(&super::variant_runtime::Layout) -> R,
    ) -> R {
        if layout_ref.is_shared() {
            return read(self.store.shared_pool().layout(layout_ref));
        }
        if layout_ref.is_store() {
            return self.store.with_variant_layout(layout_ref, read);
        }
        let layouts = self.variant_layouts.borrow();
        let Some(state) = layouts.get(layout_ref.index()) else {
            panic!("variant layout reference belongs to another TypeContext")
        };
        match &*state.borrow() {
            super::variant_runtime::LayoutState::Complete(layout) => read(layout),
            super::variant_runtime::LayoutState::Pending => {
                panic!("variant layout accessed before declaration completion")
            }
        }
    }

    /// A copy of the layout `layout_ref` refers to.
    pub fn variant_layout(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
    ) -> super::variant_runtime::Layout {
        self.with_variant_layout(layout_ref, Clone::clone)
    }

    /// Store a typedtree environment snapshot and return a stable reference.
    pub fn store_typed_env(&self, env: &Env) -> EnvRef {
        self.poison_store_build_for("store_typed_env");
        if let Some((last_id, last_ref)) = self.last_typed_env.get()
            && last_id == env.id()
        {
            return last_ref;
        }
        if let Some(existing) = self.typed_envs_by_id.borrow().get(&env.id()).copied() {
            self.last_typed_env.set(Some((env.id(), existing)));
            return existing;
        }

        let env_ref = {
            let mut typed_envs = self.typed_envs.borrow_mut();
            let env_ref = EnvRef::from_usize(typed_envs.len());
            typed_envs.push(Rc::new(env.clone()));
            env_ref
        };
        self.typed_envs_by_id.borrow_mut().insert(env.id(), env_ref);
        self.last_typed_env.set(Some((env.id(), env_ref)));
        env_ref
    }

    /// Resolve a typedtree environment reference.
    pub fn get_typed_env(&self, env_ref: EnvRef) -> Option<Rc<Env>> {
        self.typed_envs.borrow().get(env_ref.index()).cloned()
    }

    /// Whether a top-level unification needs its undo-compress snapshot:
    /// always in the explaining mode, and under any live snapshot (a
    /// speculation), never on the success path. Cost: two loads, no writes.
    /// The snapshot preserves diagnostics (compiler/ml/ctype.ml:2589-2594).
    #[inline]
    pub(crate) fn unify_takes_snapshot(&self) -> bool {
        self.explain_mode.get() == CheckMode::Explain || self.mutation_logging.compress()
    }

    /// Cost: one `Cell` write.
    pub(crate) fn set_explain_mode(&self, on: CheckMode) {
        self.explain_mode.set(on);
    }

    /// Cost: one `Cell` write; called on a failure path only.
    #[cold]
    pub(crate) fn note_unexplained_unify_failure(&self) {
        self.unexplained_unify_failure.set(true);
    }

    /// Test observation only: the live journal entries owned by this context.
    #[cfg(test)]
    pub(crate) fn journal_entries_for_test(&self) -> usize {
        self.mutation_journal.borrow().entries.len()
    }

    /// Whether this attempt encountered a failure without a diagnostic snapshot.
    /// A unit-checking caller must discard such an attempt and explain it again.
    /// Cost: one `Cell` read.
    pub fn unexplained_unify_failure(&self) -> bool {
        self.unexplained_unify_failure.get()
    }

    /// O(1) per unit: retain counters locally until the attempt is accepted.
    /// Counts made before this call are published first; from here on the
    /// context publishes nothing unless [`Self::keep_attempt_counters`] runs.
    pub(crate) fn defer_attempt_counters(&self) {
        self.types.1.set(false);
        self.attempt_counters.publish();
        self.attempt_counters.deferred.set(true);
    }

    /// Publish retained counters once: O(held map/vector entries) to merge,
    /// with process-total locks per publication, not per probe. Probes
    /// after this call count locally again and are published once, when the
    /// context is flushed or dropped.
    pub(crate) fn keep_attempt_counters(&self) {
        self.types.1.set(true);
        self.attempt_counters.deferred.set(false);
        self.attempt_counters.publish();
    }

    /// Publish the counts of a context that is not a deferred attempt now,
    /// rather than when it is dropped: for a long-lived context, such as a
    /// worker's view scratch, whose drop may come after the report.
    /// Cost: O(1) if deferred or empty; otherwise O(held map/vector entries)
    /// and process-total locks once per publication, with possible map growth.
    pub(crate) fn flush_counters(&self) {
        if !self.attempt_counters.deferred.get() {
            self.attempt_counters.publish();
        }
    }

    /// O(1) plain writes into this context's counts, allocated on the first
    /// probe; no atomic or TLS operation. Callers test the counters flag.
    pub(crate) fn record_attempt_counter(
        &self,
        record: impl FnOnce(&mut crate::perf_counters::AttemptCounters),
    ) {
        if !self.compiler_counters_enabled {
            return;
        }
        let mut local = self.attempt_counters.local.borrow_mut();
        record(local.get_or_insert_with(Default::default));
    }

    /// Read the counts this context holds and has not published (all zero
    /// when it holds none). Cost: O(1) borrow/default construction plus the
    /// supplied reader's cost; no heap allocation, TLS or global-total lock.
    pub(crate) fn attempt_counter<R>(
        &self,
        read: impl FnOnce(&crate::perf_counters::AttemptCounters) -> R,
    ) -> R {
        match self.attempt_counters.local.borrow().as_deref() {
            Some(counts) => read(counts),
            None => read(&Default::default()),
        }
    }

    /// Turn this context's counters on without `RESCRIPT_COMPILER_COUNTERS`.
    #[cfg(test)]
    pub(crate) fn enable_compiler_counters_for_test(&mut self) {
        self.compiler_counters_enabled = true;
    }

    #[inline]
    pub(crate) fn compiler_counters_enabled(&self) -> bool {
        self.compiler_counters_enabled
    }

    /// Intern a CMI longident component and return a synthetic StrIdx.
    pub fn intern_cmi_longident_name(&self, name: &str) -> StrIdx {
        self.poison_store_build_for("intern_cmi_longident_name");
        let raw = self.next_cmi_longident_idx.get();
        self.next_cmi_longident_idx.set(raw.wrapping_add(1));
        self.cmi_longident_names
            .borrow_mut()
            .insert(raw, name.to_string());
        StrIdx::from_raw(raw)
    }

    pub(crate) fn cmi_longident_component_name(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_names
            .borrow()
            .get(&idx.raw())
            .cloned()
            .or_else(|| self.store.shared_pool().longident_name(idx))
    }

    /// The world of the build this compilation belongs to.
    #[inline]
    pub(crate) fn world(&self) -> &Arc<super::world::World> {
        self.store.world()
    }

    /// The worker's persistent store leased by this compilation.
    pub(crate) fn thread_store(&self) -> &super::thread_store::ThreadTypeStore {
        &self.store
    }

    /// Whether `r` names an allocated node of this compilation's arena or of
    /// the worker store.
    pub fn contains_type_ref(&self, r: TypeExprRef) -> bool {
        if r.is_shared() {
            self.store.shared_pool().contains(r.shared_index())
        } else if r.is_store() {
            r.store_index() < self.store.type_count()
        } else {
            r.index() < self.types.len()
        }
    }

    /// Resolve a Longident component StrIdx to string, checking CMI synthetic
    /// indices first and falling back to the parse arena interner.
    pub fn resolve_longident_component(
        &self,
        arena: &crate::parse_arena::ParseArena,
        idx: StrIdx,
    ) -> String {
        self.cmi_longident_component_name(idx)
            .unwrap_or_else(|| arena.get_string(idx).to_string())
    }

    /// The name of a longident component interned with
    /// [`Self::intern_cmi_longident_name`].
    pub fn resolve_cmi_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_component_name(idx)
    }

    pub(crate) fn register_arena_longident_names(&self, arena: &crate::parse_arena::ParseArena) {
        self.poison_store_build_for("register_arena_longident_names");
        if arena.string_count() > 0 {
            self.arena_longident_names
                .borrow_mut()
                .push(arena.snapshot_strings());
        }
    }

    pub(crate) fn resolve_any_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_component_name(idx).or_else(|| {
            self.arena_longident_names
                .borrow()
                .iter()
                .find_map(|strings| strings.get(idx).map(str::to_string))
        })
    }

    /// Import synthetic CMI longident names from a portable signature.
    pub fn import_cmi_longident_names(&self, names: &[(u32, String)]) {
        self.poison_store_build_for("import_cmi_longident_names");
        let mut table = self.cmi_longident_names.borrow_mut();
        let mut next = self.next_cmi_longident_idx.get();
        for (raw, name) in names {
            table.insert(*raw, name.clone());
            if *raw >= next {
                next = raw.wrapping_add(1);
            }
        }
        self.next_cmi_longident_idx.set(next);
    }

    /// OCaml `Ctype.reset_reified_var_counter` (ctype.ml:906).
    pub(crate) fn reset_reified_var_counter(&self) {
        let mut names = self.reified_var_counters.borrow_mut();
        names.counters.clear();
        names.used.clear();
    }

    /// The `Hashtbl.replace` into `existential_constructors_key` in OCaml
    /// `Ctype.instance_constructor` (ctype.ml:960-962).
    pub(crate) fn record_existential_constructor(&self, stamp: i32, constructor: &str) {
        self.existential_constructors
            .borrow_mut()
            .insert(stamp, crate::name::Name::from(constructor));
    }

    /// OCaml `Ctype.existential_constructor id` (ctype.ml:941-944).
    pub(crate) fn existential_constructor(
        &self,
        id: &crate::ident::Ident,
    ) -> Option<crate::name::Name> {
        self.existential_constructors
            .borrow()
            .get(&id.binding_time())
            .copied()
    }

    /// Match OCaml `Ctype.get_new_abstract_name`. A numbered name can equal
    /// a base name ending in digits, as `$a1` for the second `'a` and the
    /// first `'a1`, so names already given are skipped.
    pub(crate) fn next_reified_abstract_name(&self, prefix: &str) -> String {
        self.poison_store_build_for("next_reified_abstract_name");
        let mut names = self.reified_var_counters.borrow_mut();
        let ReifiedNames { counters, used } = &mut *names;
        let name = |index: usize| {
            if index == 0 && !prefix.is_empty() && !prefix.ends_with('$') {
                prefix.to_string()
            } else {
                format!("{prefix}{index}")
            }
        };
        let mut index = counters.get(prefix).map_or(0, |previous| previous + 1);
        let mut candidate = name(index);
        while used.contains(&candidate) {
            index += 1;
            candidate = name(index);
        }
        counters.insert(prefix.to_string(), index);
        used.insert(candidate.clone());
        candidate
    }

    /// Cache a resolved module signature.
    pub fn register_resolved_module_sig(
        &self,
        path: &str,
        scope: Option<ScopeId>,
        access_path: Path,
        sig: Arc<super::decl::Signature>,
    ) {
        self.poison_store_build_for("register_resolved_module_sig");
        self.resolved_module_sig_cache
            .borrow_mut()
            .insert((path.to_string(), scope), (access_path, sig));
    }

    /// Look up a cached resolved module signature.
    pub fn find_resolved_module_sig(
        &self,
        path: &str,
        scope: Option<ScopeId>,
    ) -> Option<(Path, Arc<super::decl::Signature>)> {
        self.poison_store_build_for("read:find_resolved_module_sig");
        self.resolved_module_sig_cache
            .borrow()
            .get(&ModuleSignatureKeyRef(path, scope))
            .cloned()
    }

    /// Cache a lazily-built qualified module-components view.
    /// Register a (possibly shared) component view in this compilation's
    /// component cache.
    pub(crate) fn register_qualified_module_components_shared(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: Rc<super::env_lazy::QualifiedModuleComponents>,
    ) {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_registered(self);
        }
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, super::env_lazy::HeldComponents::Local(components));
    }

    /// Use the world view `view` in this compilation, under `key`: the one
    /// way a compilation comes to read a view. Registers the view in the
    /// component cache, adopts the view it is a child of (so adoption is
    /// transitive whatever the caller did first) and registers, for each
    /// child of the view that is a path, the (component path, alias source)
    /// pair the tables of other paths read
    /// (`alias_sources_for_component_path`). A store build that adopts a
    /// view records it, so a compilation reusing the build's result adopts
    /// the view as well.
    ///
    /// Cost: one probe of the component cache when the view is adopted
    /// already; else one insert, one probe for its parent, and one
    /// registration per child that is a path, into tables given room for
    /// them first (they are empty when a compilation starts, and growing
    /// them pair by pair rehashed them again and again).
    pub(crate) fn adopt_view(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        view: Arc<super::module_view::ModuleView>,
    ) {
        if self.holds_view(&key, &view) {
            return;
        }
        if self.compiler_counters_enabled {
            crate::perf_counters::world::record_view_adoption(self);
        }
        #[cfg(test)]
        self.view_adoptions.set(self.view_adoptions.get() + 1);
        if let Some(parent) = view.parent_view() {
            self.adopt_view(
                QualifiedModuleComponentsCacheKey::new(*parent.access_path(), None),
                parent,
            );
        }
        if let Some(target) = view.target_view() {
            self.adopt_view(
                QualifiedModuleComponentsCacheKey::new(*target.access_path(), None),
                target.clone(),
            );
        }
        let pairs = view.alias_sources();
        if !pairs.is_empty() {
            self.component_alias_sources
                .borrow_mut()
                .reserve(pairs.len());
            self.component_paths_by_alias_source
                .borrow_mut()
                .reserve(pairs.len());
            self.suspend_store_build(|| {
                for (component, source) in pairs {
                    self.register_component_alias_source(*component, *source);
                }
            });
        }
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, super::env_lazy::HeldComponents::World(view));
    }

    /// Whether this compilation has adopted `view` under `key`. One probe
    /// of the component cache.
    pub(crate) fn holds_view(
        &self,
        key: &QualifiedModuleComponentsCacheKey,
        view: &Arc<super::module_view::ModuleView>,
    ) -> bool {
        matches!(
            self.qualified_module_components_cache.borrow().get(key),
            Some(super::env_lazy::HeldComponents::World(held)) if Arc::ptr_eq(held, view)
        )
    }

    /// The forced declaration of child `name` (signature item `item`) of
    /// `view` was read: register it with this compilation the first time,
    /// where the tables of an alias path to the same module look for it
    /// (`find_qualified_module_decl`).
    ///
    /// Cost: one bit test in a table indexed by view and item; the first
    /// time per compilation and child, one registration.
    pub(crate) fn note_forced_view_module(
        &self,
        view: &super::module_view::ModuleView,
        item: usize,
        name: &str,
        id: Ident,
        md: &Arc<super::decl::ModuleDeclaration>,
    ) {
        let first = {
            let mut noted = self.noted_view_modules.borrow_mut();
            let view_index = view.id().index();
            if noted.len() <= view_index {
                noted.resize_with(view_index + 1, Vec::new);
            }
            let bits = &mut noted[view_index];
            if bits.len() <= item / 64 {
                bits.resize(item / 64 + 1, 0);
            }
            let mask = 1u64 << (item % 64);
            let first = bits[item / 64] & mask == 0;
            bits[item / 64] |= mask;
            first
        };
        if first {
            self.register_qualified_module_decl(view.access_path(), name, id, md.clone());
        }
    }

    pub(crate) fn register_qualified_module_components(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: super::env_lazy::QualifiedModuleComponents,
    ) {
        self.poison_store_build_for("register_qualified_module_components");
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_registered(self);
        }
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, super::env_lazy::HeldComponents::Local(Rc::new(components)));
    }

    /// Borrow a cached qualified module-components view.
    /// OCaml stores lazy module components once and keeps that table visible to
    /// recursive lookup while forcing nested thunks (compiler/ml/env.ml:1513-1514,
    /// 1516-1588). Borrow the cached view directly; the view itself owns the
    /// shared lazy component state needed by recursive lookups.
    pub(crate) fn with_qualified_module_components<R>(
        &self,
        key: &QualifiedModuleComponentsCacheKey,
        f: impl FnOnce(super::env_lazy::Components<'_>) -> R,
    ) -> Option<R> {
        self.poison_store_build_for("read:with_qualified_module_components");
        let cache = self.qualified_module_components_cache.borrow();
        let Some(components) = cache.get(key) else {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_qualified_component_miss(self);
            }
            return None;
        };
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_hit(self);
        }
        Some(f(components.components()))
    }

    /// Name index for the component tables of `sig`, shared by every table
    /// built from the same signature.
    pub(crate) fn signature_index(
        &self,
        sig: &Arc<super::decl::Signature>,
    ) -> Arc<super::env_lazy::SignatureIndex> {
        let key = Arc::as_ptr(sig) as usize;
        if let Some((_, found)) = self.signature_indexes.borrow().get(&key) {
            return found.clone();
        }
        // A unit's index is built once per build and read from the world once
        // per compilation; any other signature is indexed here.
        let built = self
            .world()
            .unit_signature_index(sig)
            .unwrap_or_else(|| Arc::new(super::env_lazy::SignatureIndex::build(sig)));
        self.signature_indexes
            .borrow_mut()
            .insert(key, (sig.clone(), built.clone()));
        built
    }

    pub(crate) fn register_component_alias_source(&self, component_path: Path, alias_source: Path) {
        // OCaml compiler/ml/env.ml:1440-1446 scrapes aliases by resolving the
        // target path through `find_module`; env.ml:1530 then prefixes the
        // selected component path. Record exactly that pair so later helpers
        // recover alias identity from declarations, not from name spelling.
        let mut alias_sources: AliasPaths = smallvec::smallvec![alias_source];
        for backing_source in self.flattened_backing_sources_for_alias_source(&alias_sources[0]) {
            if !alias_sources
                .iter()
                .any(|source| source.same(&backing_source))
            {
                alias_sources.push(backing_source);
            }
        }

        for alias_source in alias_sources {
            push_unique_path(
                self.component_alias_sources
                    .borrow_mut()
                    .entry(SamePathKey(component_path))
                    .or_default(),
                alias_source,
            );
            push_unique_path(
                self.component_paths_by_alias_source
                    .borrow_mut()
                    .entry(SamePathKey(alias_source))
                    .or_default(),
                component_path,
            );
        }
    }

    fn flattened_backing_sources_for_alias_source(&self, alias_source: &Path) -> Vec<Path> {
        let Ok((head, components)) = alias_source.flatten() else {
            return Vec::new();
        };
        if components.is_empty() {
            return Vec::new();
        }

        let persistent_env = self.persistent_env.borrow();
        let Some(pers) = persistent_env.as_ref() else {
            return Vec::new();
        };

        let mut sources = Vec::new();
        for split in 1..=components.len() {
            let mut qualified_prefix = Path::pident(*head);
            for component in &components[..split] {
                qualified_prefix = Path::pdot(qualified_prefix, *component);
            }

            for flat_head in pers.flattened_alias_heads_for_path(&qualified_prefix) {
                let mut source = Path::pident(Ident::create_persistent(&flat_head));
                for component in &components[split..] {
                    source = Path::pdot(source, *component);
                }
                if !sources.iter().any(|existing: &Path| existing.same(&source)) {
                    sources.push(source);
                }
            }
        }
        sources
    }

    /// Whether any component path has `alias_source` as its alias source.
    ///
    /// Inside a store build this is recorded as a guard of the piece being
    /// built instead of poisoning it. Registrations are only ever added
    /// (`register_component_alias_source`), and the build's own effects are
    /// replayed before any later read, so a compilation that gives the same
    /// answer before replaying the piece gives the same answer at every
    /// point of the build: the piece is valid for it.
    pub(crate) fn has_component_paths_for_alias_source(&self, alias_source: &Path) -> bool {
        let nonempty = self.alias_source_has_component_paths(alias_source);
        if self.in_store_build() {
            self.store_build_guards
                .borrow_mut()
                .push((*alias_source, nonempty));
        }
        nonempty
    }

    fn alias_source_has_component_paths(&self, alias_source: &Path) -> bool {
        self.component_paths_by_alias_source
            .borrow()
            .get(&SamePathKey(*alias_source))
            .is_some_and(|paths| !paths.is_empty())
    }

    /// Whether this compilation answers every guard of `piece` as the build
    /// that produced it did.
    pub(crate) fn store_guards_hold(&self, piece: &StorePiece) -> bool {
        piece
            .guards
            .iter()
            .all(|(source, nonempty)| self.alias_source_has_component_paths(source) == *nonempty)
    }

    pub(crate) fn component_paths_for_alias_source(&self, alias_source: &Path) -> Vec<Path> {
        self.poison_store_build_for("read:component_paths_for_alias_source");
        self.component_paths_by_alias_source
            .borrow()
            .get(&SamePathKey(*alias_source))
            .map(|paths| paths.to_vec())
            .unwrap_or_default()
    }

    /// Return alias source paths that back a selected component path.
    ///
    /// This mirrors the source path selected by OCaml compiler/ml/env.ml:1513
    /// through `scrape_alias`, while env.ml:1573-1578 stores child
    /// declaration/component thunks under the selected access path.
    pub(crate) fn alias_sources_for_component_path(&self, component_path: &Path) -> Vec<Path> {
        // Registered when the component tables of the path's ancestors are
        // built (or their store pieces replayed), which any build reaching
        // the path does first: the same for every compilation.
        self.component_alias_sources
            .borrow()
            .get(&SamePathKey(*component_path))
            .map(|paths| paths.to_vec())
            .unwrap_or_default()
    }

    /// Look up a module alias target from the qualified module components cache.
    ///
    /// For a path like `Pdot(Pident("Js"), "Exn", _)`, checks whether `Js`'s
    /// qualified components contain `Exn` as a `MtyAlias`. If so, returns the
    /// alias target (e.g., `Pident("Stdlib_Exn")`).
    ///
    /// Used by `matching.rs` to resolve persistent module aliases without
    /// access to the full `PersistentEnv`.
    pub fn find_module_alias_in_components(
        &self,
        parent_path: &Path,
        module_name: &str,
    ) -> Option<Arc<Path>> {
        self.poison_store_build_for("read:find_module_alias_in_components");
        let key = QualifiedModuleComponentsCacheKey::new(*parent_path, None);
        self.with_qualified_module_components(&key, |components| {
            // env.ml:865-882 `find_module ~alias:true` follows `Mty_alias`
            // only: a module declared with a module type name (`N: S`) is
            // not an alias of `S`.
            components.lookup_module_alias_target(module_name, false, self)
        })
        .flatten()
    }

    /// Cache a dotted value lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_value(
        &self,
        module_path: &Path,
        value_name: &str,
        path: Path,
        desc: Arc<super::decl::ValueDescription>,
    ) {
        self.resolved_module_value_cache
            .borrow_mut()
            .entry(*module_path)
            .or_default()
            .insert(value_name.to_string(), (path, desc));
    }

    /// Look up a cached dotted value lookup for a resolved module access path.
    pub(crate) fn find_resolved_module_value(
        &self,
        module_path: &Path,
        value_name: &str,
    ) -> Option<(Path, Arc<super::decl::ValueDescription>)> {
        self.resolved_module_value_cache
            .borrow()
            .get(module_path)
            .and_then(|values| values.get(value_name))
            .cloned()
    }

    /// Cache a dotted type lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_type(
        &self,
        env_id: ScopeId,
        module_path: &Path,
        type_name: &str,
        access_path: Path,
        id: Ident,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_module_type_cache
            .borrow_mut()
            .entry((env_id, *module_path))
            .or_default()
            .insert(type_name.to_string(), (access_path, id, decl));
    }

    /// Start or stop answering repeated `typeopt` queries from a cache. Only
    /// enabled while a finished typed tree is lowered to lambda.
    pub(crate) fn set_typeopt_cache(&self, enabled: bool) {
        *self.typeopt_answers.borrow_mut() = enabled.then(crate::fast_hash::AHashMap::new);
    }

    /// Answer a `typeopt` query `query` about `ty` in the env `env_id`,
    /// reusing an earlier answer while the cache is enabled.
    pub(crate) fn typeopt_answer(
        &self,
        env_id: EnvId,
        ty: TypeExprRef,
        query: u8,
        compute: impl FnOnce() -> bool,
    ) -> bool {
        if self.typeopt_answers.borrow().is_none() {
            return compute();
        }
        let ty = self.repr(ty);
        if let Some(answer) = self
            .typeopt_answers
            .borrow()
            .as_ref()
            .and_then(|answers| answers.get(&(env_id, ty, query)))
        {
            return *answer;
        }
        let answer = compute();
        if let Some(answers) = self.typeopt_answers.borrow_mut().as_mut() {
            answers.insert((env_id, ty, query), answer);
        }
        answer
    }

    /// The cached expansion outcome of a `Pdot` head (`ctype::PdotExpansion`).
    pub(crate) fn find_pdot_expansion(
        &self,
        scope_id: ScopeId,
        mode: u8,
        arity: usize,
        path: &Path,
    ) -> Option<super::ctype::PdotExpansion> {
        self.pdot_expansions
            .borrow()
            .get(&PdotExpansionKeyRef {
                scope_id,
                mode,
                arity,
                path,
            })
            .cloned()
    }

    pub(crate) fn register_pdot_expansion(
        &self,
        scope_id: ScopeId,
        mode: u8,
        arity: usize,
        path: &Path,
        expansion: super::ctype::PdotExpansion,
    ) {
        self.pdot_expansions.borrow_mut().insert(
            PdotExpansionKey {
                scope_id,
                mode,
                arity,
                path: *path,
            },
            expansion,
        );
    }

    /// Look up a cached dotted type lookup for a resolved module access path.
    pub(crate) fn find_resolved_type_item(
        &self,
        scope_id: ScopeId,
        path: &Path,
        strengthen_alias_types: bool,
    ) -> Option<(Ident, Arc<super::decl::TypeDeclaration>)> {
        self.resolved_type_item_cache
            .borrow()
            .get(&ScopedPathFlagRef(scope_id, path, strengthen_alias_types))
            .cloned()
    }

    pub(crate) fn register_resolved_type_item(
        &self,
        scope_id: ScopeId,
        path: &Path,
        strengthen_alias_types: bool,
        id: Ident,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_type_item_cache
            .borrow_mut()
            .insert((scope_id, *path, strengthen_alias_types), (id, decl));
    }

    pub(crate) fn find_resolved_module_type(
        &self,
        env_id: ScopeId,
        module_path: &Path,
        type_name: &str,
    ) -> Option<(Path, Ident, Arc<super::decl::TypeDeclaration>)> {
        self.resolved_module_type_cache
            .borrow()
            .get(&ScopedPathRef(env_id, module_path))
            .and_then(|types| types.get(type_name))
            .cloned()
    }

    /// Cache a resolved child-module access path.
    pub(crate) fn register_resolved_child_module_path(
        &self,
        parent_path: &Path,
        child_name: &str,
        child_path: Path,
    ) {
        self.resolved_child_module_path_cache
            .borrow_mut()
            .entry(*parent_path)
            .or_default()
            .insert(child_name.to_string(), child_path);
    }

    /// Look up a cached resolved child-module access path.
    pub(crate) fn find_resolved_child_module_path(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<Path> {
        self.resolved_child_module_path_cache
            .borrow()
            .get(parent_path)
            .and_then(|children| children.get(child_name))
            .cloned()
    }

    /// Share a forced declaration across persistent/global alias component views.
    ///
    /// Local declarations and functor-application paths are intentionally not
    /// published here: OCaml keeps descriptor component tables and later
    /// `find_module` thunks distinct.
    pub(crate) fn register_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
        id: Ident,
        md: Arc<super::decl::ModuleDeclaration>,
    ) {
        let Some(head) = parent_path.head_opt() else {
            return;
        };
        if !head.is_persistent() && !head.is_global() && head.stamp() != 0 {
            return;
        }
        self.qualified_module_decl_cache
            .borrow_mut()
            .entry(*parent_path)
            .or_default()
            .insert(child_name.to_string(), (id, md));
    }

    /// Look up a forced persistent/global qualified module declaration.
    pub(crate) fn find_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<(Ident, Arc<super::decl::ModuleDeclaration>)> {
        let head = parent_path.head_opt()?;
        if !head.is_persistent() && !head.is_global() && head.stamp() != 0 {
            return None;
        }
        // Filled by this compilation's forces (and replayed store pieces):
        // what a store build finds here, including nothing, is local state.
        self.poison_store_build_for("read:find_qualified_module_decl");
        self.qualified_module_decl_cache
            .borrow()
            .get(parent_path)
            .and_then(|modules| modules.get(child_name))
            .cloned()
    }

    /// Cache a normalized path for a specific environment identity.
    pub(crate) fn register_normalized_path_full(
        &self,
        env_id: ScopeId,
        original_path: &Path,
        normalized_path: Arc<super::ctype::NormRecipe>,
    ) {
        self.normalized_path_full_cache
            .borrow_mut()
            .insert((env_id, *original_path), normalized_path);
    }

    pub(crate) fn find_type_newtype_level(
        &self,
        scope_id: ScopeId,
        path: &Path,
    ) -> Option<Option<i32>> {
        self.type_newtype_levels
            .borrow()
            .get(&ScopedPathRef(scope_id, path))
            .copied()
    }

    pub(crate) fn register_type_newtype_level(
        &self,
        scope_id: ScopeId,
        path: &Path,
        level: Option<i32>,
    ) {
        self.type_newtype_levels
            .borrow_mut()
            .insert((scope_id, *path), level);
    }

    pub(crate) fn find_occur_variance_mask(
        &self,
        scope_id: ScopeId,
        path: &Path,
    ) -> Option<Option<u64>> {
        self.occur_variance_masks
            .borrow()
            .get(&ScopedPathRef(scope_id, path))
            .copied()
    }

    pub(crate) fn register_occur_variance_mask(
        &self,
        scope_id: ScopeId,
        path: &Path,
        mask: Option<u64>,
    ) {
        self.occur_variance_masks
            .borrow_mut()
            .insert((scope_id, *path), mask);
    }

    pub(crate) fn register_normalized_path_forward(
        &self,
        env_id: ScopeId,
        original_path: &Path,
        normalized_path: Arc<super::ctype::NormRecipe>,
    ) {
        self.normalized_path_forward_cache
            .borrow_mut()
            .insert((env_id, *original_path), normalized_path);
    }

    pub(crate) fn find_normalized_path_forward(
        &self,
        env_id: ScopeId,
        original_path: &Path,
    ) -> Option<Arc<super::ctype::NormRecipe>> {
        self.normalized_path_forward_cache
            .borrow()
            .get(&ScopedPathRef(env_id, original_path))
            .cloned()
    }

    /// Look up a cached normalized path for a specific environment identity.
    pub(crate) fn find_normalized_path_full(
        &self,
        env_id: ScopeId,
        original_path: &Path,
    ) -> Option<Arc<super::ctype::NormRecipe>> {
        self.normalized_path_full_cache
            .borrow()
            .get(&ScopedPathRef(env_id, original_path))
            .cloned()
    }

    /// Cache a normalized path after the side-effectful normalize path has run.
    pub(crate) fn register_forced_normalized_path_full(
        &self,
        env_id: ScopeId,
        original_path: &Path,
        normalized_path: Arc<super::ctype::NormRecipe>,
    ) {
        self.poison_store_build_for("register_forced_normalized_path_full");
        self.forced_normalized_path_full_cache
            .borrow_mut()
            .insert((env_id, *original_path), normalized_path);
    }

    /// Look up a side-effectful normalize path result for this environment.
    pub(crate) fn find_forced_normalized_path_full(
        &self,
        env_id: ScopeId,
        original_path: &Path,
    ) -> Option<Arc<super::ctype::NormRecipe>> {
        self.forced_normalized_path_full_cache
            .borrow()
            .get(&ScopedPathRef(env_id, original_path))
            .cloned()
    }

    /// Cache a side-effectful type-path comparison after the first comparison
    /// has already forced the same lazies OCaml would force at that call site.
    pub(crate) fn register_forced_type_path_compare(
        &self,
        env_id: ScopeId,
        left: &Path,
        right: &Path,
        same: bool,
    ) {
        self.poison_store_build_for("register_forced_type_path_compare");
        let mut cache = self.forced_type_path_compare_cache.borrow_mut();
        cache.insert((env_id, *left, *right), same);
        cache.insert((env_id, *right, *left), same);
    }

    /// Look up a side-effectful type-path comparison for this environment.
    pub(crate) fn find_forced_type_path_compare(
        &self,
        env_id: ScopeId,
        left: &Path,
        right: &Path,
    ) -> Option<bool> {
        self.forced_type_path_compare_cache
            .borrow()
            .get(&ScopedPathPairRef(env_id, left, right))
            .copied()
    }

    /// Set load paths for resolving CMI files.
    pub fn set_load_paths(&self, paths: Vec<std::path::PathBuf>) {
        *self.load_paths.borrow_mut() = Arc::new(paths);
    }

    /// Set the load paths from a shared list.
    pub fn set_load_paths_shared(&self, paths: Arc<Vec<std::path::PathBuf>>) {
        *self.load_paths.borrow_mut() = paths;
    }

    /// Get the load paths.
    pub fn load_paths(&self) -> std::cell::Ref<'_, Vec<std::path::PathBuf>> {
        std::cell::Ref::map(self.load_paths.borrow(), |paths| paths.as_ref())
    }

    pub(crate) fn set_persistent_env(&self, env: crate::cmi::persistent_env::PersistentEnv) {
        *self.persistent_env.borrow_mut() = Some(env);
    }

    pub(crate) fn persistent_env_clone(&self) -> Option<crate::cmi::persistent_env::PersistentEnv> {
        self.persistent_env.borrow().clone()
    }

    pub(crate) fn persistent_env_is_in_process(&self) -> bool {
        self.persistent_env
            .borrow()
            .as_ref()
            .is_some_and(crate::cmi::persistent_env::PersistentEnv::is_in_process_mode)
    }

    // ========================================================================
    // Type Creation
    // ========================================================================

    /// Create a new type expression.
    fn alloc_type(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        if self.in_store_build() {
            let desc = self.store_desc_lists(desc);
            self.check_store_desc(&desc);
            return self.store.alloc_type(desc, level);
        }
        let id = self.id_gen.next_type_id();
        TypeExprRef::from_usize(self.types.push(desc, level, id))
    }

    /// Allocate an immutable type list (constructor, package and
    /// polymorphic-variable arguments, tuple components). During a store
    /// build it goes to the worker store, like the nodes being built.
    pub fn new_type_list(&self, items: &[TypeExprRef]) -> TypeRefList {
        if items.is_empty() {
            return TypeRefList::EMPTY;
        }
        if self.in_store_build() {
            return self.store.alloc_type_list(items);
        }
        self.type_lists.alloc(items)
    }

    /// [`Self::new_type_list`] from an iterator.
    pub fn new_type_list_from(&self, items: impl IntoIterator<Item = TypeExprRef>) -> TypeRefList {
        let items: TypeRefs = items.into_iter().collect();
        self.new_type_list(&items)
    }

    /// The elements of a type list, borrowed from their pool.
    #[inline]
    pub fn type_list(&self, list: impl Into<TypeRefList>) -> TypeSlice<'_> {
        let list = list.into();
        if list.is_empty() {
            return TypeSlice::EMPTY;
        }
        if list.is_store() {
            return self.store_type_list(list);
        }
        self.type_lists.get(list)
    }

    /// One element of a type list.
    #[inline]
    pub fn type_list_at(&self, list: impl Into<TypeRefList>, index: usize) -> TypeExprRef {
        let list = list.into();
        if list.is_store() {
            return self.store_type_list(list).at(index);
        }
        self.type_lists.get_at(list, index)
    }

    #[inline(never)]
    fn store_type_list(&self, list: TypeRefList) -> TypeSlice<'_> {
        if list.is_shared() {
            return TypeSlice::Plain(super::shared_store::page_list(&self.shared_pages, list));
        }
        self.store.type_list(list)
    }

    /// Allocate an immutable arrow parameter list (same tier rule as
    /// [`Self::new_type_list`]).
    pub fn new_type_args(&self, args: &[TypeArg]) -> TypeArgList {
        if args.is_empty() {
            return TypeArgList::EMPTY;
        }
        if self.in_store_build() {
            return self.store.alloc_type_args(args);
        }
        self.type_lists.alloc_args(args)
    }

    /// [`Self::new_type_args`] from an iterator.
    pub fn new_type_args_from(&self, args: impl IntoIterator<Item = TypeArg>) -> TypeArgList {
        let args: TypeArgs = args.into_iter().collect();
        self.new_type_args(&args)
    }

    /// The parameters of an arrow parameter list, borrowed from their pool.
    #[inline]
    pub fn type_args(&self, list: impl Into<TypeArgList>) -> TypeArgSlice<'_> {
        let list = list.into();
        if list.is_empty() {
            return TypeArgSlice::EMPTY;
        }
        if list.is_store() {
            return self.store_type_args(list);
        }
        self.type_lists.get_args(list)
    }

    #[inline(never)]
    fn store_type_args(&self, list: TypeArgList) -> TypeArgSlice<'_> {
        if list.is_shared() {
            return TypeArgSlice::Plain(super::shared_store::page_args(&self.shared_pages, list));
        }
        self.store.type_args(list)
    }

    /// Store an immutable `Tvariant` row (same tier rule as
    /// [`Self::new_type_list`]).
    pub fn new_row_desc(&self, row: RowDesc) -> RowDescRef {
        if self.in_store_build() {
            return self.store.alloc_row_desc(row);
        }
        self.type_lists.alloc_row(row)
    }

    /// A copy of a `Tvariant` row.
    #[inline]
    pub fn row_desc(&self, row: impl Into<RowDescRef>) -> RowDesc {
        let row = row.into();
        if row.is_store() {
            return self.store_row_desc(row);
        }
        self.type_lists.get_row(row).clone()
    }

    #[inline(never)]
    fn store_row_desc(&self, row: RowDescRef) -> RowDesc {
        if row.is_shared() {
            return super::shared_store::page_row(&self.shared_pages, row).clone();
        }
        self.store.row_desc(row)
    }

    /// Store the constraint names of a `Tpackage` (same tier rule as
    /// [`Self::new_type_list`]).
    pub fn new_package_lids(&self, lids: Vec<Longident>) -> PackageLidsRef {
        if self.in_store_build() {
            return self.store.alloc_package_lids(lids);
        }
        self.type_lists.alloc_lids(lids)
    }

    /// A copy of the constraint names of a `Tpackage`.
    pub fn package_lids(&self, lids: impl Into<PackageLidsRef>) -> Vec<Longident> {
        let lids = lids.into();
        if lids.is_shared() {
            return super::shared_store::page_lids(&self.shared_pages, lids).to_vec();
        }
        if lids.is_store() {
            return self.store.package_lids(lids);
        }
        self.type_lists.get_lids(lids).to_vec()
    }

    /// [`Self::store_type_list_for`] for arrow parameter lists.
    fn store_type_args_for(&self, list: TypeArgList) -> TypeArgList {
        if list.is_empty() || list.is_store() {
            return list;
        }
        self.store.alloc_type_args(&self.type_lists.get_args(list).to_smallvec::<4>())
    }

    /// A copy of `list` that store descriptors can hold: lists allocated by
    /// this compilation are copied to the worker store (lists are immutable
    /// values, so only the elements' identities matter).
    fn store_type_list_for(&self, list: TypeRefList) -> TypeRefList {
        if list.is_empty() || list.is_store() {
            return list;
        }
        self.store.alloc_type_list(&self.type_lists.get(list).to_smallvec::<4>())
    }

    /// Create a new type at a specific level.
    pub fn alloc_type_at_level(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        self.alloc_type(desc, level)
    }

    /// Create a new type at the current level.
    pub fn new_type(&self, desc: TypeDesc) -> TypeExprRef {
        self.alloc_type(desc, self.current_level.get())
    }

    /// Create a new type at the generic level.
    pub fn new_generic_type(&self, desc: TypeDesc) -> TypeExprRef {
        self.alloc_type(desc, GENERIC_LEVEL)
    }

    /// Count a variable made by `new_var` and its variants. A variable made
    /// inside a copy session belongs to the copy.
    #[cold]
    #[inline(never)]
    fn count_fresh_var(&self, location: &'static std::panic::Location<'static>) {
        if self.copy_sessions.borrow().is_empty() {
            crate::perf_counters::record_fresh_var(self, location);
        }
    }

    /// Create a new type variable.
    #[track_caller]
    #[inline]
    pub fn new_var(&self, name: Option<crate::name::Name>) -> TypeExprRef {
        if self.compiler_counters_enabled {
            self.count_fresh_var(std::panic::Location::caller());
        }
        self.new_type(TypeDesc::Tvar(name))
    }

    /// Create a new type variable at the global level.
    #[track_caller]
    #[inline]
    pub fn new_global_var(&self, name: Option<crate::name::Name>) -> TypeExprRef {
        if self.compiler_counters_enabled {
            self.count_fresh_var(std::panic::Location::caller());
        }
        self.alloc_type(TypeDesc::Tvar(name), self.global_level.get())
    }

    /// Create a new generic type variable.
    #[track_caller]
    #[inline]
    pub fn new_generic_var(&self, name: Option<crate::name::Name>) -> TypeExprRef {
        if self.compiler_counters_enabled {
            self.count_fresh_var(std::panic::Location::caller());
        }
        self.new_generic_type(TypeDesc::Tvar(name))
    }

    /// Create an arrow (function) type. When `ret_type` is itself an arrow,
    /// its parameters are merged into the new arrow.
    fn new_arrow(
        &self,
        arg_label: ArgLabel,
        arg_type: TypeExprRef,
        ret_type: TypeExprRef,
    ) -> TypeExprRef {
        let mut args = vec![TypeArg::new(arg_label, arg_type)];
        let ret = {
            let desc = self.get_desc(self.repr(ret_type));
            match &*desc {
                TypeDesc::Tarrow {
                    args: ret_args,
                    ret,
                } => {
                    args.extend(self.type_args(ret_args).iter());
                    *ret
                }
                _ => ret_type,
            }
        };
        self.new_type(TypeDesc::Tarrow {
            args: self.new_type_args(&args),
            ret,
        })
    }

    /// Create an unlabeled arrow type.
    pub fn new_arrow_simple(&self, arg: TypeExprRef, ret: TypeExprRef) -> TypeExprRef {
        self.new_arrow(ArgLabel::Nolabel, arg, ret)
    }

    /// Create a tuple type.
    pub fn new_tuple(&self, types: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Ttuple(self.new_type_list(&types)))
    }

    /// Create a type constructor application.
    pub fn new_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.new_type(TypeDesc::Tconstr {
            path,
            args: self.new_type_list(&args),
            abbrev,
        })
    }

    /// Create a type constructor at generic level (for type schemes).
    pub fn new_generic_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_constr_at(GENERIC_LEVEL, path, args)
    }





    /// `newconstr Predef.path_X args`: a constructor holding one of
    /// `Predef`'s global paths (predef.ml:52-86), at the current level.
    pub fn new_predef_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_constr_at(self.current_level.get(), path, args)
    }

    /// `newgenty (Tconstr (Predef.path_X, args, ref Mnil))`.
    pub fn new_generic_predef_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_constr_at(GENERIC_LEVEL, path, args)
    }

    fn new_constr_at(&self, level: i32, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.alloc_type(
            TypeDesc::Tconstr {
                path,
                args: self.new_type_list(&args),
                abbrev,
            },
            level,
        )
    }

    /// Get or create a cached predef singleton helper.
    fn get_or_create_predef(&self, cache: &Cell<Option<TypeExprRef>>, path: Path) -> TypeExprRef {
        if let Some(ty) = cache.get() {
            ty
        } else {
            let ty = self.new_generic_predef_constr(path, vec![]);
            cache.set(Some(ty));
            ty
        }
    }

    /// Get the predef int singleton (generic_level).
    pub fn predef_int(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_int, super::predef::path_int())
    }
    /// Get the predef char singleton (generic_level).
    pub fn predef_char(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_char, super::predef::path_char())
    }
    /// Get the predef string singleton (generic_level).
    pub fn predef_string(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_string, super::predef::path_string())
    }
    /// Get the predef float singleton (generic_level).
    pub fn predef_float(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_float, super::predef::path_float())
    }
    /// Get the predef bool singleton (generic_level).
    pub fn predef_bool(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bool, super::predef::path_bool())
    }
    /// Get the predef unit singleton (generic_level).
    pub fn predef_unit(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_unit, super::predef::path_unit())
    }
    /// Get the predef exn singleton (generic_level).
    pub fn predef_exn(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_exn, super::predef::path_exn())
    }
    /// Get the predef bigint singleton (generic_level).
    pub fn predef_bigint(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bigint, super::predef::path_bigint())
    }

    /// The cached runtime layout of the predef `option` constructors.
    pub fn predef_option_layout(&self) -> super::variant_runtime::LayoutRef {
        if let Some(layout) = self.predef_option_layout.get() {
            layout
        } else {
            let layout = super::variant_runtime::plain_layout(
                self,
                [("None".to_string(), false), ("Some".to_string(), true)],
            );
            self.predef_option_layout.set(Some(layout));
            layout
        }
    }

    /// Get the cached generic option constructor scheme types.
    /// Returns (`'a`, `option('a)`), both allocated once at generic level.
    pub fn predef_option_scheme(&self) -> (TypeExprRef, TypeExprRef) {
        match (
            self.predef_option_inner.get(),
            self.predef_option_type.get(),
        ) {
            (Some(inner), Some(option_ty)) => (inner, option_ty),
            _ => {
                let inner = self.new_generic_var(None);
                let option_ty =
                    self.new_generic_predef_constr(super::predef::path_option(), vec![inner]);
                self.predef_option_inner.set(Some(inner));
                self.predef_option_type.set(Some(option_ty));
                (inner, option_ty)
            }
        }
    }

    /// Create a link type (for unification).
    pub fn new_link(&self, target: TypeExprRef) -> TypeExprRef {
        self.new_type(TypeDesc::Tlink(target))
    }

    /// Create a polymorphic type.
    pub fn new_poly(&self, body: TypeExprRef, vars: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Tpoly {
            body,
            vars: self.new_type_list(&vars),
        })
    }

    /// Create a universal type variable.
    pub fn new_univar(&self, name: Option<crate::name::Name>) -> TypeExprRef {
        self.new_type(TypeDesc::Tunivar(name))
    }

    /// Create a variant type.
    pub fn new_variant(&self, row: RowDesc) -> TypeExprRef {
        self.new_type(TypeDesc::Tvariant(self.new_row_desc(row)))
    }

    // ========================================================================
    // Type Access
    // ========================================================================

    /// The descriptor of a stored (worker-store or shared) node: this
    /// compilation's exception table copy if it wrote one, else the immutable
    /// published descriptor.
    #[inline(never)]
    fn store_desc(&self, r: TypeExprRef) -> TypeDesc {
        if self.compiler_counters_enabled && !self.store_build_owns(r) {
            crate::perf_counters::frozen::record(
                self,
                if r.is_shared() {
                    crate::perf_counters::frozen::Kind::DescReadShared
                } else {
                    crate::perf_counters::frozen::Kind::DescReadWorker
                },
            );
        }
        if self.frozen_writes.any.get() {
            self.frozen_writes.probe();
            if let Some(desc) = self.frozen_writes.descs.borrow().get(&r) {
                return *desc;
            }
        }
        if r.is_shared() {
            return super::shared_store::page_node(&self.shared_pages, r.shared_index()).desc;
        }
        self.store.desc(r)
    }

    /// The descriptor of `r`. Local nodes are by far the most common
    /// (hundreds of millions of reads per build), so their path is inlined
    /// into callers.
    #[inline(always)]
    fn desc(&self, r: TypeExprRef) -> TypeDesc {
        if let Some(node) = self.types.direct(r.0) {
            return node.desc.get();
        }
        self.desc_indirect(r)
    }

    /// Cost: O(1) local addressing or the existing stored-node lookup (expected
    /// O(1) exception-table probe when writes exist). Active builds also mark
    /// local reads as poisoned; optional debug tracing is outside this bound.
    #[inline(never)]
    fn desc_indirect(&self, r: TypeExprRef) -> TypeDesc {
        if r.is_store() {
            return self.store_desc(r);
        }
        self.poison_store_build();
        self.types.desc(r.index())
    }

    /// The descriptor of `r`, as a value the caller can hold across node
    /// mutations.
    #[inline]
    pub fn get_desc(&self, r: TypeExprRef) -> TypeDescSnapshot {
        TypeDescSnapshot(self.desc(r))
    }

    /// Apply `f` to the descriptor of `r`.
    #[inline(always)]
    pub(crate) fn with_desc<R>(&self, r: TypeExprRef, f: impl FnOnce(&TypeDesc) -> R) -> R {
        f(&self.desc(r))
    }

    /// The descriptor of `r` for a short read. Since descriptors are copied
    /// out, this is the same read as `get_desc`.
    #[inline]
    pub fn borrow_desc(&self, r: TypeExprRef) -> TypeDescRef<'_> {
        TypeDescRef(self.desc(r), std::marker::PhantomData)
    }

    /// Get the level of a type.
    #[inline]
    pub fn get_level(&self, r: TypeExprRef) -> i32 {
        if let Some(node) = self.types.direct(r.0) {
            return node.level.get();
        }
        self.level_indirect(r)
    }

    /// Cost: O(1) local addressing or the existing stored-level lookup (expected
    /// O(1) exception-table probe when writes exist), plus poison bookkeeping.
    /// Optional debug tracing is outside this bound.
    #[inline(never)]
    fn level_indirect(&self, r: TypeExprRef) -> i32 {
        if r.is_store() {
            return self.store_level(r);
        }
        self.poison_store_build();
        self.types.level(r.index())
    }

    #[inline(never)]
    fn store_level(&self, r: TypeExprRef) -> i32 {
        if self.compiler_counters_enabled && !self.store_build_owns(r) {
            crate::perf_counters::frozen::record(
                self,
                if r.is_shared() {
                    crate::perf_counters::frozen::Kind::LevelReadShared
                } else {
                    crate::perf_counters::frozen::Kind::LevelReadWorker
                },
            );
        }
        if self.frozen_writes.any.get() {
            self.frozen_writes.probe();
            if let Some(level) = self.frozen_writes.levels.borrow().get(&r) {
                return *level;
            }
        }
        if r.is_shared() {
            return super::shared_store::page_node(&self.shared_pages, r.shared_index()).level;
        }
        self.store.level(r)
    }

    /// Number of allocated type expressions.
    pub fn type_expr_count(&self) -> usize {
        self.types.count()
    }

    /// Preserve absence, not a copy of the published value, on the trail.
    fn frozen_mutation(&self, mutation: TypeMutation) -> TypeMutation {
        let cell = match &mutation {
            TypeMutation::TypeDesc(r, _) if r.is_store() => FrozenCell::Desc(*r),
            TypeMutation::TypeLevel(r, _) if r.is_store() => FrozenCell::Level(*r),
            TypeMutation::RowField(r, _) if r.is_store() => FrozenCell::RowField(*r),
            TypeMutation::Mutability(r, _) if r.is_persistent() => FrozenCell::Mutability(*r),
            _ => return mutation,
        };
        if self.frozen_writes.contains(cell) {
            mutation
        } else {
            TypeMutation::FrozenAbsent(cell)
        }
    }

    #[inline]
    fn record_type_mutation(
        &self,
        mutation: impl FnOnce() -> TypeMutation,
        ty: TypeExprRef,
        kind: crate::perf_counters::TypeMutationKind,
    ) {
        if !self.mutation_logging.full() || self.store_build_owns(ty) {
            return;
        }
        let mut journal = self.mutation_journal.borrow_mut();
        if journal.records_type(ty) {
            journal.push(self.frozen_mutation(mutation()));
            if self.compiler_counters_enabled {
                crate::perf_counters::record_type_mutation(self, kind);
            }
        }
    }

    #[inline]
    fn record_mutation(
        &self,
        mutation: impl FnOnce() -> TypeMutation,
        kind: crate::perf_counters::TypeMutationKind,
    ) {
        if !self.mutation_logging.full() {
            return;
        }
        self.mutation_journal.borrow_mut().push(self.frozen_mutation(mutation()));
        if self.compiler_counters_enabled {
            crate::perf_counters::record_type_mutation(self, kind);
        }
    }

    #[inline]
    fn record_row_field_mutation(&self, mutation: impl FnOnce() -> TypeMutation, row: RowFieldRef) {
        if !self.mutation_logging.full() || self.store_build_owns_row_field(row) {
            return;
        }
        let mut journal = self.mutation_journal.borrow_mut();
        if journal.records_row_field(row) {
            journal.push(self.frozen_mutation(mutation()));
            if self.compiler_counters_enabled {
                crate::perf_counters::record_type_mutation(
                    self,
                    crate::perf_counters::TypeMutationKind::Row,
                );
            }
        }
    }

    /// Set the level of a type. Stored nodes are never written in place
    /// unless the current store build is still creating them: the write goes
    /// to this compilation's exception table.
    #[inline]
    pub fn set_level(&self, r: TypeExprRef, level: i32) {
        self.record_type_mutation(
            || TypeMutation::TypeLevel(r, self.get_level(r)),
            r,
            crate::perf_counters::TypeMutationKind::Level,
        );
        self.write_level_raw(r, level);
    }

    /// Set the level of compilation-local node `r` the way [`Self::set_level`]
    /// would right after [`Self::snapshot_type_state`]: journaled whenever a
    /// full snapshot lives, whatever the node's age. (A new snapshot records
    /// every existing node; without one, a node younger than the innermost
    /// snapshot is not recorded.) For a walk that replaces one that took a
    /// snapshot of its own, so that an enclosing snapshot restores the same
    /// levels as before.
    #[inline]
    pub(crate) fn set_level_as_under_new_snapshot(&self, r: TypeExprRef, level: i32) {
        debug_assert!(!r.is_store());
        if self.mutation_logging.full() {
            self.mutation_journal
                .borrow_mut()
                .entries
                .push(TypeMutation::TypeLevel(r, self.types.level(r.index())));
            if self.compiler_counters_enabled {
                crate::perf_counters::record_type_mutation(
                    self,
                    crate::perf_counters::TypeMutationKind::Level,
                );
            }
        }
        self.poison_store_build();
        self.types.set_level(r.index(), level);
    }

    /// Level write without journaling (also used to undo).
    #[inline]
    fn write_level_raw(&self, r: TypeExprRef, level: i32) {
        if let Some(node) = self.types.direct(r.0) {
            node.level.set(level);
            return;
        }
        self.write_level_indirect(r, level)
    }

    /// Cost: O(1) for local/build-owned nodes, expected amortized O(1) for an
    /// existing frozen-write table insertion otherwise. No graph traversal;
    /// optional poison debug tracing is outside this bound.
    #[inline(never)]
    fn write_level_indirect(&self, r: TypeExprRef, level: i32) {
        if r.is_store() {
            if r.is_shared() {
                if self.compiler_counters_enabled {
                    crate::perf_counters::frozen::record(
                        self,
                        crate::perf_counters::frozen::Kind::LevelWriteShared,
                    );
                }
                self.frozen_writes.levels.borrow_mut().insert(r, level);
                self.frozen_writes.any.set(true);
                return;
            }
            if self.store_build_owns(r) {
                self.store.set_level_backing(r, level);
                return;
            }
            if self.compiler_counters_enabled {
                crate::perf_counters::frozen::record(
                    self,
                    crate::perf_counters::frozen::Kind::LevelWriteWorker,
                );
            }
            self.frozen_writes.levels.borrow_mut().insert(r, level);
            self.frozen_writes.any.set(true);
        } else {
            self.poison_store_build();
            self.types.set_level(r.index(), level);
        }
    }

    /// Set the descriptor without changing the immutable dependency graph.
    #[inline]
    pub fn set_desc(&self, r: TypeExprRef, desc: TypeDesc) {
        self.record_type_mutation(
            || TypeMutation::TypeDesc(r, self.desc(r)),
            r,
            crate::perf_counters::TypeMutationKind::Desc,
        );
        self.write_desc_raw(r, desc);
    }

    /// Descriptor write without journaling (also used to undo).
    #[inline]
    fn write_desc_raw(&self, r: TypeExprRef, desc: TypeDesc) {
        if let Some(node) = self.types.direct(r.0) {
            node.desc.set(desc);
            return;
        }
        self.write_desc_indirect(r, desc)
    }

    /// Cost: O(1) for local nodes, expected amortized O(1) for a frozen-write
    /// insertion. Build-owned descriptors retain the existing list-copy and
    /// validation cost, proportional to their payload. Optional poison debug
    /// tracing is outside these bounds.
    #[inline(never)]
    fn write_desc_indirect(&self, r: TypeExprRef, desc: TypeDesc) {
        if r.is_store() {
            if r.is_shared() {
                if self.compiler_counters_enabled {
                    crate::perf_counters::frozen::record(
                        self,
                        if matches!(desc, TypeDesc::Tlink(_)) {
                            crate::perf_counters::frozen::Kind::LinkShared
                        } else {
                            crate::perf_counters::frozen::Kind::DescWriteShared
                        },
                    );
                }
                self.frozen_writes.descs.borrow_mut().insert(r, desc);
                self.frozen_writes.any.set(true);
                return;
            }
            if self.store_build_owns(r) {
                let desc = self.store_desc_lists(desc);
                self.check_store_desc(&desc);
                self.store.set_desc_backing(r, desc);
                return;
            }
            if self.compiler_counters_enabled && matches!(desc, TypeDesc::Tlink(_)) {
                crate::perf_counters::frozen::record(
                    self,
                    crate::perf_counters::frozen::Kind::LinkWorker,
                );
            }
            self.frozen_writes.descs.borrow_mut().insert(r, desc);
            self.frozen_writes.any.set(true);
        } else {
            self.poison_store_build();
            self.types.set_desc(r.index(), desc);
        }
    }

    /// Create the `used_slot` of a warning-tracked open (env.ml:1842).
    pub(crate) fn new_open_slot(&self, loc: crate::parse_arena::LocIdx) -> u32 {
        let mut slots = self.open_slots.borrow_mut();
        slots.push(OpenSlotState {
            loc,
            used: false,
            shadowed: Vec::new(),
        });
        (slots.len() - 1) as u32
    }

    /// Record a `using name shadowed` call of an open's slot.
    pub(crate) fn record_open_slot_use(
        &self,
        slot: u32,
        kind: &'static str,
        name: &str,
        shadowed: bool,
    ) {
        self.assert_no_store_build("an open's use");
        self.open_slot_events
            .borrow_mut()
            .push(LookupEvent::OpenSlot(OpenSlotEvent {
                slot,
                kind,
                name: name.to_string(),
                shadowed,
            }));
    }

    /// Building shared store data never reports anything: the data is used
    /// by compilations that did not build it, so what a build recorded would
    /// be reported by one of them only, and which one would depend on
    /// scheduling. Every sink of this context that feeds a diagnostic calls
    /// this; lookups report from the consuming compilation instead.
    #[inline]
    #[track_caller]
    fn assert_no_store_build(&self, what: &str) {
        debug_assert!(
            !self.in_store_build(),
            "{what} was recorded while building shared store data"
        );
    }

    /// Record a `report_deprecated` call of a module lookup.
    pub(crate) fn record_module_deprecation(&self, deprecation: ModuleDeprecation) {
        self.assert_no_store_build("a module deprecation");
        self.open_slot_events
            .borrow_mut()
            .push(LookupEvent::ModuleDeprecated(deprecation));
    }

    /// Queue parser warnings produced while re-parsing source.
    pub(crate) fn push_reparse_warnings(&self, warnings: &[crate::parser::ParserWarning]) {
        self.assert_no_store_build("a parser warning");
        self.reparse_warnings
            .borrow_mut()
            .extend_from_slice(warnings);
    }

    pub(crate) fn take_reparse_warnings(&self) -> Vec<crate::parser::ParserWarning> {
        std::mem::take(&mut *self.reparse_warnings.borrow_mut())
    }

    /// Record the warning state at the outermost structure entry.
    pub(crate) fn note_report_warning_config(&self, config: &crate::diagnostics::WarningConfig) {
        let mut slot = self.report_warning_config.borrow_mut();
        if slot.is_none() {
            *slot = Some(config.clone());
        }
    }

    pub(crate) fn report_warning_config(&self) -> crate::diagnostics::WarningConfig {
        self.report_warning_config
            .borrow()
            .clone()
            .unwrap_or_default()
    }

    /// `Cmt_format.record_value_dependency` (cmt_format_common.ml:180-183).
    pub(crate) fn record_value_dependency(
        &self,
        vd1: &super::decl::ValueDescription,
        vd2: &super::decl::ValueDescription,
    ) {
        // OCaml compares the locations structurally (`<>`), so two
        // `Location.none`s are equal whichever way they were spelled here.
        let same = self.location_key(&self.resolve_loc(vd1.val_loc))
            == self.location_key(&self.resolve_loc(vd2.val_loc));
        if !same {
            self.value_deps
                .borrow_mut()
                .push((vd1.clone(), vd2.clone()));
        }
    }

    /// A location as the saved `Location.t` value: positions with resolved
    /// file names, and Rust's `Location::none` spelled as OCaml's `in_file
    /// "_none_"` position (location.ml).
    fn location_key(&self, loc: &crate::location::Location) -> (PositionKey, PositionKey, bool) {
        (
            self.position_key(&loc.loc_start),
            self.position_key(&loc.loc_end),
            loc.loc_ghost,
        )
    }

    fn position_key(&self, pos: &crate::location::Position) -> PositionKey {
        if pos.file_name == crate::intern::StrIdx::default() && pos.line == 0 {
            return (Err("_none_".to_string()), 1, 0, -1);
        }
        let name = self
            .resolve_any_longident_component(pos.file_name)
            .map(Err)
            .unwrap_or(Ok(pos.file_name.raw()));
        (name, pos.line, pos.bol, pos.cnum)
    }

    /// `Cmt_format.record_deprecated_used`.
    pub(crate) fn record_deprecated_used(&self, used: DeprecatedUse) {
        self.assert_no_store_build("a deprecated use");
        self.deprecated_used.borrow_mut().push(used);
    }

    /// Recorded deprecated uses, most recent first (as OCaml's list).
    pub fn deprecated_uses(&self) -> Vec<DeprecatedUse> {
        self.deprecated_used
            .borrow()
            .iter()
            .rev()
            .cloned()
            .collect()
    }

    /// Recorded value dependencies, most recent first (as OCaml's list).
    pub fn value_dependencies(
        &self,
    ) -> Vec<(super::decl::ValueDescription, super::decl::ValueDescription)> {
        self.value_deps.borrow().iter().rev().cloned().collect()
    }

    /// The usage tables of OCaml `Env` (env.ml:27-53).
    pub(crate) fn usage(&self) -> std::cell::RefMut<'_, super::usage::UsageTables> {
        self.usage.borrow_mut()
    }

    /// Record that a signature requires an effect of the value matched
    /// against one of its declarations.
    pub(crate) fn require_effect(&self, obligation: crate::verify::purity::Obligation) {
        self.effect_obligations.borrow_mut().push(obligation);
    }

    /// The effects signatures required so far, leaving none.
    pub(crate) fn take_effect_obligations(&self) -> Vec<crate::verify::purity::Obligation> {
        std::mem::take(&mut *self.effect_obligations.borrow_mut())
    }

    /// Whether a signature required an effect of a value.
    pub(crate) fn has_effect_obligations(&self) -> bool {
        !self.effect_obligations.borrow().is_empty()
    }

    pub(crate) fn take_open_slot_events(&self) -> Vec<LookupEvent> {
        std::mem::take(&mut *self.open_slot_events.borrow_mut())
    }

    /// Run `f` on the state of an open's slot.
    pub(crate) fn with_open_slot<R>(
        &self,
        slot: u32,
        f: impl FnOnce(&mut OpenSlotState) -> R,
    ) -> R {
        f(&mut self.open_slots.borrow_mut()[slot as usize])
    }

    /// Record `full_expand env ty` for a type in a failed unification trace.
    pub(crate) fn record_trace_expansion(&self, ty: TypeExprRef, expansion: TypeExprRef) {
        self.trace_expansions.borrow_mut().insert(ty, expansion);
    }

    /// The recorded `full_expand` of a trace type, if its unification failed
    /// with an environment.
    pub fn trace_expansion(&self, ty: TypeExprRef) -> Option<TypeExprRef> {
        self.trace_expansions.borrow().get(&ty).copied()
    }

    /// Start an OCaml-style speculative mutation trail.
    ///
    /// The snapshot is only a journal cursor plus the current type allocation
    /// frontier. Backtracking replays mutations in reverse. Allocations and
    /// unrelated lazy caches intentionally remain alive, matching Btype.
    pub(crate) fn snapshot_type_state(&self) -> TypeMutationSnapshot<'_> {
        self.snapshot_type_state_with(true)
    }

    /// A snapshot that is only passed to [`Self::undo_compress`] (OCaml's
    /// outer `unify`, ctype.ml:2589-2594), never restored: it needs the path
    /// compressions logged since it, not every change.
    pub(crate) fn snapshot_type_state_for_undo_compress(&self) -> TypeMutationSnapshot<'_> {
        self.snapshot_type_state_with(false)
    }

    fn snapshot_type_state_with(&self, full: bool) -> TypeMutationSnapshot<'_> {
        let mut journal = self.mutation_journal.borrow_mut();
        let id = journal.next_id;
        journal.next_id += 1;
        let cursor = journal.entries.len();
        journal.active.push(ActiveTypeSnapshot {
            id,
            full,
            type_len: self.types.len(),
            row_field_len: self.row_fields.borrow().len(),
        });
        let depth = journal.active.len();
        self.mutation_logging.update(&journal);
        if self.compiler_counters_enabled {
            crate::perf_counters::record_type_mutation_snapshot(self, depth);
        }
        TypeMutationSnapshot {
            journal: &self.mutation_journal,
            logging: &self.mutation_logging,
            cursor,
            id,
            restored: false,
        }
    }

    /// btype.ml `undo_compress`: revert the path compressions made since
    /// `snapshot` whose nodes still hold the compressed link, leaving every
    /// other change (and the snapshot) in place.
    pub(crate) fn undo_compress(&self, snapshot: &TypeMutationSnapshot<'_>) {
        let compressions: Vec<(TypeExprRef, TypeDesc, TypeExprRef)> = {
            let journal = self.mutation_journal.borrow();
            if !journal.active.iter().any(|active| active.id == snapshot.id) {
                return;
            }
            journal.entries[snapshot.cursor.min(journal.entries.len())..]
                .iter()
                .filter_map(|mutation| match mutation {
                    TypeMutation::Compress(ty, old, target) => Some((*ty, *old, *target)),
                    _ => None,
                })
                .collect()
        };
        for (ty, old, target) in compressions {
            if matches!(self.get_desc(ty).0, TypeDesc::Tlink(current) if current == target) {
                self.write_desc_raw(ty, old);
            }
        }
    }

    /// Backtrack to a mutation-trail cursor.
    ///
    /// Restoring an outer snapshot also invalidates every still-live nested
    /// snapshot. A later restore of one of those descendants is a no-op.
    pub(crate) fn restore_type_state(&self, mut snapshot: TypeMutationSnapshot<'_>) {
        let mutations = {
            let mut journal = self.mutation_journal.borrow_mut();
            let Some(active_index) = journal
                .active
                .iter()
                .position(|active| active.id == snapshot.id)
            else {
                snapshot.restored = true;
                return;
            };
            let mutations = journal.entries.split_off(snapshot.cursor);
            debug_assert!(
                journal.active[active_index].full,
                "a compress-only snapshot is never restored"
            );
            journal.active.truncate(active_index);
            if journal.active.is_empty() {
                journal.entries.clear();
            }
            self.mutation_logging.update(&journal);
            mutations
        };
        // btype.ml:692-700 `backtrack`: when anything was trailed it first
        // runs `cleanup_abbrev ()`, forgetting every memorized expansion
        // (including those made since the snapshot); memo contents are not
        // part of OCaml's trail, so they are not restored either.
        let has_changes = mutations.iter().any(|mutation| {
            matches!(
                mutation,
                TypeMutation::FrozenAbsent(..)
                    | TypeMutation::TypeDesc(..)
                    | TypeMutation::Compress(..)
                    | TypeMutation::TypeLevel(..)
                    | TypeMutation::RowField(..)
                    | TypeMutation::Mutability(..)
            )
        });
        if has_changes {
            let refs = std::mem::take(&mut *self.memoized_abbrev_refs.borrow_mut());
            for memo in refs {
                self.write_abbrev(memo, AbbrevMemo::Mnil);
            }
        }
        let mut restored = 0;
        for mutation in mutations.into_iter().rev() {
            match mutation {
                TypeMutation::FrozenAbsent(cell) => {
                    self.frozen_writes.remove(cell);
                    restored += 1;
                }
                TypeMutation::TypeDesc(ty, desc) | TypeMutation::Compress(ty, desc, _) => {
                    self.write_desc_raw(ty, desc);
                    restored += 1;
                }
                TypeMutation::TypeLevel(ty, level) => {
                    self.write_level_raw(ty, level);
                    restored += 1;
                }
                TypeMutation::RowField(row, field) => {
                    self.write_row_field_raw(row, field);
                    restored += 1;
                }
                TypeMutation::Mutability(cell, value) => {
                    self.write_mutability_raw(cell, value);
                    restored += 1;
                }
                TypeMutation::CurrentAbbreviations(value) => {
                    self.current_abbreviations.set(value);
                    restored += 1;
                }
                TypeMutation::CurrentLevel(value) => {
                    self.current_level.set(value);
                    restored += 1;
                }
                TypeMutation::NongenLevel(value) => {
                    self.nongen_level.set(value);
                    restored += 1;
                }
                TypeMutation::GlobalLevel(value) => {
                    self.global_level.set(value);
                    restored += 1;
                }
                TypeMutation::SavedLevels(value) => {
                    *self.saved_levels.borrow_mut() = value;
                    restored += 1;
                }
            }
        }
        snapshot.restored = true;
        if self.compiler_counters_enabled {
            crate::perf_counters::record_type_mutation_backtrack(self, restored);
        }
    }

    // ========================================================================
    // Arity Aliases (sexp dedup for update_uncurried_arity)
    // ========================================================================

    /// Record that `new_ref` is an arity-updated version of `original_ref`.
    /// The sexp serializer will use `original_ref` as the dedup key for both.
    pub fn set_arity_alias(&self, new_ref: TypeExprRef, original_ref: TypeExprRef) {
        self.poison_store_build_for("set_arity_alias");
        self.arity_aliases
            .borrow_mut()
            .insert(new_ref, original_ref);
    }

    /// Get the arity alias for a TypeExprRef, if any.
    pub fn get_arity_alias(&self, te: TypeExprRef) -> Option<TypeExprRef> {
        self.arity_aliases.borrow().get(&te).copied()
    }

    /// The summary of the label array `lbl_all`, computed once per array.
    pub(crate) fn label_family_summary(
        &self,
        lbl_all: super::decl::LabelArrayRef,
    ) -> Option<Arc<RecordLabelDescriptionSummary>> {
        if let Some(summary) = self.label_family_summaries.borrow().get(&lbl_all) {
            return Some(summary.clone());
        }
        let labels = self.label_family(lbl_all)?;
        let summary = Arc::new(RecordLabelDescriptionSummary::from_labels(&labels));
        self.label_family_summaries
            .borrow_mut()
            .insert(lbl_all, summary.clone());
        Some(summary)
    }

    /// The handle the next array pushed by `push_label_family` gets: in the
    /// worker store's pool during a store build (what it builds is shared
    /// with later compilations), otherwise in this compilation's pool.
    fn next_label_family(&self) -> super::decl::LabelArrayRef {
        if self.in_store_build() {
            super::decl::LabelArrayRef::store(self.store.label_family_count())
        } else {
            super::decl::LabelArrayRef::local(self.label_families.borrow().len())
        }
    }

    fn push_label_family(
        &self,
        labels: Arc<Vec<super::decl::LabelDescription>>,
    ) -> super::decl::LabelArrayRef {
        if self.in_store_build() {
            super::decl::LabelArrayRef::store(self.store.push_label_family(labels))
        } else {
            let mut families = self.label_families.borrow_mut();
            families.push(labels);
            super::decl::LabelArrayRef::local(families.len() - 1)
        }
    }

    /// Store the labels built by `build`, which receives the `lbl_all`
    /// reference they share (OCaml ties that knot by mutating `lbl_all`,
    /// compiler/ml/datarepr.ml:261-288).
    pub fn alloc_label_array(
        &self,
        build: impl FnOnce(super::decl::LabelArrayRef) -> Vec<super::decl::LabelDescription>,
    ) -> Vec<super::decl::LabelDescription> {
        let lbl_all = self.next_label_family();
        let labels = build(lbl_all);
        let pushed = self.push_label_family(Arc::new(labels.clone()));
        debug_assert_eq!(pushed, lbl_all);
        labels
    }

    /// The array a label's `lbl_all` names; `None` for `LabelArrayRef::NONE`.
    pub fn label_family(
        &self,
        lbl_all: super::decl::LabelArrayRef,
    ) -> Option<Arc<Vec<super::decl::LabelDescription>>> {
        use super::decl::LabelArrayTier;
        match lbl_all.tier()? {
            LabelArrayTier::Frozen(index) => self.world().label_array(index).cloned(),
            LabelArrayTier::Store(store_idx) => self.store.label_family(store_idx),
            LabelArrayTier::Local(local_idx) => self.label_families.borrow().get(local_idx).cloned(),
        }
    }

    /// The labels of `lbl_all`, when this compilation registered it.
    pub fn label_all(
        &self,
        lbl_all: super::decl::LabelArrayRef,
    ) -> Option<Vec<super::decl::LabelDescription>> {
        self.label_family(lbl_all).map(|labels| labels.to_vec())
    }

    // ========================================================================
    // Simple Abbreviations (cross-instance sharing for nullary Tconstr)
    // ========================================================================

    /// OCaml's check_abbrev_env: clear abbreviation cache when environment changes.
    /// OCaml calls cleanup_abbrev() which clears ALL registered memo refs including
    /// simple_abbrevs when it has memoized entries.
    /// OCaml uses physical env inequality (!=); Rust uses env ID comparison.
    pub fn check_abbrev_env(&self, env: &crate::types::env::Env) {
        let env_id = env.id();
        if Some(env_id) != self.previous_env_id.get() {
            self.clear_abbrev_memos();
            self.previous_env_id.set(Some(env_id));
        }
    }

    /// Access the dedicated simple_abbrevs memo reference.
    pub fn simple_abbrevs_memo(&self) -> AbbrevMemoRef {
        self.simple_abbrevs.get()
    }

    /// Clear simple abbreviations. Called during generalize/generalize_structure,
    /// matching OCaml's `simple_abbrevs := Mnil`.
    pub fn clear_simple_abbrevs(&self) {
        let simple = self.simple_abbrevs.get();
        if simple != AbbrevMemoRef::nil() {
            self.clear_abbrev_memo(simple);
        }
    }

    /// Clear all per-node abbreviation memo chains (OCaml cleanup_abbrev).
    pub fn clear_abbrev_memos(&self) {
        let refs = self.memoized_abbrev_refs.borrow().clone();
        for memo in refs {
            self.write_abbrev(memo, AbbrevMemo::Mnil);
        }
        self.memoized_abbrev_refs.borrow_mut().clear();
    }

    /// Current value of a memo cell: this compilation's exception table for store
    /// cells, the local table otherwise. Missing cells read as `Mnil`.
    fn read_abbrev(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        if memo.is_store() {
            if self.frozen_writes.any.get() {
                self.frozen_writes.probe();
                if let Some(value) = self.frozen_writes.memos.borrow().get(&memo) {
                    return value.clone();
                }
            }
            return if memo.is_shared() { AbbrevMemo::Mnil } else { self.store.abbrev(memo) };
        }
        let abbrevs = self.abbrevs.borrow();
        abbrevs
            .get(memo.index())
            .map(|cell| cell.borrow().clone())
            .unwrap_or(AbbrevMemo::Mnil)
    }

    /// Apply `f` to a memo cell without copying it (the chain scans below
    /// only compare paths and follow `next`).
    fn with_abbrev<R>(&self, memo: AbbrevMemoRef, f: impl FnOnce(&AbbrevMemo) -> R) -> R {
        if memo.is_store() {
            if self.frozen_writes.any.get() {
                self.frozen_writes.probe();
                if let Some(value) = self.frozen_writes.memos.borrow().get(&memo) {
                    return f(value);
                }
            }
            return if memo.is_shared() { f(&AbbrevMemo::Mnil) } else { self.store.with_abbrev(memo, f) };
        }
        let abbrevs = self.abbrevs.borrow();
        match abbrevs.get(memo.index()) {
            Some(cell) => f(&cell.borrow()),
            None => f(&AbbrevMemo::Mnil),
        }
    }

    /// Write a memo cell; store cells are written to this compilation's
    /// overlay only. Missing local cells are ignored.
    fn write_abbrev(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if self.compiler_counters_enabled
            && memo.is_store()
            && (memo.is_shared()
                || !self.in_store_build()
                || memo.store_index() < self.store_build_abbrev_start.get())
        {
            crate::perf_counters::frozen::record(
                self,
                crate::perf_counters::frozen::Kind::MemoWrite,
            );
        }
        if memo.is_store() {
            if !memo.is_shared() && self.in_store_build()
                && memo.store_index() >= self.store_build_abbrev_start.get()
            {
                match &value {
                    AbbrevMemo::Mcons { abbrev, expansion, next, .. } => {
                        self.check_store_ref(*abbrev);
                        self.check_store_ref(*expansion);
                        self.check_store_memo(*next);
                    }
                    AbbrevMemo::Mlink(next) => self.check_store_memo(*next),
                    AbbrevMemo::Mnil => {}
                }
                self.store.set_abbrev_backing(memo, value);
                return;
            }
            // Memos are caches, not semantic trail entries (btype.ml:692-700).
            // Shared memos are published empty, so clearing one removes its exception.
            if memo.is_shared() && matches!(value, AbbrevMemo::Mnil) {
                self.frozen_writes.remove(FrozenCell::Memo(memo));
            } else {
                self.frozen_writes.memos.borrow_mut().insert(memo, value);
                self.frozen_writes.any.set(true);
            }
            return;
        }
        let abbrevs = self.abbrevs.borrow();
        if let Some(cell) = abbrevs.get(memo.index()) {
            *cell.borrow_mut() = value;
        }
    }

    /// Get the current abbreviation context (set during subst_with_memo).
    pub fn current_abbreviations(&self) -> AbbrevMemoRef {
        self.current_abbreviations.get()
    }

    /// Set the current abbreviation context.
    pub fn set_current_abbreviations(&self, abbrev: AbbrevMemoRef) {
        self.record_mutation(
            || TypeMutation::CurrentAbbreviations(self.current_abbreviations.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.current_abbreviations.set(abbrev);
    }

    /// Walk an abbreviation memo chain (following `Mlink`s) and return the
    /// first `Mcons` entry for which `select(private_flag, path, abbrev,
    /// expansion)` yields a type.
    ///
    /// The walk gives up after 128 cells; OCaml's `find_expans`/`find_repr`
    /// (ctype.ml) recurse without a bound.
    fn scan_abbrev_chain(
        &self,
        memo: AbbrevMemoRef,
        select: impl Fn(PrivateFlag, &Path, TypeExprRef, TypeExprRef) -> Option<TypeExprRef>,
    ) -> Option<TypeExprRef> {
        let mut current = memo;
        for _ in 0..128 {
            let step = self.with_abbrev(current, |node| match node {
                AbbrevMemo::Mnil => Err(None),
                AbbrevMemo::Mcons {
                    private_flag,
                    path,
                    abbrev,
                    expansion,
                    next,
                } => match select(*private_flag, path, *abbrev, *expansion) {
                    Some(found) => Err(Some(found)),
                    None => Ok(*next),
                },
                AbbrevMemo::Mlink(next) => Ok(*next),
            });
            match step {
                Ok(next) => current = next,
                Err(found) => return found,
            }
        }
        None
    }

    /// Find a cached expansion for `(priv,path)` in an abbreviation memo chain.
    pub fn find_abbrev_expansion(
        &self,
        memo: AbbrevMemoRef,
        private_flag: PrivateFlag,
        path: &Path,
    ) -> Option<TypeExprRef> {
        self.scan_abbrev_chain(memo, |cached_private, cached_path, _, expansion| {
            (private_flag <= cached_private && path.same(cached_path)).then_some(expansion)
        })
    }

    /// Find the original type (abbrev field) for a path in a memo chain.
    /// This is OCaml's `find_repr` — returns the ORIGINAL type node that was
    /// memoized, creating Tlink sharing in copy_type_cached.
    pub fn find_abbrev_repr(&self, memo: AbbrevMemoRef, path: &Path) -> Option<TypeExprRef> {
        // Match OCaml find_repr: only public memo entries participate in repr
        // reuse during copy.
        self.scan_abbrev_chain(memo, |cached_private, cached_path, abbrev, _| {
            (cached_private == PrivateFlag::Public && path.same(cached_path)).then_some(abbrev)
        })
    }

    /// Snapshot an abbreviation memo node.
    pub fn get_abbrev_memo(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        self.read_abbrev(memo)
    }

    /// Reset a per-node abbreviation memo chain to Mnil.
    pub fn clear_abbrev_memo(&self, memo: AbbrevMemoRef) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        self.write_abbrev(memo, AbbrevMemo::Mnil);
    }

    /// Overwrite a per-node abbreviation memo chain with a saved snapshot.
    pub fn restore_abbrev_memo(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        self.write_abbrev(memo, value);
    }

    /// Prepend a cached abbreviation expansion to a node-local memo chain.
    pub fn memorize_abbrev_expansion(
        &self,
        memo: AbbrevMemoRef,
        private_flag: PrivateFlag,
        path: Path,
        abbrev: TypeExprRef,
        expansion: TypeExprRef,
    ) {
        // Nil is a shared sentinel and must not be mutated.
        if memo == AbbrevMemoRef::nil() {
            return;
        }

        if memo.is_store() {
            let previous = self.read_abbrev(memo);
            let next = if matches!(previous, AbbrevMemo::Mnil) {
                AbbrevMemoRef::nil()
            } else {
                self.alloc_abbrev(previous)
            };
            self.write_abbrev(
                memo,
                AbbrevMemo::Mcons {
                    private_flag,
                    path,
                    abbrev,
                    expansion,
                    next,
                },
            );
            self.memoized_abbrev_refs.borrow_mut().push(memo);
            return;
        }

        {
            let mut abbrevs = self.abbrevs.borrow_mut();
            let memo_idx = memo.index();
            if memo_idx >= abbrevs.len() {
                return;
            }

            let previous = abbrevs[memo_idx].borrow().clone();
            let next = if matches!(previous, AbbrevMemo::Mnil) {
                AbbrevMemoRef::nil()
            } else {
                let idx = abbrevs.len();
                abbrevs.push(RefCell::new(previous));
                AbbrevMemoRef::from_usize(idx)
            };

            *abbrevs[memo_idx].borrow_mut() = AbbrevMemo::Mcons {
                private_flag,
                path,
                abbrev,
                expansion,
                next,
            };
        }
        self.memoized_abbrev_refs.borrow_mut().push(memo);
    }

    // ========================================================================
    // Abbreviation Memos
    // ========================================================================

    /// Allocate an abbreviation memo (Mnil).
    pub fn alloc_abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    /// Allocate an abbreviation memo.
    pub fn alloc_abbrev(&self, memo: AbbrevMemo) -> AbbrevMemoRef {
        if self.in_store_build() {
            if let AbbrevMemo::Mcons {
                abbrev,
                expansion,
                next,
                ..
            } = &memo
            {
                self.check_store_ref(*abbrev);
                self.check_store_ref(*expansion);
                self.check_store_memo(*next);
            }
            return self.store.alloc_abbrev(memo);
        }
        let mut abbrevs = self.abbrevs.borrow_mut();
        let idx = abbrevs.len();
        abbrevs.push(RefCell::new(memo));
        AbbrevMemoRef::from_usize(idx)
    }

    // ========================================================================
    // Row Fields
    // ========================================================================

    /// Allocate a row field reference.
    pub fn alloc_row_field(&self, field: Option<RowField>) -> RowFieldRef {
        if self.in_store_build() {
            if let Some(field) = &field {
                self.check_store_row_field(field);
            }
            return self.store.alloc_row_field(field);
        }
        let mut row_fields = self.row_fields.borrow_mut();
        let idx = row_fields.len();
        row_fields.push(RefCell::new(field));
        RowFieldRef::from_usize(idx)
    }

    /// Get the value stored in a row field reference.
    pub fn get_row_field(&self, rf: RowFieldRef) -> Option<RowField> {
        if rf.is_null() {
            return None;
        }
        if rf.is_store() {
            if self.frozen_writes.any.get() {
                self.frozen_writes.probe();
                if let Some(value) = self.frozen_writes.row_fields.borrow().get(&rf) {
                    return value.clone();
                }
            }
            return self.store.row_field(rf);
        }
        let row_fields = self.row_fields.borrow();
        row_fields
            .get(rf.index())
            .and_then(|cell| cell.borrow().clone())
    }

    /// Set the value of a row field reference (like OCaml's set_row_field).
    pub fn set_row_field(&self, rf: RowFieldRef, field: RowField) {
        self.write_row_field(rf, Some(field));
    }

    /// Clear the value stored in a row field reference.
    pub fn clear_row_field(&self, rf: RowFieldRef) {
        self.write_row_field(rf, None);
    }

    fn write_row_field(&self, rf: RowFieldRef, value: Option<RowField>) {
        if rf.is_null() {
            return;
        }
        self.record_row_field_mutation(|| TypeMutation::RowField(rf, self.get_row_field(rf)), rf);
        self.write_row_field_raw(rf, value);
    }

    /// Row field write without journaling (also used to undo). Store rows
    /// still being built are written in place; other store rows go to this
    /// compilation's exception table.
    fn write_row_field_raw(&self, rf: RowFieldRef, value: Option<RowField>) {
        if rf.is_null() {
            return;
        }
        if rf.is_store() {
            if self.store_build_owns_row_field(rf) {
                if let Some(field) = &value {
                    self.check_store_row_field(field);
                }
                self.store.set_row_field_backing(rf, value);
                return;
            }
            if self.compiler_counters_enabled {
                crate::perf_counters::frozen::record(
                    self,
                    crate::perf_counters::frozen::Kind::RowFieldWrite,
                );
            }
            self.frozen_writes.row_fields.borrow_mut().insert(rf, value);
            self.frozen_writes.any.set(true);
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.index()) {
            *cell.borrow_mut() = value;
        }
    }

    // ========================================================================
    // Object-field mutability cells
    // ========================================================================

    /// Allocate a mutability cell holding `value` (OCaml `ref value`).
    pub fn alloc_mutability(&self, value: FieldMutability) -> MutabilityRef {
        if self.in_store_build() {
            // Store graphs only hold persistent value cells.
            match value {
                FieldMutability::Value(flag) => return MutabilityRef::new_persistent(flag),
                FieldMutability::Link(_) => self.poison_store_build(),
            }
        }
        let mut cells = self.mutabilities.borrow_mut();
        let idx = cells.len();
        cells.push(Cell::new(value));
        MutabilityRef::from_usize(idx)
    }

    /// The contents of a mutability cell (OCaml `!r`).
    pub fn get_mutability(&self, r: MutabilityRef) -> FieldMutability {
        if r.is_persistent() {
            if self.frozen_writes.any.get() {
                self.frozen_writes.probe();
                if let Some(value) = self.frozen_writes.mutabilities.borrow().get(&r) {
                    return *value;
                }
            }
            return FieldMutability::Value(r.persistent_value());
        }
        self.mutabilities.borrow()[r.index()].get()
    }

    /// btype.ml `mutability_ref_repr`: chase links to the terminal cell.
    pub fn mutability_ref_repr(&self, mut r: MutabilityRef) -> MutabilityRef {
        loop {
            match self.get_mutability(r) {
                FieldMutability::Link(next) => r = next,
                FieldMutability::Value(_) => return r,
            }
        }
    }

    /// btype.ml `mutability_repr`: the semantic value of a cell's class.
    pub fn mutability_repr(&self, r: MutabilityRef) -> super::asttypes::MutableFlag {
        match self.get_mutability(self.mutability_ref_repr(r)) {
            FieldMutability::Value(flag) => flag,
            FieldMutability::Link(_) => unreachable!("mutability_ref_repr returns a value cell"),
        }
    }

    /// btype.ml `set_mutability`: logged (backtrackable) update of a terminal
    /// cell. Link compression and separately allocated references cannot use
    /// the node-age test, so the change is logged whenever a trail is active.
    pub fn set_mutability(&self, r: MutabilityRef, value: FieldMutability) {
        if r.is_persistent() && self.in_store_build() {
            // A semantic change to a dependency cell would not travel with the
            // shared result.
            self.poison_store_build();
        }
        // Only a full snapshot restores semantic changes.
        if self.mutation_logging.full() {
            let old = self.get_mutability(r);
            self.mutation_journal
                .borrow_mut()
                .entries
                .push(self.frozen_mutation(TypeMutation::Mutability(r, old)));
        }
        self.write_mutability_raw(r, value);
    }

    /// Unlogged cell write (copy-session links and their restoration, undo).
    fn write_mutability_raw(&self, r: MutabilityRef, value: FieldMutability) {
        if r.is_persistent() {
            if self.compiler_counters_enabled {
                crate::perf_counters::frozen::record(
                    self,
                    crate::perf_counters::frozen::Kind::MutabilityWrite,
                );
            }
            self.frozen_writes.mutabilities.borrow_mut().insert(r, value);
            self.frozen_writes.any.set(true);
            return;
        }
        self.mutabilities.borrow()[r.index()].set(value);
    }

    // ========================================================================
    // Graph-copy sessions (btype.ml `type_copy_session`)
    // ========================================================================

    /// btype.ml `with_copy_session`: run a graph-copy operation with scoped
    /// temporary state. The scope is nestable and restores its own temporary
    /// mutability links on return (and on unwinding).
    pub fn with_copy_session<R>(&self, f: impl FnOnce() -> R) -> R {
        struct Guard<'a>(&'a TypeContext);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.end_copy_session();
            }
        }
        self.begin_copy_session();
        let _guard = Guard(self);
        f()
    }

    /// For the compiler counters: whether the function asking should count
    /// this call. A counted function starts with
    ///
    /// ```ignore
    /// if ctx.counts_this_call() {
    ///     return ctx.counted_copy(cause, || this_function(same arguments));
    /// }
    /// ```
    ///
    /// so that with the counters off it pays this one test and its body is
    /// what it was. With them on, the counting code calls the function
    /// again, and that second call, which must not count itself, gets
    /// `false` here.
    #[inline]
    pub(crate) fn counts_this_call(&self) -> bool {
        self.compiler_counters_enabled && !self.counted_call_reentered.replace(false)
    }

    /// See [`Self::counts_this_call`]: run `again`, the calling function
    /// called again, and count the type nodes it allocates as copied for
    /// `cause`. Nodes of a counted copy nested in it are counted once, for
    /// the inner cause.
    #[cold]
    #[inline(never)]
    pub(crate) fn counted_copy<R>(
        &self,
        cause: crate::perf_counters::CopyCause,
        again: impl FnOnce() -> R,
    ) -> R {
        let allocated = self.allocated_type_nodes();
        let counted = self.counted_copy_nodes.get();
        self.counted_call_reentered.set(true);
        let result = again();
        self.counted_call_reentered.set(false);
        let nested = self.counted_copy_nodes.get() - counted;
        let own = self.allocated_type_nodes() - allocated - nested;
        self.counted_copy_nodes.set(counted + nested + own);
        crate::perf_counters::record_copy(self, cause, own);
        result
    }

    /// The type nodes this compilation has allocated so far, in its own
    /// pool and in the worker store.
    fn allocated_type_nodes(&self) -> usize {
        self.types.len() + self.store.type_count()
    }

    /// btype.ml `begin_type_copy_session`.
    pub(crate) fn begin_copy_session(&self) {
        self.copy_sessions.borrow_mut().push(CopySession::default());
    }

    /// btype.ml `end_type_copy_session`.
    pub(crate) fn end_copy_session(&self) {
        let session = self
            .copy_sessions
            .borrow_mut()
            .pop()
            .expect("copy session stack underflow");
        for (r, value) in session.saved_mutabilities.into_iter().rev() {
            match value {
                Some(value) => self.write_mutability_raw(r, value),
                None => self.frozen_writes.remove(FrozenCell::Mutability(r)),
            }
        }
    }

    /// btype.ml `dup_mutability`: duplicate a mutability class for the
    /// current copy session. The source representative temporarily links to
    /// the duplicate, so all fields in this session which shared the source
    /// class reach the same duplicate.
    pub fn dup_mutability(&self, r: MutabilityRef) -> MutabilityRef {
        let r = self.mutability_ref_repr(r);
        let in_session = match self.copy_sessions.borrow().last() {
            Some(session) => {
                if session.new_mutabilities.contains(&r) {
                    return r;
                }
                true
            }
            None => false,
        };
        if !in_session {
            // A copy outside any session (a Rust-only structural copy) gets
            // an independent cell.
            return self.alloc_mutability(self.get_mutability(r));
        }
        let old = self.get_mutability(r);
        let r2 = self.alloc_mutability(old);
        {
            let mut sessions = self.copy_sessions.borrow_mut();
            let session = sessions
                .last_mut()
                .expect("dup_mutability outside a copy session");
            session.new_mutabilities.push(r2);
            let saved = if r.is_persistent()
                && !self.frozen_writes.contains(FrozenCell::Mutability(r))
            {
                None
            } else {
                Some(old)
            };
            session.saved_mutabilities.push((r, saved));
        }
        self.write_mutability_raw(r, FieldMutability::Link(r2));
        r2
    }

    /// btype.ml `row_terminator_generic`: whether an object row being copied
    /// ends in a generic variable (a scheme instantiation), memoized per node
    /// for the session. `copied` follows a node already copied in this
    /// session to its copy (OCaml's `Tsubst` mark).
    pub fn row_terminator_generic(
        &self,
        rest: TypeExprRef,
        copied: &dyn Fn(TypeExprRef) -> Option<TypeExprRef>,
    ) -> bool {
        let t = self.repr(rest);
        if let Some(b) = self
            .copy_sessions
            .borrow()
            .last()
            .and_then(|session| session.copy_policy_memo.get(&t).copied())
        {
            return b;
        }
        enum Next {
            Follow(TypeExprRef),
            Done(bool),
        }
        let next = if let Some(copy) = copied(t) {
            Next::Follow(copy)
        } else {
            match &*self.get_desc(t) {
                TypeDesc::Tfield { rest, .. } => Next::Follow(*rest),
                TypeDesc::Tvar(..) => Next::Done(self.get_level(t) == GENERIC_LEVEL),
                // Already copied in this session: follow the copy.
                TypeDesc::Tsubst(t2) => Next::Follow(*t2),
                _ => Next::Done(false),
            }
        };
        let b = match next {
            Next::Follow(next) => self.row_terminator_generic(next, copied),
            Next::Done(b) => b,
        };
        if let Some(session) = self.copy_sessions.borrow_mut().last_mut() {
            session.copy_policy_memo.insert(t, b);
        }
        b
    }

    /// The mutability cell of a copied `Tfield` (btype.ml `copy_type_desc`):
    /// unless an independent graph is requested, instantiating a generalized
    /// row duplicates each cell once per session, while other copies hold
    /// the shared representative. The policy is determined before either
    /// child is copied.
    pub fn copy_field_mutability(
        &self,
        mutability: MutabilityRef,
        rest: TypeExprRef,
        fresh_mutability: bool,
        copied: &dyn Fn(TypeExprRef) -> Option<TypeExprRef>,
    ) -> MutabilityRef {
        if fresh_mutability || self.row_terminator_generic(rest, copied) {
            self.dup_mutability(mutability)
        } else {
            self.mutability_ref_repr(mutability)
        }
    }

    // ========================================================================
    // Level Management
    // ========================================================================

    /// Get the current level.
    pub fn current_level(&self) -> i32 {
        self.current_level.get()
    }

    /// Temporarily set the current level. Used by subst_with_memo to match
    /// OCaml's `current_level := level` which ensures fresh copies during
    /// instance_parameterized_type are created at the Tconstr's level.
    pub fn set_current_level(&self, level: i32) {
        self.record_mutation(
            || TypeMutation::CurrentLevel(self.current_level.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.current_level.set(level);
    }

    /// Get the non-generalizable level.
    pub fn nongen_level(&self) -> i32 {
        self.nongen_level.get()
    }

    /// Get the global level.
    pub fn global_level(&self) -> i32 {
        self.global_level.get()
    }

    /// Get the current ident stamp value (equivalent of OCaml's `Ident.current_time()`).
    pub fn current_stamp(&self) -> i32 {
        // OCaml compiler/ext/ident.ml:57-58 reads the single active
        // `Ident.create` stamp counter. Rust's `Ident::create_local` counter is
        // for helper-created paths and test fixtures; letting it feed
        // Ctype.init_def shifts later typedtree binders after unrelated helper
        // path construction.
        self.id_gen.current_stamp()
    }

    /// Consume one identifier stamp without materializing an `Ident`.
    ///
    /// This mirrors OCaml save-signature renaming in places where the renamed
    /// identifier is immediately discarded but the stamp stream must advance.
    pub fn consume_ident_stamp(&self) {
        let _ = self.id_gen.next_stamp();
    }

    /// Consume multiple identifier stamps without materializing `Ident`s.
    pub fn consume_ident_stamps(&self, count: i32) {
        let _ = self.id_gen.advance_stamp_by(count);
    }

    /// Set the ident stamp counter to at least `t`.
    /// Matches OCaml's `Ident.set_current_time`.
    pub fn set_current_time(&self, t: i32) {
        self.id_gen.set_current_stamp(t);
    }

    /// Shares the compilation's identifier stream with additive downstream
    /// stages. M5's inactive indexed path uses this instead of reconstructing
    /// a fresh generator from a scanned stamp frontier.
    #[cfg(test)]
    pub(crate) fn id_generator(&self) -> Arc<IdGenerator> {
        Arc::clone(&self.id_gen)
    }

    #[cfg(test)]
    pub(crate) fn current_def_level_state(&self) -> (i32, i32, i32, usize) {
        (
            self.current_level.get(),
            self.nongen_level.get(),
            self.global_level.get(),
            self.saved_levels.borrow().len(),
        )
    }

    /// Register a raw module signature for lazy renaming.
    /// Called during load_pervasives to store sigs for normalize_path.
    pub fn register_raw_module_sig(&self, name: &str, sig: Arc<super::decl::Signature>) {
        self.poison_store_build_for("register_raw_module_sig");
        self.raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn register_gentype_raw_module_sig(
        &self,
        name: &str,
        sig: Arc<super::decl::Signature>,
    ) {
        self.poison_store_build_for("register_gentype_raw_module_sig");
        self.gentype_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn register_gentype_portable_raw_module_sig(
        &self,
        name: &str,
        pers_struct: Arc<crate::cmi::portable_types::PortablePersStruct>,
    ) {
        self.poison_store_build_for("register_gentype_portable_raw_module_sig");
        self.gentype_portable_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), pers_struct);
    }

    pub(crate) fn get_gentype_raw_module_sig(
        &self,
        name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        if let Some(sig) = self.gentype_raw_module_sigs.borrow().get(name).cloned() {
            return Some(sig);
        }
        let portable = self
            .gentype_portable_raw_module_sigs
            .borrow_mut()
            .remove(name)?;
        let sig = Arc::new(crate::cmi::portable_types::internalize_raw_signature(
            &portable, self,
        )?);
        self.gentype_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig.clone());
        Some(sig)
    }

    /// Whether the raw signature of the persistent module `name` is loaded.
    pub fn has_raw_module_sig(&self, name: &str) -> bool {
        self.poison_store_build_for("read:has_raw_module_sig");
        self.raw_module_sigs.borrow().contains_key(name)
    }

    pub(crate) fn find_raw_module_sig(&self, name: &str) -> Option<Arc<super::decl::Signature>> {
        self.raw_module_sigs.borrow().get(name).cloned()
    }

    pub(crate) fn with_raw_module_sig<T>(
        &self,
        name: &str,
        f: impl FnOnce(&super::decl::Signature) -> T,
    ) -> Option<T> {
        let raw = self.raw_module_sigs.borrow();
        raw.get(name).map(|sig| f(sig.as_ref()))
    }

    pub(crate) fn get_or_load_raw_module_sig(
        &self,
        module_name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        self.poison_store_build_for("get_or_load_raw_module_sig");
        if let Some(sig) = self.raw_module_sigs.borrow().get(module_name).cloned() {
            return Some(sig);
        }
        if let Some(sig) = self
            .raw_component_module_sigs
            .borrow()
            .get(module_name)
            .cloned()
        {
            return Some(sig);
        }
        // OCaml compiler/ml/env.ml:669-678 creates persistent `ps_comps` from
        // the CMI signature separately from `ps_sig`, and env.ml:781-788 returns
        // those components for exact persistent `Pident` descriptor lookup.
        // Keep this fallback separate from `raw_module_sigs`: that map drives
        // ps_sig lazy renaming, and component-only loads must not be freshened:
        // OCaml has only looked them up through ps_comps.
        let sig = self.load_lazy_raw_module_sig_for_rename(module_name)?;
        self.raw_component_module_sigs
            .borrow_mut()
            .insert(module_name.to_string(), sig.clone());
        Some(sig)
    }

    /// Trigger module signature renaming for a persistent module.
    /// Matches OCaml's find_module → Lazy.force ps.ps_sig which renames
    /// bound idents the first time a module is accessed during normalize_path.
    pub fn trigger_module_sig_rename(&self, module_name: &str) {
        if self.renamed_module_sigs.borrow().contains_key(module_name) {
            return; // Already renamed
        }
        self.rename_one_module_sig(module_name);
    }

    fn rename_one_module_sig(&self, module_name: &str) {
        self.poison_store_build_for("rename_one_module_sig");
        let raw_sig = {
            let raw = self.raw_module_sigs.borrow();
            raw.get(module_name).cloned()
        }
        .or_else(|| {
            self.raw_component_module_sigs
                .borrow()
                .get(module_name)
                .cloned()
        })
        .or_else(|| self.load_lazy_raw_module_sig_for_rename(module_name));
        if let Some(sig) = raw_sig {
            self.raw_module_sigs
                .borrow_mut()
                .entry(module_name.to_string())
                .or_insert_with(|| sig.clone());
            if self.compiler_counters_enabled() {
                crate::perf_counters::record_signature_freshen_name(
                    self,
                    "type_context_lazy_rename",
                    module_name,
                    sig.len(),
                );
            }
            // OCaml `Subst.signature` copies and freshens in one traversal
            // sequence (compiler/ml/subst.ml:358-364). Keep this lazy rename
            // to that single pass instead of copying before calling the
            // freshening helper.
            let renamed = self.defer_renamed_sig("type_context_lazy_rename", sig);
            self.renamed_module_sigs
                .borrow_mut()
                .insert(module_name.to_string(), renamed);
        }
    }

    fn load_lazy_raw_module_sig_for_rename(
        &self,
        module_name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        if self.persistent_env_is_in_process() {
            let mut pers_env = self.persistent_env_clone().unwrap_or_else(|| {
                panic!(
                    "in-process invariant violated: missing PersistentEnv while forcing raw signature for {module_name}"
                )
            });
            // Source fallback can re-enter normalization while the same module
            // has only a cache placeholder. The rename force is a side effect;
            // skip the transient miss and let a later lookup force the
            // published signature.
            return pers_env.read_raw_sig_shared(module_name, self);
        }

        let cmi_path = {
            let load_paths = self.load_paths.borrow();
            let cmi_filename = format!("{module_name}.cmi");
            load_paths.iter().find_map(|dir| {
                let exact = dir.join(&cmi_filename);
                if exact.exists() {
                    return Some(exact);
                }

                let first = module_name.chars().next()?;
                if !first.is_ascii_uppercase() {
                    return None;
                }
                let uncap_name = format!("{}{}", first.to_ascii_lowercase(), &module_name[1..]);
                let uncap = dir.join(format!("{uncap_name}.cmi"));
                uncap.exists().then_some(uncap)
            })
        };
        let cmi_path = cmi_path?;
        let cmi = crate::cmi::cmi_format::read_cmi(&cmi_path.to_string_lossy()).ok()?;
        let mut sig_ctx = crate::cmi::sig_reader::SigReadContext::new(self);
        let mut sig = sig_ctx.read_signature(&cmi.cmi_sign);
        let module_path = Path::pident(Ident::create_persistent(module_name));
        // OCaml compiler/ml/env.ml:1000-1007 reaches `lookup_module_descr`
        // for dotted accesses, and env.ml:568-571/1516-1605 forces the
        // persistent structure's component lazy. Loading whichever CMI the
        // force requested lets the Rust force point consume the same
        // `Subst.signature` stamps instead of special-casing one module family.
        crate::cmi::persistent_env::substitute_type_paths_in_sig(&sig, &module_path, self);
        crate::cmi::persistent_env::qualify_unit_sig_decl_paths_in_place(
            &mut sig,
            &module_path,
            self,
        );
        crate::cmi::persistent_env::substitute_submodule_paths(&sig, &module_path, self);
        Some(Arc::new(sig))
    }

    /// Create a new identifier using the typing context's shared stamp source.
    pub fn create_ident(&self, name: impl Into<crate::name::Name>) -> Ident {
        if self.in_store_build() || self.world_scratch.get() {
            return self.store_binder(&Ident::create_persistent(name));
        }
        // OCaml compiler/ext/ident.ml:28-40 increments the active
        // currentstamp directly in `Ident.create`/`Ident.rename`; unrelated
        // helper-created local identifiers must not advance the typedtree
        // context's stamp stream.
        self.id_gen.create(name)
    }

    /// Create a new identifier named by a string of a parse arena, as
    /// [`Self::create_ident`] does.
    pub fn create_ast_ident(
        &self,
        arena: &crate::parse_arena::ParseArena,
        name: crate::intern::StrIdx,
    ) -> Ident {
        self.create_ident(arena.get_string(name))
    }

    pub(crate) fn create_ast_persistent_ident(
        &self,
        arena: &crate::parse_arena::ParseArena,
        name: crate::intern::StrIdx,
    ) -> Ident {
        Ident::create_persistent(arena.get_string(name))
    }

    pub(crate) fn create_ast_dotted(
        &self,
        arena: &crate::parse_arena::ParseArena,
        prefix: super::Path,
        name: crate::intern::StrIdx,
        pos: i32,
    ) -> super::Path {
        super::Path::pdot_pos(prefix, arena.get_string(name), pos)
    }





    /// Fresh binder for shared store data: a stamp of the process-wide store
    /// range (`thread_store::next_store_stamp`), so it can never be
    /// `Ident::same` as an identifier of a compilation. The compilation's own
    /// stamp counter is not advanced, so its stamps do not depend on which
    /// store data it built and which it found built. One atomic increment.
    fn store_binder(&self, id: &Ident) -> Ident {
        if self.compiler_counters_enabled {
            crate::perf_counters::store_views::record_binder(self);
        }
        let stamp = super::thread_store::next_store_stamp();
        let mut fresh = id.with_stamp(stamp);
        if id.is_persistent() {
            fresh = Ident::new(id.name(), stamp, crate::ident::IdentFlags::NONE);
        }
        fresh
    }

    /// Retain parser allocation identity alongside interned coordinates.
    /// The arena's lazily assigned scope survives moves and later contexts.
    pub fn intern_ast_loc(
        &self,
        arena: &crate::parse_arena::ParseArena,
        index: crate::parse_arena::LocIdx,
    ) -> super::DeclLoc {
        let loc = arena.to_location(index);
        if !arena.stores_locations() {
            return self.intern_loc(loc);
        }
        let scope = arena.declaration_location_scope(|| self.fresh_location_scope());
        let source = arena.get_location(index);
        let identity = super::decl_loc::LocationIdentity {
            scope,
            location: index.0,
            start: source.loc_start.0,
            end: source.loc_end.0,
        };
        self.intern_loc_with_identity(loc, identity)
    }

    pub(crate) fn dotted_from_ident(
        &self,
        prefix: Arc<super::Path>,
        id: Ident,
        pos: i32,
    ) -> super::Path {
        super::Path::pdot_pos(*prefix, id.name_atom(), pos)
    }



    pub(crate) fn copy_dotted_with_prefix(&self, source: &super::Path, prefix: Arc<super::Path>) -> super::Path {
        let super::path::PathView::Pdot(_, text, pos) = source.view() else { panic!("expected dotted source path") };
        super::Path::pdot_pos(*prefix, *text, *pos)
    }

    pub(crate) fn rebuild_dotted(
        &self,
        source: &super::Path,
        f: impl FnOnce(&Arc<super::Path>) -> Arc<super::Path>,
    ) -> super::Path {
        let super::path::PathView::Pdot(prefix, text, pos) = source.view() else {
            panic!("expected dotted source path")
        };
        super::Path::pdot_pos(*f(&Arc::new(*prefix)), *text, *pos)
    }

    /// Select the stable namespace before allocating this unit's locations,
    /// shape blocks or private interface imports. O(filename bytes), once per
    /// compilation, not per location. Installation directories are not identity:
    /// snapshot relocation must preserve scopes as well as displayed filenames.
    /// The driver supplies package name plus package-relative path, including
    /// the extension to distinguish implementation and interface arenas. Imports
    /// separately namespace these source-local identities by persistent unit.
    pub(crate) fn set_location_namespace(&self, unit: &str) {
        use std::hash::{Hash, Hasher};
        assert_eq!(self.next_identity_scope.get(), 1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        ("source unit", unit).hash(&mut hash);
        self.location_namespace.set(Some(hash.finish()));
    }

    /// A scope for one parser arena or decoded interface. Named compilations
    /// use a unit-local ordinal, not the worker's table-owner counter. Anonymous
    /// contexts (such as standalone identity tests) retain process uniqueness.
    pub(crate) fn fresh_location_scope(&self) -> u64 {
        let next = self.next_identity_scope.get();
        self.next_identity_scope
            .set(next.checked_add(1).expect("location scopes exhausted"));
        if let Some(namespace) = self.location_namespace.get() {
            super::variant_runtime::identity_in_namespace(namespace, next as u64)
        } else {
            ((self.decl_loc_owner as u64) << 32) | next as u64
        }
    }

    pub(crate) fn fresh_shape_allocation(&self) -> super::ShapeAllocation {
        super::ShapeAllocation::in_namespace(self.fresh_location_scope(), 0)
    }

    pub(crate) fn intern_loc_with_identity(
        &self,
        loc: crate::location::Location,
        identity: super::decl_loc::LocationIdentity,
    ) -> super::DeclLoc {
        if self.in_store_build() {
            return self.store.intern_decl_loc_with_identity(loc, identity);
        }
        super::DeclLoc::table(
            super::decl_loc::DeclLocKind::Local,
            self.decl_loc_owner,
            self.decl_locs.intern_with_identity(loc, identity),
        )
    }

    /// Intern a coordinate-only location from a non-parser boundary.
    #[inline]
    pub fn intern_loc(&self, loc: crate::location::Location) -> super::DeclLoc {
        if let Some(source) = super::DeclLoc::source(&loc) {
            return source;
        }
        self.intern_located_loc(loc)
    }

    #[cold]
    #[inline(never)]
    fn intern_located_loc(&self, loc: crate::location::Location) -> super::DeclLoc {
        if self.in_store_build() {
            return self.store.intern_decl_loc(loc);
        }
        super::DeclLoc::table(
            super::decl_loc::DeclLocKind::Local,
            self.decl_loc_owner,
            self.decl_locs.intern(loc),
        )
    }

    /// The location a handle of this compilation (or of the worker store or
    /// shared pool it reads) denotes.
    #[inline]
    pub fn resolve_loc(&self, loc: super::DeclLoc) -> crate::location::Location {
        match loc.source_location() {
            Some(loc) => loc,
            None => self.resolve_table_loc(loc),
        }
    }

    #[cold]
    #[inline(never)]
    fn resolve_table_loc(&self, loc: super::DeclLoc) -> crate::location::Location {
        use super::decl_loc::DeclLocKind;
        match loc.kind() {
            DeclLocKind::Local => {
                assert_eq!(
                    loc.owner(),
                    self.decl_loc_owner,
                    "declaration location of another compilation"
                );
                self.decl_locs.get(loc.index())
            }
            DeclLocKind::Store => self.store.decl_loc(loc),
            DeclLocKind::Shared => super::shared_store::page_location(
                &self.shared_pages,
                loc.owner(),
                loc.index(),
            ),
            DeclLocKind::Source | DeclLocKind::Portable => {
                panic!("unresolvable declaration location {loc:?}")
            }
        }
    }

    /// Number of located entries in this compilation's own table.
    pub fn local_decl_loc_count(&self) -> usize {
        self.decl_locs.len()
    }

    /// A store build that keeps a location of this compilation must stay
    /// private to it, like one that reads a compilation-local type node.
    #[inline]
    pub(crate) fn check_store_decl_loc(&self, loc: super::DeclLoc) {
        if loc.kind() == super::decl_loc::DeclLocKind::Local {
            self.poison_store_build_for("local-decl-loc");
        }
    }

    /// Allocation identity, if retained by the location's owning table.
    pub(crate) fn location_identity(
        &self,
        loc: super::DeclLoc,
    ) -> Option<super::decl_loc::LocationIdentity> {
        use super::decl_loc::DeclLocKind;
        match loc.kind() {
            DeclLocKind::Source => None,
            DeclLocKind::Local => {
                assert_eq!(loc.owner(), self.decl_loc_owner);
                self.decl_locs.identity(loc.index())
            }
            DeclLocKind::Store => self.store.decl_loc_identity(loc),
            DeclLocKind::Shared => super::shared_store::page_location_identity(
                &self.shared_pages,
                loc.owner(),
                loc.index(),
            ),
            DeclLocKind::Portable => panic!("portable location outside its table"),
        }
    }

    /// Import coordinates and allocation identities into a fresh namespace.
    pub(crate) fn import_portable_decl_locs<'a>(
        &self,
        table: &super::decl_loc::DeclLocTable,
        files: &'a dyn Fn(crate::intern::StrIdx) -> crate::intern::StrIdx,
    ) -> super::decl_loc::DeclLocImport<'a> {
        let mut table = table.clone();
        let namespace = self.fresh_location_scope();
        let scopes = table.remap_for_import_with(files, |scope| {
            super::variant_runtime::identity_in_namespace(namespace, scope)
        });
        let (base, instances) = self.decl_locs.append_portable(&table);
        super::decl_loc::DeclLocImport {
            kind: super::decl_loc::DeclLocKind::Local,
            owner: self.decl_loc_owner,
            base,
            instances,
            files,
            scopes,
            namespace: Some(namespace),
        }
    }

    #[cfg(test)]
    pub(crate) fn import_decl_locs<'a>(
        &self,
        locations: impl IntoIterator<Item = crate::location::Location>,
        files: &'a dyn Fn(crate::intern::StrIdx) -> crate::intern::StrIdx,
    ) -> super::decl_loc::DeclLocImport<'a> {
        super::decl_loc::DeclLocImport {
            kind: super::decl_loc::DeclLocKind::Local,
            owner: self.decl_loc_owner,
            base: self.decl_locs.append(locations),
            instances: Vec::new(),
            files,
            scopes: Default::default(),
            namespace: None,
        }
    }

    /// Whether allocations currently go to the worker store.
    #[inline(always)]
    pub(crate) fn in_store_build(&self) -> bool {
        self.store_build_depth.get() != 0
    }

    /// Record that the current store build depends on compilation-local
    /// state; its result is then kept private to this compilation.
    #[inline(always)]
    pub(crate) fn poison_store_build(&self) {
        self.poison_store_build_for("local-read");
    }

    #[inline(always)]
    pub(crate) fn poison_store_build_for(&self, reason: &'static str) {
        if self.store_build_depth.get() != 0 {
            self.poison_store_build_slow(reason);
        }
    }

    #[cold]
    #[inline(never)]
    fn poison_store_build_slow(&self, reason: &'static str) {
        if !self.store_build_poisoned.replace(true) && store_debug_enabled() {
            eprintln!("[store-poison] {reason}");
            if std::env::var_os("RESCRIPT_STORE_DEBUG_BT").is_some() {
                let bt = std::backtrace::Backtrace::force_capture().to_string();
                let frames: Vec<&str> = bt
                    .lines()
                    .filter(|l| l.contains("rescript_compiler::") && !l.contains("poison_store"))
                    .take(8)
                    .collect();
                eprintln!(
                    "[store-poison-bt] {reason} :: {}",
                    frames.join(" <- ").replace("rescript_compiler::", "")
                );
            }
        }
    }

    /// Whether `r` was allocated by the store build in progress. Such nodes
    /// are written straight into the store and outlive any type snapshot
    /// taken before the build, so the undo journal must not record (and
    /// later roll back) their writes, just as it skips nodes created after
    /// the snapshot.
    #[inline]
    fn store_build_owns(&self, r: TypeExprRef) -> bool {
        r.is_store()
            && self.in_store_build()
            && !r.is_shared()
            && r.store_index() >= self.store_build_type_start.get()
    }

    /// Row-field counterpart of [`Self::store_build_owns`].
    fn store_build_owns_row_field(&self, rf: RowFieldRef) -> bool {
        rf.is_store()
            && self.in_store_build()
            && rf.store_index() >= self.store_build_row_start.get()
    }

    #[inline]
    fn check_store_ref(&self, r: TypeExprRef) {
        if !r.is_store() {
            self.poison_store_build();
        }
    }

    #[inline]
    fn check_store_memo(&self, memo: AbbrevMemoRef) {
        // Memo cells 0 (`Mnil`) and 1 (`simple_abbrevs`) have the same role in
        // every compilation.
        if !memo.is_store() && memo.0 > 1 {
            self.poison_store_build();
        }
    }

    fn check_store_row_field(&self, field: &RowField) {
        match field {
            RowField::Rpresent(Some(ty)) => self.check_store_ref(*ty),
            RowField::Rpresent(None) | RowField::Rabsent => {}
            RowField::Reither { types, link, .. } => {
                for ty in types {
                    self.check_store_ref(*ty);
                }
                if !link.is_null() && !link.is_store() {
                    self.poison_store_build();
                }
            }
        }
    }

    /// `desc` with its payloads (type and parameter lists, row, package
    /// names) in the worker store (see `store_type_list_for`).
    fn store_desc_lists(&self, mut desc: TypeDesc) -> TypeDesc {
        match &mut desc {
            TypeDesc::Ttuple(list)
            | TypeDesc::Tconstr { args: list, .. }
            | TypeDesc::Tpoly { vars: list, .. }
            | TypeDesc::Tpackage { args: list, .. } => *list = self.store_type_list_for(*list),
            TypeDesc::Tarrow { args, .. } => *args = self.store_type_args_for(*args),
            TypeDesc::Tvariant(row) if !row.is_store() => {
                *row = self.store.alloc_row_desc(self.type_lists.get_row(*row).clone());
            }
            _ => {}
        }
        if let TypeDesc::Tpackage { lids, .. } = &mut desc
            && !lids.is_store()
        {
            *lids = self
                .store
                .alloc_package_lids(self.type_lists.get_lids(*lids).to_vec());
        }
        desc
    }

    /// Poison the store build if `desc` refers to compilation-local cells.
    fn check_store_desc(&self, desc: &TypeDesc) {
        match desc {
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
            TypeDesc::Tarrow { args, ret } => {
                for arg in self.type_args(args).iter() {
                    self.check_store_ref(arg.typ);
                    self.check_store_decl_loc(arg.label().loc());
                }
                self.check_store_ref(*ret);
            }
            TypeDesc::Ttuple(items) => {
                for ty in self.type_list(items).iter() {
                    self.check_store_ref(ty);
                }
            }
            TypeDesc::Tconstr { args, abbrev, .. } => {
                for ty in self.type_list(args).iter() {
                    self.check_store_ref(ty);
                }
                self.check_store_memo(*abbrev);
            }
            TypeDesc::Tobject { fields } => self.check_store_ref(*fields),
            TypeDesc::Tfield {
                mutability,
                typ,
                rest,
                ..
            } => {
                if !mutability.is_persistent() {
                    self.poison_store_build();
                }
                self.check_store_ref(*typ);
                self.check_store_ref(*rest);
            }
            TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => self.check_store_ref(*ty),
            TypeDesc::Tvariant(row) => {
                let row = self.row_desc(row);
                self.check_store_ref(row.row_more);
                for (_, field) in row.row_fields.iter() {
                    self.check_store_row_field(field);
                }
                if let Some((_, args)) = &row.row_name {
                    for ty in args {
                        self.check_store_ref(*ty);
                    }
                }
            }
            TypeDesc::Tpoly { body, vars } => {
                self.check_store_ref(*body);
                for ty in self.type_list(vars).iter() {
                    self.check_store_ref(ty);
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for ty in self.type_list(args).iter() {
                    self.check_store_ref(ty);
                }
            }
        }
    }

    pub(crate) fn local_stored_components(
        &self,
        id: u64,
    ) -> Option<Rc<super::env_lazy::QualifiedModuleComponents>> {
        self.local_stored_components.borrow().get(&id).cloned()
    }

    pub(crate) fn set_local_stored_components(
        &self,
        id: u64,
        components: Rc<super::env_lazy::QualifiedModuleComponents>,
    ) {
        self.local_stored_components
            .borrow_mut()
            .insert(id, components);
    }

    /// Run `build` with every type-graph allocation going to the worker
    /// store, so its result can be shared with later compilations on this
    /// worker. Returns the replay record to publish with the result, or
    /// `None` when the build read compilation-local state (the result is
    /// then only valid in this compilation).
    pub(crate) fn build_in_store<R>(
        &self,
        build: impl FnOnce() -> R,
    ) -> (R, Option<Rc<StorePiece>>) {
        self.build_in_store_with_guards(false, build)
    }

    /// `build_in_store` for a caller that checks `store_guards_hold` before
    /// reusing the result. Other callers treat a guarded build as private.
    pub(crate) fn build_in_store_guarded<R>(
        &self,
        build: impl FnOnce() -> R,
    ) -> (R, Option<Rc<StorePiece>>) {
        self.build_in_store_with_guards(true, build)
    }

    fn build_in_store_with_guards<R>(
        &self,
        guarded: bool,
        build: impl FnOnce() -> R,
    ) -> (R, Option<Rc<StorePiece>>) {
        let depth = self.store_build_depth.get();
        let outer_effects = std::mem::take(&mut *self.store_build_effects.borrow_mut());
        let outer_guards = std::mem::take(&mut *self.store_build_guards.borrow_mut());
        let outer_poisoned = self.store_build_poisoned.replace(false);
        if depth == 0 {
            self.store_build_type_start.set(self.store.type_count());
            self.store_build_row_start.set(self.store.row_field_count());
            if self.compiler_counters_enabled {
                self.store_build_abbrev_start.set(self.store.abbrev_count());
            }
        }
        self.store_build_depth.set(depth + 1);
        self.types.set_direct(depth + 1 == 0);
        super::thread_store::set_store_build_depth(depth + 1);
        let result = build();
        self.store_build_depth.set(depth);
        self.types.set_direct(depth == 0);
        super::thread_store::set_store_build_depth(depth);
        if depth == 0 && self.compiler_counters_enabled {
            crate::perf_counters::record_store_build_nodes(
                self,
                self.store.type_count() - self.store_build_type_start.get(),
            );
        }
        let effects = std::mem::replace(&mut *self.store_build_effects.borrow_mut(), outer_effects);
        let guards = std::mem::replace(&mut *self.store_build_guards.borrow_mut(), outer_guards);
        let mut poisoned = self.store_build_poisoned.replace(outer_poisoned);
        if !guards.is_empty() && !guarded {
            if !poisoned && store_debug_enabled() {
                eprintln!("[store-poison] unguarded-alias-source-read");
            }
            poisoned = true;
        }
        if self.compiler_counters_enabled {
            crate::perf_counters::store_views::record_piece(
                self,
                poisoned,
                effects.is_empty() && guards.is_empty(),
            );
        }
        if poisoned {
            if depth > 0 {
                // The enclosing build may hold this result.
                self.store_build_poisoned.set(true);
                self.store_build_effects.borrow_mut().extend(effects);
            }
            return (result, None);
        }
        if depth > 0 {
            // The enclosing build holds this result, so it depends on the
            // same answers.
            self.store_build_guards
                .borrow_mut()
                .extend(guards.iter().cloned());
        }
        if effects.is_empty() && guards.is_empty() {
            // Most builds have no effect on the compilation and read no
            // guarded answer: touching, replaying or checking such a piece
            // does nothing, so they all share one piece and the enclosing
            // build need not record it.
            return (result, Some(EMPTY_STORE_PIECE.with(Rc::clone)));
        }
        let piece = Rc::new(StorePiece {
            id: NEXT_STORE_PIECE_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            effects,
            guards,
        });
        self.touched_store_pieces.borrow_mut().insert(piece.id);
        if depth > 0 {
            self.store_build_effects
                .borrow_mut()
                .push(StoreEffect::Piece(piece.clone()));
        }
        (result, Some(piece))
    }

    /// Note that this compilation is using shared store data built by `piece`:
    /// the first time, apply the effects that building it had.
    pub(crate) fn touch_store_piece(&self, piece: &Rc<StorePiece>) {
        if piece.effects.is_empty() && piece.guards.is_empty() {
            return;
        }
        if self.in_store_build() {
            self.store_build_effects
                .borrow_mut()
                .push(StoreEffect::Piece(piece.clone()));
            self.store_build_guards
                .borrow_mut()
                .extend(piece.guards.iter().cloned());
        }
        if self.touched_store_pieces.borrow().contains(&piece.id) {
            return;
        }
        self.suspend_store_build(|| self.replay_store_piece(piece));
    }

    fn replay_store_piece(&self, piece: &Rc<StorePiece>) {
        if !self.touched_store_pieces.borrow_mut().insert(piece.id) {
            return;
        }
        if self.compiler_counters_enabled {
            use crate::perf_counters::store_views as counters;
            counters::record_piece_replay(self);
            for effect in &piece.effects {
                match effect {
                    StoreEffect::Piece(_) => {}
                    StoreEffect::PreparePers(_) => counters::record_effect_replayed(self, 0),
                }
            }
        }
        for effect in &piece.effects {
            match effect {
                StoreEffect::Piece(inner) => self.replay_store_piece(inner),
                StoreEffect::PreparePers(name) => {
                    let replayed = self
                        .persistent_env
                        .borrow()
                        .as_ref()
                        .is_none_or(|pers| pers.replay_cached_pers_struct(name, self));
                    if replayed {
                        continue;
                    }
                    if let Some(mut pers) = self.persistent_env_clone() {
                        let _ = pers.find_pers_struct(name, self);
                    }
                }
            }
        }
    }

    /// A fresh stamp of this compilation's counter, for a store binder its
    /// published signature mentions (see
    /// `cmi::portable_types::serialize_pers_struct`).
    pub(crate) fn published_binder_stamp(&self) -> i32 {
        self.id_gen.next_stamp()
    }

    /// Record an effect of the current store build on this compilation.
    pub(crate) fn record_store_effect(&self, effect: StoreEffect) {
        if !self.in_store_build() {
            return;
        }
        let mut effects = self.store_build_effects.borrow_mut();
        let duplicate = match &effect {
            StoreEffect::PreparePers(name) => effects
                .iter()
                .any(|e| matches!(e, StoreEffect::PreparePers(other) if other == name)),
            _ => false,
        };
        if !duplicate {
            effects.push(effect);
        }
    }

    /// Run `f` as this compilation (allocating locally), in the middle of a
    /// store build: used for effects on the compilation that are journaled
    /// separately.
    pub(crate) fn suspend_store_build<R>(&self, f: impl FnOnce() -> R) -> R {
        let depth = self.store_build_depth.replace(0);
        self.types.set_direct(true);
        super::thread_store::set_store_build_depth(0);
        let result = f();
        self.store_build_depth.set(depth);
        self.types.set_direct(depth == 0);
        super::thread_store::set_store_build_depth(depth);
        result
    }

    /// `Ident.rename`: the identifier with the same name and a fresh stamp.
    pub fn rename_ident(&self, id: &Ident) -> Ident {
        self.rename_ident_stamp(id)
    }

    fn rename_ident_stamp(&self, id: &Ident) -> Ident {
        if self.in_store_build() || self.world_scratch.get() {
            return self.store_binder(id);
        }
        // See `create_ident`: this mirrors compiler/ext/ident.ml:38-40.
        id.rename(&self.id_gen)
    }

    /// Register a lazy `Subst.signature Subst.identity` rename of `source`.
    ///
    /// OCaml `ps_sig` (compiler/ml/env.ml:669-678) is forced by `find_module`
    /// (compiler/ml/env.ml:865-875), and most forces only come from
    /// `normalize_path` (compiler/ml/env.ml:903-914), which discards the
    /// signature unless it is an alias. The copy is therefore made when its
    /// contents are first read, with the stamps current at that time.
    pub(crate) fn defer_renamed_sig(
        &self,
        kind: &'static str,
        source: Arc<super::decl::Signature>,
    ) -> Arc<DeferredRenamedSig> {
        Arc::new(DeferredRenamedSig {
            kind,
            source,
            renamed: std::sync::OnceLock::new(),
        })
    }

    /// Copy a deferred renamed signature the first time it is read. The copy
    /// belongs to this compilation: it is made outside any store build (which
    /// it makes private), with this compilation's stamps and nodes.
    pub(crate) fn materialize_renamed_sig(
        &self,
        deferred: &DeferredRenamedSig,
    ) -> Arc<super::decl::Signature> {
        deferred
            .renamed
            .get_or_init(|| {
                self.poison_store_build_for("materialize-renamed-sig");
                Arc::new(self.suspend_store_build(|| {
                    crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
                        deferred.kind,
                        deferred.source.as_ref(),
                        self,
                    )
                }))
            })
            .clone()
    }

    /// Materialized renamed signature for `module_name`, if it was forced.
    pub(crate) fn renamed_module_sig(
        &self,
        module_name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        self.poison_store_build_for("read:renamed_module_sig");
        let deferred = self
            .renamed_module_sigs
            .borrow()
            .get(module_name)
            .cloned()?;
        Some(self.materialize_renamed_sig(&deferred))
    }

    /// Initialize definition level (equivalent of OCaml's `Ctype.init_def`).
    pub fn init_def(&self, level: i32) {
        self.record_level_state();
        self.current_level.set(level);
        self.nongen_level.set(level);
    }

    fn record_level_state(&self) {
        self.record_mutation(
            || TypeMutation::CurrentLevel(self.current_level.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.record_mutation(
            || TypeMutation::NongenLevel(self.nongen_level.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.record_mutation(
            || TypeMutation::SavedLevels(self.saved_levels.borrow().clone()),
            crate::perf_counters::TypeMutationKind::State,
        );
    }

    /// Begin a new definition scope.
    pub fn begin_def(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.record_level_state();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.current_level.set(current + 1);
        self.nongen_level.set(current + 1);
    }

    /// Begin a class definition scope.
    pub fn begin_class_def(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.record_level_state();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.current_level.set(current + 1);
    }

    /// Raise the non-generalizable level.
    pub fn raise_nongen_level(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.record_level_state();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.nongen_level.set(current);
    }

    /// End a definition scope.
    pub fn end_def(&self) {
        if !self.saved_levels.borrow().is_empty() {
            self.record_level_state();
        }
        if let Some((current, nongen)) = self.saved_levels.borrow_mut().pop() {
            self.current_level.set(current);
            self.nongen_level.set(nongen);
        }
    }

    /// Reset the global level.
    pub fn reset_global_level(&self) {
        self.record_mutation(
            || TypeMutation::GlobalLevel(self.global_level.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.global_level.set(self.current_level.get() + 1);
    }

    /// Increase the global level and return the old value.
    pub fn increase_global_level(&self) -> i32 {
        let old = self.global_level.get();
        self.record_mutation(
            || TypeMutation::GlobalLevel(old),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.global_level.set(self.current_level.get());
        old
    }

    /// Restore the global level.
    pub fn restore_global_level(&self, level: i32) {
        self.record_mutation(
            || TypeMutation::GlobalLevel(self.global_level.get()),
            crate::perf_counters::TypeMutationKind::State,
        );
        self.global_level.set(level);
    }

    // ========================================================================
    // GADT Tracking
    // ========================================================================

    /// Check and set GADT instance tracing.
    pub fn check_trace_gadt_instances(&self, has_constraints: bool) -> bool {
        if !self.trace_gadt_instances.get() && has_constraints {
            self.trace_gadt_instances.set(true);
            true
        } else {
            false
        }
    }

    /// Reset GADT instance tracing.
    pub fn reset_trace_gadt_instances(&self, was_set: bool) {
        if was_set {
            self.trace_gadt_instances.set(false);
        }
    }

    /// Is GADT instance tracing currently enabled?
    /// `!Ctype.passive_variants`.
    pub fn passive_variants(&self) -> bool {
        self.passive_variants.get()
    }

    /// Sets `Ctype.passive_variants`, returning the previous value.
    pub fn set_passive_variants(&self, value: bool) -> bool {
        self.passive_variants.replace(value)
    }

    /// `!Ctype.rigid_variants`.
    pub fn rigid_variants(&self) -> bool {
        self.rigid_variants.get()
    }

    /// Sets `Ctype.rigid_variants`, returning the previous value.
    pub fn set_rigid_variants(&self, value: bool) -> bool {
        self.rigid_variants.replace(value)
    }

    /// Whether GADT instances are being tracked (OCaml `Ctype.trace_gadt_instances`).
    pub fn trace_gadt_instances(&self) -> bool {
        self.trace_gadt_instances.get()
    }

    // ========================================================================
    // Type Representative (Union-Find)
    // ========================================================================

    /// Get the representative of a type (follow Tlink chains).
    ///
    /// This uses path compression to update intermediate links
    /// to point directly to the representative, improving
    /// subsequent lookup performance.
    #[inline]
    pub fn repr(&self, t: TypeExprRef) -> TypeExprRef {
        // Fast path, inlined into callers: `t` is already a representative.
        let next = self.with_desc(t, |desc| match desc {
            TypeDesc::Tlink(next) => Some(*next),
            _ => None,
        });
        let Some(first_next) = next else {
            return t;
        };
        self.repr_chain(t, first_next)
    }

    /// Follow a link chain starting at `t` (whose next node is `first_next`)
    /// and compress it.
    #[inline(never)]
    fn repr_chain(&self, t: TypeExprRef, first_next: TypeExprRef) -> TypeExprRef {
        // Follow chain to the end, collecting nodes for path compression.
        // Uses a fixed-size stack buffer — chains longer than 32 are
        // vanishingly rare and just won't get full compression.
        let mut chain = [TypeExprRef(0); 32];
        let mut chain_len: usize = 1;
        chain[0] = t;

        let mut current = first_next;
        for _ in 0..10_000 {
            let next = self.with_desc(current, |desc| match desc {
                TypeDesc::Tlink(next) => Some(*next),
                _ => None,
            });
            match next {
                Some(next_ref) => {
                    if chain_len < 32 {
                        chain[chain_len] = current;
                        chain_len += 1;
                    }
                    current = next_ref;
                }
                None => break,
            }
        }

        // Path compression: relink all traversed nodes to the representative
        // (OCaml `Btype.repr_link`). Frozen nodes are followed, never compressed.
        for &node in &chain[..chain_len] {
            if node.is_store() && !self.store_build_owns(node) {
                continue;
            }
            if node != current {
                // A direct link already points at the representative. OCaml
                // btype.ml:107-115 does not log/write it (`compress = false`);
                // otherwise `repr_link` logs the write as `Ccompress`.
                let direct =
                    matches!(*self.borrow_desc(node), TypeDesc::Tlink(target) if target == current);
                if !direct {
                    if self.mutation_logging.compress() && !self.store_build_owns(node) {
                        let old = self.get_desc(node).0;
                        self.mutation_journal
                            .borrow_mut()
                            .push(TypeMutation::Compress(node, old, current));
                    }
                    self.write_desc_raw(node, TypeDesc::Tlink(current));
                }
            }
        }

        current
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn check_mode_snapshot_cost_at_ten_thousand_unifications() {
        use super::super::ctype::{unify, UnifyState};
        assert_eq!(std::mem::size_of::<CheckMode>(), 1);
        for mode in [CheckMode::Success, CheckMode::Explain] {
            let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
            ctx.set_explain_mode(mode);
            for _ in 0..10_000 {
                let left = ctx.new_type(TypeDesc::Tvar(None));
                let right = ctx.new_type(TypeDesc::Tvar(None));
                unify(&ctx, &mut UnifyState::new(), left, right).unwrap();
            }
            let journal = ctx.mutation_journal.borrow();
            assert_eq!(journal.next_id, if mode == CheckMode::Explain { 10_000 } else { 0 });
            assert_eq!(journal.logged_writes, 0);
            assert!(!ctx.unexplained_unify_failure());
        }
    }

    #[test]
    fn unexplained_failure_is_recorded_only_without_snapshot() {
        use super::super::ctype::{unify, UnifyState};
        for mode in [CheckMode::Success, CheckMode::Explain] {
            for speculative in [false, true] {
                let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
                ctx.set_explain_mode(mode);
                let left = ctx.new_constr(super::super::predef::path_bool(), vec![]);
                let right = ctx.new_constr(super::super::predef::path_string(), vec![]);
                let snapshot = speculative.then(|| ctx.snapshot_type_state());
                assert!(unify(&ctx, &mut UnifyState::new(), left, right).is_err());
                assert_eq!(
                    ctx.unexplained_unify_failure(),
                    mode == CheckMode::Success && !speculative,
                );
                drop(snapshot);
            }
        }
    }

    #[test]
    fn success_mode_keeps_speculation_journal() {
        use super::super::ctype::{unify, UnifyState};
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        ctx.set_explain_mode(CheckMode::Success);
        let left = ctx.new_type(TypeDesc::Tvar(None));
        let right = ctx.new_type(TypeDesc::Tvar(None));
        let snapshot = ctx.snapshot_type_state();
        assert!(ctx.unify_takes_snapshot());
        unify(&ctx, &mut UnifyState::new(), left, right).unwrap();
        assert_eq!(ctx.mutation_journal.borrow().next_id, 2);
        assert!(ctx.mutation_journal.borrow().logged_writes > 0);
        drop(snapshot);
        assert!(!ctx.unify_takes_snapshot());
    }

    fn frozen_arrows(ctx: &TypeContext) -> [TypeExprRef; 4] {
        use super::super::shared_store::{SharedGraphParts, SharedGraphPayloads, SharedGraphSizes, shared_ref};
        let sizes = SharedGraphSizes { nodes: 4, arg_items: 2, ..Default::default() };
        let base = ctx.store.shared_pool().publish(sizes, |base| {
            let var = shared_ref(base, 0);
            let int = shared_ref(base, 1);
            SharedGraphParts {
                nodes: vec![
                    (TypeDesc::Tvar(None), GENERIC_LEVEL),
                    (TypeDesc::Tconstr {
                        path: Path::pident(Ident::create_persistent("int")),
                        args: TypeRefList::EMPTY,
                        abbrev: AbbrevMemoRef::nil(),
                    }, GENERIC_LEVEL),
                    (TypeDesc::Tarrow {
                        args: TypeArgList::from_parts(shared_ref(base, sizes.args_start()).0, 1),
                        ret: int,
                    }, GENERIC_LEVEL),
                    (TypeDesc::Tarrow {
                        args: TypeArgList::from_parts(shared_ref(base, sizes.args_start() + 1).0, 1),
                        ret: int,
                    }, GENERIC_LEVEL),
                ],
                payloads: SharedGraphPayloads {
                    args: vec![TypeArg::new(ArgLabel::Nolabel, var), TypeArg::new(ArgLabel::Nolabel, int)],
                    ..Default::default()
                },
                layouts: Vec::new(),
                locations: Default::default(),
                carried: Default::default(),
            }
        }).unwrap();
        std::array::from_fn(|i| shared_ref(base, i))
    }

    fn assert_no_frozen_writes(ctx: &TypeContext) {
        assert!(!ctx.frozen_writes.any.get());
        assert!(ctx.frozen_writes.descs.borrow().is_empty());
        assert!(ctx.frozen_writes.levels.borrow().is_empty());
        assert!(ctx.frozen_writes.memos.borrow().is_empty());
        assert!(ctx.frozen_writes.row_fields.borrow().is_empty());
        assert!(ctx.frozen_writes.mutabilities.borrow().is_empty());
    }

    #[test]
    fn type_mutation_size_stays_40_bytes() {
        assert_eq!(std::mem::size_of::<TypeMutation>(), 40);
    }

    #[test]
    fn frozen_read_does_not_probe_when_nothing_was_written() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let nodes = frozen_arrows(&ctx);
        for i in 0..1_000 {
            ctx.get_desc(nodes[i % nodes.len()]);
            assert_eq!(ctx.get_level(nodes[i % nodes.len()]), GENERIC_LEVEL);
        }
        assert_eq!(ctx.frozen_writes.probes.get(), 0);
        assert_no_frozen_writes(&ctx);
        // Positive control: the counter really sees exception-table probes.
        ctx.set_level(nodes[0], 1);
        ctx.get_level(nodes[0]);
        assert_eq!(ctx.frozen_writes.probes.get(), 1);
        let local = ctx.new_var(None);
        ctx.get_level(local);
        ctx.get_desc(local);
        assert_eq!(ctx.frozen_writes.probes.get(), 1);
    }

    #[test]
    fn matches_on_frozen_types_leaves_no_exception() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let [var, _, generic, concrete] = frozen_arrows(&ctx);
        // A rigid 'a cannot match int, but int can match an instantiable 'a.
        assert!(!super::super::ctype::matches(&ctx, &Env::empty(), generic, concrete));
        assert_no_frozen_writes(&ctx);
        assert!(super::super::ctype::matches(&ctx, &Env::empty(), concrete, generic));
        assert_no_frozen_writes(&ctx);
        assert!(matches!(*ctx.borrow_desc(var), TypeDesc::Tvar(None)));
        assert_eq!(ctx.get_level(var), GENERIC_LEVEL);
    }

    #[test]
    fn lasting_link_on_frozen_node_is_seen_only_here() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let [var, int, _, _] = frozen_arrows(&ctx);
        let other = TypeContext::new(Arc::new(IdGenerator::new()));
        super::super::ctype::link_type(&ctx, var, int);
        assert_eq!(ctx.repr(var), int);
        assert_eq!(other.repr(var), var);
        let snapshot = ctx.snapshot_type_state();
        ctx.set_desc(var, TypeDesc::Tnil);
        ctx.restore_type_state(snapshot);
        assert_eq!(ctx.repr(var), int);
        assert!(ctx.frozen_writes.any.get());
        assert_eq!(ctx.frozen_writes.descs.borrow().len(), 1);
        assert_no_frozen_writes(&other);
    }

    #[test]
    fn frozen_mutabilities_restore_absence_and_existing_entries() {
        use super::super::asttypes::MutableFlag;
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let cell = MutabilityRef::new_persistent(MutableFlag::Immutable);
        let snapshot = ctx.snapshot_type_state();
        ctx.set_mutability(cell, FieldMutability::Value(MutableFlag::Mutable));
        ctx.with_copy_session(|| {
            let copy = ctx.dup_mutability(cell);
            assert_eq!(ctx.mutability_ref_repr(cell), copy);
            ctx.with_copy_session(|| { ctx.dup_mutability(cell); });
            assert_eq!(ctx.mutability_ref_repr(cell), copy);
        });
        assert_eq!(ctx.mutability_repr(cell), MutableFlag::Mutable);
        ctx.restore_type_state(snapshot);
        assert_no_frozen_writes(&ctx);
        ctx.with_copy_session(|| { ctx.dup_mutability(cell); });
        assert_no_frozen_writes(&ctx);
        assert_eq!(ctx.mutability_repr(cell), MutableFlag::Immutable);
    }

    #[test]
    fn store_build_writes_do_not_create_exceptions() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        ctx.build_in_store(|| {
            let ty = ctx.new_generic_var(None);
            let row = ctx.alloc_row_field(Some(RowField::Rabsent));
            let memo = ctx.alloc_abbrev_nil();
            ctx.set_desc(ty, TypeDesc::Tnil);
            ctx.set_level(ty, 12);
            ctx.clear_row_field(row);
            ctx.write_abbrev(memo, AbbrevMemo::Mlink(AbbrevMemoRef::nil()));
            assert!(matches!(ctx.store.abbrev(memo), AbbrevMemo::Mlink(_)));
            assert_no_frozen_writes(&ctx);
        });
    }

    #[test]
    fn module_signature_cache_separates_scope_keys() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let env = Env::empty();
        let mut other = env.clone();
        other.add_gadt_instance_level();
        let path = Path::pident(Ident::create_persistent("M"));
        let signature = Arc::new(Vec::new());
        ctx.register_resolved_module_sig("M", Some(env.scope_id()), path, signature.clone());
        assert!(ctx.find_resolved_module_sig("M", None).is_none());
        assert!(
            ctx.find_resolved_module_sig("M", Some(other.scope_id()))
                .is_none()
        );
        let (_, found) = ctx
            .find_resolved_module_sig("M", Some(env.clone().scope_id()))
            .unwrap();
        assert!(Arc::ptr_eq(&found, &signature));
        ctx.register_resolved_module_sig("M", None, path, signature);
        assert!(ctx.find_resolved_module_sig("M", None).is_some());
    }

    #[test]
    fn typed_environment_snapshots_share_ownership() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let env = Env::empty();
        let env_ref = ctx.store_typed_env(&env);
        assert_eq!(ctx.store_typed_env(&env.clone()), env_ref);
        let first = ctx.get_typed_env(env_ref).expect("stored environment");
        let other = env.implicit_coercion();
        ctx.store_typed_env(&other);
        assert_eq!(ctx.store_typed_env(&env), env_ref);
        let second = ctx.get_typed_env(env_ref).expect("same environment");
        assert!(Rc::ptr_eq(&first, &second));

        // A retained snapshot must remain usable after its context is dropped.
        drop(ctx);
        assert_eq!(first.id(), env.id());
        assert_eq!(second.id(), env.id());
    }

    #[test]
    fn type_nodes_lease_scan_is_linear_at_10000_entries() {
        std::thread::spawn(|| {
            let busy = TypeNodes::new();
            // Simulate 10,000 occupied entries without allocating 10,000 arrays.
            // Each alias is busy because this test retains the original lease.
            FIRST_NODE_ARRAYS.with(|arrays| {
                let mut arrays = arrays.borrow_mut();
                arrays.extend((1..10_000).map(|_| Rc::clone(&busy.first)));
            });
            let fresh = TypeNodes::new();
            FIRST_ARRAY_LEASE_PROBES.with(|count| assert_eq!(count.get(), 10_000));
            FIRST_ARRAY_INITIALIZATIONS.with(|count| {
                assert_eq!(count.get(), TypeNodes::FIRST_LEN);
            });
            assert!(!Rc::ptr_eq(&busy.first, &fresh.first));
            drop(fresh);
            let reused = TypeNodes::new();
            FIRST_ARRAY_LEASE_PROBES.with(|count| assert_eq!(count.get(), 10_001));
            FIRST_ARRAY_INITIALIZATIONS.with(|count| assert_eq!(count.get(), 0));
            assert_eq!(reused.len(), 0);
            // Leave only the first entry; the next lease must stop after one probe.
            drop(reused);
            FIRST_NODE_ARRAYS.with(|arrays| arrays.borrow_mut().truncate(1));
            drop(busy);
            let reused = TypeNodes::new();
            FIRST_ARRAY_LEASE_PROBES.with(|count| assert_eq!(count.get(), 1));
            assert_eq!(reused.len(), 0);
        }).join().unwrap();
    }

    #[test]
    fn type_nodes_lease_exclusively_and_reuse_without_clearing() {
        // A fresh thread gives this test a fresh lease list.
        std::thread::spawn(|| {
            let first = TypeContext::new(Arc::new(IdGenerator::new()));
            let second = TypeContext::new(Arc::new(IdGenerator::new()));
            assert!(!Rc::ptr_eq(&first.types.first, &second.types.first));
            let address = Rc::as_ptr(&first.types.first);
            let idx = first.types.push(TypeDesc::Tvar(None), 37, 91);
            drop(first);
            let reused = TypeContext::new(Arc::new(IdGenerator::new()));
            assert_eq!(Rc::as_ptr(&reused.types.first), address);
            assert_eq!(reused.types.len(), 0);
            // Inspect the backing slot, not a live handle: leasing must not clear it.
            assert_eq!(reused.types.first[idx].level.get(), 37);
            assert_eq!(reused.types.push(TypeDesc::Tnil, 4, 5), idx);
            assert!(matches!(reused.types.desc(idx), TypeDesc::Tnil));
            assert_eq!(reused.types.level(idx), 4);
            assert_eq!(reused.types.id(idx), 5);
        }).join().unwrap();
    }

    /// A view build's scratch context creates no first array: the arrays of
    /// the thread are those of the compilation that started the build,
    /// however many scratch contexts follow and however much they allocate.
    #[test]
    fn scratch_contexts_take_no_first_array() {
        // A fresh thread gives this test a fresh lease list.
        std::thread::spawn(|| {
            let arrays = || {
                (
                    FIRST_NODE_ARRAYS.with(|arrays| arrays.borrow().len()),
                    super::super::type_expr::first_list_arrays(),
                )
            };
            let compilation = TypeContext::new(Arc::new(IdGenerator::new()));
            let marker = compilation.types.push(TypeDesc::Tvar(None), 37, 91);
            let before = arrays();
            // The compilation's nodes and its store's nodes.
            assert_eq!(before, (2, (2, 2)));
            for _ in 0..3 {
                let scratch = TypeContext::new_scratch(Arc::new(IdGenerator::new()));
                assert_eq!(scratch.type_expr_count(), 0);
                let mut tuples = Vec::new();
                for n in 0..10_000usize {
                    let var = scratch.new_var(None);
                    let items = vec![var; n % 3 + 1];
                    tuples.push((scratch.new_tuple(items), var, n % 3 + 1));
                }
                let (stored, piece) = scratch.build_in_store(|| {
                    let var = scratch.new_generic_var(None);
                    scratch.new_generic_type(TypeDesc::Ttuple(scratch.new_type_list(&[var, var])))
                });
                assert!(stored.is_store() && piece.is_some());
                assert_eq!(scratch.type_expr_count(), 20_000);
                for (tuple, var, len) in tuples {
                    let TypeDesc::Ttuple(list) = *scratch.get_desc(tuple) else {
                        panic!("expected a tuple");
                    };
                    let items = scratch.type_list(list);
                    assert_eq!(items.len(), len);
                    assert!((0..len).all(|i| items.get(i) == Some(var)));
                }
                assert_eq!(arrays(), before);
            }
            // The array the scratch contexts held was not written.
            assert_eq!(compilation.types.level(marker), 37);
            assert_eq!(compilation.types.len(), 1);
            // The worker's store is still the compilation's: a new
            // compilation gets a second one, as before.
            drop(compilation);
            let next = TypeContext::new(Arc::new(IdGenerator::new()));
            assert_eq!(next.types.len(), 0);
            assert_eq!(arrays(), before);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn type_nodes_direct_excludes_far_and_tagged_handles() {
        let nodes = TypeNodes::new();
        assert!(nodes.direct(0).is_some());
        assert!(nodes.direct(TypeNodes::FIRST_LEN as u32 - 1).is_some());
        assert!(nodes.direct(TypeNodes::FIRST_LEN as u32).is_none());
        assert!(nodes.direct(1 << 30).is_none());
        assert!(nodes.direct(1 << 31).is_none());
        nodes.set_direct(false);
        assert!(nodes.direct(0).is_none());
        nodes.set_direct(true);
        assert!(nodes.direct(0).is_some());
    }

    #[test]
    fn local_node_access_poisons_store_builds() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_type(TypeDesc::Tnil);
        for access in 0..4 {
            let (_, piece) = ctx.build_in_store(|| {
                assert_eq!(ctx.types.fast_limit.get(), 0);
                match access {
                    0 => { ctx.desc(local); }
                    1 => { ctx.get_level(local); }
                    2 => ctx.write_desc_raw(local, TypeDesc::Tnil),
                    3 => ctx.write_level_raw(local, 7),
                    _ => unreachable!(),
                }
            });
            assert!(piece.is_none());
            assert_eq!(ctx.types.fast_limit.get(), TypeNodes::FIRST_LEN as u32);
        }
    }

    #[test]
    fn local_node_direct_limit_tracks_nested_and_suspended_store_builds() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_type(TypeDesc::Tnil);
        let (_, piece) = ctx.build_in_store(|| {
            ctx.suspend_store_build(|| {
                assert_eq!(ctx.types.fast_limit.get(), TypeNodes::FIRST_LEN as u32);
                assert!(matches!(ctx.desc(local), TypeDesc::Tnil));
                let (_, nested) = ctx.build_in_store(|| ctx.get_level(local));
                assert!(nested.is_none());
                assert_eq!(ctx.types.fast_limit.get(), TypeNodes::FIRST_LEN as u32);
            });
            assert_eq!(ctx.types.fast_limit.get(), 0);
            let (_, nested) = ctx.build_in_store(|| ctx.desc(local));
            assert!(nested.is_none());
            assert_eq!(ctx.types.fast_limit.get(), 0);
        });
        assert!(piece.is_none());
        assert_eq!(ctx.types.fast_limit.get(), TypeNodes::FIRST_LEN as u32);
    }

    #[test]
    fn type_node_size_is_32_bytes() {
        assert_eq!(std::mem::size_of::<TypeNode>(), 32);
    }

    #[test]
    fn type_nodes_address_every_node_across_chunks() {
        let nodes = TypeNodes::new();
        let count = TypeNodes::FIRST_LEN + (1 << (TypeNodes::FIRST_CHUNK_BITS + 3)) + 5;
        for i in 0..count {
            assert_eq!(nodes.push(TypeDesc::Tnil, i as i32, -(i as i32)), i);
        }
        assert_eq!(nodes.len(), count);
        for i in (0..count).step_by(7) {
            nodes.set_level(i, i as i32 + 1);
        }
        for i in 0..count {
            let level = if i % 7 == 0 { i as i32 + 1 } else { i as i32 };
            assert_eq!(nodes.level(i), level);
            assert_eq!(nodes.id(i), -(i as i32));
            assert!(matches!(nodes.desc(i), TypeDesc::Tnil));
        }
    }

    #[test]
    fn borrowed_path_keys_find_owned_cache_entries() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let scope = Env::empty().scope_id();
        let mut other = Env::empty();
        other.add_gadt_instance_level();
        let module = Path::pdot(super::super::predef::path_int(), "M");
        let ty = Path::pdot_pos(module, "t", 3);
        ctx.register_type_newtype_level(scope, &ty, Some(2));
        assert_eq!(ctx.find_type_newtype_level(scope, &ty), Some(Some(2)));
        assert_eq!(ctx.find_type_newtype_level(other.scope_id(), &ty), None);
        ctx.register_forced_type_path_compare(scope, &module, &ty, true);
        assert_eq!(
            ctx.find_forced_type_path_compare(scope, &ty, &module),
            Some(true)
        );
        assert_eq!(ctx.find_forced_type_path_compare(scope, &ty, &ty), None);
    }

    #[test]
    fn shared_node_writes_stay_in_the_writing_compilation() {
        let a = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        let pool = a.store.shared_pool();
        let base = pool
            .publish(
                super::super::shared_store::SharedGraphSizes {
                    nodes: 2,
                    ..Default::default()
                },
                |_| super::super::shared_store::SharedGraphParts {
                    nodes: vec![
                        (TypeDesc::Tvar(None), GENERIC_LEVEL),
                        (TypeDesc::Tnil, GENERIC_LEVEL),
                    ],
                    payloads: Default::default(),
                    layouts: Vec::new(),
                    locations: Default::default(),
                    carried: Default::default(),
                },
            )
            .expect("pool has room");
        let var = super::super::shared_store::shared_ref(base, 0);
        let nil = super::super::shared_store::shared_ref(base, 1);
        assert!(var.is_shared() && a.contains_type_ref(var));

        // OCaml `link_type`/level updates on a dependency node: visible in this
        // compilation only.
        a.set_desc(var, TypeDesc::Tlink(nil));
        a.set_level(var, 3);
        assert_eq!(a.repr(var), nil);
        assert_eq!(a.get_level(var), 3);

        let b = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        assert!(matches!(*b.borrow_desc(var), TypeDesc::Tvar(None)));
        assert_eq!(b.get_level(var), GENERIC_LEVEL);
        std::thread::spawn(move || {
            let c = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
            assert!(matches!(*c.borrow_desc(var), TypeDesc::Tvar(None)));
            assert!(matches!(*c.borrow_desc(nil), TypeDesc::Tnil));
        })
        .join()
        .unwrap();

        // Backtracking restores the published view.
        let snapshot = b.snapshot_type_state();
        b.set_desc(var, TypeDesc::Tnil);
        b.restore_type_state(snapshot);
        assert!(matches!(*b.borrow_desc(var), TypeDesc::Tvar(None)));
    }

    #[test]
    fn store_build_allocates_shared_nodes_and_leaves_the_stamp_counter_alone() {
        let builder = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        let ((ty, binder), piece) = builder.build_in_store(|| {
            let var = builder.new_generic_var(Some("a".into()));
            let ty = builder.new_generic_type(TypeDesc::Ttuple(builder.new_type_list(&[var, var])));
            let binder = builder.rename_ident(&Ident::create_persistent("t"));
            (ty, binder)
        });
        let piece = piece.expect("store build stays shareable");
        assert!(ty.is_store(), "store builds allocate in the worker store");
        // The binder is in the store range, disjoint from local stamps, and
        // the builder's own counter did not move.
        assert_eq!(builder.current_stamp(), 10);
        assert!(binder.stamp() > super::super::thread_store::next_store_stamp() - 1000);
        assert!(binder.stamp() >= 1 << 29);
        drop(builder);

        // A later compilation on the worker reuses the node; using the piece
        // does not move its counter either, so a compilation's stamps do not
        // depend on whether it built the data or found it built.
        let user = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        user.touch_store_piece(&piece);
        user.touch_store_piece(&piece);
        assert_eq!(user.current_stamp(), 10);
        match &*user.get_desc(ty) {
            TypeDesc::Ttuple(items) => assert_eq!(items.len(), 2),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn store_build_reading_local_nodes_is_private() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_generic_var(None);
        let (_, piece) = ctx
            .build_in_store(|| ctx.new_generic_type(TypeDesc::Ttuple(ctx.new_type_list(&[local]))));
        assert!(
            piece.is_none(),
            "a build referring to a local node is not shared"
        );
        let (_, piece) = ctx.build_in_store(|| ctx.repr(local));
        assert!(
            piece.is_none(),
            "a build reading a local node is not shared"
        );
    }

    #[test]
    fn downstream_id_generator_accessor_keeps_compilation_identity() {
        let generator = Arc::new(IdGenerator::with_start_stamp(17));
        let ctx = TypeContext::new(generator.clone());
        let downstream = ctx.id_generator();
        assert!(Arc::ptr_eq(&generator, &downstream));
        assert_eq!(downstream.create("downstream").stamp(), 18);
        assert_eq!(ctx.current_stamp(), 18);
    }

    #[test]
    fn test_new_var() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let v1 = ctx.new_var(Some(crate::name::Name::new("a")));
        let v2 = ctx.new_var(None);

        assert_ne!(v1, v2);
    }

    #[test]
    fn test_new_arrow() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(t1, t2);

        let desc = ctx.get_desc(arrow);
        assert!(matches!(*desc, TypeDesc::Tarrow { .. }));
    }

    #[test]
    fn variant_layout_can_be_read_without_cloning() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let layout_ref = super::super::variant_runtime::plain_layout(
            &ctx,
            [("First".to_string(), false), ("Second".to_string(), true)],
        );

        let constructor_count =
            ctx.with_variant_layout(layout_ref, |layout| layout.constructors.len());

        assert_eq!(constructor_count, 2);
    }

    #[test]
    fn test_level_management() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        assert_eq!(ctx.current_level(), 0);

        ctx.begin_def();
        assert_eq!(ctx.current_level(), 1);

        ctx.begin_def();
        assert_eq!(ctx.current_level(), 2);

        ctx.end_def();
        assert_eq!(ctx.current_level(), 1);

        ctx.end_def();
        assert_eq!(ctx.current_level(), 0);
    }

    #[test]
    fn component_alias_sources_are_path_based() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let selected_path = Path::pdot_pos(
            Path::pident(Ident::create_persistent("Selected")),
            "Child",
            7,
        );
        let selected_path_no_pos =
            Path::pdot(Path::pident(Ident::create_persistent("Selected")), "Child");
        let alias_source = Path::pdot_pos(
            Path::pident(Ident::create_persistent("Selected__Backing")),
            "Child",
            3,
        );
        let alias_source_no_pos = Path::pdot(
            Path::pident(Ident::create_persistent("Selected__Backing")),
            "Child",
        );
        let spelling_only_source = Path::pident(Ident::create_persistent("Other__Child"));

        assert!(
            ctx.component_paths_for_alias_source(&alias_source_no_pos)
                .is_empty()
        );
        assert!(
            ctx.alias_sources_for_component_path(&selected_path_no_pos)
                .is_empty()
        );

        ctx.register_component_alias_source(selected_path, alias_source);

        assert!(
            ctx.component_paths_for_alias_source(&alias_source_no_pos)
                .iter()
                .any(|path| path.same(&selected_path_no_pos))
        );
        assert!(
            ctx.alias_sources_for_component_path(&selected_path_no_pos)
                .iter()
                .any(|path| path.same(&alias_source_no_pos))
        );
        assert!(
            ctx.component_paths_for_alias_source(&spelling_only_source)
                .is_empty()
        );
    }

    #[test]
    fn store_access_and_exception_backtracking() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_var(None);
        let stored = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        assert!(matches!(*ctx.borrow_desc(stored), TypeDesc::Tnil));
        assert_eq!(ctx.get_level(stored), GENERIC_LEVEL);
        assert_eq!(ctx.repr(stored), stored);
        let link = ctx.new_link(stored);
        assert_eq!(ctx.repr(link), stored);
        assert_ne!(local, stored);

        let memo = ctx.store.alloc_abbrev(AbbrevMemo::Mnil);
        let row = ctx.store.alloc_row_field(Some(RowField::Rabsent));
        let snapshot = ctx.snapshot_type_state();
        ctx.restore_abbrev_memo(memo, AbbrevMemo::Mlink(AbbrevMemoRef::nil()));
        ctx.set_row_field(row, RowField::Rpresent(Some(local)));
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mlink(_)));
        assert!(matches!(ctx.get_row_field(row), Some(RowField::Rpresent(Some(t))) if t == local));
        assert!(matches!(ctx.store.abbrev(memo), AbbrevMemo::Mnil));
        assert!(matches!(ctx.store.row_field(row), Some(RowField::Rabsent)));
        let nested = ctx.snapshot_type_state();
        ctx.clear_row_field(row);
        ctx.restore_type_state(nested);
        assert!(matches!(ctx.get_row_field(row), Some(RowField::Rpresent(Some(t))) if t == local));
        ctx.restore_type_state(snapshot);
        assert!(ctx.frozen_writes.row_fields.borrow().is_empty());
        assert_eq!(ctx.frozen_writes.memos.borrow().len(), 1);
        assert!(ctx.frozen_writes.any.get());
        // Memo contents are not part of the trail (btype.ml:692-700); store
        // memos stay in this compilation's exception table.
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mlink(_)));
        assert!(matches!(ctx.store.abbrev(memo), AbbrevMemo::Mnil));
        assert!(matches!(ctx.get_row_field(row), Some(RowField::Rabsent)));

        ctx.clear_row_field(row);
        assert!(ctx.get_row_field(row).is_none());
        assert!(matches!(ctx.store.row_field(row), Some(RowField::Rabsent)));
        ctx.memoized_abbrev_refs.borrow_mut().push(memo);
        ctx.restore_abbrev_memo(memo, AbbrevMemo::Mlink(AbbrevMemoRef::nil()));
        ctx.clear_abbrev_memos();
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mnil));
    }

    #[test]
    fn frozen_counters_exclude_local_owned_and_disabled_accesses() {
        use crate::perf_counters::frozen::{Kind, count};
        let mut ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let stored = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        let memo = ctx.store.alloc_abbrev(AbbrevMemo::Mnil);
        let read_before = count(&ctx, Kind::DescReadWorker);
        let level_before = count(&ctx, Kind::LevelReadWorker);
        let write_before = count(&ctx, Kind::LinkWorker);
        let memo_before = count(&ctx, Kind::MemoWrite);
        ctx.compiler_counters_enabled = false;
        ctx.get_desc(stored);
        ctx.get_level(stored);
        ctx.write_desc_raw(stored, TypeDesc::Tlink(stored));
        ctx.write_abbrev(memo, AbbrevMemo::Mnil);
        assert_eq!(count(&ctx, Kind::DescReadWorker), read_before);
        assert_eq!(count(&ctx, Kind::LevelReadWorker), level_before);
        assert_eq!(count(&ctx, Kind::LinkWorker), write_before);
        assert_eq!(count(&ctx, Kind::MemoWrite), memo_before);
        ctx.compiler_counters_enabled = true;
        let local = ctx.new_var(None);
        ctx.get_desc(local);
        ctx.get_level(local);
        ctx.write_desc_raw(local, TypeDesc::Tlink(stored));
        ctx.build_in_store(|| {
            let owned = ctx.new_generic_type(TypeDesc::Tnil);
            ctx.get_desc(owned);
            ctx.get_level(owned);
            ctx.write_desc_raw(owned, TypeDesc::Tlink(stored));
            let owned_memo = ctx.alloc_abbrev_nil();
            ctx.write_abbrev(owned_memo, AbbrevMemo::Mnil);
        });
        assert_eq!(count(&ctx, Kind::DescReadWorker), read_before);
        assert_eq!(count(&ctx, Kind::LevelReadWorker), level_before);
        assert_eq!(count(&ctx, Kind::LinkWorker), write_before);
        assert_eq!(count(&ctx, Kind::MemoWrite), memo_before);
        ctx.get_desc(stored);
        ctx.get_level(stored);
        ctx.write_desc_raw(stored, TypeDesc::Tlink(local));
        ctx.write_abbrev(memo, AbbrevMemo::Mnil);
        assert_eq!(count(&ctx, Kind::DescReadWorker), read_before + 1);
        assert_eq!(count(&ctx, Kind::LevelReadWorker), level_before + 1);
        assert_eq!(count(&ctx, Kind::LinkWorker), write_before + 1);
        assert_eq!(count(&ctx, Kind::MemoWrite), memo_before + 1);

        let base = ctx
            .store
            .shared_pool()
            .publish(
                super::super::shared_store::SharedGraphSizes {
                    nodes: 1,
                    ..Default::default()
                },
                |_| super::super::shared_store::SharedGraphParts {
                    nodes: vec![(TypeDesc::Tnil, GENERIC_LEVEL)],
                    payloads: Default::default(),
                    layouts: Vec::new(),
                    locations: Default::default(),
                    carried: Default::default(),
                },
            )
            .unwrap();
        let shared = super::super::shared_store::shared_ref(base, 0);
        let links = count(&ctx, Kind::LinkShared);
        let descriptors = count(&ctx, Kind::DescWriteShared);
        let levels = count(&ctx, Kind::LevelWriteShared);
        let snapshot = ctx.snapshot_type_state();
        ctx.set_desc(shared, TypeDesc::Tlink(local));
        ctx.set_level(shared, 1);
        ctx.restore_type_state(snapshot);
        assert_eq!(count(&ctx, Kind::LinkShared), links + 1);
        // Restoring absence removes the exception without writing a value.
        assert_eq!(count(&ctx, Kind::DescWriteShared), descriptors);
        assert_eq!(count(&ctx, Kind::LevelWriteShared), levels + 1);
    }

    #[test]
    fn store_descriptor_and_level_writes_are_isolated_and_backtracked() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let ty = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        let untouched = ctx.store.alloc_type(
            TypeDesc::Tvar(None),
            GENERIC_LEVEL,
        );
        let initial = ctx.snapshot_type_state();
        ctx.set_desc(
            ty,
            TypeDesc::Tvar(
                Some("stored".into())),
        );
        ctx.set_level(ty, 12);
        let changed = ctx.snapshot_type_state();
        let local = ctx.new_var(None);
        super::super::ctype::link_type(&ctx, ty, local);
        assert_eq!(ctx.repr(ty), local);
        assert_eq!(ctx.get_level(ty), 12);
        assert!(
            matches!(*ctx.borrow_desc(local), TypeDesc::Tvar(Some(ref name)) if name == "stored")
        );
        ctx.set_desc(untouched, TypeDesc::Tlink(local));
        ctx.set_level(untouched, 5);
        assert!(matches!(ctx.store.desc(ty), TypeDesc::Tnil));
        assert_eq!(ctx.store.level(ty), GENERIC_LEVEL);
        ctx.restore_type_state(changed);
        assert!(
            matches!(*ctx.borrow_desc(ty), TypeDesc::Tvar(Some(ref name)) if name == "stored")
        );
        assert_eq!(ctx.get_level(ty), 12);
        assert!(matches!(
            *ctx.borrow_desc(untouched),
            TypeDesc::Tvar(None)
        ));
        assert_eq!(ctx.get_level(untouched), GENERIC_LEVEL);
        ctx.restore_type_state(initial);
        assert!(matches!(*ctx.borrow_desc(ty), TypeDesc::Tnil));
        assert_eq!(ctx.get_level(ty), GENERIC_LEVEL);
        // Writing after rollback cannot reuse a descriptor from the abandoned
        // snapshot (its arena allocation intentionally remains alive).
        ctx.set_desc(ty, TypeDesc::Ttuple(ctx.new_type_list(&[local])));
        assert!(
            matches!(*ctx.borrow_desc(ty), TypeDesc::Ttuple(ts) if ctx.type_list(ts).to_vec() == [local])
        );
    }

    #[test]
    fn descriptor_replacement_preserves_earlier_copies_and_backtracking() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let original = Path::pident(ctx.create_ident("t"));
        let t = ctx.new_constr(original, vec![]);
        let path_of = |ty| match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, .. } => *path,
            _ => unreachable!(),
        };
        let before = ctx.new_type(ctx.get_desc(t).into_desc());
        let changed = Path::pident(ctx.create_ident("u"));
        ctx.set_desc(
            t,
            TypeDesc::Tconstr {
                path: changed,
                args: ctx.new_type_list(&[]),
                abbrev: ctx.alloc_abbrev_nil(),
            },
        );
        assert_eq!(path_of(before), original);
        assert_eq!(path_of(t), changed);
        let snapshot = ctx.snapshot_type_state();
        let speculative = ctx.new_constr(Path::pident(ctx.create_ident("w")), vec![]);
        ctx.set_desc(t, ctx.get_desc(speculative).into_desc());
        ctx.restore_type_state(snapshot);
        assert_eq!(path_of(t), changed);
        let later = ctx.new_constr(Path::pident(ctx.create_ident("x")), vec![]);
        assert_ne!(later, speculative);
        assert_ne!(later, t);
    }

    #[test]
    fn failed_unification_restores_stored_constructor_links() {
        use super::super::ctype::{UnifyState, unify};
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int_path = super::super::predef::path_int();
        let stored_int = ctx.store.alloc_type(
            TypeDesc::Tconstr {
                path: int_path,
                args: TypeRefList::EMPTY,
                abbrev: ctx.store.alloc_abbrev(AbbrevMemo::Mnil),
            },
            GENERIC_LEVEL,
        );
        let local_int = ctx.new_constr(int_path, vec![]);
        let left_bool = ctx.new_constr(super::super::predef::path_bool(), vec![]);
        let right_string = ctx.new_constr(super::super::predef::path_string(), vec![]);
        let left = ctx.new_tuple(vec![stored_int, left_bool]);
        let right = ctx.new_tuple(vec![local_int, right_string]);
        let snapshot = ctx.snapshot_type_state();
        let mut state = UnifyState::new();
        assert!(unify(&ctx, &mut state, left, right).is_err());
        // The first tuple element unified before the second element failed.
        // Skipping stored-source links would incorrectly leave it unchanged.
        assert_eq!(ctx.repr(stored_int), local_int);
        ctx.restore_type_state(snapshot);
        assert_eq!(ctx.repr(stored_int), stored_int);
        assert_eq!(ctx.get_level(stored_int), GENERIC_LEVEL);
        assert!(matches!(
            ctx.store.desc(stored_int),
            TypeDesc::Tconstr { .. }
        ));
    }

    #[test]
    fn store_links_are_followed_without_compressing_dependencies() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let target = ctx.new_var(None);
        let middle = ctx.new_link(target);
        let stored = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        super::super::ctype::link_type(&ctx, stored, middle);
        let snapshot = ctx.snapshot_type_state();
        let entries = ctx.mutation_journal.borrow().entries.len();
        assert_eq!(ctx.repr(stored), target);
        assert_eq!(ctx.mutation_journal.borrow().entries.len(), entries);
        assert_eq!(ctx.frozen_writes.descs.borrow().len(), 1);
        ctx.restore_type_state(snapshot);
        assert!(matches!(*ctx.borrow_desc(stored), TypeDesc::Tlink(t) if t == middle));
        assert!(matches!(ctx.store.desc(stored), TypeDesc::Tnil));
    }

    #[test]
    fn test_repr() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_link(t1);
        let t3 = ctx.new_link(t2);

        // repr should follow the chain
        assert_eq!(ctx.repr(t3), t1);
        assert_eq!(ctx.repr(t2), t1);
        assert_eq!(ctx.repr(t1), t1);
    }

    #[test]
    fn test_repr_path_compression() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_link(t1);
        let t3 = ctx.new_link(t2);

        // First call to repr(t3) should do path compression
        assert_eq!(ctx.repr(t3), t1);

        // After path compression, t3 should now point directly to t1
        let desc = ctx.get_desc(t3);
        match &*desc {
            TypeDesc::Tlink(target) => assert_eq!(*target, t1),
            _ => panic!("Expected Tlink after path compression"),
        }
    }

    #[test]
    fn mutation_trail_restores_repeated_changes() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let ty = ctx.new_var(Some(crate::name::Name::new("original")));
        let level = ctx.get_level(ty);
        let snapshot = ctx.snapshot_type_state();

        ctx.set_desc(ty, TypeDesc::Tvar(Some(crate::name::Name::new("first"))));
        ctx.set_desc(ty, TypeDesc::Tnil);
        ctx.set_level(ty, level + 1);
        ctx.set_level(ty, level + 2);
        ctx.restore_type_state(snapshot);

        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "original"));
        assert_eq!(ctx.get_level(ty), level);
    }

    proptest! {
        #[test]
        fn mutation_trail_restores_generated_repeated_type_mutations(
            mutations in prop::collection::vec((0usize..8, any::<bool>(), -10i32..100), 1..128),
        ) {
            let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
            let types: Vec<_> = (0..8)
                .map(|index| ctx.new_var(Some(crate::name::Name::new(&format!("original-{index}")))))
                .collect();
            let original_levels: Vec<_> = types.iter().map(|ty| ctx.get_level(*ty)).collect();
            let snapshot = ctx.snapshot_type_state();

            for (index, nil, level) in mutations {
                let ty = types[index];
                let desc = if nil {
                    TypeDesc::Tnil
                } else {
                    TypeDesc::Tvar(Some(crate::name::Name::new(&format!("mutated-{index}-{level}"))))
                };
                ctx.set_desc(ty, desc);
                ctx.set_level(ty, level);
            }
            ctx.restore_type_state(snapshot);

            for (index, ty) in types.into_iter().enumerate() {
                let expected_name = format!("original-{index}");
                prop_assert!(matches!(
                    &*ctx.get_desc(ty),
                    TypeDesc::Tvar(Some(name)) if name == &expected_name
                ));
                prop_assert_eq!(ctx.get_level(ty), original_levels[index]);
            }
        }
    }

    #[test]
    fn mutation_trail_supports_nested_snapshots() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let ty = ctx.new_var(Some(crate::name::Name::new("outer")));
        let outer = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tvar(Some(crate::name::Name::new("middle"))));

        let inner = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tnil);
        ctx.begin_def();
        ctx.restore_type_state(inner);
        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "middle"));
        assert_eq!(ctx.current_level(), 0);

        ctx.restore_type_state(outer);
        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "outer"));
    }

    #[test]
    fn mutation_trail_leaves_new_type_allocations_and_their_state_alive() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let old = ctx.new_var(Some(crate::name::Name::new("old")));
        let snapshot = ctx.snapshot_type_state();
        let allocated = ctx.new_var(Some(crate::name::Name::new("new")));
        ctx.set_desc(allocated, TypeDesc::Tnil);
        ctx.set_level(allocated, 42);
        ctx.set_desc(old, TypeDesc::Tnil);

        ctx.restore_type_state(snapshot);

        assert_eq!(ctx.type_expr_count(), 2);
        assert!(matches!(&*ctx.get_desc(allocated), TypeDesc::Tnil));
        assert_eq!(ctx.get_level(allocated), 42);
        assert!(matches!(&*ctx.get_desc(old), TypeDesc::Tvar(Some(name)) if name == "old"));
    }

    #[test]
    fn mutation_trail_restores_row_cells() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let row = ctx.alloc_row_field(Some(RowField::Rpresent(None)));
        let snapshot = ctx.snapshot_type_state();
        ctx.set_row_field(row, RowField::Rabsent);
        let allocated = ctx.alloc_row_field(Some(RowField::Rpresent(None)));
        ctx.set_row_field(allocated, RowField::Rabsent);

        ctx.restore_type_state(snapshot);

        assert!(matches!(
            ctx.get_row_field(row),
            Some(RowField::Rpresent(None))
        ));
        assert!(matches!(
            ctx.get_row_field(allocated),
            Some(RowField::Rabsent)
        ));
    }

    #[test]
    fn mutation_trail_leaves_new_abbreviation_memos_alive() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let snapshot = ctx.snapshot_type_state();
        let memo = ctx.alloc_abbrev_nil();
        let abbrev = ctx.new_var(None);
        let expansion = ctx.new_var(None);
        let path = Path::pident(Ident::create_persistent("Allocated"));
        ctx.memorize_abbrev_expansion(memo, PrivateFlag::Public, path, abbrev, expansion);

        ctx.restore_type_state(snapshot);

        // btype.ml:544-553: memorized expansions are not trailed, and a
        // backtrack with nothing trailed leaves them (and `memo`) alone.
        assert_eq!(
            ctx.find_abbrev_expansion(memo, PrivateFlag::Public, &path),
            Some(expansion)
        );
        assert_eq!(&*ctx.memoized_abbrev_refs.borrow(), &[memo]);
    }

    #[test]
    fn mutation_trail_does_not_restore_abbreviation_memos() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let memo = ctx.alloc_abbrev_nil();
        let abbrev = ctx.new_var(None);
        let first = ctx.new_var(None);
        let second = ctx.new_var(None);
        let path = Path::pident(Ident::create_persistent("Alias"));
        ctx.memorize_abbrev_expansion(memo, PrivateFlag::Public, path, abbrev, first);
        let snapshot = ctx.snapshot_type_state();
        ctx.memorize_abbrev_expansion(
            memo,
            PrivateFlag::Public,
            Path::pident(Ident::create_persistent("Other")),
            abbrev,
            second,
        );
        ctx.clear_abbrev_memos();

        ctx.restore_type_state(snapshot);

        // btype.ml:544-547 `cleanup_abbrev` is not undone by `backtrack`
        // (btype.ml:692-702): memo contents are not part of the trail.
        assert_eq!(
            ctx.find_abbrev_expansion(memo, PrivateFlag::Public, &path),
            None
        );
        assert!(ctx.memoized_abbrev_refs.borrow().is_empty());
        let _ = first;
    }

    #[test]
    fn mutation_trail_restores_definition_and_abbreviation_state() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let initial_levels = ctx.current_def_level_state();
        let memo = ctx.alloc_abbrev_nil();
        let snapshot = ctx.snapshot_type_state();

        ctx.set_current_abbreviations(memo);
        ctx.begin_def();
        ctx.reset_global_level();
        assert_ne!(ctx.current_def_level_state(), initial_levels);

        ctx.restore_type_state(snapshot);

        assert_eq!(ctx.current_abbreviations(), AbbrevMemoRef::nil());
        assert_eq!(ctx.current_def_level_state(), initial_levels);
    }

    #[test]
    fn restoring_a_nested_snapshot_does_not_journal_the_restore() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let ty = ctx.new_var(Some(crate::name::Name::new("original")));
        let outer = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tvar(Some(crate::name::Name::new("outer"))));
        let inner = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tnil);

        ctx.restore_type_state(inner);

        assert_eq!(ctx.mutation_journal.borrow().entries.len(), 1);
        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "outer"));
        ctx.restore_type_state(outer);
        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "original"));
    }

    #[test]
    fn outer_backtrack_restores_committed_inner_mutations() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let pre_type = ctx.new_var(Some(crate::name::Name::new("pre")));
        let pre_row = ctx.alloc_row_field(Some(RowField::Rpresent(None)));
        let pre_memo = ctx.alloc_abbrev_nil();
        let pre_abbrev = ctx.new_var(None);
        let pre_expansion = ctx.new_var(None);
        let pre_path = Path::pident(Ident::create_persistent("Pre"));
        ctx.memorize_abbrev_expansion(
            pre_memo,
            PrivateFlag::Public,
            pre_path,
            pre_abbrev,
            pre_expansion,
        );
        let initial_levels = ctx.current_def_level_state();
        let outer = ctx.snapshot_type_state();

        let post_type = ctx.new_var(Some(crate::name::Name::new("post")));
        let post_row = ctx.alloc_row_field(Some(RowField::Rpresent(None)));
        let post_memo = ctx.alloc_abbrev_nil();
        let post_abbrev = ctx.new_var(None);
        let post_expansion = ctx.new_var(None);
        let post_path = Path::pident(Ident::create_persistent("Post"));

        let restored_inner = ctx.snapshot_type_state();
        ctx.set_desc(post_type, TypeDesc::Tnil);
        ctx.set_row_field(post_row, RowField::Rabsent);
        ctx.memorize_abbrev_expansion(
            post_memo,
            PrivateFlag::Public,
            post_path,
            post_abbrev,
            post_expansion,
        );
        ctx.restore_type_state(restored_inner);

        assert!(
            matches!(&*ctx.get_desc(post_type), TypeDesc::Tvar(Some(name)) if name == "post")
        );
        assert!(matches!(
            ctx.get_row_field(post_row),
            Some(RowField::Rpresent(None))
        ));
        assert_eq!(
            ctx.find_abbrev_expansion(post_memo, PrivateFlag::Public, &post_path),
            None
        );

        let committed_inner = ctx.snapshot_type_state();
        ctx.set_desc(pre_type, TypeDesc::Tnil);
        ctx.set_row_field(pre_row, RowField::Rabsent);
        ctx.clear_abbrev_memo(pre_memo);
        ctx.set_desc(post_type, TypeDesc::Tnil);
        ctx.set_row_field(post_row, RowField::Rabsent);
        ctx.memorize_abbrev_expansion(
            post_memo,
            PrivateFlag::Public,
            post_path,
            post_abbrev,
            post_expansion,
        );
        ctx.begin_def();
        drop(committed_inner);
        ctx.restore_type_state(outer);

        assert!(
            matches!(&*ctx.get_desc(pre_type), TypeDesc::Tvar(Some(name)) if name == "pre")
        );
        assert!(matches!(
            ctx.get_row_field(pre_row),
            Some(RowField::Rpresent(None))
        ));
        // btype.ml:692-702: a backtrack over trailed changes runs
        // `cleanup_abbrev`, forgetting every memorized expansion, including
        // those memorized before the snapshot.
        assert_eq!(
            ctx.find_abbrev_expansion(pre_memo, PrivateFlag::Public, &pre_path),
            None
        );
        let _ = pre_expansion;
        assert!(
            matches!(&*ctx.get_desc(post_type), TypeDesc::Tvar(Some(name)) if name == "post")
        );
        assert!(matches!(
            ctx.get_row_field(post_row),
            Some(RowField::Rpresent(None))
        ));
        assert_eq!(
            ctx.find_abbrev_expansion(post_memo, PrivateFlag::Public, &post_path),
            None
        );
        assert_eq!(ctx.current_def_level_state(), initial_levels);
        assert!(ctx.memoized_abbrev_refs.borrow().is_empty());
        assert!(!ctx.mutation_logging.full() && !ctx.mutation_logging.compress());
    }

    #[test]
    fn restoring_an_outer_snapshot_invalidates_nested_snapshots() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let ty = ctx.new_var(Some(crate::name::Name::new("original")));
        let outer = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tvar(Some(crate::name::Name::new("outer"))));
        let inner = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tnil);

        ctx.restore_type_state(outer);
        ctx.restore_type_state(inner);

        assert!(matches!(&*ctx.get_desc(ty), TypeDesc::Tvar(Some(name)) if name == "original"));
        assert!(!ctx.mutation_logging.full() && !ctx.mutation_logging.compress());
    }

    #[test]
    fn test_tuple() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let tuple = ctx.new_tuple(vec![t1, t2]);

        let desc = ctx.get_desc(tuple);
        match &*desc {
            TypeDesc::Ttuple(types) => assert_eq!(types.len(), 2),
            _ => panic!("Expected tuple"),
        }
    }
}
