//! Per-thread persistent type store.
//!
//! OCaml's `persistent_structures` table (`compiler/ml/env.ml:669-678`)
//! shares loaded signatures within a compilation, but `Res_compmisc.init_path`
//! resets it between units (`compiler/core/res_compmisc.ml:35`). The Rust
//! in-process build avoids re-internalizing immutable raw dependency storage
//! for every unit on a worker. Each compilation isolates descriptor, level,
//! memo and row writes in `TypeContext` overlays; forced component binders and
//! substitution state remain unit-local, matching `initial_env`'s identifier
//! reset (`compiler/core/res_compmisc.ml:49`).
//!
//! References into the store carry `type_expr::STORE_REF_TAG`. The store is
//! `!Send` by construction and is only reached through the exclusive owned lease a
//! `TypeContext` takes at creation; no node or store is refcounted.
//!
//! Design: `projects/in-process-performance/THREAD_TYPE_STORE.md`.

use super::context::TypeArena;
use super::decl::{Signature, TypeDeclaration};
use super::path::Path;
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, RowField, RowFieldRef, TypeDesc, TypeExpr, TypeExprRef,
};
use super::variant_runtime::{Layout, LayoutRef};
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::PortablePersStruct;
use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use crate::intern::StrIdx;
use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::sync::Arc;
use std::sync::atomic::{AtomicI32, AtomicU64, Ordering};

/// First node id handed out by a store. Compilation-local ids start at the
/// `IdGenerator` base and never reach this range in practice.
const STORE_TYPE_ID_BASE: i32 = 1 << 30;

/// Build generation. `begin_build` bumps it once per `rescript build`; a
/// worker whose store was filled during an earlier build (watch mode) drops
/// that store and starts empty, so no store outlives the build that published
/// the signatures it holds and long-running processes do not accumulate every
/// republished graph.
static BUILD_GENERATION: AtomicU64 = AtomicU64::new(0);

/// Start a new build: stores filled by earlier builds are discarded on their
/// next lease.
pub fn begin_build() {
    BUILD_GENERATION.fetch_add(1, Ordering::SeqCst);
}

/// Number of builds started with `begin_build` in this process (0 when none
/// has, e.g. a standalone `bsc` run).
pub fn build_generation() -> u64 {
    BUILD_GENERATION.load(Ordering::SeqCst)
}

/// First binder stamp handed out to identifiers created while building shared
/// store data. Compilation-local stamps restart per unit and stay far below
/// this range, so a shared binder can never be `Ident::same` as a local one.
const STORE_STAMP_BASE: i32 = 1 << 29;

/// Binder stamps of shared store data, unique across all workers of the
/// process (shared data never leaves its worker, but a unit's published
/// signature could mention one of these stamps).
static STORE_STAMP: AtomicI32 = AtomicI32::new(STORE_STAMP_BASE);

pub(crate) fn next_store_stamp() -> i32 {
    STORE_STAMP.fetch_add(1, Ordering::Relaxed) + 1
}

/// Dependency signature internalized once into the store.
struct PersEntry {
    /// Keeps the portable struct alive so its address cannot be reused as a
    /// key for a different graph.
    _owner: Arc<PortablePersStruct>,
    ps: Arc<PersStruct>,
}

/// One type declaration of a store-owned signature, with the keys a unit's
/// `TypeContext` registers it under.
#[derive(Debug)]
pub(crate) struct SigTypeRegistration {
    pub(crate) name: smol_str::SmolStr,
    pub(crate) stamp: i32,
    pub(crate) qualified_name: smol_str::SmolStr,
    pub(crate) qualified_path: Path,
    pub(crate) decl: Arc<TypeDeclaration>,
}

/// The type registrations of one store-owned signature, shared by every unit
/// that loads it, with an exact-path index built on first use.
#[derive(Debug)]
pub(crate) struct SigTypeBatch {
    entries: Box<[SigTypeRegistration]>,
    exact_index: std::sync::OnceLock<crate::fast_hash::AHashMap<Path, u32>>,
}

impl SigTypeBatch {
    /// The declaration the batch registers last under `path`, as replaying
    /// its entries into a map keyed by `qualified_path` would leave it.
    pub(crate) fn find_exact(&self, path: &Path) -> Option<&Arc<TypeDeclaration>> {
        let index = self.exact_index.get_or_init(|| {
            let mut index = crate::fast_hash::AHashMap::with_capacity(self.entries.len());
            for (position, entry) in self.entries.iter().enumerate() {
                index.insert(entry.qualified_path.clone(), position as u32);
            }
            index
        });
        index
            .get(path)
            .map(|&position| &self.entries[position as usize].decl)
    }
}

impl std::ops::Deref for SigTypeBatch {
    type Target = [SigTypeRegistration];

    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

/// Store-built label descriptions of one record type, their summary, and the
/// replay record of building them.
pub(crate) type SharedRecordLabels = (
    Arc<Vec<crate::types::decl::LabelDescription>>,
    Arc<crate::types::context::RecordLabelDescriptionSummary>,
    Arc<crate::types::context::StorePiece>,
);

/// Shared dependency state for one worker thread.
pub(crate) struct ThreadTypeStore {
    types: TypeArena,
    /// Initial memo values of store `Tconstr` nodes (always `Mnil` after
    /// internalization, like `compiler/ml/subst.ml:173-177` on save). Writes go
    /// to the reading compilation's overlay.
    abbrevs: RefCell<Vec<AbbrevMemo>>,
    row_fields: RefCell<Vec<Option<RowField>>>,
    variant_layouts: RefCell<Vec<Layout>>,
    next_type_id: Cell<i32>,
    /// The next [`PathBlock`](crate::types::type_expr::PathBlock) token for a
    /// path written into an existing node. Kept here so tokens are unique
    /// among every node one worker's compilations can reach.
    next_path_block_token: Cell<u32>,
    /// The next [`IdentOrigin`](crate::ident::IdentOrigin) for an identifier
    /// block decoded from a compiled interface (0 is "not decoded").
    next_ident_origin: Cell<u32>,
    /// Internalized dependency signatures keyed by the identity of the
    /// portable struct they were built from (`compiler/ml/env.ml:669-678`:
    /// one `persistent_structures` entry per read unit).
    pers: RefCell<HashMap<usize, PersEntry>>,
    /// Signatures retained by `pers`; their items keep one address for the
    /// life of the store.
    shared_signatures: RefCell<HashSet<usize>>,
    /// One `Arc` per declaration of a store-owned signature, keyed by the
    /// declaration's address, so per-unit registries share an allocation
    /// instead of cloning every dependency declaration for every compilation.
    type_decl_arcs: RefCell<HashMap<usize, Arc<TypeDeclaration>>>,
    /// Per-unit type registrations of a store-owned signature under one module
    /// path, keyed by the signature's item address and that path.
    sig_type_registrations: RefCell<HashMap<(usize, Path), Arc<SigTypeBatch>>>,
    /// Component-table name indexes of store-owned signatures, keyed by the
    /// signature's address (kept alive by `pers`).
    signature_indexes: RefCell<HashMap<usize, Arc<crate::types::env_lazy::SignatureIndex>>>,
    /// Component views of persistent-rooted module paths built as store
    /// builds, with the replay record of building them (OCaml builds such a
    /// view once per process, from `Env.empty`: compiler/ml/env.ml:669-678).
    shared_components: RefCell<
        HashMap<
            crate::types::context::QualifiedModuleComponentsCacheKey,
            (
                Arc<crate::types::env_lazy::QualifiedModuleComponents>,
                Arc<crate::types::context::StorePiece>,
            ),
        >,
    >,
    /// Label descriptions of large regular records of dependency types,
    /// built as store builds (see `typecore::build_record_label_descriptions_info`).
    record_labels: RefCell<HashMap<Path, SharedRecordLabels>>,
    /// The predefined environment built as a store build, with its replay
    /// record (see `env::initial_env`).
    initial_env: RefCell<
        Option<(
            crate::types::env::Env,
            Arc<crate::types::context::StorePiece>,
        )>,
    >,
    generation: u64,
    /// The build's process-wide pool of immutable dependency graphs; holding
    /// it keeps every shared node this store's signatures refer to alive.
    shared: Arc<super::shared_store::SharedTypePool>,
    /// Locations of store-owned declarations and type labels
    /// (`DeclLocKind::Store` handles; see `types::decl_loc`).
    decl_locs: super::decl_loc::OwnedDeclLocs,
    decl_loc_owner: u32,
    path_provenance: RefCell<super::path_provenance::PathProvenance>,
}

impl ThreadTypeStore {
    /// An identifier origin no other decoded block holds.
    pub(crate) fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin {
        crate::ident::IdentOrigin::next_in(
            crate::ident::IdentOrigin::STORE,
            &self.next_ident_origin,
        )
    }

    /// A path block no other node holds.
    pub(crate) fn fresh_path_block(&self) -> crate::types::type_expr::PathBlock {
        let token = self.next_path_block_token.get();
        self.next_path_block_token
            .set(token.checked_add(1).expect("path block tokens exhausted"));
        crate::types::type_expr::PathBlock::token(token)
    }

    fn new() -> Self {
        let generation = BUILD_GENERATION.load(Ordering::SeqCst);
        ThreadTypeStore {
            types: TypeArena::new(),
            abbrevs: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            variant_layouts: RefCell::new(Vec::new()),
            next_type_id: Cell::new(STORE_TYPE_ID_BASE),
            next_path_block_token: Cell::new(0),
            next_ident_origin: Cell::new(crate::ident::IdentOrigin::STORE.start),
            pers: RefCell::new(HashMap::new()),
            shared_signatures: RefCell::new(HashSet::new()),
            type_decl_arcs: RefCell::new(HashMap::new()),
            sig_type_registrations: RefCell::new(HashMap::new()),
            signature_indexes: RefCell::new(HashMap::new()),
            shared_components: RefCell::new(HashMap::new()),
            record_labels: RefCell::new(HashMap::new()),
            initial_env: RefCell::new(None),
            generation,
            shared: super::shared_store::pool_for(generation),
            decl_locs: Default::default(),
            path_provenance: Default::default(),
            decl_loc_owner: super::decl_loc::next_table_owner(),
        }
    }

    pub(crate) fn record_ident_name(
        &self,
        id: &crate::ident::Ident,
        allocation: super::path_provenance::NameAllocation,
    ) {
        self.path_provenance
            .borrow_mut()
            .record_name(id, allocation);
    }

    pub(crate) fn ident_name_allocation(
        &self,
        id: &crate::ident::Ident,
    ) -> Option<super::path_provenance::NameAllocation> {
        self.path_provenance.borrow().name(id)
            .or_else(|| self.shared.ident_name_allocation(id))
    }

    pub(crate) fn dotted_with_name(
        &self,
        prefix: Arc<super::Path>,
        text: crate::name::Name,
        name: super::path_provenance::NameAllocation,
        pos: i32,
    ) -> super::Path {
        self.path_provenance
            .borrow_mut()
            .dotted(prefix, text, name, pos)
    }

    pub(crate) fn dotted_allocation(
        &self,
        path: &super::Path,
    ) -> Option<super::path_provenance::DottedAllocation> {
        self.path_provenance
            .borrow()
            .get(path)
            .cloned()
            .or_else(|| self.shared.dotted_allocation(path))
    }

    /// Store handle for a declaration location built into the store.
    pub(crate) fn intern_decl_loc(&self, loc: crate::location::Location) -> super::DeclLoc {
        if let Some(source) = super::DeclLoc::source(&loc) {
            return source;
        }
        super::DeclLoc::table(
            super::decl_loc::DeclLocKind::Store,
            self.decl_loc_owner,
            self.decl_locs.intern(loc),
        )
    }

    pub(crate) fn intern_decl_loc_with_identity(
        &self,
        loc: crate::location::Location,
        identity: super::decl_loc::LocationIdentity,
    ) -> super::DeclLoc {
        super::DeclLoc::table(
            super::decl_loc::DeclLocKind::Store,
            self.decl_loc_owner,
            self.decl_locs.intern_with_identity(loc, identity),
        )
    }

    /// Allocation identity of a location owned by this store.
    pub(crate) fn decl_loc_identity(
        &self,
        loc: super::DeclLoc,
    ) -> Option<super::decl_loc::LocationIdentity> {
        assert_eq!(loc.owner(), self.decl_loc_owner);
        self.decl_locs.identity(loc.index())
    }

    /// Import coordinates and allocation identities into a fresh namespace.
    pub(crate) fn import_portable_decl_locs<'a>(
        &self,
        table: &super::decl_loc::DeclLocTable,
        files: &'a dyn Fn(crate::intern::StrIdx) -> crate::intern::StrIdx,
    ) -> super::decl_loc::DeclLocImport<'a> {
        let mut table = table.clone();
        table.remap_for_import(files);
        let (base, instances) = self.decl_locs.append_portable(&table);
        super::decl_loc::DeclLocImport {
            kind: super::decl_loc::DeclLocKind::Store,
            owner: self.decl_loc_owner,
            base,
            instances,
            files,
        }
    }

    #[cfg(test)]
    pub(crate) fn import_decl_locs<'a>(
        &self,
        locations: impl IntoIterator<Item = crate::location::Location>,
        files: &'a dyn Fn(StrIdx) -> StrIdx,
    ) -> super::decl_loc::DeclLocImport<'a> {
        super::decl_loc::DeclLocImport {
            kind: super::decl_loc::DeclLocKind::Store,
            owner: self.decl_loc_owner,
            base: self.decl_locs.append(locations),
            instances: Vec::new(),
            files,
        }
    }

    /// The location of a store handle.
    pub(crate) fn decl_loc(&self, loc: super::DeclLoc) -> crate::location::Location {
        assert_eq!(
            loc.owner(),
            self.decl_loc_owner,
            "store declaration location resolved by another worker store"
        );
        self.decl_locs.get(loc.index())
    }

    /// The process-wide pool of this store's build.
    #[inline]
    pub(crate) fn shared_pool(&self) -> &super::shared_store::SharedTypePool {
        &self.shared
    }

    /// The shared internalization of `pps`, if this thread already built one.
    pub(crate) fn pers_struct(&self, pps: &Arc<PortablePersStruct>) -> Option<Arc<PersStruct>> {
        self.pers
            .borrow()
            .get(&(Arc::as_ptr(pps) as usize))
            .map(|entry| entry.ps.clone())
    }

    /// Record the shared internalization of `pps`.
    pub(crate) fn insert_pers_struct(&self, pps: Arc<PortablePersStruct>, ps: Arc<PersStruct>) {
        self.shared_signatures
            .borrow_mut()
            .insert(Arc::as_ptr(&ps.ps_sig) as usize);
        self.pers
            .borrow_mut()
            .insert(Arc::as_ptr(&pps) as usize, PersEntry { _owner: pps, ps });
    }

    /// Whether `sig` is retained by this store, so references into its items
    /// stay valid for the store's lifetime.
    pub(crate) fn owns_signature(&self, sig: &Arc<Signature>) -> bool {
        self.shared_signatures
            .borrow()
            .contains(&(Arc::as_ptr(sig) as usize))
    }

    /// Shared handle for a declaration that lives inside a store-owned
    /// signature (`owns_signature` must hold for its root). Equal in content to
    /// `Arc::new(decl.clone())`; allocated once per store.
    pub(crate) fn shared_type_decl(&self, decl: &TypeDeclaration) -> Arc<TypeDeclaration> {
        let key = decl as *const TypeDeclaration as usize;
        if let Some(shared) = self.type_decl_arcs.borrow().get(&key) {
            return shared.clone();
        }
        let shared = Arc::new(decl.clone());
        self.type_decl_arcs.borrow_mut().insert(key, shared.clone());
        shared
    }

    /// Registrations for `sig` under `module_path`, built once per store.
    pub(crate) fn sig_type_registrations(
        &self,
        sig: &Signature,
        module_path: &Path,
        build: impl FnOnce() -> Vec<SigTypeRegistration>,
    ) -> Arc<SigTypeBatch> {
        let key = (sig.as_ptr() as usize, module_path.clone());
        if let Some(found) = self.sig_type_registrations.borrow().get(&key) {
            return found.clone();
        }
        let built = Arc::new(SigTypeBatch {
            entries: build().into_boxed_slice(),
            exact_index: std::sync::OnceLock::new(),
        });
        self.sig_type_registrations
            .borrow_mut()
            .insert(key, built.clone());
        built
    }

    /// Name index of a store-owned signature (`owns_signature` must hold),
    /// built once per store.
    pub(crate) fn signature_index(
        &self,
        sig: &Arc<Signature>,
    ) -> Arc<crate::types::env_lazy::SignatureIndex> {
        let key = Arc::as_ptr(sig) as usize;
        if let Some(found) = self.signature_indexes.borrow().get(&key) {
            return found.clone();
        }
        let built = Arc::new(crate::types::env_lazy::SignatureIndex::build(sig));
        self.signature_indexes
            .borrow_mut()
            .insert(key, built.clone());
        built
    }

    pub(crate) fn shared_components(
        &self,
        key: &crate::types::context::QualifiedModuleComponentsCacheKey,
    ) -> Option<(
        Arc<crate::types::env_lazy::QualifiedModuleComponents>,
        Arc<crate::types::context::StorePiece>,
    )> {
        self.shared_components.borrow().get(key).cloned()
    }

    pub(crate) fn publish_shared_components(
        &self,
        key: crate::types::context::QualifiedModuleComponentsCacheKey,
        components: Arc<crate::types::env_lazy::QualifiedModuleComponents>,
        piece: Arc<crate::types::context::StorePiece>,
    ) {
        self.shared_components
            .borrow_mut()
            .entry(key)
            .or_insert((components, piece));
    }

    pub(crate) fn cached_record_labels(&self, record_path: &Path) -> Option<SharedRecordLabels> {
        self.record_labels.borrow().get(record_path).cloned()
    }

    pub(crate) fn publish_record_labels(&self, record_path: Path, labels: SharedRecordLabels) {
        self.record_labels
            .borrow_mut()
            .entry(record_path)
            .or_insert(labels);
    }

    pub(crate) fn cached_initial_env(
        &self,
    ) -> Option<(
        crate::types::env::Env,
        Arc<crate::types::context::StorePiece>,
    )> {
        self.initial_env.borrow().clone()
    }

    pub(crate) fn publish_initial_env(
        &self,
        env: crate::types::env::Env,
        piece: Arc<crate::types::context::StorePiece>,
    ) {
        self.initial_env.borrow_mut().get_or_insert((env, piece));
    }

    /// Intern a longident component name for a store node. Names live in
    /// the process-wide pool, so every compilation resolves them without
    /// copying the table into each exported signature.
    pub(crate) fn intern_longident_name(&self, name: &str) -> StrIdx {
        self.shared_pool().intern_longident_name(name)
    }

    #[inline]
    pub(crate) fn node(&self, r: TypeExprRef) -> &TypeExpr {
        self.types.get_at(r.store_index())
    }

    pub(crate) fn type_count(&self) -> usize {
        self.types.len()
    }

    pub(crate) fn alloc_type(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        let id = self.next_type_id.get();
        self.next_type_id
            .set(id.checked_add(1).expect("thread store type id exhausted"));
        TypeExprRef::from_store_index(self.types.push_raw(TypeExpr::new(desc, level, id)))
    }

    /// Write the descriptor of a store node that is still being built by the
    /// current compilation (see `TypeContext::build_in_store`).
    pub(crate) fn set_desc_backing(&self, r: TypeExprRef, desc: TypeDesc) {
        self.node(r).set_desc(desc);
    }

    /// Write the level of a store node that is still being built.
    pub(crate) fn set_level_backing(&self, r: TypeExprRef, level: i32) {
        self.node(r).set_level(level);
    }

    pub(crate) fn row_field_count(&self) -> usize {
        self.row_fields.borrow().len()
    }

    /// Write a store row-field cell that is still being built.
    pub(crate) fn set_row_field_backing(&self, rf: RowFieldRef, field: Option<RowField>) {
        self.row_fields.borrow_mut()[rf.store_index()] = field;
    }

    /// Apply `f` to a store memo cell without copying it.
    pub(crate) fn with_abbrev<R>(
        &self,
        memo: AbbrevMemoRef,
        f: impl FnOnce(&AbbrevMemo) -> R,
    ) -> R {
        match self.abbrevs.borrow().get(memo.store_index()) {
            Some(value) => f(value),
            None => f(&AbbrevMemo::Mnil),
        }
    }

    pub(crate) fn abbrev(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        self.abbrevs
            .borrow()
            .get(memo.store_index())
            .cloned()
            .unwrap_or(AbbrevMemo::Mnil)
    }

    pub(crate) fn alloc_abbrev(&self, memo: AbbrevMemo) -> AbbrevMemoRef {
        let mut abbrevs = self.abbrevs.borrow_mut();
        let idx = abbrevs.len();
        abbrevs.push(memo);
        AbbrevMemoRef::from_store_index(idx)
    }

    pub(crate) fn row_field(&self, rf: RowFieldRef) -> Option<RowField> {
        self.row_fields
            .borrow()
            .get(rf.store_index())
            .cloned()
            .flatten()
    }

    pub(crate) fn alloc_row_field(&self, field: Option<RowField>) -> RowFieldRef {
        let mut row_fields = self.row_fields.borrow_mut();
        let idx = row_fields.len();
        row_fields.push(field);
        RowFieldRef::from_store_index(idx)
    }

    pub(crate) fn with_variant_layout<R>(
        &self,
        layout_ref: LayoutRef,
        read: impl FnOnce(&Layout) -> R,
    ) -> R {
        let layouts = self.variant_layouts.borrow();
        let Some(layout) = layouts.get(layout_ref.store_index()) else {
            panic!("variant layout reference belongs to another thread store")
        };
        read(layout)
    }

    pub(crate) fn alloc_complete_variant_layout(&self, layout: Layout) -> LayoutRef {
        let mut layouts = self.variant_layouts.borrow_mut();
        let idx = layouts.len();
        layouts.push(layout);
        LayoutRef::from_store_index(idx)
    }
}

thread_local! {
    /// Depth of `TypeContext::build_in_store` on this thread, so lazily built
    /// structures can record at construction whether they are store-resident.
    static STORE_BUILD_ACTIVE: Cell<u32> = const { Cell::new(0) };
}

pub(crate) fn store_build_active() -> bool {
    STORE_BUILD_ACTIVE.with(|depth| depth.get() != 0)
}

pub(crate) fn set_store_build_depth(depth: u32) {
    STORE_BUILD_ACTIVE.with(|active| active.set(depth));
}

thread_local! {
    static THREAD_TYPE_STORE: RefCell<Option<Box<ThreadTypeStore>>> = const { RefCell::new(None) };
}

/// Exclusive ownership during a compilation. Nested contexts get a separate
/// store, so level marking cannot leak into another live compilation. Returning
/// the store to the worker slot avoids reference counting and arena teardown.
pub(crate) struct StoreLease(Option<Box<ThreadTypeStore>>);

impl Deref for StoreLease {
    type Target = ThreadTypeStore;

    fn deref(&self) -> &ThreadTypeStore {
        self.0.as_deref().expect("live store lease")
    }
}

impl Drop for StoreLease {
    fn drop(&mut self) {
        // A panic may leave a mark traversal unfinished. Do not reuse its graph.
        if !std::thread::panicking() {
            let store = self.0.take();
            // TLS may already be gone during thread shutdown.
            let _returned = THREAD_TYPE_STORE.try_with(|slot| slot.replace(store));
        }
    }
}

/// `RESCRIPT_FRESH_STORE=1` gives every compilation an empty store, so the
/// store caches nothing across compilations: a build's output must not change
/// with it (checks that store builds are independent of compilation state).
fn fresh_store_per_compilation() -> bool {
    static FRESH: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FRESH.get_or_init(|| std::env::var_os("RESCRIPT_FRESH_STORE").is_some())
}

pub(crate) fn current() -> StoreLease {
    let generation = BUILD_GENERATION.load(Ordering::SeqCst);
    let fresh = fresh_store_per_compilation();
    StoreLease(Some(THREAD_TYPE_STORE.with(
        |slot| match slot.borrow_mut().take() {
            Some(store) if store.generation == generation && !fresh => store,
            _ => Box::new(ThreadTypeStore::new()),
        },
    )))
}

const OVERLAY_PAGE: usize = 256;

/// Sparse, page-allocated map from store cell index to this compilation's
/// value for that cell. Reads are two indexed loads; pages are allocated on
/// first write, so a compilation that touches a handful of dependency memos
/// pays for a handful of pages, not for the whole store.
#[derive(Clone, Debug)]
pub(crate) struct PagedOverlay<T> {
    pages: Vec<Option<Box<[Option<T>]>>>,
}

impl<T: Clone> PagedOverlay<T> {
    pub(crate) fn new() -> Self {
        PagedOverlay { pages: Vec::new() }
    }

    #[inline]
    pub(crate) fn get(&self, idx: usize) -> Option<&T> {
        self.pages
            .get(idx / OVERLAY_PAGE)?
            .as_deref()?
            .get(idx % OVERLAY_PAGE)?
            .as_ref()
    }

    pub(crate) fn set(&mut self, idx: usize, value: T) {
        let page = idx / OVERLAY_PAGE;
        if page >= self.pages.len() {
            self.pages.resize_with(page + 1, || None);
        }
        let slot =
            self.pages[page].get_or_insert_with(|| vec![None; OVERLAY_PAGE].into_boxed_slice());
        slot[idx % OVERLAY_PAGE] = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::type_expr::GENERIC_LEVEL;

    #[test]
    fn overlay_pages_and_clones_are_independent() {
        let mut overlay = PagedOverlay::new();
        for index in [0, 255, 256, 4096] {
            assert_eq!(overlay.get(index), None);
            overlay.set(index, Some(index));
        }
        let snapshot = overlay.clone();
        overlay.set(255, None);
        assert_eq!(overlay.get(255), Some(&None));
        assert_eq!(snapshot.get(255), Some(&Some(255)));
        assert_eq!(overlay.get(257), None);
        assert!(overlay.pages[2].is_none());
    }

    #[test]
    fn store_lease_is_exclusive_and_reused() {
        // Isolate the worker slot from other unit tests on the harness thread.
        std::thread::spawn(|| {
            let outer = current();
            let outer_ty = outer.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
            let nested = current();
            assert_eq!(nested.type_count(), 0);
            nested.alloc_type(
                TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                GENERIC_LEVEL,
            );
            assert!(matches!(*outer.node(outer_ty).desc(), TypeDesc::Tnil));
            drop(nested);
            drop(outer);
            let reused = current();
            assert_eq!(reused.type_count(), 1);
            assert!(matches!(*reused.node(outer_ty).desc(), TypeDesc::Tnil));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn new_build_generation_discards_the_worker_store() {
        std::thread::spawn(|| {
            let lease = current();
            lease.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
            drop(lease);
            assert_eq!(current().type_count(), 1);
            begin_build();
            assert_eq!(current().type_count(), 0);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn panicking_compilation_does_not_recycle_store() {
        std::thread::spawn(|| {
            let result = std::panic::catch_unwind(|| {
                let lease = current();
                lease.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
                panic!("unfinished traversal");
            });
            assert!(result.is_err());
            assert_eq!(current().type_count(), 0);
        })
        .join()
        .unwrap();
    }
}
