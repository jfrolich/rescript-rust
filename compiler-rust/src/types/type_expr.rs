//! Core type expressions for the type system.
//!
//! This module defines `TypeExpr` and `TypeDesc`, the fundamental types
//! for representing types in the ReScript type checker.
//!
//! # Memory Model
//!
//! Type expressions are allocated in a `TypeArena` owned by the `TypeContext`.
//! They use interior mutability (`RefCell`) for the unification algorithm,
//! which requires mutating the `desc` field to create `Tlink` chains.
//!
//! # Concurrency
//!
//! Type expressions are NOT thread-safe - they use `RefCell` for interior
//! mutability. However, this is fine because:
//! - Each compilation gets its own `TypeContext`
//! - Parallelism happens at the file level, not within type checking
//!
//! # Level-based Generalization
//!
//! Each type has a `level` that tracks its binding depth:
//! - `generic_level` (100000000): Fully polymorphic type variables
//! - Other levels: Track when the type was introduced
//! - Variables with level > current_level can be generalized

use super::asttypes::{ArgLabel, Label, PrivateFlag};
use super::path::Path;
use crate::parser::longident::Longident;
use serde::{Deserialize, Serialize};
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};

/// The generic level for fully polymorphic types.
pub const GENERIC_LEVEL: i32 = 100_000_000;

/// The lowest level (used for marking during traversal).
pub const LOWEST_LEVEL: i32 = 0;

/// Pivot level for traversal marking.
pub const PIVOT_LEVEL: i32 = (2 * LOWEST_LEVEL) - 1;

/// A type expression.
///
/// This is the core type representation used throughout the type checker.
/// It uses interior mutability for the unification algorithm.
///
/// # Fields
///
/// - `desc`: The type descriptor (what kind of type this is)
/// - `level`: The binding level for generalization
/// - `id`: A unique identifier for this type expression
#[derive(Debug)]
pub struct TypeExpr {
    /// The type descriptor. Uses `RefCell` for unification.
    desc: RefCell<TypeDesc>,
    /// The binding level. Uses `Cell` for generalization.
    level: Cell<i32>,
    /// Unique identifier for this type expression.
    id: i32,
}

impl TypeExpr {
    /// Create a new type expression.
    pub fn new(desc: TypeDesc, level: i32, id: i32) -> Self {
        TypeExpr {
            desc: RefCell::new(desc),
            level: Cell::new(level),
            id,
        }
    }

    /// Get the type descriptor.
    ///
    /// # Panics
    ///
    /// Panics if the descriptor is currently borrowed mutably.
    pub fn desc(&self) -> std::cell::Ref<'_, TypeDesc> {
        self.desc.borrow()
    }

    /// Get a mutable reference to the type descriptor.
    ///
    /// # Panics
    ///
    /// Panics if the descriptor is currently borrowed.
    pub fn desc_mut(&self) -> std::cell::RefMut<'_, TypeDesc> {
        self.desc.borrow_mut()
    }

    /// Set the type descriptor.
    pub fn set_desc(&self, desc: TypeDesc) {
        *self.desc.borrow_mut() = desc;
    }

    /// Get the binding level.
    pub fn level(&self) -> i32 {
        self.level.get()
    }

    /// Set the binding level.
    pub fn set_level(&self, level: i32) {
        self.level.set(level);
    }

    /// Get the unique ID.
    pub fn id(&self) -> i32 {
        self.id
    }

    /// Check if this type is at the generic level.
    pub fn is_generic(&self) -> bool {
        self.level.get() == GENERIC_LEVEL
    }

    /// Check if this is a type variable.
    pub fn is_var(&self) -> bool {
        matches!(*self.desc.borrow(), TypeDesc::Tvar(_))
    }

    /// Check if this is a universal type variable.
    pub fn is_univar(&self) -> bool {
        matches!(*self.desc.borrow(), TypeDesc::Tunivar(_))
    }

    /// Check if this is a type constructor application.
    pub fn is_constr(&self) -> bool {
        matches!(*self.desc.borrow(), TypeDesc::Tconstr { .. })
    }
}

impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        // Two type expressions are equal if they have the same id
        self.id == other.id
    }
}

impl Eq for TypeExpr {}

impl Hash for TypeExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Ord for TypeExpr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl PartialOrd for TypeExpr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Number of type references a `TypeRefList` stores without allocating.
const TYPE_REF_LIST_INLINE: usize = 3;

/// Immutable list of type references in a type descriptor (constructor and
/// package arguments, tuple components, polymorphic variables).
///
/// Intentional Rust performance representation of the OCaml `type_expr list`
/// fields in `compiler/ml/types.ml:24-50`. Type-checking code snapshots
/// descriptors constantly (`TypeContext::get_desc`); short lists are stored
/// inline and longer ones share one allocation, so snapshots never allocate.
/// Element order and physical identities are unchanged.
#[derive(Clone)]
pub enum TypeRefList {
    Inline {
        len: u8,
        items: [TypeExprRef; TYPE_REF_LIST_INLINE],
    },
    Shared(std::sync::Arc<[TypeExprRef]>),
}

impl TypeRefList {
    pub const fn new() -> Self {
        TypeRefList::Inline {
            len: 0,
            items: [TypeExprRef(0); TYPE_REF_LIST_INLINE],
        }
    }

    pub fn from_slice(items: &[TypeExprRef]) -> Self {
        if items.len() <= TYPE_REF_LIST_INLINE {
            let mut inline = [TypeExprRef(0); TYPE_REF_LIST_INLINE];
            inline[..items.len()].copy_from_slice(items);
            TypeRefList::Inline {
                len: items.len() as u8,
                items: inline,
            }
        } else {
            TypeRefList::Shared(std::sync::Arc::from(items))
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[TypeExprRef] {
        match self {
            TypeRefList::Inline { len, items } => &items[..*len as usize],
            TypeRefList::Shared(items) => items,
        }
    }
}

impl Default for TypeRefList {
    fn default() -> Self {
        Self::new()
    }
}

impl std::ops::Deref for TypeRefList {
    type Target = [TypeExprRef];

    #[inline]
    fn deref(&self) -> &[TypeExprRef] {
        self.as_slice()
    }
}

impl std::fmt::Debug for TypeRefList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.as_slice()).finish()
    }
}

impl PartialEq for TypeRefList {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for TypeRefList {}

impl<const N: usize> PartialEq<[TypeExprRef; N]> for TypeRefList {
    fn eq(&self, other: &[TypeExprRef; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<Vec<TypeExprRef>> for TypeRefList {
    fn eq(&self, other: &Vec<TypeExprRef>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl From<Vec<TypeExprRef>> for TypeRefList {
    fn from(items: Vec<TypeExprRef>) -> Self {
        if items.len() <= TYPE_REF_LIST_INLINE {
            Self::from_slice(&items)
        } else {
            TypeRefList::Shared(std::sync::Arc::from(items))
        }
    }
}

impl From<&[TypeExprRef]> for TypeRefList {
    fn from(items: &[TypeExprRef]) -> Self {
        Self::from_slice(items)
    }
}

impl<const N: usize> From<[TypeExprRef; N]> for TypeRefList {
    fn from(items: [TypeExprRef; N]) -> Self {
        Self::from_slice(&items)
    }
}

impl FromIterator<TypeExprRef> for TypeRefList {
    fn from_iter<I: IntoIterator<Item = TypeExprRef>>(iter: I) -> Self {
        let items: smallvec::SmallVec<[TypeExprRef; 8]> = iter.into_iter().collect();
        Self::from_slice(&items)
    }
}

impl<'a> IntoIterator for &'a TypeRefList {
    type Item = &'a TypeExprRef;
    type IntoIter = std::slice::Iter<'a, TypeExprRef>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl IntoIterator for TypeRefList {
    type Item = TypeExprRef;
    type IntoIter = smallvec::IntoIter<[TypeExprRef; 8]>;

    fn into_iter(self) -> Self::IntoIter {
        smallvec::SmallVec::<[TypeExprRef; 8]>::from_slice(self.as_slice()).into_iter()
    }
}

/// Immutable list of arrow parameters (see `TypeRefList`): cloning a
/// descriptor shares it instead of copying parameters and their labels.
#[derive(Clone)]
pub struct TypeArgList(std::sync::Arc<[TypeArg]>);

impl TypeArgList {
    #[inline]
    pub fn as_slice(&self) -> &[TypeArg] {
        &self.0
    }
}

impl Default for TypeArgList {
    fn default() -> Self {
        TypeArgList(std::sync::Arc::from(Vec::new()))
    }
}

impl std::ops::Deref for TypeArgList {
    type Target = [TypeArg];

    #[inline]
    fn deref(&self) -> &[TypeArg] {
        &self.0
    }
}

impl std::fmt::Debug for TypeArgList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl From<Vec<TypeArg>> for TypeArgList {
    fn from(items: Vec<TypeArg>) -> Self {
        TypeArgList(std::sync::Arc::from(items))
    }
}

impl From<&[TypeArg]> for TypeArgList {
    fn from(items: &[TypeArg]) -> Self {
        TypeArgList(std::sync::Arc::from(items))
    }
}

impl FromIterator<TypeArg> for TypeArgList {
    fn from_iter<I: IntoIterator<Item = TypeArg>>(iter: I) -> Self {
        TypeArgList(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a TypeArgList {
    type Item = &'a TypeArg;
    type IntoIter = std::slice::Iter<'a, TypeArg>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl IntoIterator for TypeArgList {
    type Item = TypeArg;
    type IntoIter = std::vec::IntoIter<TypeArg>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.to_vec().into_iter()
    }
}

/// Type descriptor - the actual content of a type expression.
#[derive(Debug, Clone)]
pub enum TypeDesc {
    /// Type variable: `'a` or `'_a`
    Tvar(Option<String>),

    /// N-ary arrow (function) type: `(arg1, ..., argN) -> ret`.
    ///
    /// Mirrors `compiler/ml/types.ml`, where `Tarrow` stores the complete
    /// parameter list in one node rather than a chain of unary arrows.
    Tarrow {
        /// Arguments in source order.
        args: TypeArgList,
        /// The return type.
        ret: TypeExprRef,
    },

    /// Tuple type: `(t1, t2, ...)`
    Ttuple(TypeRefList),

    /// Type constructor: `int`, `list<'a>`, etc.
    Tconstr {
        /// The path to the type constructor
        path: Path,
        /// Type arguments
        args: TypeRefList,
        /// Abbreviation memo (for expansion caching)
        abbrev: AbbrevMemoRef,
    },

    /// Object type: `{"f1": t1, ..., "fn": tn}` (types.ml `Tobject`). The
    /// fields are a linked list of `Tfield`/`Tnil`, terminated by a row
    /// variable when the row is open.
    Tobject {
        /// Fields as a linked list of Tfield/Tnil
        fields: TypeExprRef,
    },

    /// Object field (types.ml `Tfield {name; mutability; typ; rest}`).
    Tfield {
        /// Field name
        name: String,
        /// The field's shared mutability cell; read its semantic value with
        /// `TypeContext::mutability_repr`.
        mutability: MutabilityRef,
        /// Field type
        typ: TypeExprRef,
        /// Rest of the fields
        rest: TypeExprRef,
    },

    /// End of object fields
    Tnil,

    /// Link to another type (used during unification)
    Tlink(TypeExprRef),

    /// Substitution marker (used during copying)
    Tsubst(TypeExprRef),

    /// Polymorphic variant type
    Tvariant(Box<RowDesc>),

    /// Universal type variable (from forall quantifier)
    Tunivar(Option<String>),

    /// Polymorphic type: `'a1 ... 'an. ty`
    Tpoly {
        /// The body type
        body: TypeExprRef,
        /// Bound type variables
        vars: TypeRefList,
    },

    /// First-class module type (package)
    Tpackage {
        /// Module type path
        path: Path,
        /// Longidents for package constraints
        lids: Box<Vec<Longident>>,
        /// Type arguments
        args: TypeRefList,
    },
}

/// Top bit distinguishes worker-store indices from compilation-local indices.
pub(crate) const STORE_REF_TAG: u32 = 1 << 31;

/// Second bit (only with `STORE_REF_TAG`) selects the process-wide shared
/// pool of immutable dependency graphs (`types::shared_store`) instead of the
/// worker store. Shared references are also `is_store()`: every non-local
/// cell is read-only outside a store build and written through overlays.
pub(crate) const SHARED_REF_TAG: u32 = 1 << 30;
const SHARED_REF_BITS: u32 = STORE_REF_TAG | SHARED_REF_TAG;

/// Compact physical identity for a type node, matching OCaml `type_expr`
/// identity (`compiler/ml/types.ml:22`, `compiler/ml/btype.ml:46-48`).
/// The top bit selects the worker store; remaining bits index its arena or
/// the compilation-local arena. No structural equality or deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeExprRef(pub u32);

impl TypeExprRef {
    /// Create a null reference (for placeholder purposes).
    pub fn null() -> Self {
        TypeExprRef(0)
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("type arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local type arena index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th node of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("type store index exceeds u32::MAX");
        assert!(
            raw & SHARED_REF_BITS == 0,
            "type store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Reference to the `idx`-th node of the process-wide shared pool.
    #[inline]
    pub(crate) fn from_shared_index(idx: u32) -> Self {
        assert!(
            idx & SHARED_REF_BITS == 0,
            "shared type index exceeds the tag range"
        );
        Self(idx | SHARED_REF_BITS)
    }

    /// Whether this node lives outside the compilation (worker store or
    /// shared pool).
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    /// Whether this node lives in the process-wide shared pool.
    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.0 & SHARED_REF_BITS == SHARED_REF_BITS
    }

    /// Index into the shared pool.
    #[inline]
    pub(crate) fn shared_index(self) -> u32 {
        debug_assert!(self.is_shared(), "non-shared type reference used as a shared index");
        self.0 & !SHARED_REF_BITS
    }

    /// Index into the compilation-local arena.
    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(
            !self.is_store(),
            "store type reference used as a local index"
        );
        self.0 as usize
    }

    /// Index into the per-thread store arena.
    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(
            self.is_store() && !self.is_shared(),
            "local or shared type reference used as a store index"
        );
        (self.0 & !STORE_REF_TAG) as usize
    }

    /// Identity key for visited sets and side tables: unique across the local
    /// arena and the store, never an arena position.
    #[inline]
    pub(crate) fn key(self) -> usize {
        self.0 as usize
    }
}

/// Intentional Rust performance representation for short-lived type-node maps.
///
/// This preserves physical-identity semantics: the key is still the exact
/// `TypeExprRef`, matching the OCaml compiler's type-node identity model. The
/// reference node shape is compiler/ml/types.ml:22 and allocation path is
/// compiler/ml/btype.ml:46-48. The storage avoids hashing for short-lived
/// copy/substitution caches.
const TYPE_EXPR_MAP_INLINE_CAPACITY: usize = 8;
const TYPE_EXPR_MAP_DENSE_RATIO: usize = 8;
const TYPE_EXPR_MAP_MIN_SPARSE_SPAN: usize = 256;

#[derive(Debug, Clone)]
enum TypeExprRefMapStorage<T> {
    Inline {
        entries: [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
    },
    Dense {
        offset: u32,
        values: Vec<Option<T>>,
    },
    Sparse(crate::fast_hash::AHashMap<TypeExprRef, T>),
}

/// Identity-exact hybrid storage for short-lived type-copy maps.
///
/// Most record-label copies touch only a handful of far-apart arena handles,
/// while signature freshening touches hundreds of mostly dense handles. Keep
/// the common tiny case inline, then select dense or sparse storage from the
/// observed handle span. A later outlier can demote dense storage to sparse;
/// sufficiently dense sparse storage can promote once to direct indexing.
#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefMap<T> {
    storage: TypeExprRefMapStorage<T>,
    entry_count: usize,
    min_key: Option<u32>,
    max_key: u32,
}

impl<T> TypeExprRefMap<T> {
    fn empty_inline() -> TypeExprRefMapStorage<T> {
        TypeExprRefMapStorage::Inline {
            entries: std::array::from_fn(|_| None),
            len: 0,
        }
    }

    pub(crate) fn new() -> Self {
        Self {
            storage: Self::empty_inline(),
            entry_count: 0,
            min_key: None,
            max_key: 0,
        }
    }

    #[inline]
    fn span(&self) -> usize {
        self.min_key
            .map_or(0, |min| ((self.max_key - min) as usize).saturating_add(1))
    }

    #[inline]
    fn record_new_key(&mut self, key: TypeExprRef) {
        match self.min_key {
            None => {
                self.min_key = Some(key.0);
                self.max_key = key.0;
            }
            Some(min) => {
                if key.0 < min {
                    self.min_key = Some(key.0);
                }
                self.max_key = self.max_key.max(key.0);
            }
        }
        self.entry_count += 1;
    }

    #[inline]
    pub(crate) fn get(&self, key: TypeExprRef) -> Option<&T> {
        match &self.storage {
            TypeExprRefMapStorage::Inline { entries, len } => {
                for entry in &entries[..*len] {
                    if let Some((stored, value)) = entry
                        && *stored == key
                    {
                        return Some(value);
                    }
                }
                None
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                let idx = key.0.checked_sub(*offset)? as usize;
                values.get(idx)?.as_ref()
            }
            TypeExprRefMapStorage::Sparse(values) => values.get(&key),
        }
    }

    fn dense_from_inline(
        entries: &mut [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
        min: u32,
        span: usize,
        key: TypeExprRef,
        value: T,
    ) -> TypeExprRefMapStorage<T> {
        let mut values = Vec::with_capacity(span);
        values.resize_with(span, || None);
        for entry in entries.iter_mut().take(len) {
            let (stored, stored_value) = entry.take().expect("occupied inline type-map slot");
            values[(stored.0 - min) as usize] = Some(stored_value);
        }
        values[(key.0 - min) as usize] = Some(value);
        TypeExprRefMapStorage::Dense {
            offset: min,
            values,
        }
    }

    fn sparse_from_inline(
        entries: &mut [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
        key: TypeExprRef,
        value: T,
    ) -> TypeExprRefMapStorage<T> {
        let mut values = crate::fast_hash::AHashMap::with_capacity(len + 1);
        for entry in entries.iter_mut().take(len) {
            let (stored, stored_value) = entry.take().expect("occupied inline type-map slot");
            values.insert(stored, stored_value);
        }
        values.insert(key, value);
        TypeExprRefMapStorage::Sparse(values)
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef, value: T) -> Option<T> {
        match &mut self.storage {
            TypeExprRefMapStorage::Inline { entries, len } => {
                for entry in entries.iter_mut().take(*len) {
                    let (stored, stored_value) =
                        entry.as_mut().expect("occupied inline type-map slot");
                    if *stored == key {
                        return Some(std::mem::replace(stored_value, value));
                    }
                }
                if *len < TYPE_EXPR_MAP_INLINE_CAPACITY {
                    entries[*len] = Some((key, value));
                    *len += 1;
                    self.record_new_key(key);
                    return None;
                }
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                if let Some(idx) = key.0.checked_sub(*offset).map(|idx| idx as usize)
                    && let Some(slot) = values.get_mut(idx)
                    && slot.is_some()
                {
                    return slot.replace(value);
                }
            }
            TypeExprRefMapStorage::Sparse(values) => {
                if let Some(stored) = values.get_mut(&key) {
                    return Some(std::mem::replace(stored, value));
                }
            }
        }

        self.record_new_key(key);
        let span = self.span();
        let entry_count = self.entry_count;

        match &mut self.storage {
            TypeExprRefMapStorage::Inline { .. } => {
                let mut old = std::mem::replace(&mut self.storage, Self::empty_inline());
                let TypeExprRefMapStorage::Inline { entries, len } = &mut old else {
                    unreachable!();
                };
                let min = self.min_key.expect("nonempty type-map bounds");
                if span <= entry_count.saturating_mul(TYPE_EXPR_MAP_DENSE_RATIO) {
                    self.storage = Self::dense_from_inline(entries, *len, min, span, key, value);
                } else {
                    self.storage = Self::sparse_from_inline(entries, *len, key, value);
                }
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                if span > TYPE_EXPR_MAP_MIN_SPARSE_SPAN
                    && span > entry_count.saturating_mul(TYPE_EXPR_MAP_DENSE_RATIO)
                {
                    let mut sparse = crate::fast_hash::AHashMap::with_capacity(entry_count);
                    for (idx, slot) in values.iter_mut().enumerate() {
                        if let Some(stored_value) = slot.take() {
                            sparse.insert(TypeExprRef(*offset + idx as u32), stored_value);
                        }
                    }
                    sparse.insert(key, value);
                    self.storage = TypeExprRefMapStorage::Sparse(sparse);
                } else {
                    let min = self.min_key.expect("nonempty type-map bounds");
                    if min < *offset {
                        let prepend = (*offset - min) as usize;
                        let mut copied = Vec::with_capacity(values.len() + prepend);
                        copied.resize_with(prepend, || None);
                        copied.append(values);
                        *values = copied;
                        *offset = min;
                    }
                    let idx = (key.0 - *offset) as usize;
                    if idx >= values.len() {
                        values.resize_with(idx + 1, || None);
                    }
                    values[idx] = Some(value);
                }
            }
            TypeExprRefMapStorage::Sparse(values) => {
                values.insert(key, value);
                if entry_count >= 32 && span <= entry_count.saturating_mul(4) {
                    let min = self.min_key.expect("nonempty type-map bounds");
                    let mut dense = Vec::with_capacity(span);
                    dense.resize_with(span, || None);
                    for (stored, stored_value) in values.drain() {
                        dense[(stored.0 - min) as usize] = Some(stored_value);
                    }
                    self.storage = TypeExprRefMapStorage::Dense {
                        offset: min,
                        values: dense,
                    };
                }
            }
        }
        None
    }
}

impl<T> Default for TypeExprRefMap<T> {
    fn default() -> Self {
        Self::new()
    }
}


/// Number of keys a `TypeExprRefSet` holds inline before it spills to a
/// hash set.
const TYPE_EXPR_SET_INLINE: usize = 16;

/// Multiplicative hash for `TypeExprRef` keys (arena indices).
#[derive(Default, Clone, Copy)]
struct TypeKeyHasher(u64);

impl Hasher for TypeKeyHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(b)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
    }

    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.0 = u64::from(n).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

type TypeKeySet = std::collections::HashSet<u32, std::hash::BuildHasherDefault<TypeKeyHasher>>;

#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefSet {
    /// Most traversals visit only a few nodes; keep those keys inline so the
    /// set allocates nothing.
    inline: [u32; TYPE_EXPR_SET_INLINE],
    inline_len: u8,
    /// Keys once the inline storage is full; storage comes from a per-thread
    /// pool so large traversals reuse capacity.
    spilled: Option<TypeKeySet>,
}

thread_local! {
    /// Cleared hash sets of dropped spilled `TypeExprRefSet`s.
    static SPILLED_SET_POOL: std::cell::RefCell<Vec<TypeKeySet>> = const { std::cell::RefCell::new(Vec::new()) };
}

const SPILLED_SET_POOL_MAX: usize = 8;
const SPILLED_SET_POOL_MAX_CAPACITY: usize = 1 << 16;

impl TypeExprRefSet {
    pub(crate) fn new() -> Self {
        Self {
            inline: [0; TYPE_EXPR_SET_INLINE],
            inline_len: 0,
            spilled: None,
        }
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef) -> bool {
        if let Some(spilled) = self.spilled.as_mut() {
            return spilled.insert(key.0);
        }
        let len = self.inline_len as usize;
        if self.inline[..len].contains(&key.0) {
            return false;
        }
        if len < TYPE_EXPR_SET_INLINE {
            self.inline[len] = key.0;
            self.inline_len += 1;
            return true;
        }
        self.spill().insert(key.0)
    }

    #[cold]
    fn spill(&mut self) -> &mut TypeKeySet {
        let mut set = SPILLED_SET_POOL
            .with(|pool| pool.borrow_mut().pop())
            .unwrap_or_default();
        set.extend(self.inline[..self.inline_len as usize].iter().copied());
        self.spilled.insert(set)
    }
}

impl Drop for TypeExprRefSet {
    fn drop(&mut self) {
        if let Some(mut set) = self.spilled.take() {
            if set.capacity() > SPILLED_SET_POOL_MAX_CAPACITY {
                return;
            }
            set.clear();
            SPILLED_SET_POOL.with(|pool| {
                let mut pool = pool.borrow_mut();
                if pool.len() < SPILLED_SET_POOL_MAX {
                    pool.push(set);
                }
            });
        }
    }
}

impl Default for TypeExprRefSet {
    fn default() -> Self {
        Self::new()
    }
}

/// An argument in a function type.
///
/// OCaml types.ml:24 and btype.ml:422-423 preserve labels while mapping types.
/// Keep the common unlabeled case inline; located labels retain owned metadata.
#[derive(Clone)]
pub struct TypeArg {
    label: Option<Box<ArgLabel>>,
    /// The argument type (physical arena identity).
    pub typ: TypeExprRef,
}

impl std::fmt::Debug for TypeArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeArg")
            .field("lbl", self.label())
            .field("typ", &self.typ)
            .finish()
    }
}

impl TypeArg {
    /// Create a new type argument, allocating only for a located label.
    pub fn new(lbl: ArgLabel, typ: TypeExprRef) -> Self {
        let label = match lbl {
            ArgLabel::Nolabel => None,
            label => Some(Box::new(label)),
        };
        Self { label, typ }
    }

    /// Borrow the original label without copying or allocating metadata.
    pub fn label(&self) -> &ArgLabel {
        self.label.as_deref().unwrap_or(&ArgLabel::Nolabel)
    }

    /// Create an unlabeled argument without allocating label storage.
    pub fn unlabeled(typ: TypeExprRef) -> Self {
        Self { label: None, typ }
    }
}

/// Abbreviation memo for type expansion caching.
#[derive(Debug, Clone)]
pub enum AbbrevMemo {
    /// No abbreviation
    Mnil,
    /// Abbreviation: (private_flag, path, abbrev, expansion, next)
    Mcons {
        private_flag: PrivateFlag,
        path: Path,
        abbrev: TypeExprRef,
        expansion: TypeExprRef,
        next: AbbrevMemoRef,
    },
    /// Link to another memo
    Mlink(AbbrevMemoRef),
}

/// Reference to an abbreviation memo.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbbrevMemoRef(pub u32);

impl AbbrevMemoRef {
    /// Create a nil memo reference.
    pub fn nil() -> Self {
        AbbrevMemoRef(0)
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("abbrev memo arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local abbrev memo index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th abbreviation memo cell of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("abbrev memo store index exceeds u32::MAX");
        assert!(
            raw & SHARED_REF_BITS == 0,
            "abbrev memo store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Memo cell of the shared-pool `Tconstr` node with index `idx`; one cell
    /// per node, initially `Mnil` (`compiler/ml/subst.ml:173-177`).
    #[inline]
    pub(crate) fn from_shared_index(idx: u32) -> Self {
        assert!(
            idx & SHARED_REF_BITS == 0,
            "shared abbrev memo index exceeds the tag range"
        );
        Self(idx | SHARED_REF_BITS)
    }

    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.0 & SHARED_REF_BITS == SHARED_REF_BITS
    }

    #[inline]
    pub(crate) fn shared_index(self) -> usize {
        debug_assert!(self.is_shared());
        (self.0 & !SHARED_REF_BITS) as usize
    }

    /// Whether this memo cell belongs to a per-thread store node.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_store(), "store abbrev memo used as a local index");
        self.0 as usize
    }

    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(
            self.is_store() && !self.is_shared(),
            "local or shared abbrev memo used as a store index"
        );
        (self.0 & !STORE_REF_TAG) as usize
    }
}

/// Assignment capability of an object field (types.ml `field_mutability`).
///
/// The semantic value is `Immutable` or `Mutable`; `Link` is an internal edge
/// between cells of the same class, not a third value. Code making a semantic
/// decision must use `TypeContext::mutability_repr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldMutability {
    Value(super::asttypes::MutableFlag),
    Link(MutabilityRef),
}

/// A `field_mutability ref` cell.
///
/// Cells of the compilation's own graph index its cell arena. Cells of
/// dependency graphs (worker store and shared pool) are persistent: they are
/// never written in place, carry a process-unique identity, and encode their
/// initial value (saved graphs only hold `Mutability_value` cells,
/// subst.ml `for_saving`); a compilation's writes to them go to its overlay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MutabilityRef(pub u32);

/// Next persistent cell identity, process-wide.
static NEXT_PERSISTENT_MUTABILITY: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

impl MutabilityRef {
    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("mutability cell index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local mutability cell index collides with the persistent tag"
        );
        Self(raw)
    }

    /// A fresh persistent cell holding `flag`.
    pub(crate) fn new_persistent(flag: super::asttypes::MutableFlag) -> Self {
        let id = NEXT_PERSISTENT_MUTABILITY.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        assert!(id < (1 << 30), "persistent mutability cells exhausted");
        let bit = match flag {
            super::asttypes::MutableFlag::Immutable => 0,
            super::asttypes::MutableFlag::Mutable => 1,
        };
        Self(STORE_REF_TAG | (id << 1) | bit)
    }

    #[inline]
    pub fn is_persistent(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_persistent());
        self.0 as usize
    }

    /// The initial value of a persistent cell.
    #[inline]
    pub(crate) fn persistent_value(self) -> super::asttypes::MutableFlag {
        debug_assert!(self.is_persistent());
        if self.0 & 1 != 0 {
            super::asttypes::MutableFlag::Mutable
        } else {
            super::asttypes::MutableFlag::Immutable
        }
    }
}

/// Row description for polymorphic variants.
#[derive(Debug, Clone)]
pub struct RowDesc {
    /// The variant fields: (label, row_field). Shared copy-on-write, so
    /// snapshots of variant descriptors do not copy the field list.
    pub row_fields: super::decl::SharedVec<(Label, RowField)>,
    /// The row variable
    pub row_more: TypeExprRef,
    /// Is the row closed?
    pub row_closed: bool,
    /// Is the row fixed?
    pub row_fixed: bool,
    /// Optional row name
    pub row_name: Option<(Path, Vec<TypeExprRef>)>,
}

/// Row field for polymorphic variants.
#[derive(Debug, Clone)]
pub enum RowField {
    /// Present variant: Some(type) for valued, None for constant
    Rpresent(Option<TypeExprRef>),
    /// Either variant (during type inference)
    Reither {
        /// Is this a constant constructor?
        constant: bool,
        /// Possible types
        types: Vec<TypeExprRef>,
        /// Is this a pattern match tag?
        matched: bool,
        /// Link to resolved field
        link: RowFieldRef,
    },
    /// Absent variant
    Rabsent,
}

/// Reference to a row field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RowFieldRef(pub u32);

impl RowFieldRef {
    /// Create a null reference.
    pub fn null() -> Self {
        RowFieldRef(u32::MAX)
    }

    /// Check if this is a null reference.
    pub fn is_null(&self) -> bool {
        self.0 == u32::MAX
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("row field arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local row field index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th row field cell of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("row field store index exceeds u32::MAX");
        assert!(
            raw < STORE_REF_TAG - 1,
            "row field store index collides with null sentinel"
        );
        assert!(
            raw & STORE_REF_TAG == 0,
            "row field store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Whether this cell belongs to a per-thread store row. The null
    /// sentinel also has the top bit set and is excluded.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0 && !self.is_null()
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_store(), "store row field used as a local index");
        self.0 as usize
    }

    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(self.is_store(), "local row field used as a store index");
        (self.0 & !STORE_REF_TAG) as usize
    }
}

// ============================================================================
// Serialization support
// ============================================================================

/// Serializable version of TypeDesc for FFI.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeDescSer {
    Tvar(Option<String>),
    Tarrow {
        args: Vec<(ArgLabel, usize)>,
        ret_type: usize,
    },
    Ttuple(Vec<usize>),
    Tconstr {
        path: Path,
        args: Vec<usize>,
    },
    Tlink(usize),
    Tunivar(Option<String>),
    Tpoly {
        body: usize,
        vars: Vec<usize>,
    },
    // Simplified for now
    Other,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_type_node_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<crate::ident::Ident>(), 16);
        assert_eq!(size_of::<Path>(), 24);
        assert!(size_of::<TypeDesc>() <= 72);
        assert!(size_of::<TypeExpr>() <= 88);
    }

    #[test]
    fn store_tags_preserve_identity_and_sentinels() {
        for index in [0, 1, 255, 256, 10_000] {
            let local = TypeExprRef::from_usize(index);
            let store = TypeExprRef::from_store_index(index);
            assert!(!local.is_store());
            assert!(store.is_store());
            assert_eq!(local.index(), index);
            assert_eq!(store.store_index(), index);
            assert_ne!(local, store);
            assert_eq!(AbbrevMemoRef::from_store_index(index).store_index(), index);
            assert_eq!(RowFieldRef::from_store_index(index).store_index(), index);
        }
        assert!(!RowFieldRef::null().is_store());
        assert!(!RowFieldRef::from_store_index(0).is_null());
        assert_ne!(AbbrevMemoRef::nil(), AbbrevMemoRef::from_store_index(0));
        assert_eq!(std::mem::size_of::<TypeExprRef>(), 4);
    }

    #[test]
    #[should_panic(expected = "collides with the store tag")]
    fn local_index_cannot_use_store_bit() {
        TypeExprRef::from_usize(STORE_REF_TAG as usize);
    }

    #[test]
    #[should_panic(expected = "null sentinel")]
    fn store_row_index_cannot_use_null_sentinel() {
        RowFieldRef::from_store_index((STORE_REF_TAG - 1) as usize);
    }

    #[test]
    fn mixed_store_local_maps_and_sets_stay_small() {
        for store_first in [false, true] {
            let mut map = TypeExprRefMap::new();
            let mut set = TypeExprRefSet::new();
            for store in [store_first, !store_first] {
                for index in 0..40 {
                    let key = if store {
                        TypeExprRef::from_store_index(index)
                    } else {
                        TypeExprRef::from_usize(index)
                    };
                    assert!(set.insert(key));
                    assert!(!set.insert(key));
                    assert_eq!(map.insert(key, store), None);
                }
            }
            for index in 0..40 {
                assert_eq!(map.get(TypeExprRef::from_store_index(index)), Some(&true));
                assert_eq!(map.get(TypeExprRef::from_usize(index)), Some(&false));
            }
            assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
            assert_eq!(set.spilled.as_ref().unwrap().len(), 80);
        }
    }

    #[test]
    fn test_type_expr_creation() {
        let ty = TypeExpr::new(TypeDesc::Tvar(Some("a".to_string())), GENERIC_LEVEL, 1);
        assert_eq!(ty.id(), 1);
        assert_eq!(ty.level(), GENERIC_LEVEL);
        assert!(ty.is_generic());
        assert!(ty.is_var());
    }

    #[test]
    fn test_type_expr_mutation() {
        let ty = TypeExpr::new(TypeDesc::Tvar(None), 0, 1);
        ty.set_level(GENERIC_LEVEL);
        assert_eq!(ty.level(), GENERIC_LEVEL);

        ty.set_desc(TypeDesc::Tnil);
        assert!(matches!(*ty.desc(), TypeDesc::Tnil));
    }

    #[test]
    fn test_type_expr_equality() {
        let ty1 = TypeExpr::new(TypeDesc::Tvar(None), 0, 1);
        let ty2 = TypeExpr::new(TypeDesc::Tvar(None), 0, 1);
        let ty3 = TypeExpr::new(TypeDesc::Tvar(None), 0, 2);

        assert_eq!(ty1, ty2); // Same id
        assert_ne!(ty1, ty3); // Different id
    }

    #[test]
    fn test_type_arg() {
        let arg = TypeArg::unlabeled(TypeExprRef(1));
        assert!(matches!(arg.label(), ArgLabel::Nolabel));
        assert_eq!(arg.typ, TypeExprRef(1));
    }

    #[test]
    fn type_arg_hot_cold_ownership_and_metadata() {
        use crate::intern::StrIdx;
        use crate::location::{Location, Position};
        if cfg!(target_pointer_width = "64") {
            assert_eq!(std::mem::size_of::<TypeArg>(), 16);
        }
        let typ = TypeExprRef(u32::MAX);
        for arg in [
            TypeArg::unlabeled(typ),
            TypeArg::new(ArgLabel::Nolabel, typ),
        ] {
            assert!(arg.label.is_none());
            assert!(arg.clone().label.is_none());
            assert!(matches!(arg.label(), ArgLabel::Nolabel));
            assert_eq!(arg.typ, typ);
            assert_eq!(
                format!("{:?}", arg),
                format!("TypeArg {{ lbl: Nolabel, typ: {:?} }}", typ)
            );
        }
        for ghost in [false, true] {
            let loc = Location {
                loc_start: Position::new(StrIdx(17), 3, 21, 24),
                loc_end: Position::new(StrIdx(29), 5, 44, 49),
                loc_ghost: ghost,
            };
            for optional in [false, true] {
                let name = "long_owned_label_with_unicode_λ";
                let label = if optional {
                    ArgLabel::optional(name, loc)
                } else {
                    ArgLabel::labelled(name, loc)
                };
                let expected_debug = format!("TypeArg {{ lbl: {:?}, typ: {:?} }}", label, typ);
                let arg = TypeArg::new(label, typ);
                assert_eq!(format!("{:?}", arg), expected_debug);
                let address = arg.label() as *const ArgLabel;
                let mut moved = arg;
                assert_eq!(moved.label() as *const ArgLabel, address);
                let cloned = moved.clone();
                assert_ne!(cloned.label() as *const ArgLabel, address);
                assert_eq!(cloned.typ, typ);
                let payload = match cloned.label() {
                    ArgLabel::Labelled(l) if !optional => l,
                    ArgLabel::Optional(l) if optional => l,
                    _ => panic!("label kind changed"),
                };
                assert_eq!(payload.txt, name);
                assert_eq!(payload.loc.loc_start.file_name, StrIdx(17));
                assert_eq!(payload.loc.loc_start.line, 3);
                assert_eq!(payload.loc.loc_start.bol, 21);
                assert_eq!(payload.loc.loc_start.cnum, 24);
                assert_eq!(payload.loc.loc_end.file_name, StrIdx(29));
                assert_eq!(payload.loc.loc_end.line, 5);
                assert_eq!(payload.loc.loc_end.bol, 44);
                assert_eq!(payload.loc.loc_end.cnum, 49);
                assert_eq!(payload.loc.loc_ghost, ghost);
                match moved.label.as_deref_mut().unwrap() {
                    ArgLabel::Labelled(l) | ArgLabel::Optional(l) => {
                        assert_ne!(l.txt.as_ptr(), payload.txt.as_ptr());
                        l.txt.push_str("_changed");
                        l.loc.loc_ghost = !ghost;
                    }
                    _ => unreachable!(),
                }
                // Replacement drops the original box; the independent clone survives.
                moved = TypeArg::unlabeled(TypeExprRef(7));
                assert!(moved.label.is_none());
                assert_eq!(cloned.label().label_name(), Some(name));
                drop(moved);
                assert_eq!(format!("{:?}", cloned), expected_debug);
                drop(cloned);
            }
        }
    }

    #[test]
    fn type_expr_ref_map_preserves_replace_and_clone_semantics() {
        let mut map = TypeExprRefMap::new();
        assert_eq!(map.insert(TypeExprRef(42), 1), None);
        assert_eq!(map.insert(TypeExprRef(42), 2), Some(1));
        assert_eq!(map.get(TypeExprRef(42)), Some(&2));

        let cloned = map.clone();
        assert_eq!(cloned.get(TypeExprRef(42)), Some(&2));
        assert_eq!(cloned.entry_count, 1);
    }

    #[test]
    fn type_expr_ref_map_keeps_far_apart_small_maps_sparse() {
        let mut map = TypeExprRefMap::new();
        for index in 0..12 {
            let key = TypeExprRef(index * 10_000);
            assert_eq!(map.insert(key, index), None);
        }
        for index in 0..12 {
            assert_eq!(map.get(TypeExprRef(index * 10_000)), Some(&index));
        }
        assert_eq!(map.entry_count, 12);
        assert_eq!(map.span(), 110_001);
        let TypeExprRefMapStorage::Sparse(values) = &map.storage else {
            panic!("expected sparse storage");
        };
        assert!(values.capacity() < map.span());
    }

    #[test]
    fn type_expr_ref_map_promotes_dense_runs_and_demotes_for_outliers() {
        let mut map = TypeExprRefMap::new();
        for index in 100..140 {
            assert_eq!(map.insert(TypeExprRef(index), index), None);
        }
        assert!(matches!(&map.storage, TypeExprRefMapStorage::Dense { .. }));
        assert_eq!(map.get(TypeExprRef(123)), Some(&123));

        assert_eq!(map.insert(TypeExprRef(100_000), 100_000), None);
        assert_eq!(map.entry_count, 41);
        assert!(matches!(&map.storage, TypeExprRefMapStorage::Sparse(_)));
        assert_eq!(map.get(TypeExprRef(100)), Some(&100));
        assert_eq!(map.get(TypeExprRef(100_000)), Some(&100_000));
    }

    #[test]
    fn type_expr_ref_map_matches_std_map_across_mixed_transitions() {
        let mut map = TypeExprRefMap::new();
        let mut expected = std::collections::HashMap::new();
        let mut state = 0x9e37_79b9_u32;

        for step in 0..5_000_u32 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let key = match step % 4 {
                0 => state % 128,
                1 => 100_000 + state % 256,
                2 => 1_000_000 - state % 512,
                _ => state % 1_000_000,
            };
            let value = state ^ step;
            assert_eq!(
                map.insert(TypeExprRef(key), value),
                expected.insert(key, value)
            );

            let probe = state.rotate_left(11) % 1_000_256;
            assert_eq!(map.get(TypeExprRef(probe)), expected.get(&probe));
            assert_eq!(map.get(TypeExprRef(key)), expected.get(&key));

            if step % 317 == 0 {
                let cloned = map.clone();
                for (&stored, value) in &expected {
                    assert_eq!(cloned.get(TypeExprRef(stored)), Some(value));
                }
            }
        }
        assert_eq!(map.entry_count, expected.len());
    }

    #[test]
    fn type_expr_ref_map_bounds_and_sparse_promotion() {
        let mut map = TypeExprRefMap::new();
        for key in [0, u32::MAX, 1, u32::MAX - 1, 2, 3, 4, 5, 6] {
            assert_eq!(map.insert(TypeExprRef(key), key), None);
            assert_eq!(map.get(TypeExprRef(key)), Some(&key));
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
        assert_eq!(map.get(TypeExprRef(u32::MAX - 2)), None);
        // Reset/reuse is assignment in the current API; there is no clear method.
        map = TypeExprRefMap::default();
        for key in (100..109).rev() {
            map.insert(TypeExprRef(key), key);
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        map.insert(TypeExprRef(99), 99);
        assert_eq!(map.get(TypeExprRef(98)), None);
        assert_eq!(map.get(TypeExprRef(110)), None);
        map.insert(TypeExprRef(300), 300);
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        map.insert(TypeExprRef(400), 400);
        assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
        for key in 99..401 {
            map.insert(TypeExprRef(key), key);
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        let mut cloned = map.clone();
        cloned.insert(TypeExprRef(99), 0);
        for key in 99..401 {
            assert_eq!(map.get(TypeExprRef(key)), Some(&key));
        }
    }

    #[test]
    fn type_expr_ref_map_drops_owned_values_once() {
        struct Owned<'a>(&'a std::cell::Cell<usize>);
        impl Drop for Owned<'_> {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let drops = std::cell::Cell::new(0);
        let mut map = TypeExprRefMap::new();
        for key in 100..140 {
            map.insert(TypeExprRef(key), Owned(&drops));
        }
        map.insert(TypeExprRef(500), Owned(&drops));
        for key in 140..500 {
            map.insert(TypeExprRef(key), Owned(&drops));
        }
        assert_eq!(drops.get(), 0);
        let old = map.insert(TypeExprRef(100), Owned(&drops));
        assert_eq!(drops.get(), 0);
        drop(old);
        assert_eq!(drops.get(), 1);
        drop(map);
        assert_eq!(drops.get(), 402);
    }

    #[test]
    fn type_expr_ref_map_copy_fixture_preserves_cycles_and_identity() {
        use crate::context::IdGenerator;
        use crate::types::{
            TypeContext,
            decl::{ValueDescription, ValueKind},
        };
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let shared = ctx.new_var(None);
        let distinct = ctx.new_var(None);
        let cycle = ctx.new_var(None);
        let mut items = vec![shared, shared, distinct, cycle];
        // Force widely separated physical keys without allocating a huge arena.
        for _ in 0..12 {
            for _ in 0..300 {
                ctx.new_var(None);
            }
            items.push(ctx.new_var(None));
        }
        ctx.set_desc(cycle, TypeDesc::Ttuple(items.clone().into()));
        let value = ValueDescription {
            val_type: cycle,
            val_kind: ValueKind::ValReg,
            val_loc: crate::location::Location::none(),
            val_attributes: vec![],
            val_path: None,
        };
        let copied = crate::types::typecore::copy_lookup_value_description_for_subst(&value, &ctx);
        assert_ne!(copied.val_type, cycle);
        let desc = ctx.get_desc(copied.val_type);
        let TypeDesc::Ttuple(actual) = &*desc else {
            panic!("tuple expected")
        };
        assert_eq!(actual[0], shared);
        assert_eq!(actual[1], shared);
        assert_eq!(actual[2], distinct);
        assert_ne!(actual[0], actual[2]);
        assert_eq!(actual[3], copied.val_type);
        assert_eq!(&actual[4..], &items[4..]);
    }

    #[test]
    fn test_row_desc() {
        let row = RowDesc {
            row_fields: vec![].into(),
            row_more: TypeExprRef(1),
            row_closed: true,
            row_fixed: false,
            row_name: None,
        };
        assert!(row.row_closed);
        assert!(!row.row_fixed);
    }
}
