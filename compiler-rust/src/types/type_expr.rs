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

/// A compact range into the owning `TypeContext`'s append-only arrow-argument
/// storage. The range is meaningful only in that context.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TypeArgRange {
    pub(crate) start: u32,
    pub(crate) len: u32,
}

/// Internal descriptor storage. This mirrors `TypeDesc`, replacing only the
/// arrow argument owner with a compact context-local range. Keeping a flat enum
/// avoids adding an outer discriminant to every type node.
#[derive(Debug, Clone)]
pub(crate) enum StoredTypeDesc {
    Tvar(Option<String>),
    Tarrow {
        args: TypeArgRange,
        ret: TypeExprRef,
    },
    Ttuple(Vec<TypeExprRef>),
    Tconstr {
        path: Path,
        args: Vec<TypeExprRef>,
        abbrev: AbbrevMemoRef,
    },
    Tobject {
        fields: TypeExprRef,
        name: ObjectName,
    },
    Tfield {
        name: String,
        kind: FieldKind,
        typ: TypeExprRef,
        rest: TypeExprRef,
    },
    Tnil,
    Tlink(TypeExprRef),
    Tsubst(TypeExprRef),
    Tvariant(RowDesc),
    Tunivar(Option<String>),
    Tpoly {
        body: TypeExprRef,
        vars: Vec<TypeExprRef>,
    },
    Tpackage {
        path: Path,
        lids: Vec<Longident>,
        args: Vec<TypeExprRef>,
    },
}

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
    desc: RefCell<StoredTypeDesc>,
    /// The binding level. Uses `Cell` for generalization.
    level: Cell<i32>,
    /// Unique identifier for this type expression.
    id: i32,
}

impl TypeExpr {
    /// Create a new type expression.
    pub(crate) fn new(desc: TypeDesc, level: i32, id: i32) -> Self {
        TypeExpr {
            desc: RefCell::new(StoredTypeDesc::from_non_arrow(desc)),
            level: Cell::new(level),
            id,
        }
    }

    pub(crate) fn new_stored(desc: StoredTypeDesc, level: i32, id: i32) -> Self {
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
    pub fn desc(&self) -> TypeDesc {
        self.desc.borrow().to_non_arrow()
    }

    pub(crate) fn stored_desc(&self) -> std::cell::Ref<'_, StoredTypeDesc> {
        self.desc.borrow()
    }

    /// Set a descriptor on a standalone type expression.
    pub fn set_desc(&self, desc: TypeDesc) {
        *self.desc.borrow_mut() = StoredTypeDesc::from_non_arrow(desc);
    }

    pub(crate) fn set_stored_desc(&self, desc: StoredTypeDesc) {
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
        matches!(&*self.desc.borrow(), StoredTypeDesc::Tvar(_))
    }

    /// Check if this is a universal type variable.
    pub fn is_univar(&self) -> bool {
        matches!(&*self.desc.borrow(), StoredTypeDesc::Tunivar(_))
    }

    /// Check if this is a type constructor application.
    pub fn is_constr(&self) -> bool {
        matches!(&*self.desc.borrow(), StoredTypeDesc::Tconstr { .. })
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
        args: Vec<TypeArg>,
        /// The return type.
        ret: TypeExprRef,
    },

    /// Tuple type: `(t1, t2, ...)`
    Ttuple(Vec<TypeExprRef>),

    /// Type constructor: `int`, `list<'a>`, etc.
    Tconstr {
        /// The path to the type constructor
        path: Path,
        /// Type arguments
        args: Vec<TypeExprRef>,
        /// Abbreviation memo (for expansion caching)
        abbrev: AbbrevMemoRef,
    },

    /// Object type: `< method1: t1; method2: t2; ... >`
    Tobject {
        /// Fields as a linked list of Tfield/Tnil
        fields: TypeExprRef,
        /// Optional class path
        name: ObjectName,
    },

    /// Object field: `method: type; rest`
    Tfield {
        /// Field name
        name: String,
        /// Field kind (present, absent, etc.)
        kind: FieldKind,
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
    Tvariant(RowDesc),

    /// Universal type variable (from forall quantifier)
    Tunivar(Option<String>),

    /// Polymorphic type: `'a1 ... 'an. ty`
    Tpoly {
        /// The body type
        body: TypeExprRef,
        /// Bound type variables
        vars: Vec<TypeExprRef>,
    },

    /// First-class module type (package)
    Tpackage {
        /// Module type path
        path: Path,
        /// Longidents for package constraints
        lids: Vec<Longident>,
        /// Type arguments
        args: Vec<TypeExprRef>,
    },
}

impl StoredTypeDesc {
    pub(crate) fn from_non_arrow(desc: TypeDesc) -> Self {
        match desc {
            TypeDesc::Tvar(name) => Self::Tvar(name),
            TypeDesc::Tarrow { .. } => {
                panic!("arrow descriptors require context-owned argument storage")
            }
            TypeDesc::Ttuple(types) => Self::Ttuple(types),
            TypeDesc::Tconstr { path, args, abbrev } => Self::Tconstr { path, args, abbrev },
            TypeDesc::Tobject { fields, name } => Self::Tobject { fields, name },
            TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => Self::Tfield {
                name,
                kind,
                typ,
                rest,
            },
            TypeDesc::Tnil => Self::Tnil,
            TypeDesc::Tlink(ty) => Self::Tlink(ty),
            TypeDesc::Tsubst(ty) => Self::Tsubst(ty),
            TypeDesc::Tvariant(row) => Self::Tvariant(row),
            TypeDesc::Tunivar(name) => Self::Tunivar(name),
            TypeDesc::Tpoly { body, vars } => Self::Tpoly { body, vars },
            TypeDesc::Tpackage { path, lids, args } => Self::Tpackage { path, lids, args },
        }
    }

    pub(crate) fn to_non_arrow(&self) -> TypeDesc {
        match self {
            Self::Tvar(name) => TypeDesc::Tvar(name.clone()),
            Self::Tarrow { .. } => {
                panic!("pooled arrow descriptors require TypeContext::get_desc")
            }
            Self::Ttuple(types) => TypeDesc::Ttuple(types.clone()),
            Self::Tconstr { path, args, abbrev } => TypeDesc::Tconstr {
                path: path.clone(),
                args: args.clone(),
                abbrev: *abbrev,
            },
            Self::Tobject { fields, name } => TypeDesc::Tobject {
                fields: *fields,
                name: name.clone(),
            },
            Self::Tfield {
                name,
                kind,
                typ,
                rest,
            } => TypeDesc::Tfield {
                name: name.clone(),
                kind: kind.clone(),
                typ: *typ,
                rest: *rest,
            },
            Self::Tnil => TypeDesc::Tnil,
            Self::Tlink(ty) => TypeDesc::Tlink(*ty),
            Self::Tsubst(ty) => TypeDesc::Tsubst(*ty),
            Self::Tvariant(row) => TypeDesc::Tvariant(row.clone()),
            Self::Tunivar(name) => TypeDesc::Tunivar(name.clone()),
            Self::Tpoly { body, vars } => TypeDesc::Tpoly {
                body: *body,
                vars: vars.clone(),
            },
            Self::Tpackage { path, lids, args } => TypeDesc::Tpackage {
                path: path.clone(),
                lids: lids.clone(),
                args: args.clone(),
            },
        }
    }
}

/// A reference to a type expression.
///
/// Intentional Rust performance representation for OCaml type-node identity.
///
/// OCaml stores a type node as `{mutable desc; mutable level; id}`
/// (compiler/ml/types.ml:22) and relies on physical identity plus the `id`.
/// Rust keeps that identity as an arena index instead of a pointer-shaped
/// object handle.
///
/// In the arena-based design, this is an index or pointer.
/// Type arenas are dense and far below `u32::MAX`; keeping the handle compact
/// reduces typedtree and type descriptor memory traffic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeExprRef(pub u32);

impl TypeExprRef {
    /// Create a null reference (for placeholder purposes).
    pub fn null() -> Self {
        TypeExprRef(0)
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        Self(u32::try_from(idx).expect("type arena index exceeds u32::MAX"))
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
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
    Sparse(ahash::AHashMap<TypeExprRef, T>),
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
        let mut values = ahash::AHashMap::with_capacity(len + 1);
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
                    let mut sparse = ahash::AHashMap::with_capacity(entry_count);
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

/// Intentional Rust performance representation for short-lived type-node sets.
///
/// Like [`TypeExprRefMap`], this is still keyed by exact type-node identity.
/// It replaces short-lived `HashSet<TypeExprRef>` visited tables in hot
/// type traversals without changing OCaml physical-sharing semantics from
/// compiler/ml/types.ml:22.
#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefSet {
    offset: u32,
    values: Vec<u8>,
}

impl TypeExprRefSet {
    pub(crate) fn new() -> Self {
        Self {
            offset: 0,
            values: Vec::new(),
        }
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef) -> bool {
        if self.values.is_empty() {
            self.offset = key.0;
            self.values.push(1);
            return true;
        }

        if key.0 < self.offset {
            let prepend = (self.offset - key.0) as usize;
            let mut values = Vec::with_capacity(self.values.len() + prepend);
            values.resize(prepend, 0);
            values.append(&mut self.values);
            self.values = values;
            self.offset = key.0;
        }

        let idx = (key.0 - self.offset) as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, 0);
        }

        let slot = &mut self.values[idx];
        if *slot == 0 {
            *slot = 1;
            true
        } else {
            false
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
        Self(u32::try_from(idx).expect("abbrev memo arena index exceeds u32::MAX"))
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Object name (path and type arguments).
pub type ObjectName = Option<(Path, Vec<TypeExprRef>)>;

/// Object name reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectNameRef(pub u32);

/// Field kind for object fields.
#[derive(Debug, Clone)]
pub enum FieldKind {
    /// Variable field kind
    Fvar(FieldKindRef),
    /// Present field
    Fpresent,
    /// Absent field
    Fabsent,
}

/// Reference to a field kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldKindRef(pub u32);

impl FieldKindRef {
    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        Self(u32::try_from(idx).expect("field kind arena index exceeds u32::MAX"))
    }
}

/// Row description for polymorphic variants.
#[derive(Debug, Clone)]
pub struct RowDesc {
    /// The variant fields: (label, row_field)
    pub row_fields: Vec<(Label, RowField)>,
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
        Self(u32::try_from(idx).expect("row field arena index exceeds u32::MAX"))
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
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
        assert!(matches!(ty.desc(), TypeDesc::Tnil));
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
        for arg in [TypeArg::unlabeled(typ), TypeArg::new(ArgLabel::Nolabel, typ)] {
            assert!(arg.label.is_none());
            assert!(arg.clone().label.is_none());
            assert!(matches!(arg.label(), ArgLabel::Nolabel));
            assert_eq!(arg.typ, typ);
            assert_eq!(format!("{:?}", arg),
                format!("TypeArg {{ lbl: Nolabel, typ: {:?} }}", typ));
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
        ctx.set_desc(cycle, TypeDesc::Ttuple(items.clone()));
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
            row_fields: vec![],
            row_more: TypeExprRef(1),
            row_closed: true,
            row_fixed: false,
            row_name: None,
        };
        assert!(row.row_closed);
        assert!(!row.row_fixed);
    }
}
