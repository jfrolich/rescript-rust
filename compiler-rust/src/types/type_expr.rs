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
#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefMap<T> {
    offset: u32,
    values: Vec<Option<T>>,
}

impl<T> TypeExprRefMap<T> {
    pub(crate) fn new() -> Self {
        Self {
            offset: 0,
            values: Vec::new(),
        }
    }

    #[inline]
    pub(crate) fn get(&self, key: TypeExprRef) -> Option<&T> {
        let idx = key.0.checked_sub(self.offset)? as usize;
        self.values.get(idx)?.as_ref()
    }

    #[inline]
    pub(crate) fn storage_len(&self) -> usize {
        self.values.len()
    }

    #[inline]
    pub(crate) fn storage_capacity(&self) -> usize {
        self.values.capacity()
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef, value: T) -> Option<T> {
        if self.values.is_empty() {
            self.offset = key.0;
            self.values.push(Some(value));
            return None;
        }

        if key.0 < self.offset {
            let prepend = (self.offset - key.0) as usize;
            let mut values = Vec::with_capacity(self.values.len() + prepend);
            values.resize_with(prepend, || None);
            values.append(&mut self.values);
            self.values = values;
            self.offset = key.0;
        }

        let idx = (key.0 - self.offset) as usize;
        if idx >= self.values.len() {
            self.values.resize_with(idx + 1, || None);
        }
        self.values[idx].replace(value)
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
#[derive(Debug, Clone)]
pub struct TypeArg {
    /// The argument label
    pub lbl: ArgLabel,
    /// The argument type
    pub typ: TypeExprRef,
}

impl TypeArg {
    /// Create a new type argument.
    pub fn new(lbl: ArgLabel, typ: TypeExprRef) -> Self {
        TypeArg { lbl, typ }
    }

    /// Create an unlabeled argument.
    pub fn unlabeled(typ: TypeExprRef) -> Self {
        TypeArg {
            lbl: ArgLabel::Nolabel,
            typ,
        }
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
        assert!(matches!(arg.lbl, ArgLabel::Nolabel));
        assert_eq!(arg.typ, TypeExprRef(1));
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
