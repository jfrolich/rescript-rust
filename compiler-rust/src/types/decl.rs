//! Type declarations and signatures.
//!
//! This module defines the types for type declarations, value descriptions,
//! module types, and signatures - the building blocks of module interfaces.

use super::asttypes::{Located, MutableFlag, PrivateFlag};
use super::path::Path;
use super::type_expr::TypeExprRef;
use super::variance::Variance;
use crate::ident::Ident;
use crate::location::Location;
use serde::{Deserialize, Serialize};

// ============================================================================
// Value Descriptions
// ============================================================================

/// A value description (type of a let-bound value).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDescription {
    /// Type of the value
    pub val_type: TypeExprRef,
    /// Kind of value (regular or primitive)
    pub val_kind: ValueKind,
    /// Source location
    pub val_loc: Location,
    /// Attributes
    pub val_attributes: Vec<Attribute>,
    /// Full path to the value (for module items, None for local bindings)
    pub val_path: Option<Path>,
}

/// Kind of value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueKind {
    /// Regular value
    ValReg,
    /// Primitive value
    ValPrim(PrimitiveDescription),
}

/// Description of a primitive operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveDescription {
    /// Primitive name
    pub prim_name: String,
    /// Arity
    pub prim_arity: i32,
    /// Native name (if different)
    pub prim_native_name: String,
    /// Native float flag
    pub prim_native_float: bool,
    /// Is it from a type constructor instead of a concrete function type?
    pub prim_from_constructor: bool,
}

// ============================================================================
// Type Declarations
// ============================================================================

/// A type declaration (`type t = ...`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDeclaration {
    /// Type parameters
    pub type_params: Vec<TypeExprRef>,
    /// Number of type parameters
    pub type_arity: i32,
    /// Kind of type (abstract, record, variant, open)
    pub type_kind: TypeKind,
    /// Private flag
    pub type_private: PrivateFlag,
    /// Manifest type (for type aliases)
    pub type_manifest: Option<TypeExprRef>,
    /// Variance of type parameters
    pub type_variance: Vec<Variance>,
    /// Newtype level (for local abstract types)
    pub type_newtype_level: Option<(i32, i32)>,
    /// Source location
    pub type_loc: Location,
    /// Attributes
    pub type_attributes: Vec<Attribute>,
    /// Is this type immediate (unboxed)?
    pub type_immediate: bool,
    /// Runtime representation for single-payload unboxing.
    pub type_representation: TypeRepresentation,
    /// Inlined types (for record printing)
    pub type_inlined_types: Vec<TypeInlinedType>,
    /// Qualified path for this type (e.g., Pdot(Pident "Pervasives") "ref").
    /// Set when loading types from modules; None for locally defined types.
    pub type_path: Option<super::path::Path>,
}

/// A lookup result that keeps an existing component declaration shared.
///
/// This owns no new type graph. Borrowed Env declarations and already-cached
/// component Arcs can be inspected without copying their metadata containers.
/// Call `into_owned` at a boundary that mutates or transfers the declaration.
pub(crate) enum TypeDeclarationRef<'a> {
    Borrowed(&'a TypeDeclaration),
    Shared(std::sync::Arc<TypeDeclaration>),
    Owned(Box<TypeDeclaration>),
}

impl TypeDeclarationRef<'_> {
    pub(crate) fn owned(decl: TypeDeclaration) -> Self {
        Self::Owned(Box::new(decl))
    }

    pub(crate) fn into_owned(self) -> TypeDeclaration {
        match self {
            Self::Borrowed(decl) => decl.clone(),
            Self::Shared(decl) => std::sync::Arc::unwrap_or_clone(decl),
            Self::Owned(decl) => *decl,
        }
    }
}

impl std::ops::Deref for TypeDeclarationRef<'_> {
    type Target = TypeDeclaration;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(decl) => decl,
            Self::Shared(decl) => decl,
            Self::Owned(decl) => decl,
        }
    }
}

/// An inlined type representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeInlinedType {
    /// Inlined record
    Record {
        type_name: String,
        labels: Vec<LabelDeclaration>,
    },
}

/// Kind of type definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// Abstract type
    TypeAbstract,
    /// Record type
    TypeRecord(Vec<LabelDeclaration>, RecordRepresentation),
    /// Variant type with its canonical runtime layout.
    TypeVariant(
        Vec<ConstructorDeclaration>,
        super::variant_runtime::LayoutRef,
    ),
    /// Open type (extensible)
    TypeOpen,
}

impl TypeDeclaration {
    pub fn variant_layout_ref(&self) -> Option<super::variant_runtime::LayoutRef> {
        match self.type_kind {
            TypeKind::TypeVariant(_, layout) => Some(layout),
            TypeKind::TypeAbstract | TypeKind::TypeRecord(..) | TypeKind::TypeOpen => None,
        }
    }
}

/// Record representation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordRepresentation {
    /// Regular record (all fields boxed/tagged)
    RecordRegular,
    /// Float record (unused, kept for compatibility)
    RecordFloatUnused,
    /// Unboxed single-field record
    RecordUnboxed(bool),
    /// Inlined record (in variant constructor)
    RecordInlined {
        name: String,
        representation: super::variant_runtime::ConstructorReference,
    },
    /// Extension record
    RecordExtension,
}

/// Runtime representation for single-payload unboxing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRepresentation {
    Boxed,
    Unboxed,
}

/// A label (field) declaration in a record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelDeclaration {
    /// Label identifier
    pub ld_id: Ident,
    /// Is the field mutable?
    pub ld_mutable: MutableFlag,
    /// Is the field optional?
    pub ld_optional: bool,
    /// Field type
    pub ld_type: TypeExprRef,
    /// Source location
    pub ld_loc: Location,
    /// Attributes
    pub ld_attributes: Vec<Attribute>,
}

/// A constructor declaration in a variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDeclaration {
    /// Constructor identifier
    pub cd_id: Ident,
    /// Constructor arguments
    pub cd_args: ConstructorArguments,
    /// Result type (for GADTs)
    pub cd_res: Option<TypeExprRef>,
    /// Source location
    pub cd_loc: Location,
    /// Attributes
    pub cd_attributes: Vec<Attribute>,
}

/// Constructor arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructorArguments {
    /// Tuple arguments
    CstrTuple(Vec<TypeExprRef>),
    /// Inline record arguments
    CstrRecord(Vec<LabelDeclaration>),
}

// ============================================================================
// Extension Constructors
// ============================================================================

/// An extension constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionConstructor {
    /// Path to the extensible type
    pub ext_type_path: Path,
    /// Type parameters
    pub ext_type_params: Vec<TypeExprRef>,
    /// Constructor arguments
    pub ext_args: ConstructorArguments,
    /// Result type (for GADTs)
    pub ext_ret_type: Option<TypeExprRef>,
    /// Private flag
    pub ext_private: PrivateFlag,
    /// Source location
    pub ext_loc: Location,
    /// Attributes
    pub ext_attributes: Vec<Attribute>,
    /// Is this an exception?
    pub ext_is_exception: bool,
}

// ============================================================================
// Constructor and Label Descriptions
// ============================================================================

/// A constructor description (used in typing environment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDescription {
    /// Constructor name
    pub cstr_name: String,
    /// Result type
    pub cstr_res: TypeExprRef,
    /// Existential type variables
    pub cstr_existentials: Vec<TypeExprRef>,
    /// Argument types
    pub cstr_args: Vec<TypeExprRef>,
    /// Number of arguments
    pub cstr_arity: i32,
    /// Semantic constructor kind and canonical runtime representation.
    pub cstr_kind: ConstructorKind,
    /// Is this a GADT constructor?
    pub cstr_generalized: bool,
    /// Private flag
    pub cstr_private: PrivateFlag,
    /// Source location
    pub cstr_loc: Location,
    /// Attributes
    pub cstr_attributes: Vec<Attribute>,
    /// Inlined record declaration (if any)
    pub cstr_inlined: Option<Box<TypeDeclaration>>,
}

/// Semantic constructor identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstructorKind {
    /// Constructor declared by an ordinary variant.
    Ordinary(super::variant_runtime::ConstructorReference),
    /// Extensible constructor, identified by its extension path.
    Extension(Path),
}

/// Whether two descriptions denote the same constructor for a common
/// scrutinee type.
pub fn same_constructor(c1: &ConstructorDescription, c2: &ConstructorDescription) -> bool {
    match (&c1.cstr_kind, &c2.cstr_kind) {
        (ConstructorKind::Ordinary(_), ConstructorKind::Ordinary(_)) => {
            c1.cstr_name == c2.cstr_name
        }
        (ConstructorKind::Extension(p1), ConstructorKind::Extension(p2)) => p1.same(p2),
        _ => false,
    }
}

/// Conservative equality used while checking extension patterns.
pub fn may_equal_constructor(c1: &ConstructorDescription, c2: &ConstructorDescription) -> bool {
    match (&c1.cstr_kind, &c2.cstr_kind) {
        (ConstructorKind::Extension(_), ConstructorKind::Extension(_)) => {
            c1.cstr_arity == c2.cstr_arity
        }
        _ => same_constructor(c1, c2),
    }
}

/// A label description (used in typing environment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelDescription {
    /// Short name
    pub lbl_name: String,
    /// Result type (the record type)
    pub lbl_res: TypeExprRef,
    /// Argument type (the field type)
    pub lbl_arg: TypeExprRef,
    /// Is this mutable?
    pub lbl_mut: MutableFlag,
    /// Is this optional?
    pub lbl_optional: bool,
    /// Position in block
    pub lbl_pos: i32,
    /// All labels in this type (index reference)
    pub lbl_all: LabelArrayRef,
    /// Record representation
    pub lbl_repres: RecordRepresentation,
    /// Private flag
    pub lbl_private: PrivateFlag,
    /// Source location
    pub lbl_loc: Location,
    /// Attributes
    pub lbl_attributes: Vec<Attribute>,
}

/// Reference to an array of label descriptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LabelArrayRef(pub u32);

// ============================================================================
// Module Types
// ============================================================================

/// A module type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleType {
    /// Module type identifier
    MtyIdent(Path),
    /// Signature. Shared like OCaml's immutable signature list, so copying a
    /// module type during lookup does not copy every item.
    MtySignature(std::sync::Arc<Signature>),
    /// Functor
    MtyFunctor {
        param: Ident,
        param_type: Option<Box<ModuleType>>,
        result: Box<ModuleType>,
    },
    /// Module alias
    MtyAlias(AliasPresence, Path),
}

/// Alias presence flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasPresence {
    /// Alias is present
    MtaPresent,
    /// Alias is absent
    MtaAbsent,
}

/// A signature (list of signature items).
pub type Signature = Vec<SignatureItem>;

/// Copy-on-write access to a shared module-type signature.
pub fn signature_mut(signature: &mut std::sync::Arc<Signature>) -> &mut Signature {
    std::sync::Arc::make_mut(signature)
}

/// A signature item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureItem {
    /// Value in signature
    SigValue(Ident, ValueDescription),
    /// Type in signature
    SigType(Ident, TypeDeclaration, RecStatus),
    /// Type extension in signature
    SigTypext(Ident, ExtensionConstructor, ExtStatus),
    /// Module in signature
    SigModule(Ident, ModuleDeclaration, RecStatus),
    /// Module type in signature
    SigModtype(Ident, ModtypeDeclaration),
    /// Class (dummy for OCaml compatibility)
    SigClass,
    /// Class type (dummy for OCaml compatibility)
    SigClassType,
}

/// Return the runtime slot and declaration for the last submodule with the
/// given name in a signature, using OCaml's component-table slot accounting.
pub fn signature_runtime_module<'a>(
    sig: &'a [SignatureItem],
    name: &str,
) -> Option<(usize, &'a ModuleDeclaration)> {
    let mut runtime_pos = 0usize;
    let mut found = None;
    for item in sig {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigModule(id, md, _) => {
                let current = runtime_pos;
                if id.name() == name {
                    found = Some((current, md));
                }
                runtime_pos += 1;
            }
            SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigType(_, _, _)
            | SignatureItem::SigModtype(_, _)
            | SignatureItem::SigClassType => {}
        }
    }
    found
}

/// Return runtime-bound identifiers from a signature, paired with their
/// runtime slot, following OCaml `Translmod.bound_value_identifiers`.
pub fn signature_runtime_bound_idents(sig: &[SignatureItem]) -> Vec<(Ident, usize)> {
    let mut runtime_pos = 0usize;
    let mut bound = Vec::new();
    for item in sig {
        match item {
            SignatureItem::SigValue(id, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    bound.push((id.clone(), runtime_pos));
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigTypext(id, _, _) | SignatureItem::SigModule(id, _, _) => {
                bound.push((id.clone(), runtime_pos));
                runtime_pos += 1;
            }
            SignatureItem::SigClass => {
                runtime_pos += 1;
            }
            SignatureItem::SigType(_, _, _)
            | SignatureItem::SigModtype(_, _)
            | SignatureItem::SigClassType => {}
        }
    }
    bound
}

/// A module declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleDeclaration {
    /// Module type
    pub md_type: ModuleType,
    /// Attributes
    pub md_attributes: Vec<Attribute>,
    /// Source location
    pub md_loc: Location,
    /// Qualified path for this module when accessed through an opened parent.
    /// E.g., Pdot(Pident "Stdlib") "Console" for Console from opened Stdlib.
    pub md_path: Option<super::path::Path>,
}

/// A module type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModtypeDeclaration {
    /// Module type (None for abstract)
    pub mtd_type: Option<ModuleType>,
    /// Attributes
    pub mtd_attributes: Vec<Attribute>,
    /// Source location
    pub mtd_loc: Location,
}

/// Recursive status for type/module declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecStatus {
    /// Not first in a nonrecursive group
    TrecNot,
    /// First in a recursive group
    TrecFirst,
    /// Not first in a recursive/nonrecursive group
    TrecNext,
}

/// Extension status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtStatus {
    /// First constructor of an extension
    TextFirst,
    /// Not first constructor
    TextNext,
    /// An exception
    TextException,
}

// ============================================================================
// Attributes
// ============================================================================

/// An attribute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Attribute {
    /// Attribute name
    pub attr_name: Located<String>,
    /// Attribute payload (simplified)
    pub attr_payload: AttributePayload,
    /// Source location
    pub attr_loc: Location,
}

/// Attribute payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum AttributePayload {
    /// Empty payload
    Empty,
    /// String payload
    Str(String),
    /// Integer payload
    Int(i64),
    /// Unparsed integer payload from source attributes.
    IntLiteral(String),
    /// Float payload
    Float(String),
    /// BigInt payload
    BigInt(String),
    /// Boolean payload
    Bool(bool),
    /// Identifier payload
    Ident(String),
    /// Deprecated payload with optional migration metadata.
    Deprecated {
        reason: String,
        can_be_automigrated: bool,
    },
    /// Structure payload (list of string pairs)
    Structure(Vec<(String, String)>),
}

pub const INTERNAL_OPTIONAL_ATTR_NAME: &str = "internal.optional";

pub fn has_internal_optional_attr(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| attr.attr_name.txt == INTERNAL_OPTIONAL_ATTR_NAME)
}

pub fn internal_optional_attr() -> Attribute {
    Attribute {
        attr_name: Located::noloc(INTERNAL_OPTIONAL_ATTR_NAME.to_string()),
        attr_payload: AttributePayload::Structure(vec![]),
        attr_loc: Location::none(),
    }
}

pub fn variant_has_optional_shape(cdecls: &[ConstructorDeclaration]) -> bool {
    matches!(
        cdecls,
        [
            ConstructorDeclaration {
                cd_id,
                cd_args: ConstructorArguments::CstrTuple(args1),
                ..
            },
            ConstructorDeclaration {
                cd_id: cd_id2,
                cd_args: ConstructorArguments::CstrTuple(args2),
                ..
            }
        ] if (
            cd_id.name() == "None" && args1.is_empty() && cd_id2.name() == "Some" && args2.len() == 1
        ) || (
            cd_id.name() == "Some" && args1.len() == 1 && cd_id2.name() == "None" && args2.is_empty()
        )
    )
}

pub fn constructor_description_attrs_for_variant(
    cdecls: &[ConstructorDeclaration],
    cd: &ConstructorDeclaration,
) -> Vec<Attribute> {
    let mut attrs = cd.cd_attributes.clone();
    if variant_has_optional_shape(cdecls) && !has_internal_optional_attr(&attrs) {
        attrs.insert(0, internal_optional_attr());
    }
    attrs
}

/// Parse like OCaml's `int_of_string` on a 64-bit runtime.
pub(crate) fn parse_ocaml_int_literal(s: &str) -> Option<i64> {
    let stripped: String = s.chars().filter(|c| *c != '_').collect();
    let (negative, digits) = if let Some(rest) = stripped.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = stripped.strip_prefix('+') {
        (false, rest)
    } else {
        (false, stripped.as_str())
    };
    let (base, digits) = if let Some(rest) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        (16, rest)
    } else if let Some(rest) = digits
        .strip_prefix("0o")
        .or_else(|| digits.strip_prefix("0O"))
    {
        (8, rest)
    } else if let Some(rest) = digits
        .strip_prefix("0b")
        .or_else(|| digits.strip_prefix("0B"))
    {
        (2, rest)
    } else {
        (10, digits)
    };
    if digits.is_empty() {
        return None;
    }
    let magnitude = i128::from_str_radix(digits, base).ok()?;
    let value = if negative { -magnitude } else { magnitude };
    let min = -(1i128 << 62);
    let max = (1i128 << 62) - 1;
    if value < min || value > max {
        None
    } else {
        Some(value as i64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_record_representation() {
        let r1 = RecordRepresentation::RecordRegular;
        let r2 = RecordRepresentation::RecordRegular;
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_value_kind() {
        let vk = ValueKind::ValReg;
        assert!(matches!(vk, ValueKind::ValReg));
    }
}
