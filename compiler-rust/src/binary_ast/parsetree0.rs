//! Parsetree0 - Frozen PPX-compatible AST types
//!
//! This module defines the parsetree0 AST types that are used for binary AST
//! serialization. These types are "frozen" to maintain PPX compatibility.
//!
//! The types here mirror `compiler/ml/parsetree0.ml` exactly.

use crate::location::{Located, Location};
use crate::parse_arena::StrIdx;
use crate::parser::longident::Longident;

// ========== Asttypes (flags and labels) ==========

/// Recursion flag: whether a let binding is recursive
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RecFlag {
    /// `let`.
    Nonrecursive = 0,
    /// `let rec`.
    Recursive = 1,
}

/// Direction flag for for-loops
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DirectionFlag {
    /// `for i in a to b`.
    Upto = 0,
    /// `for i in a downto b`.
    Downto = 1,
}

/// Private flag for type declarations
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PrivateFlag {
    /// `private`: values can be read but not built outside the definition.
    Private = 0,
    /// No `private` marker.
    Public = 1,
}

/// Mutability flag for record fields
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MutableFlag {
    /// An immutable field.
    Immutable = 0,
    /// A `mutable` field.
    Mutable = 1,
}

/// Virtual flag (unused in ReScript, kept for OCaml compatibility)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VirtualFlag {
    /// `virtual`.
    Virtual = 0,
    /// Not `virtual`.
    Concrete = 1,
}

/// Override flag for open statements
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum OverrideFlag {
    /// `open!`, which silences shadowing warnings.
    Override = 0,
    /// Plain `open`.
    Fresh = 1,
}

/// Closed flag for record patterns and polymorphic variants
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ClosedFlag {
    /// Closed: no further fields or constructors.
    Closed = 0,
    /// Open: `..` allows more fields or constructors.
    Open = 1,
}

/// Variance for type parameters
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Variance {
    /// `+'a`.
    Covariant = 0,
    /// `-'a`.
    Contravariant = 1,
    /// No variance annotation.
    Invariant = 2,
}

/// A label (string)
pub type Label = String;

/// Argument label for function parameters (parsetree0 uses Noloc version)
/// Uses StrIdx to allow sharing with Longident::Lident when the same
/// identifier is used for both label and value (punning).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ArgLabel {
    /// Unlabeled argument
    Nolabel,
    /// Labeled argument (~label)
    Labelled(StrIdx),
    /// Optional argument (?label)
    Optional(StrIdx),
}

// ========== Constants ==========

/// Constant values in the AST
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Constant {
    /// Integer constant: 3, 3l, 3L, 3n
    Integer(String, Option<char>),
    /// Character constant: 'c'
    Char(i32),
    /// String constant: "str" or {delim|str|delim}
    String(String, Option<String>),
    /// Float constant: 3.14, 2e5
    Float(String, Option<char>),
}

// ========== Attributes and Extensions ==========

/// An attribute: `[@id ARG]` or `[@@id ARG]`
pub type Attribute = (Located<String>, Payload);

/// An extension point: [%id ARG] or [%%id ARG]
pub type Extension = (Located<String>, Payload);

/// A list of attributes
pub type Attributes = Vec<Attribute>;

/// Payload of an attribute or extension
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Payload {
    /// Structure payload
    PStr(Structure),
    /// Signature payload: : SIG
    PSig(Signature),
    /// Type payload: : T
    PTyp(Box<CoreType>),
    /// Pattern payload: ? P or ? P when E
    PPat(Box<Pattern>, Option<Box<Expression>>),
}

// ========== Core Types ==========

/// A type expression
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CoreType {
    /// What kind of type expression this is.
    pub ptyp_desc: CoreTypeDesc,
    /// Source location of the type expression.
    pub ptyp_loc: Location,
    /// Attributes attached to the type expression.
    pub ptyp_attributes: Attributes,
}

/// Core type description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum CoreTypeDesc {
    /// Wildcard: _
    Any,
    /// Type variable: 'a
    Var(String),
    /// Arrow type: T1 -> T2
    Arrow(ArgLabel, Box<CoreType>, Box<CoreType>),
    /// Tuple type: T1 * T2 * ... * Tn
    Tuple(Vec<CoreType>),
    /// Type constructor: tconstr, T tconstr, (T1, ..., Tn) tconstr
    Constr(Located<Longident>, Vec<CoreType>),
    /// Object type: < l1:T1; ...; ln:Tn > or < l1:T1; ...; ln:Tn; .. >
    Object(Vec<ObjectField>, ClosedFlag),
    /// Class type (dummy, not used in ReScript)
    Class,
    /// Type alias: T as 'a
    Alias(Box<CoreType>, String),
    /// Polymorphic variant: [ `A | `B ]
    Variant(Vec<RowField>, ClosedFlag, Option<Vec<Label>>),
    /// Polymorphic type: 'a1 ... 'an. T
    Poly(Vec<Located<String>>, Box<CoreType>),
    /// First-class module type: (module S)
    Package(PackageType),
    /// Extension: [%id]
    Extension(Extension),
}

/// Package type: (module S with type t1 = T1 and ... and tn = Tn)
pub type PackageType = (Located<Longident>, Vec<(Located<Longident>, CoreType)>);

/// Row field in a polymorphic variant
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum RowField {
    /// Tag: `A, `A of T, etc.
    Rtag(Located<Label>, Attributes, bool, Vec<CoreType>),
    /// Inherited type: `[ T ]`
    Rinherit(CoreType),
}

/// Object field
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ObjectField {
    /// Named field: l: T
    Otag(Located<Label>, Attributes, CoreType),
    /// Inherited type
    Oinherit(CoreType),
}

// ========== Patterns ==========

/// A pattern
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Pattern {
    /// What kind of pattern this is.
    pub ppat_desc: PatternDesc,
    /// Source location of the pattern.
    pub ppat_loc: Location,
    /// Attributes attached to the pattern.
    pub ppat_attributes: Attributes,
}

/// Pattern description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum PatternDesc {
    /// Wildcard: _
    Any,
    /// Variable: x
    Var(Located<String>),
    /// Alias: P as 'a
    Alias(Box<Pattern>, Located<String>),
    /// Constant: 1, 'a', "str", etc.
    Constant(Constant),
    /// Interval: 'a'..'z'
    Interval(Constant, Constant),
    /// Tuple: (P1, ..., Pn)
    Tuple(Vec<Pattern>),
    /// Constructor: C or C P
    Construct(Located<Longident>, Option<Box<Pattern>>),
    /// Polymorphic variant: `A or `A P
    Variant(Label, Option<Box<Pattern>>),
    /// Record: { l1=P1; ...; ln=Pn } or { l1=P1; ...; ln=Pn; _ }
    /// Optional fields carry the `res.optional` attribute.
    Record(Vec<(Located<Longident>, Pattern)>, ClosedFlag),
    /// Array: [| P1; ...; Pn |]
    Array(Vec<Pattern>),
    /// Or pattern: P1 | P2
    Or(Box<Pattern>, Box<Pattern>),
    /// Constraint: (P : T)
    Constraint(Box<Pattern>, Box<CoreType>),
    /// Type pattern: #tconstr
    Type(Located<Longident>),
    /// Lazy pattern: lazy P
    Lazy(Box<Pattern>),
    /// Unpack: (module P)
    Unpack(Located<String>),
    /// Exception: exception P
    Exception(Box<Pattern>),
    /// Extension: [%id]
    Extension(Extension),
    /// Open: M.(P)
    Open(Located<Longident>, Box<Pattern>),
}

// ========== Expressions ==========

/// An expression
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Expression {
    /// What kind of expression this is.
    pub pexp_desc: ExpressionDesc,
    /// Source location of the expression.
    pub pexp_loc: Location,
    /// Attributes attached to the expression.
    pub pexp_attributes: Attributes,
}

/// Expression description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ExpressionDesc {
    /// Identifier: x, M.x
    Ident(Located<Longident>),
    /// Constant: 1, 'a', "str", etc.
    Constant(Constant),
    /// Let binding: let P = E in E
    Let(RecFlag, Vec<ValueBinding>, Box<Expression>),
    /// function P1 -> E1 | ... | Pn -> En
    Function(Vec<Case>),
    /// fun ~l:(P = E0) -> E1: one parameter; `(P1, P2) => E` is a chain
    /// wrapped in `Function$` with a `res.arity` attribute.
    Fun(
        ArgLabel,
        Option<Box<Expression>>,
        Box<Pattern>,
        Box<Expression>,
    ),
    /// E0 ~l1:E1 ... ~ln:En
    Apply(Box<Expression>, Vec<(ArgLabel, Expression)>),
    /// Match: match E with P1 -> E1 | ... | Pn -> En
    Match(Box<Expression>, Vec<Case>),
    /// Try: try E with P1 -> E1 | ... | Pn -> En
    Try(Box<Expression>, Vec<Case>),
    /// Tuple: (E1, ..., En)
    Tuple(Vec<Expression>),
    /// Constructor: C or C E
    Construct(Located<Longident>, Option<Box<Expression>>),
    /// Polymorphic variant: `A or `A E
    Variant(Label, Option<Box<Expression>>),
    /// Record: { l1=E1; ...; ln=En } or { E with l1=E1; ...; ln=En }
    /// Optional fields carry the `res.optional` attribute.
    Record(
        Vec<(Located<Longident>, Expression)>,
        Option<Box<Expression>>,
    ),
    /// Field access: E.l
    Field(Box<Expression>, Located<Longident>),
    /// Field update: E1.l <- E2
    Setfield(Box<Expression>, Located<Longident>, Box<Expression>),
    /// Array: [| E1; ...; En |]
    Array(Vec<Expression>),
    /// If-then-else: if E1 then E2 else E3
    Ifthenelse(Box<Expression>, Box<Expression>, Option<Box<Expression>>),
    /// Sequence: E1; E2
    Sequence(Box<Expression>, Box<Expression>),
    /// While loop: while E1 do E2 done
    While(Box<Expression>, Box<Expression>),
    /// For loop: for i = E1 to/downto E2 do E3 done
    For(
        Box<Pattern>,
        Box<Expression>,
        Box<Expression>,
        DirectionFlag,
        Box<Expression>,
    ),
    /// Type constraint: (E : T)
    Constraint(Box<Expression>, Box<CoreType>),
    /// Coercion: (E :> T)
    Coerce(Box<Expression>, (), Box<CoreType>),
    /// Method send: E # m
    Send(Box<Expression>, Located<Label>),
    /// New object: new M.c
    New(Located<Longident>),
    /// Instance variable assignment: x <- E
    Setinstvar(Located<Label>, Box<Expression>),
    /// Override: {< x1 = E1; ...; xn = En >}
    Override(Vec<(Located<Label>, Expression)>),
    /// Let module: let module M = ME in E
    Letmodule(Located<String>, Box<ModuleExpr>, Box<Expression>),
    /// Let exception: let exception C in E
    Letexception(Box<ExtensionConstructor>, Box<Expression>),
    /// Assert: assert E
    Assert(Box<Expression>),
    /// Lazy: lazy E
    Lazy(Box<Expression>),
    /// Poly: used for method bodies
    Poly(Box<Expression>, Option<Box<CoreType>>),
    /// Object (dummy, not used in ReScript)
    Object,
    /// New type: fun (type t) -> E
    Newtype(Located<String>, Box<Expression>),
    /// Pack: (module ME)
    Pack(Box<ModuleExpr>),
    /// Open: M.(E) or let open M in E
    Open(OverrideFlag, Located<Longident>, Box<Expression>),
    /// Extension: [%id]
    Extension(Extension),
    /// Unreachable: .
    Unreachable,
}

/// A case in a match or function expression
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Case {
    /// The case pattern.
    pub pc_lhs: Pattern,
    /// The `when` guard, if any.
    pub pc_guard: Option<Expression>,
    /// The case body.
    pub pc_rhs: Expression,
}

// ========== Value bindings ==========

/// A value binding: let P = E
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ValueBinding {
    /// The bound pattern.
    pub pvb_pat: Pattern,
    /// The bound expression.
    pub pvb_expr: Expression,
    /// Attributes on the binding.
    pub pvb_attributes: Attributes,
    /// Source location of the binding.
    pub pvb_loc: Location,
}

/// A value description: val x: T or external x: T = "s1" ... "sn"
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ValueDescription {
    /// The value name.
    pub pval_name: Located<String>,
    /// The declared type.
    pub pval_type: CoreType,
    /// The `external` primitive strings; empty for a plain `let` declaration.
    pub pval_prim: Vec<String>,
    /// Attributes on the declaration.
    pub pval_attributes: Attributes,
    /// Source location of the declaration.
    pub pval_loc: Location,
}

// ========== Type declarations ==========

/// A type declaration
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct TypeDeclaration {
    /// The type name.
    pub ptype_name: Located<String>,
    /// Type parameters with their variance.
    pub ptype_params: Vec<(CoreType, Variance)>,
    /// `constraint 'a = typ` clauses.
    pub ptype_cstrs: Vec<(CoreType, CoreType, Location)>,
    /// Abstract, variant, record or open.
    pub ptype_kind: TypeKind,
    /// Whether the type is `private`.
    pub ptype_private: PrivateFlag,
    /// The `= typ` the declaration abbreviates, if any.
    pub ptype_manifest: Option<CoreType>,
    /// Attributes on the declaration.
    pub ptype_attributes: Attributes,
    /// Source location of the declaration.
    pub ptype_loc: Location,
}

/// Type kind
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum TypeKind {
    /// Abstract type
    Abstract,
    /// Variant type
    Variant(Vec<ConstructorDeclaration>),
    /// Record type
    Record(Vec<LabelDeclaration>),
    /// Open type (extensible)
    Open,
}

/// A label declaration (record field)
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct LabelDeclaration {
    /// The field name.
    pub pld_name: Located<String>,
    /// Whether the field is `mutable`.
    pub pld_mutable: MutableFlag,
    /// The field type.
    pub pld_type: CoreType,
    /// Source location of the field.
    pub pld_loc: Location,
    /// Attributes on the field.
    pub pld_attributes: Attributes,
}

/// A constructor declaration
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ConstructorDeclaration {
    /// The constructor name.
    pub pcd_name: Located<String>,
    /// The constructor arguments.
    pub pcd_args: ConstructorArguments,
    /// The GADT result type, if any.
    pub pcd_res: Option<CoreType>,
    /// Source location of the constructor.
    pub pcd_loc: Location,
    /// Attributes on the constructor.
    pub pcd_attributes: Attributes,
}

/// Constructor arguments
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ConstructorArguments {
    /// Tuple arguments: C of T1 * T2
    Tuple(Vec<CoreType>),
    /// Record arguments: C of { l1: T1; l2: T2 }
    Record(Vec<LabelDeclaration>),
}

// ========== Type extensions ==========

/// A type extension: type t += ...
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct TypeExtension {
    /// The extended type.
    pub ptyext_path: Located<Longident>,
    /// Type parameters with their variance.
    pub ptyext_params: Vec<(CoreType, Variance)>,
    /// The added constructors.
    pub ptyext_constructors: Vec<ExtensionConstructor>,
    /// Whether the extension is `private`.
    pub ptyext_private: PrivateFlag,
    /// Attributes on the extension.
    pub ptyext_attributes: Attributes,
}

/// An extension constructor
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ExtensionConstructor {
    /// The constructor name.
    pub pext_name: Located<String>,
    /// A new constructor or a rebinding of an existing one.
    pub pext_kind: ExtensionConstructorKind,
    /// Source location of the constructor.
    pub pext_loc: Location,
    /// Attributes on the constructor.
    pub pext_attributes: Attributes,
}

/// Extension constructor kind
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ExtensionConstructorKind {
    /// Declaration: | C of T1 * ... * Tn
    Decl(ConstructorArguments, Option<CoreType>),
    /// Rebind: | C = D
    Rebind(Located<Longident>),
}

// ========== Module types ==========

/// A module type
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ModuleType {
    /// What kind of module type this is.
    pub pmty_desc: ModuleTypeDesc,
    /// Source location of the module type.
    pub pmty_loc: Location,
    /// Attributes attached to the module type.
    pub pmty_attributes: Attributes,
}

/// Module type description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ModuleTypeDesc {
    /// Identifier: S
    Ident(Located<Longident>),
    /// Signature: sig ... end
    Signature(Signature),
    /// Functor: functor(X : MT1) -> MT2
    Functor(Located<String>, Option<Box<ModuleType>>, Box<ModuleType>),
    /// With constraint: MT with ...
    With(Box<ModuleType>, Vec<WithConstraint>),
    /// Typeof: module type of ME
    Typeof(Box<ModuleExpr>),
    /// Extension: [%id]
    Extension(Extension),
    /// Alias: (module M)
    Alias(Located<Longident>),
}

/// With constraint
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum WithConstraint {
    /// Type constraint: with type X.t = T
    Type(Located<Longident>, TypeDeclaration),
    /// Module constraint: with module X.Y = Z
    Module(Located<Longident>, Located<Longident>),
    /// Type substitution: with type X.t := T
    TypeSubst(Located<Longident>, TypeDeclaration),
    /// Module substitution: with module X.Y := Z
    ModSubst(Located<Longident>, Located<Longident>),
}

// ========== Signatures ==========

/// A signature
pub type Signature = Vec<SignatureItem>;

/// A signature item
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SignatureItem {
    /// What kind of signature item this is.
    pub psig_desc: SignatureItemDesc,
    /// Source location of the item.
    pub psig_loc: Location,
}

/// Signature item description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum SignatureItemDesc {
    /// Value: val x: T
    Value(ValueDescription),
    /// Type: type t1 = ... and ... and tn = ...
    Type(RecFlag, Vec<TypeDeclaration>),
    /// Type extension: type t += ...
    Typext(TypeExtension),
    /// Exception: exception C of T
    Exception(ExtensionConstructor),
    /// Module: module X : MT
    Module(ModuleDeclaration),
    /// Recursive modules: module rec X1 : MT1 and ... and Xn : MTn
    Recmodule(Vec<ModuleDeclaration>),
    /// Module type: module type S = MT
    Modtype(ModuleTypeDeclaration),
    /// Open: open X
    Open(OpenDescription),
    /// Include: include MT
    Include(IncludeDescription),
    /// Class (dummy)
    Class,
    /// Class type (dummy)
    ClassType,
    /// Attribute: `[@@@id]`
    Attribute(Attribute),
    /// Extension: [%%id]
    Extension(Extension, Attributes),
}

/// Module declaration
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ModuleDeclaration {
    /// The module name.
    pub pmd_name: Located<String>,
    /// The module type.
    pub pmd_type: ModuleType,
    /// Attributes on the declaration.
    pub pmd_attributes: Attributes,
    /// Source location of the declaration.
    pub pmd_loc: Location,
}

/// Module type declaration
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ModuleTypeDeclaration {
    /// The module type name.
    pub pmtd_name: Located<String>,
    /// The definition; `None` for an abstract module type.
    pub pmtd_type: Option<ModuleType>,
    /// Attributes on the declaration.
    pub pmtd_attributes: Attributes,
    /// Source location of the declaration.
    pub pmtd_loc: Location,
}

/// Open description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct OpenDescription {
    /// The opened module path.
    pub popen_lid: Located<Longident>,
    /// `open!` or plain `open`.
    pub popen_override: OverrideFlag,
    /// Source location of the `open`.
    pub popen_loc: Location,
    /// Attributes on the `open`.
    pub popen_attributes: Attributes,
}

/// Include infos (generic)
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct IncludeInfos<A> {
    /// The included module or module type.
    pub pincl_mod: A,
    /// Source location of the `include`.
    pub pincl_loc: Location,
    /// Attributes on the `include`.
    pub pincl_attributes: Attributes,
}

/// Include description: include MT
pub type IncludeDescription = IncludeInfos<ModuleType>;

/// Include declaration: include ME
pub type IncludeDeclaration = IncludeInfos<ModuleExpr>;

// ========== Module expressions ==========

/// A module expression
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ModuleExpr {
    /// What kind of module expression this is.
    pub pmod_desc: ModuleExprDesc,
    /// Source location of the module expression.
    pub pmod_loc: Location,
    /// Attributes attached to the module expression.
    pub pmod_attributes: Attributes,
}

/// Module expression description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ModuleExprDesc {
    /// Identifier: X
    Ident(Located<Longident>),
    /// Structure: struct ... end
    Structure(Structure),
    /// Functor: functor(X : MT1) -> ME
    Functor(Located<String>, Option<Box<ModuleType>>, Box<ModuleExpr>),
    /// Application: ME1(ME2)
    Apply(Box<ModuleExpr>, Box<ModuleExpr>),
    /// Constraint: (ME : MT)
    Constraint(Box<ModuleExpr>, Box<ModuleType>),
    /// Unpack: (val E)
    Unpack(Box<Expression>),
    /// Extension: [%id]
    Extension(Extension),
}

// ========== Structures ==========

/// A structure
pub type Structure = Vec<StructureItem>;

/// A structure item
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct StructureItem {
    /// What kind of structure item this is.
    pub pstr_desc: StructureItemDesc,
    /// Source location of the item.
    pub pstr_loc: Location,
}

/// Structure item description
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum StructureItemDesc {
    /// Evaluation: E
    Eval(Expression, Attributes),
    /// Value: let P1 = E1 and ... and Pn = En
    Value(RecFlag, Vec<ValueBinding>),
    /// Primitive: val x: T or external x: T = "s1" ... "sn"
    Primitive(ValueDescription),
    /// Type: type t1 = ... and ... and tn = ...
    Type(RecFlag, Vec<TypeDeclaration>),
    /// Type extension: type t += ...
    Typext(TypeExtension),
    /// Exception: exception C of T
    Exception(ExtensionConstructor),
    /// Module: module X = ME
    Module(ModuleBinding),
    /// Recursive modules: module rec X1 = ME1 and ... and Xn = MEn
    Recmodule(Vec<ModuleBinding>),
    /// Module type: module type S = MT
    Modtype(ModuleTypeDeclaration),
    /// Open: open X
    Open(OpenDescription),
    /// Class (dummy)
    Class,
    /// Class type (dummy)
    ClassType,
    /// Include: include ME
    Include(IncludeDeclaration),
    /// Attribute: `[@@@id]`
    Attribute(Attribute),
    /// Extension: [%%id]
    Extension(Extension, Attributes),
}

/// A module binding: X = ME
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ModuleBinding {
    /// The module name.
    pub pmb_name: Located<String>,
    /// The bound module expression.
    pub pmb_expr: ModuleExpr,
    /// Attributes on the binding.
    pub pmb_attributes: Attributes,
    /// Source location of the binding.
    pub pmb_loc: Location,
}
