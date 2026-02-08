//! Abstract Syntax Tree types for ReScript.
//!
//! This module defines the AST produced by the parser, mirroring
//! OCaml's `Parsetree` with ReScript-specific extensions.
//!
//! Note: We use `Pexp_`, `Ppat_`, etc. naming convention to match
//! OCaml's Parsetree for easier cross-referencing.

#![allow(non_camel_case_types)]
#![allow(missing_docs)]

use std::borrow::Cow;

use crate::parse_arena::{ArityIdx, LidentIdx, Located, LocIdx, PosIdx, StrIdx};
use serde::{Deserialize, Serialize};

/// Extend the lifetime of a `Cow<'a, str>` to `'static` for zero-copy AST storage.
///
/// # Safety
///
/// This is sound when the borrowed source string outlives the AST in all execution
/// paths. In our codebase, the source `String` lives in `generate_ast()` /
/// `res_parser::main()`, and the AST is created, transformed, marshaled, and dropped
/// within the same function scope — so borrowed references into the source are always
/// valid for the AST's lifetime.
///
/// For `Cow::Owned` values, this is a no-op (transmuting the lifetime of an owned
/// value doesn't affect anything).
#[inline(always)]
pub fn extend_cow_lifetime(cow: Cow<'_, str>) -> Cow<'static, str> {
    // SAFETY: See doc comment above. The source string outlives the AST.
    unsafe { std::mem::transmute::<Cow<'_, str>, Cow<'static, str>>(cow) }
}

/// Re-export Located for convenience.
/// Note: Located<T> uses LocIdx for efficient arena-based storage.
pub type Loc<T> = Located<T>;

/// Location type alias - uses arena index for efficient storage.
pub type Location = LocIdx;

/// A string with location information.
/// Uses StrIdx for efficient sharing in Marshal output.
pub type StringLoc = Located<StrIdx>;

/// Arity information for functions.
///
/// This is now an arena index instead of an enum. Arity values are stored in
/// the ParseArena and deduplicated by content:
/// - `arena.push_arity(None)` → ArityIdx pointing to "Unknown" arity
/// - `arena.push_arity(Some(n))` → ArityIdx pointing to "Full(n)" arity
///
/// Two arities with the same value get the same index, enabling marshal sharing
/// that matches OCaml's constant folding behavior.
pub type Arity = ArityIdx;

/// Recursive flag for let bindings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecFlag {
    /// Non-recursive binding.
    Nonrecursive,
    /// Recursive binding.
    Recursive,
}

/// Direction flag for for-loops.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DirectionFlag {
    /// Counting upward.
    Upto,
    /// Counting downward.
    Downto,
}

/// Closed flag for record patterns and types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClosedFlag {
    /// Closed (exact match).
    Closed,
    /// Open (allows extra fields).
    Open,
}

/// Override flag for open statements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum OverrideFlag {
    /// Normal open.
    Fresh,
    /// Override open.
    Override,
}

/// Mutable flag for record fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MutableFlag {
    /// Immutable field.
    Immutable,
    /// Mutable field.
    Mutable,
}

/// Private flag for type definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivateFlag {
    /// Public type.
    Public,
    /// Private type.
    Private,
}

/// Variance for type parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Variance {
    /// Covariant (+).
    Covariant,
    /// Contravariant (-).
    Contravariant,
    /// Invariant (no annotation).
    Invariant,
}

/// Argument label for function parameters.
/// Uses Located<StrIdx> to allow sharing with Longident::Lident when the same
/// identifier is used for both label and value (punning).
/// The location matches OCaml's `Labelled of string loc`.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum ArgLabel {
    /// No label.
    Nolabel,
    /// Labeled argument: `~foo` with location.
    Labelled(Located<StrIdx>),
    /// Optional argument: `?foo` with location.
    Optional(Located<StrIdx>),
}

impl ArgLabel {
    /// Check if this is an unlabeled argument.
    pub fn is_nolabel(&self) -> bool {
        matches!(self, ArgLabel::Nolabel)
    }

    /// Check if this is an optional argument.
    pub fn is_optional(&self) -> bool {
        matches!(self, ArgLabel::Optional(_))
    }

    /// Get the label StrIdx, if any.
    pub fn name_idx(&self) -> Option<StrIdx> {
        match self {
            ArgLabel::Nolabel => None,
            ArgLabel::Labelled(s) | ArgLabel::Optional(s) => Some(s.txt),
        }
    }

    /// Get the located StrIdx, if any.
    pub fn located(&self) -> Option<&Located<StrIdx>> {
        match self {
            ArgLabel::Nolabel => None,
            ArgLabel::Labelled(s) | ArgLabel::Optional(s) => Some(s),
        }
    }
}

/// A label (used for variant constructors, object methods, etc.).
///
/// Uses `Cow<'static, str>` to enable zero-copy from source for the common case.
/// Parser-produced labels borrow from source via unsafe lifetime extension (sound
/// because the source string outlives the AST in all execution paths).
/// PPX-generated labels use `Cow::Owned`.
pub type Label = Cow<'static, str>;

// ============================================================================
// Constants
// ============================================================================

/// Constant values.
///
/// Uses `Cow<'static, str>` for string data to enable zero-copy from source.
/// The `'static` lifetime is sound because the source string outlives the AST
/// in all execution paths. Parser-produced constants use `Cow::Borrowed` (zero-copy),
/// while PPX-generated constants use `Cow::Owned`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constant {
    /// Integer constant with optional suffix (l, L, n).
    Integer(Cow<'static, str>, Option<char>),
    /// Character constant (Unicode codepoint).
    Char(i32),
    /// String constant with optional delimiter.
    String(Cow<'static, str>, Option<Cow<'static, str>>),
    /// Float constant with optional suffix.
    Float(Cow<'static, str>, Option<char>),
}

// ============================================================================
// Attributes and Extensions
// ============================================================================

/// An attribute: `[@id payload]`.
pub type Attribute = (StringLoc, Payload);

/// A list of attributes.
pub type Attributes = Vec<Attribute>;

/// An extension point: `[%id payload]`.
pub type Extension = (StringLoc, Payload);

/// Payload of an attribute or extension.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Payload {
    /// Structure payload: `[@@attr structure]`.
    PStr(Box<Vec<StructureItem>>),
    /// Signature payload: `[@@attr: signature]`.
    PSig(Box<Vec<SignatureItem>>),
    /// Type payload: `[@@attr: type]`.
    PTyp(Box<CoreType>),
    /// Pattern payload with optional guard: `[@@attr? pattern when guard]`.
    PPat(Box<(Box<Pattern>, Option<Box<Expression>>)>),
}

// ============================================================================
// Core Types
// ============================================================================

/// A core type (type expression).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CoreType {
    /// Type description.
    pub ptyp_desc: Box<CoreTypeDesc>,
    /// Location.
    pub ptyp_loc: Location,
    /// Attributes.
    pub ptyp_attributes: Attributes,
}

/// Argument in an arrow type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeArg {
    /// Attributes on the argument.
    pub attrs: Attributes,
    /// Argument label.
    pub lbl: ArgLabel,
    /// Argument type.
    pub typ: CoreType,
}

/// Core type descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CoreTypeDesc {
    /// Any type: `_`.
    Ptyp_any,
    /// Type variable: `'a`.
    Ptyp_var(Box<Cow<'static, str>>),
    /// Arrow type: `T1 -> T2`.
    Ptyp_arrow(Box<(Box<TypeArg>, Box<CoreType>, Arity)>),
    /// Tuple type: `(T1, T2, ..., Tn)`.
    Ptyp_tuple(Box<Vec<CoreType>>),
    /// Type constructor: `tconstr` or `T tconstr` or `(T1, ..., Tn) tconstr`.
    Ptyp_constr(Box<(Loc<LidentIdx>, Vec<CoreType>)>),
    /// Object type: `{. field: T, ... }`.
    Ptyp_object(Box<(Vec<ObjectField>, ClosedFlag)>),
    /// Type alias: `T as 'a`.
    Ptyp_alias(Box<(Box<CoreType>, Cow<'static, str>)>),
    /// Polymorphic variant: `[> \`A | \`B ]`.
    Ptyp_variant(Box<(Vec<RowField>, ClosedFlag, Option<Vec<Label>>)>),
    /// Polymorphic type: `'a 'b. T`.
    Ptyp_poly(Box<(Vec<StringLoc>, Box<CoreType>)>),
    /// Package type: `module S`.
    Ptyp_package(Box<PackageType>),
    /// Extension: `[%id]`.
    Ptyp_extension(Box<Extension>),
}

/// Package type: `module S with type t = T`.
pub type PackageType = (Loc<LidentIdx>, Vec<(Loc<LidentIdx>, CoreType)>);

/// Row field in a polymorphic variant.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RowField {
    /// Tag: `\`A of T1 & T2`.
    Rtag(Loc<Label>, Attributes, bool, Vec<CoreType>),
    /// Inherited type: `[T]`.
    Rinherit(CoreType),
}

/// Object field.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ObjectField {
    /// Named field: `name: T`.
    Otag(StringLoc, Attributes, CoreType),
    /// Inherited type.
    Oinherit(CoreType),
}

// ============================================================================
// Patterns
// ============================================================================

/// A pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Pattern {
    /// Pattern description.
    pub ppat_desc: Box<PatternDesc>,
    /// Location.
    pub ppat_loc: Location,
    /// Attributes.
    pub ppat_attributes: Attributes,
}

/// Pattern descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PatternDesc {
    /// Wildcard: `_`.
    Ppat_any,
    /// Variable: `x`.
    Ppat_var(StringLoc),
    /// Alias: `P as x`.
    Ppat_alias(Box<Pattern>, StringLoc),
    /// Constant: `1`, `'a'`, `"hello"`.
    Ppat_constant(Box<Constant>),
    /// Interval: `'a'..'z'`.
    Ppat_interval(Box<(Constant, Constant)>),
    /// Tuple: `(P1, P2, ..., Pn)`.
    Ppat_tuple(Box<Vec<Pattern>>),
    /// Constructor: `C` or `C(P)`.
    Ppat_construct(Loc<LidentIdx>, Option<Box<Pattern>>),
    /// Variant: `\`A` or `\`A(P)`.
    Ppat_variant(Box<(Label, Option<Box<Pattern>>)>),
    /// Record: `{l1: P1, ..., ln: Pn}`.
    Ppat_record(Box<(Vec<PatternRecordField>, ClosedFlag)>),
    /// Array: `[P1, ..., Pn]`.
    Ppat_array(Box<Vec<Pattern>>),
    /// Or-pattern: `P1 | P2`.
    Ppat_or(Box<Pattern>, Box<Pattern>),
    /// Constraint: `(P: T)`.
    Ppat_constraint(Box<(Box<Pattern>, CoreType)>),
    /// Type pattern: `#tconstr`.
    Ppat_type(Loc<LidentIdx>),
    /// Unpack: `module(P)`.
    Ppat_unpack(StringLoc),
    /// Exception: `exception P`.
    Ppat_exception(Box<Pattern>),
    /// Extension: `[%id]`.
    Ppat_extension(Box<Extension>),
    /// Open: `M.(P)`.
    Ppat_open(Loc<LidentIdx>, Box<Pattern>),
}

/// A record field in a pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PatternRecordField {
    /// Field name.
    pub lid: Loc<LidentIdx>,
    /// Pattern.
    pub pat: Pattern,
    /// Whether this is optional.
    pub opt: bool,
}

// ============================================================================
// Expressions
// ============================================================================

/// An expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expression {
    /// Expression description.
    pub pexp_desc: Box<ExpressionDesc>,
    /// Location.
    pub pexp_loc: Location,
    /// Attributes.
    pub pexp_attributes: Attributes,
}

/// Named struct for Pexp_fun variant (boxed for enum size optimization).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpFun {
    pub arg_label: ArgLabel,
    pub default: Option<Box<Expression>>,
    pub lhs: Pattern,
    pub rhs: Box<Expression>,
    pub arity: Arity,
    pub is_async: bool,
}

/// Named struct for Pexp_apply variant (boxed for enum size optimization).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpApply {
    pub funct: Box<Expression>,
    pub args: Vec<(ArgLabel, Expression)>,
    pub partial: bool,
    pub transformed_jsx: bool,
}

/// Expression descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExpressionDesc {
    /// Identifier: `x` or `M.x`.
    Pexp_ident(Loc<LidentIdx>),
    /// Constant: `1`, `'a'`, `"hello"`.
    Pexp_constant(Box<Constant>),
    /// Let binding: `let P = E in E'`.
    Pexp_let(Box<(RecFlag, Vec<ValueBinding>, Box<Expression>)>),
    /// Function: `(P) => E`.
    Pexp_fun(Box<PexpFun>),
    /// Application: `E(E1, E2, ...)`.
    Pexp_apply(Box<PexpApply>),
    /// Match: `switch E { | P1 => E1 | ... }`.
    Pexp_match(Box<(Box<Expression>, Vec<Case>)>),
    /// Try: `try E { | P1 => E1 | ... }`.
    Pexp_try(Box<(Box<Expression>, Vec<Case>)>),
    /// Tuple: `(E1, E2, ..., En)`.
    Pexp_tuple(Box<Vec<Expression>>),
    /// Constructor: `C` or `C(E)`.
    Pexp_construct(Loc<LidentIdx>, Option<Box<Expression>>),
    /// Variant: `\`A` or `\`A(E)`.
    Pexp_variant(Box<(Label, Option<Box<Expression>>)>),
    /// Record: `{l1: E1, ..., ln: En}` or `{...E, l1: E1, ...}`.
    Pexp_record(Box<(Vec<ExpressionRecordField>, Option<Box<Expression>>)>),
    /// Field access: `E.l`.
    Pexp_field(Box<Expression>, Loc<LidentIdx>),
    /// Field set: `E.l = E'`.
    Pexp_setfield(Box<(Box<Expression>, Loc<LidentIdx>, Box<Expression>)>),
    /// Array: `[E1, ..., En]`.
    Pexp_array(Box<Vec<Expression>>),
    /// If-then-else: `if E1 { E2 } else { E3 }`.
    Pexp_ifthenelse(Box<(Box<Expression>, Box<Expression>, Option<Box<Expression>>)>),
    /// Sequence: `E1; E2`.
    Pexp_sequence(Box<Expression>, Box<Expression>),
    /// While: `while E1 { E2 }`.
    Pexp_while(Box<Expression>, Box<Expression>),
    /// For: `for i in E1 to E2 { E3 }`.
    Pexp_for(Box<(Pattern, Box<Expression>, Box<Expression>, DirectionFlag, Box<Expression>)>),
    /// Constraint: `(E: T)`.
    Pexp_constraint(Box<(Box<Expression>, CoreType)>),
    /// Coercion: `(E :> T)`.
    Pexp_coerce(Box<(Box<Expression>, Option<CoreType>, CoreType)>),
    /// Send: `E#m`.
    Pexp_send(Box<(Box<Expression>, Loc<Label>)>),
    /// Let module: `{ module M = ME; E }`.
    Pexp_letmodule(Box<(StringLoc, ModuleExpr, Box<Expression>)>),
    /// Let exception: `{ exception C; E }`.
    Pexp_letexception(Box<(ExtensionConstructor, Box<Expression>)>),
    /// Assert: `assert(E)`.
    Pexp_assert(Box<Expression>),
    /// Newtype: `(type t) => E`.
    Pexp_newtype(Box<(StringLoc, Box<Expression>)>),
    /// Pack: `module(ME)`.
    Pexp_pack(Box<ModuleExpr>),
    /// Open: `M.{ E }` or `open M; E`.
    Pexp_open(Box<(OverrideFlag, Loc<LidentIdx>, Box<Expression>)>),
    /// Extension: `[%id]`.
    Pexp_extension(Box<Extension>),
    /// Await: `await E`.
    Pexp_await(Box<Expression>),
    /// JSX element.
    Pexp_jsx_element(Box<JsxElement>),
}

/// A record field in an expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExpressionRecordField {
    /// Field name.
    pub lid: Loc<LidentIdx>,
    /// Expression.
    pub expr: Expression,
    /// Whether this is optional.
    pub opt: bool,
}

/// A case in a match or try expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Case {
    /// Position of the `|` bar.
    pub pc_bar: Option<PosIdx>,
    /// Left-hand side pattern.
    pub pc_lhs: Pattern,
    /// Optional guard expression.
    pub pc_guard: Option<Expression>,
    /// Right-hand side expression.
    pub pc_rhs: Expression,
}

/// A value binding: `let P = E`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueBinding {
    /// Pattern.
    pub pvb_pat: Pattern,
    /// Expression.
    pub pvb_expr: Expression,
    /// Attributes.
    pub pvb_attributes: Attributes,
    /// Location.
    pub pvb_loc: Location,
}

// ============================================================================
// JSX
// ============================================================================

/// A JSX element.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[allow(clippy::large_enum_variant)]
pub enum JsxElement {
    /// Fragment: `<> ... </>`.
    Fragment(JsxFragment),
    /// Unary element: `<div />`.
    Unary(JsxUnaryElement),
    /// Container element: `<div> ... </div>`.
    Container(JsxContainerElement),
}

/// JSX tag name.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum JsxTagName {
    /// Lowercase tag: `div`.
    Lower(String),
    /// Qualified lowercase: `Mod.div`.
    QualifiedLower { path: LidentIdx, name: String },
    /// Uppercase tag (component): `Button`.
    Upper(LidentIdx),
    /// Invalid tag name (for error recovery).
    Invalid(String),
}

/// JSX fragment: `<> children </>`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsxFragment {
    /// Opening `>` position (arena index for sharing with other positions).
    pub opening: crate::parse_arena::PosIdx,
    /// Children.
    pub children: Vec<Expression>,
    /// Closing `</` position (arena index for sharing with other positions).
    pub closing: crate::parse_arena::PosIdx,
}

/// JSX unary element: `<div ... />`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsxUnaryElement {
    /// Tag name.
    pub tag_name: Loc<JsxTagName>,
    /// Props.
    pub props: Vec<JsxProp>,
}

/// JSX container element: `<div ...> children </div>`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsxContainerElement {
    /// Opening tag name.
    pub tag_name_start: Loc<JsxTagName>,
    /// Opening `>` position.
    pub opening_end: PosIdx,
    /// Props.
    pub props: Vec<JsxProp>,
    /// Children.
    pub children: Vec<Expression>,
    /// Closing tag.
    pub closing_tag: Option<JsxClosingTag>,
}

/// JSX closing tag: `</div>`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsxClosingTag {
    /// `</` position.
    pub start: PosIdx,
    /// Tag name.
    pub name: Loc<JsxTagName>,
    /// `>` position.
    pub end: PosIdx,
}

/// JSX prop.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum JsxProp {
    /// Punning: `disabled` or `?disabled`.
    Punning { optional: bool, name: StringLoc },
    /// Value: `onClick={handler}` or `key=?{maybeKey}`.
    Value {
        name: StringLoc,
        optional: bool,
        value: Expression,
    },
    /// Spreading: `{...props}`.
    Spreading { loc: Location, expr: Expression },
}

// ============================================================================
// Modules
// ============================================================================

/// A module expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleExpr {
    /// Module expression description.
    pub pmod_desc: Box<ModuleExprDesc>,
    /// Location.
    pub pmod_loc: Location,
    /// Attributes.
    pub pmod_attributes: Attributes,
}

/// Module expression descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ModuleExprDesc {
    /// Module identifier: `M`.
    Pmod_ident(Loc<LidentIdx>),
    /// Module structure: `{ ... }`.
    Pmod_structure(Box<Vec<StructureItem>>),
    /// Functor: `(X: S) => ME`.
    Pmod_functor(Box<(StringLoc, Option<Box<ModuleType>>, Box<ModuleExpr>)>),
    /// Functor application: `F(M)`.
    Pmod_apply(Box<ModuleExpr>, Box<ModuleExpr>),
    /// Constraint: `(ME: MT)`.
    Pmod_constraint(Box<ModuleExpr>, Box<ModuleType>),
    /// Unpack: `unpack(E)`.
    Pmod_unpack(Box<Expression>),
    /// Extension: `[%id]`.
    Pmod_extension(Box<Extension>),
}

/// A module type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleType {
    /// Module type description.
    pub pmty_desc: Box<ModuleTypeDesc>,
    /// Location.
    pub pmty_loc: Location,
    /// Attributes.
    pub pmty_attributes: Attributes,
}

/// Module type descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ModuleTypeDesc {
    /// Module type identifier: `S`.
    Pmty_ident(Loc<LidentIdx>),
    /// Signature: `{ ... }`.
    Pmty_signature(Box<Vec<SignatureItem>>),
    /// Functor type: `(X: S) => MT`.
    Pmty_functor(Box<(StringLoc, Option<Box<ModuleType>>, Box<ModuleType>)>),
    /// With constraint: `MT with type t = T`.
    Pmty_with(Box<(Box<ModuleType>, Vec<WithConstraint>)>),
    /// Type of: `module type of ME`.
    Pmty_typeof(Box<ModuleExpr>),
    /// Extension: `[%id]`.
    Pmty_extension(Box<Extension>),
    /// Alias: `module M`.
    Pmty_alias(Loc<LidentIdx>),
}

/// With constraint.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum WithConstraint {
    /// Type constraint: `type t = T`.
    Pwith_type(Loc<LidentIdx>, TypeDeclaration),
    /// Module constraint: `module M = M'`.
    Pwith_module(Loc<LidentIdx>, Loc<LidentIdx>),
    /// Type substitution: `type t := T`.
    Pwith_typesubst(Loc<LidentIdx>, TypeDeclaration),
    /// Module substitution: `module M := M'`.
    Pwith_modsubst(Loc<LidentIdx>, Loc<LidentIdx>),
}

// ============================================================================
// Structure and Signature Items
// ============================================================================

/// A structure item.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructureItem {
    /// Structure item description.
    pub pstr_desc: Box<StructureItemDesc>,
    /// Location.
    pub pstr_loc: Location,
}

/// Structure item descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum StructureItemDesc {
    /// Expression: `E`.
    Pstr_eval(Box<(Expression, Attributes)>),
    /// Value: `let P = E`.
    Pstr_value(Box<(RecFlag, Vec<ValueBinding>)>),
    /// Primitive declaration: `external`.
    Pstr_primitive(Box<ValueDescription>),
    /// Type declaration: `type t = ...`.
    Pstr_type(Box<(RecFlag, Vec<TypeDeclaration>)>),
    /// Type extension: `type t += ...`.
    Pstr_typext(Box<TypeExtension>),
    /// Exception: `exception C`.
    Pstr_exception(Box<ExtensionConstructor>),
    /// Module: `module M = ...`.
    Pstr_module(Box<ModuleBinding>),
    /// Recursive modules: `module rec M = ...`.
    Pstr_recmodule(Box<Vec<ModuleBinding>>),
    /// Module type: `module type S = ...`.
    Pstr_modtype(Box<ModuleTypeDeclaration>),
    /// Open: `open M`.
    Pstr_open(Box<OpenDescription>),
    /// Include: `include M`.
    Pstr_include(Box<IncludeDeclaration>),
    /// Attribute: `@@attr`.
    Pstr_attribute(Box<Attribute>),
    /// Extension: `[%%id]`.
    Pstr_extension(Box<(Extension, Attributes)>),
}

/// A signature item.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SignatureItem {
    /// Signature item description.
    pub psig_desc: Box<SignatureItemDesc>,
    /// Location.
    pub psig_loc: Location,
}

/// Signature item descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SignatureItemDesc {
    /// Value: `let x: T`.
    Psig_value(Box<ValueDescription>),
    /// Type declaration: `type t = ...`.
    Psig_type(Box<(RecFlag, Vec<TypeDeclaration>)>),
    /// Type extension: `type t += ...`.
    Psig_typext(Box<TypeExtension>),
    /// Exception: `exception C`.
    Psig_exception(Box<ExtensionConstructor>),
    /// Module: `module M: S`.
    Psig_module(Box<ModuleDeclaration>),
    /// Recursive modules: `module rec M: S`.
    Psig_recmodule(Box<Vec<ModuleDeclaration>>),
    /// Module type: `module type S = ...`.
    Psig_modtype(Box<ModuleTypeDeclaration>),
    /// Open: `open M`.
    Psig_open(Box<OpenDescription>),
    /// Include: `include S`.
    Psig_include(Box<IncludeDescription>),
    /// Attribute: `@@attr`.
    Psig_attribute(Box<Attribute>),
    /// Extension: `[%%id]`.
    Psig_extension(Box<(Extension, Attributes)>),
}

// ============================================================================
// Declarations
// ============================================================================

/// Value description: `external` or `let` in signature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueDescription {
    /// Name.
    pub pval_name: StringLoc,
    /// Type.
    pub pval_type: CoreType,
    /// Primitive names (for externals).
    pub pval_prim: Vec<StrIdx>,
    /// Attributes.
    pub pval_attributes: Attributes,
    /// Location.
    pub pval_loc: Location,
}

/// Type declaration: `type t = ...`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeDeclaration {
    /// Name.
    pub ptype_name: StringLoc,
    /// Type parameters.
    pub ptype_params: Vec<(CoreType, Variance)>,
    /// Constraints.
    pub ptype_cstrs: Vec<(CoreType, CoreType, Location)>,
    /// Kind.
    pub ptype_kind: TypeKind,
    /// Private flag.
    pub ptype_private: PrivateFlag,
    /// Manifest.
    pub ptype_manifest: Option<CoreType>,
    /// Attributes.
    pub ptype_attributes: Attributes,
    /// Location.
    pub ptype_loc: Location,
}

/// Type kind.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeKind {
    /// Abstract type.
    Ptype_abstract,
    /// Variant type.
    Ptype_variant(Vec<ConstructorDeclaration>),
    /// Record type.
    Ptype_record(Vec<LabelDeclaration>),
    /// Open type.
    Ptype_open,
}

/// Constructor declaration.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ConstructorDeclaration {
    /// Name.
    pub pcd_name: StringLoc,
    /// Arguments.
    pub pcd_args: ConstructorArguments,
    /// Return type.
    pub pcd_res: Option<CoreType>,
    /// Location.
    pub pcd_loc: Location,
    /// Attributes.
    pub pcd_attributes: Attributes,
}

/// Constructor arguments.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConstructorArguments {
    /// Tuple arguments: `C(T1, T2)`.
    Pcstr_tuple(Vec<CoreType>),
    /// Record arguments: `C({field: T})`.
    Pcstr_record(Vec<LabelDeclaration>),
}

/// Label declaration (record field).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LabelDeclaration {
    /// Name.
    pub pld_name: StringLoc,
    /// Mutable flag.
    pub pld_mutable: MutableFlag,
    /// Type.
    pub pld_type: CoreType,
    /// Location.
    pub pld_loc: Location,
    /// Attributes.
    pub pld_attributes: Attributes,
    /// Optional flag.
    pub pld_optional: bool,
}

/// Type extension: `type t += ...`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeExtension {
    /// Extended type.
    pub ptyext_path: Loc<LidentIdx>,
    /// Type parameters.
    pub ptyext_params: Vec<(CoreType, Variance)>,
    /// Constructors.
    pub ptyext_constructors: Vec<ExtensionConstructor>,
    /// Private flag.
    pub ptyext_private: PrivateFlag,
    /// Attributes.
    pub ptyext_attributes: Attributes,
}

/// Extension constructor.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExtensionConstructor {
    /// Name.
    pub pext_name: StringLoc,
    /// Kind.
    pub pext_kind: ExtensionConstructorKind,
    /// Location.
    pub pext_loc: Location,
    /// Attributes.
    pub pext_attributes: Attributes,
}

/// Extension constructor kind.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExtensionConstructorKind {
    /// Declaration: `C of T`.
    Pext_decl(ConstructorArguments, Option<CoreType>),
    /// Rebind: `C = D`.
    Pext_rebind(Loc<LidentIdx>),
}

/// Module binding: `module M = ME`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleBinding {
    /// Name.
    pub pmb_name: StringLoc,
    /// Expression.
    pub pmb_expr: ModuleExpr,
    /// Attributes.
    pub pmb_attributes: Attributes,
    /// Location.
    pub pmb_loc: Location,
}

/// Module declaration: `module M: S`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleDeclaration {
    /// Name.
    pub pmd_name: StringLoc,
    /// Type.
    pub pmd_type: ModuleType,
    /// Attributes.
    pub pmd_attributes: Attributes,
    /// Location.
    pub pmd_loc: Location,
}

/// Module type declaration: `module type S = MT`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleTypeDeclaration {
    /// Name.
    pub pmtd_name: StringLoc,
    /// Type.
    pub pmtd_type: Option<ModuleType>,
    /// Attributes.
    pub pmtd_attributes: Attributes,
    /// Location.
    pub pmtd_loc: Location,
}

/// Open description: `open M`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OpenDescription {
    /// Opened module.
    pub popen_lid: Loc<LidentIdx>,
    /// Override flag.
    pub popen_override: OverrideFlag,
    /// Location.
    pub popen_loc: Location,
    /// Attributes.
    pub popen_attributes: Attributes,
}

/// Include declaration: `include ME`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IncludeDeclaration {
    /// Included module.
    pub pincl_mod: ModuleExpr,
    /// Location.
    pub pincl_loc: Location,
    /// Attributes.
    pub pincl_attributes: Attributes,
}

/// Include description: `include S`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IncludeDescription {
    /// Included module type.
    pub pincl_mod: ModuleType,
    /// Location.
    pub pincl_loc: Location,
    /// Attributes.
    pub pincl_attributes: Attributes,
}

// ============================================================================
// Top-level structure
// ============================================================================

/// A complete structure (module implementation).
pub type Structure = Vec<StructureItem>;

/// A complete signature (module interface).
pub type Signature = Vec<SignatureItem>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_arena::ParseArena;

    #[test]
    fn test_arg_label() {
        let mut arena = ParseArena::new();
        let x = arena.intern("x");
        assert!(ArgLabel::Nolabel.is_nolabel());
        assert!(!ArgLabel::Labelled(Located::mknoloc(x)).is_nolabel());
        assert!(ArgLabel::Optional(Located::mknoloc(x)).is_optional());
        assert_eq!(ArgLabel::Labelled(Located::mknoloc(x)).name_idx(), Some(x));
    }

    #[test]
    fn test_constant() {
        let c = Constant::Integer(Cow::Borrowed("42"), None);
        assert!(matches!(c, Constant::Integer(..)));

        let c = Constant::String(Cow::Borrowed("hello"), None);
        assert!(matches!(c, Constant::String(..)));
    }

    #[test]
    fn test_types_are_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Constant>();
        assert_send_sync::<ArgLabel>();
        assert_send_sync::<RecFlag>();
        assert_send_sync::<ClosedFlag>();
    }

    #[test]
    #[ignore]
    fn measure_ast_sizes() {
        use std::mem::size_of;
        println!("\n=== AST Enum Sizes (after boxing) ===");
        println!("Token:              {} bytes", size_of::<crate::parser::token::Token>());
        println!("ExpressionDesc:     {} bytes", size_of::<ExpressionDesc>());
        println!("PatternDesc:        {} bytes", size_of::<PatternDesc>());
        println!("CoreTypeDesc:       {} bytes", size_of::<CoreTypeDesc>());
        println!("StructureItemDesc:  {} bytes", size_of::<StructureItemDesc>());
        println!("SignatureItemDesc:  {} bytes", size_of::<SignatureItemDesc>());
        println!("ModuleExprDesc:     {} bytes", size_of::<ModuleExprDesc>());
        println!("ModuleTypeDesc:     {} bytes", size_of::<ModuleTypeDesc>());
        println!("Payload:            {} bytes", size_of::<Payload>());
        println!("Expression:         {} bytes", size_of::<Expression>());
        println!("Pattern:            {} bytes", size_of::<Pattern>());
        println!("CoreType:           {} bytes", size_of::<CoreType>());
        println!("StructureItem:      {} bytes", size_of::<StructureItem>());
        println!("Constant:           {} bytes", size_of::<Constant>());
        println!("ArgLabel:           {} bytes", size_of::<ArgLabel>());
        println!("ValueBinding:       {} bytes", size_of::<ValueBinding>());
        println!("TypeDeclaration:    {} bytes", size_of::<TypeDeclaration>());
        println!("PexpFun:            {} bytes", size_of::<PexpFun>());
        println!("PexpApply:          {} bytes", size_of::<PexpApply>());
    }
}
