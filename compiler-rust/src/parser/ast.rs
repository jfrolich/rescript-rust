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

use crate::parse_arena::{
    ArityIdx, CoreTypeIdx, ExprIdx, LidentIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, PatIdx,
    PosIdx, StrIdx,
};
use serde::{Deserialize, Serialize};

/// Convert any `Cow<'_, str>` into `Cow<'static, str>` without unsafe.
///
/// Borrowed values are copied into owned strings; owned values are moved through.
#[inline(always)]
pub fn extend_cow_lifetime(cow: Cow<'_, str>) -> Cow<'static, str> {
    match cow {
        Cow::Borrowed(s) => Cow::Owned(s.to_string()),
        Cow::Owned(s) => Cow::Owned(s),
    }
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
/// Uses `Cow<'static, str>` for stable storage across parser and PPX passes.
/// Values may be borrowed (for true `'static` literals) or owned.
pub type Label = Cow<'static, str>;

// ============================================================================
// Constants
// ============================================================================

/// Constant values.
///
/// Uses `Cow<'static, str>` for string data to support shared APIs between parser
/// and PPX-generated nodes. Parser-produced values are normalized to owned strings
/// when needed to keep this representation fully safe.
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
///
/// Uses `Option<Box<Vec<Attribute>>>` internally (8 bytes) instead of `Vec<Attribute>`
/// (24 bytes) since ~95% of AST nodes have empty attributes. This saves 16 bytes
/// per Expression, Pattern, CoreType, and many other nodes (40→24 bytes each).
///
/// The empty case is represented as `None` (no heap allocation at all).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Attributes(
    #[serde(
        serialize_with = "serialize_attributes",
        deserialize_with = "deserialize_attributes"
    )]
    pub(crate) Option<Box<Vec<Attribute>>>,
);

fn serialize_attributes<S: serde::Serializer>(
    attrs: &Option<Box<Vec<Attribute>>>,
    s: S,
) -> Result<S::Ok, S::Error> {
    match attrs {
        None => Vec::<Attribute>::new().serialize(s),
        Some(v) => v.serialize(s),
    }
}

fn deserialize_attributes<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<Option<Box<Vec<Attribute>>>, D::Error> {
    let v = Vec::<Attribute>::deserialize(d)?;
    if v.is_empty() {
        Ok(None)
    } else {
        Ok(Some(Box::new(v)))
    }
}

impl Attributes {
    /// Create an empty attributes list (no heap allocation).
    #[inline(always)]
    pub fn new() -> Self {
        Self(None)
    }

    /// Create attributes from a Vec. If the vec is empty, stores None.
    #[inline]
    pub fn from_vec(v: Vec<Attribute>) -> Self {
        if v.is_empty() {
            Self(None)
        } else {
            Self(Some(Box::new(v)))
        }
    }

    /// Check if this attributes list is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Get the number of attributes.
    #[inline]
    pub fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(v) => v.len(),
        }
    }

    /// Get a slice of the attributes.
    #[inline]
    pub fn as_slice(&self) -> &[Attribute] {
        match &self.0 {
            None => &[],
            Some(v) => v.as_slice(),
        }
    }

    /// Get an iterator over the attributes.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, Attribute> {
        self.as_slice().iter()
    }

    /// Push an attribute, allocating the inner Vec if needed.
    #[inline]
    pub fn push(&mut self, attr: Attribute) {
        match &mut self.0 {
            None => {
                self.0 = Some(Box::new(vec![attr]));
            }
            Some(v) => v.push(attr),
        }
    }

    /// Insert an attribute at the given position.
    #[inline]
    pub fn insert(&mut self, index: usize, attr: Attribute) {
        match &mut self.0 {
            None => {
                assert_eq!(index, 0);
                self.0 = Some(Box::new(vec![attr]));
            }
            Some(v) => v.insert(index, attr),
        }
    }

    /// Extend with attributes from an iterator.
    pub fn extend<I: IntoIterator<Item = Attribute>>(&mut self, iter: I) {
        let mut iter = iter.into_iter();
        if let Some(first) = iter.next() {
            match &mut self.0 {
                None => {
                    let mut v = vec![first];
                    v.extend(iter);
                    self.0 = Some(Box::new(v));
                }
                Some(v) => {
                    v.push(first);
                    v.extend(iter);
                }
            }
        }
    }

    /// Concatenate this attributes list with another, returning a new one.
    /// `self` attrs come first, `other` attrs come after.
    pub fn concat(self, other: Attributes) -> Attributes {
        match (self.0, other.0) {
            (None, None) => Attributes(None),
            (Some(v), None) => Attributes(Some(v)),
            (None, Some(v)) => Attributes(Some(v)),
            (Some(mut a), Some(b)) => {
                a.extend(b.into_iter());
                Attributes(Some(a))
            }
        }
    }

    /// Get the inner Vec mutably, allocating if needed.
    pub fn as_mut_vec(&mut self) -> &mut Vec<Attribute> {
        if self.0.is_none() {
            self.0 = Some(Box::new(Vec::new()));
        }
        self.0.as_mut().unwrap()
    }

    /// Convert to a Vec, consuming self.
    pub fn into_vec(self) -> Vec<Attribute> {
        match self.0 {
            None => Vec::new(),
            Some(v) => *v,
        }
    }
}

impl Default for Attributes {
    #[inline(always)]
    fn default() -> Self {
        Self(None)
    }
}

impl std::ops::Deref for Attributes {
    type Target = [Attribute];
    #[inline]
    fn deref(&self) -> &[Attribute] {
        self.as_slice()
    }
}

impl From<Vec<Attribute>> for Attributes {
    #[inline]
    fn from(v: Vec<Attribute>) -> Self {
        Self::from_vec(v)
    }
}

impl std::iter::FromIterator<Attribute> for Attributes {
    fn from_iter<I: IntoIterator<Item = Attribute>>(iter: I) -> Self {
        Self::from_vec(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a Attributes {
    type Item = &'a Attribute;
    type IntoIter = std::slice::Iter<'a, Attribute>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut Attributes {
    type Item = &'a mut Attribute;
    type IntoIter = std::slice::IterMut<'a, Attribute>;
    fn into_iter(self) -> Self::IntoIter {
        match &mut self.0 {
            None => [].iter_mut(),
            Some(v) => v.iter_mut(),
        }
    }
}

impl IntoIterator for Attributes {
    type Item = Attribute;
    type IntoIter = std::vec::IntoIter<Attribute>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

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
    PTyp(CoreTypeIdx),
    /// Pattern payload with optional guard: `[@@attr? pattern when guard]`.
    PPat(Box<(PatIdx, Option<ExprIdx>)>),
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
    /// Argument type (arena index).
    pub typ: CoreTypeIdx,
}

/// Core type descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CoreTypeDesc {
    /// Any type: `_`.
    Ptyp_any,
    /// Type variable: `'a`.
    Ptyp_var(Box<Cow<'static, str>>),
    /// Arrow type: `T1 -> T2`.
    Ptyp_arrow(Box<(Box<TypeArg>, CoreTypeIdx, Arity)>),
    /// Tuple type: `(T1, T2, ..., Tn)`.
    Ptyp_tuple(Box<Vec<CoreTypeIdx>>),
    /// Type constructor: `tconstr` or `T tconstr` or `(T1, ..., Tn) tconstr`.
    Ptyp_constr(Box<(Loc<LidentIdx>, Vec<CoreTypeIdx>)>),
    /// Object type: `{. field: T, ... }`.
    Ptyp_object(Box<(Vec<ObjectField>, ClosedFlag)>),
    /// Type alias: `T as 'a`.
    Ptyp_alias(Box<(CoreTypeIdx, Cow<'static, str>)>),
    /// Polymorphic variant: `[> \`A | \`B ]`.
    Ptyp_variant(Box<(Vec<RowField>, ClosedFlag, Option<Vec<Label>>)>),
    /// Polymorphic type: `'a 'b. T`.
    Ptyp_poly(Box<(Vec<StringLoc>, CoreTypeIdx)>),
    /// Package type: `module S`.
    Ptyp_package(Box<PackageType>),
    /// Extension: `[%id]`.
    Ptyp_extension(Box<Extension>),
}

/// Package type: `module S with type t = T`.
pub type PackageType = (Loc<LidentIdx>, Vec<(Loc<LidentIdx>, CoreTypeIdx)>);

/// Row field in a polymorphic variant.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RowField {
    /// Tag: `\`A of T1 & T2`.
    Rtag(Loc<Label>, Attributes, bool, Vec<CoreTypeIdx>),
    /// Inherited type: `[T]`.
    Rinherit(CoreTypeIdx),
}

/// Object field.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ObjectField {
    /// Named field: `name: T`.
    Otag(StringLoc, Attributes, CoreTypeIdx),
    /// Inherited type.
    Oinherit(CoreTypeIdx),
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
    Ppat_alias(PatIdx, StringLoc),
    /// Constant: `1`, `'a'`, `"hello"`.
    Ppat_constant(Box<Constant>),
    /// Interval: `'a'..'z'`.
    Ppat_interval(Box<(Constant, Constant)>),
    /// Tuple: `(P1, P2, ..., Pn)`.
    Ppat_tuple(Box<Vec<PatIdx>>),
    /// Constructor: `C` or `C(P)`.
    Ppat_construct(Loc<LidentIdx>, Option<PatIdx>),
    /// Variant: `\`A` or `\`A(P)`.
    Ppat_variant(Box<(Label, Option<PatIdx>)>),
    /// Record: `{l1: P1, ..., ln: Pn}`.
    /// Record: `{l1: P1, ...}`, closed flag, and an optional `...Type.t as name` rest
    /// (compiler/ml/parsetree.ml:164-168).
    Ppat_record(Box<(Vec<PatternRecordField>, ClosedFlag, Option<RecordPatRest>)>),
    /// Array: `[P1, ..., Pn]`.
    Ppat_array(Box<Vec<PatIdx>>),
    /// Or-pattern: `P1 | P2`.
    Ppat_or(PatIdx, PatIdx),
    /// Constraint: `(P: T)`.
    Ppat_constraint(Box<(PatIdx, CoreTypeIdx)>),
    /// Type pattern: `#tconstr`.
    Ppat_type(Loc<LidentIdx>),
    /// Unpack: `module(P)`.
    Ppat_unpack(StringLoc),
    /// Exception: `exception P`.
    Ppat_exception(PatIdx),
    /// Extension: `[%id]`.
    Ppat_extension(Box<Extension>),
    /// Open: `M.(P)`.
    Ppat_open(Loc<LidentIdx>, PatIdx),
}

/// A record field in a pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PatternRecordField {
    /// Field name.
    pub lid: Loc<LidentIdx>,
    /// Pattern (arena index).
    pub pat: PatIdx,
    /// Whether this is optional.
    pub opt: bool,
}

/// Record-rest pattern binding (`...Type.t as name`).
/// Mirrors OCaml compiler/ml/parsetree.ml:164-168 `record_pat_rest`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RecordPatRest {
    /// Location of the whole `...rest` row.
    pub rest_loc: Location,
    /// Name of the bound rest variable.
    pub rest_name: StringLoc,
    /// Type annotation from `...Type.t as name`.
    pub rest_type: Option<CoreTypeIdx>,
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

/// A source-level function parameter. N-ary function nodes store their full
/// parameter list in `ParseArena`'s sparse function-shape side table.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunParam {
    pub p_attrs: Attributes,
    pub p_lbl: ArgLabel,
    pub p_default: Option<ExprIdx>,
    pub p_pat: PatIdx,
}

/// Compact inline payload for `Pexp_fun`.
///
/// Recursive expression data remains arena-indexed. The parser-facing n-ary
/// shape (`newtypes`, `params`, `body`) is kept in a sparse side table keyed by
/// the owning `ExprIdx`; these fields retain the first parameter as compact
/// fallback data for ASTs read from the frozen v0 PPX format.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpFun {
    pub arg_label: ArgLabel,
    pub default: Option<ExprIdx>,
    pub lhs: PatIdx,
    pub rhs: ExprIdx,
    pub arity: Arity,
    pub is_async: bool,
}

/// Named struct for Pexp_apply variant (boxed for enum size optimization).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpApply {
    pub funct: ExprIdx,
    pub args: Vec<(ArgLabel, ExprIdx)>,
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
    Pexp_let(Box<(RecFlag, Vec<ValueBinding>, ExprIdx)>),
    /// Function: `(P) => E`.
    Pexp_fun(Box<PexpFun>),
    /// Application: `E(E1, E2, ...)`.
    Pexp_apply(Box<PexpApply>),
    /// Match: `switch E { | P1 => E1 | ... }`.
    Pexp_match(Box<(ExprIdx, Vec<Case>)>),
    /// Try: `try E { | P1 => E1 | ... }`.
    Pexp_try(Box<(ExprIdx, Vec<Case>)>),
    /// Tuple: `(E1, E2, ..., En)`.
    Pexp_tuple(Box<Vec<ExprIdx>>),
    /// Constructor: `C` or `C(E)`.
    Pexp_construct(Loc<LidentIdx>, Option<ExprIdx>),
    /// Variant: `\`A` or `\`A(E)`.
    Pexp_variant(Box<(Label, Option<ExprIdx>)>),
    /// Record: `{l1: E1, ..., ln: En}` or `{...E, l1: E1, ...}`.
    Pexp_record(Box<(Vec<ExpressionRecordField>, Option<ExprIdx>)>),
    /// Field access: `E.l`.
    Pexp_field(ExprIdx, Loc<LidentIdx>),
    /// Field set: `E.l = E'`.
    Pexp_setfield(Box<(ExprIdx, Loc<LidentIdx>, ExprIdx)>),
    /// Array: `[E1, ..., En]`.
    Pexp_array(Box<Vec<ExprIdx>>),
    /// If-then-else: `if E1 { E2 } else { E3 }`.
    Pexp_ifthenelse(Box<(ExprIdx, ExprIdx, Option<ExprIdx>)>),
    /// Sequence: `E1; E2`.
    Pexp_sequence(ExprIdx, ExprIdx),
    /// `break` (upstream #8348). Exits the nearest enclosing loop.
    Pexp_break,
    /// `continue` (upstream #8348). Skips to the next iteration of the
    /// nearest enclosing loop.
    Pexp_continue,
    /// While: `while E1 { E2 }`.
    Pexp_while(ExprIdx, ExprIdx),
    /// For: `for i in E1 to E2 { E3 }`.
    Pexp_for(Box<(PatIdx, ExprIdx, ExprIdx, DirectionFlag, ExprIdx)>),
    /// For-of: `for pat of iterable { body }` (upstream #7887).
    Pexp_for_of(Box<(PatIdx, ExprIdx, ExprIdx)>),
    /// For-await-of: `for await pat of asyncIterable { body }` (upstream #7887).
    Pexp_for_await_of(Box<(PatIdx, ExprIdx, ExprIdx)>),
    /// Constraint: `(E: T)`.
    Pexp_constraint(Box<(ExprIdx, CoreTypeIdx)>),
    /// Coercion: `(E :> T)`.
    Pexp_coerce(Box<(ExprIdx, Option<CoreTypeIdx>, CoreTypeIdx)>),
    /// Send: `E#m`.
    Pexp_send(Box<(ExprIdx, Loc<Label>)>),
    /// Let module: `{ module M = ME; E }`.
    Pexp_letmodule(Box<(StringLoc, ModExprIdx, ExprIdx)>),
    /// Let exception: `{ exception C; E }`.
    Pexp_letexception(Box<(ExtensionConstructor, ExprIdx)>),
    /// Assert: `assert(E)`.
    Pexp_assert(ExprIdx),
    /// Newtype: `(type t) => E`.
    Pexp_newtype(Box<(StringLoc, ExprIdx)>),
    /// Pack: `module(ME)`.
    Pexp_pack(ModExprIdx),
    /// Open: `M.{ E }` or `open M; E`.
    Pexp_open(Box<(OverrideFlag, Loc<LidentIdx>, ExprIdx)>),
    /// Extension: `[%id]`.
    Pexp_extension(Box<Extension>),
    /// Await: `await E`.
    Pexp_await(ExprIdx),
    /// JSX element.
    Pexp_jsx_element(Box<JsxElement>),
    /// Inline for: `inline for pat in collection { body }` (comptime loop unrolling).
    Pexp_inline_for(Box<(PatIdx, ExprIdx, ExprIdx)>),
    /// Comptime type info: `@typeInfo(T)` — returns type information for T.
    Pexp_comptime_typeinfo(CoreTypeIdx),
    /// Comptime field access: `@field(value, "name")` — accesses a field by comptime-known name.
    Pexp_comptime_field(Box<(ExprIdx, ExprIdx)>),
    /// Comptime compile error: `@compileError("msg")` — compile-time error.
    Pexp_comptime_compile_error(ExprIdx),
    /// Comptime type name: `@typeName(T)` — returns the type name as a string.
    Pexp_comptime_typename(CoreTypeIdx),
    /// Comptime record builder: `@record(TypeName, arrayOfFieldSpecs)`.
    /// The array contains @field({name: comptimeName, value: runtimeExpr}) items.
    /// Can be a literal array or an inline for expression.
    Pexp_comptime_record(Box<(CoreTypeIdx, ExprIdx)>),
    /// Comptime variant builder: `@variant(TypeName, "CtorName", payload?)`.
    /// Builds a typed variant constructor from comptime-known constructor name.
    Pexp_comptime_variant(Box<(CoreTypeIdx, ExprIdx, Option<ExprIdx>)>),
    /// Type-level variant builder: `@buildVariant(arrayOfCases)`.
    /// Produces a variant TYPE declaration, not a value.
    /// The array must contain @variantCase({...}) elements.
    Pexp_comptime_build_variant(ExprIdx),
    /// Type-level variant case descriptor: `@variantCase({name: "Name", as_?: "..."})`.
    /// Evaluates to a comptime record describing one constructor.
    Pexp_comptime_variant_case(ExprIdx),
    /// Type-level record builder: `@buildRecord(arrayOfFields)`.
    /// Produces a record TYPE declaration. Array contains @recordField({...}).
    Pexp_comptime_build_record(ExprIdx),
    /// Type-level record field descriptor: `@recordField({name, typ, optional?})`.
    Pexp_comptime_record_field(ExprIdx),
}

/// A record field in an expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExpressionRecordField {
    /// Field name.
    pub lid: Loc<LidentIdx>,
    /// Expression (arena index).
    pub expr: ExprIdx,
    /// Whether this is optional.
    pub opt: bool,
}

/// A case in a match or try expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Case {
    /// Position of the `|` bar.
    pub pc_bar: Option<PosIdx>,
    /// Left-hand side pattern (arena index).
    pub pc_lhs: PatIdx,
    /// Optional guard expression (arena index).
    pub pc_guard: Option<ExprIdx>,
    /// Right-hand side expression (arena index).
    pub pc_rhs: ExprIdx,
}

/// A locally abstract value-binding constraint: `: type a. t`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueConstraint {
    /// Locally abstract type names, in source order.
    pub pvc_newtypes: Vec<StringLoc>,
    /// The constrained expression type.
    pub pvc_type: CoreTypeIdx,
    /// Rust-side cached polymorphic pattern used by typecore; not part of the wire record.
    pub(crate) pvc_pattern: Option<PatIdx>,
    /// Rust-side cached legacy wrapper used to reuse the existing newtype typer.
    pub(crate) pvc_expression: Option<ExprIdx>,
}

/// A value binding: `let P = E`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueBinding {
    /// Pattern (arena index).
    pub pvb_pat: PatIdx,
    /// Expression (arena index).
    pub pvb_expr: ExprIdx,
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
    /// Children (arena indices).
    pub children: Vec<ExprIdx>,
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
    /// Children (arena indices).
    pub children: Vec<ExprIdx>,
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
        value: ExprIdx,
    },
    /// Spreading: `{...props}`.
    Spreading { loc: Location, expr: ExprIdx },
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
    Pmod_functor(Box<(StringLoc, Option<ModTypeIdx>, ModExprIdx)>),
    /// Functor application: `F(M)`.
    Pmod_apply(ModExprIdx, ModExprIdx),
    /// Constraint: `(ME: MT)`.
    Pmod_constraint(ModExprIdx, ModTypeIdx),
    /// Unpack: `unpack(E)`.
    Pmod_unpack(ExprIdx),
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
    Pmty_functor(Box<(StringLoc, Option<ModTypeIdx>, ModTypeIdx)>),
    /// With constraint: `MT with type t = T`.
    Pmty_with(Box<(ModTypeIdx, Vec<WithConstraint>)>),
    /// Type of: `module type of ME`.
    Pmty_typeof(ModExprIdx),
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
    Pstr_eval(Box<(ExprIdx, Attributes)>),
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

/// `Parsetree.primitive_repr`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PrimitiveRepr {
    /// As written in the source: an intrinsic (`"%identity"`, `"#raw_expr"`)
    /// or the not-yet-digested JS name of an FFI external.
    PrimName(StrIdx),
    /// Produced by the frontend digestion of an FFI external's attributes;
    /// never observed by external PPXes, which run before digestion.
    PrimFfi {
        name: String,
        spec: Box<crate::types::external_ffi_types::ExternalFfi>,
    },
    /// An `@inline(<literal>)` value declaration: a compile-time constant.
    PrimInlineConst(Box<crate::types::external_ffi_types::InlineConst>),
}

impl PrimitiveRepr {
    /// `Ffi_debug.primitive_repr`: the strings the sexp parity printers
    /// show for a primitive.
    pub fn debug_strings(&self, arena: &crate::parse_arena::ParseArena) -> Vec<String> {
        use crate::types::external_ffi_types::debug;
        match self {
            PrimitiveRepr::PrimName(s) => vec![arena.get_string(*s).to_string()],
            PrimitiveRepr::PrimFfi { name, spec } => vec![name.clone(), debug::spec(spec)],
            PrimitiveRepr::PrimInlineConst(c) => vec![debug::inline_const(c)],
        }
    }
}

/// Value description: `external` or `let` in signature.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ValueDescription {
    /// Name.
    pub pval_name: StringLoc,
    /// Type (arena index).
    pub pval_type: CoreTypeIdx,
    /// The primitive (for externals): `None` for `val x: T`.
    pub pval_prim: Option<PrimitiveRepr>,
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
    pub ptype_params: Vec<(CoreTypeIdx, Variance)>,
    /// Constraints.
    pub ptype_cstrs: Vec<(CoreTypeIdx, CoreTypeIdx, Location)>,
    /// Kind.
    pub ptype_kind: TypeKind,
    /// Private flag.
    pub ptype_private: PrivateFlag,
    /// Manifest (arena index).
    pub ptype_manifest: Option<CoreTypeIdx>,
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
    /// Return type (arena index).
    pub pcd_res: Option<CoreTypeIdx>,
    /// Location.
    pub pcd_loc: Location,
    /// Attributes.
    pub pcd_attributes: Attributes,
}

/// Constructor arguments.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConstructorArguments {
    /// Tuple arguments: `C(T1, T2)`.
    Pcstr_tuple(Vec<CoreTypeIdx>),
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
    /// Type (arena index).
    pub pld_type: CoreTypeIdx,
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
    pub ptyext_params: Vec<(CoreTypeIdx, Variance)>,
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
    Pext_decl(ConstructorArguments, Option<CoreTypeIdx>),
    /// Rebind: `C = D`.
    Pext_rebind(Loc<LidentIdx>),
}

/// Module binding: `module M = ME`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModuleBinding {
    /// Name.
    pub pmb_name: StringLoc,
    /// Expression (arena index).
    pub pmb_expr: ModExprIdx,
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
    /// Type (arena index).
    pub pmd_type: ModTypeIdx,
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
    /// Type (arena index).
    pub pmtd_type: Option<ModTypeIdx>,
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
    /// Included module (arena index).
    pub pincl_mod: ModExprIdx,
    /// Location.
    pub pincl_loc: Location,
    /// Attributes.
    pub pincl_attributes: Attributes,
}

/// Include description: `include S`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct IncludeDescription {
    /// Included module type (arena index).
    pub pincl_mod: ModTypeIdx,
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
        println!(
            "Token:              {} bytes",
            size_of::<crate::parser::token::Token>()
        );
        println!("ExpressionDesc:     {} bytes", size_of::<ExpressionDesc>());
        println!("PatternDesc:        {} bytes", size_of::<PatternDesc>());
        println!("CoreTypeDesc:       {} bytes", size_of::<CoreTypeDesc>());
        println!(
            "StructureItemDesc:  {} bytes",
            size_of::<StructureItemDesc>()
        );
        println!(
            "SignatureItemDesc:  {} bytes",
            size_of::<SignatureItemDesc>()
        );
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
        println!("Case:               {} bytes", size_of::<Case>());
        println!(
            "ConstructorDecl:    {} bytes",
            size_of::<ConstructorDeclaration>()
        );
        println!(
            "ExprRecordField:    {} bytes",
            size_of::<ExpressionRecordField>()
        );
        println!(
            "PatRecordField:     {} bytes",
            size_of::<PatternRecordField>()
        );
        println!("TypeArg:            {} bytes", size_of::<TypeArg>());
        println!("ModuleBinding:      {} bytes", size_of::<ModuleBinding>());
        println!(
            "ModuleDeclaration:  {} bytes",
            size_of::<ModuleDeclaration>()
        );
        println!(
            "LabelDeclaration:   {} bytes",
            size_of::<LabelDeclaration>()
        );
        println!("JsxProp:            {} bytes", size_of::<JsxProp>());
    }
}
