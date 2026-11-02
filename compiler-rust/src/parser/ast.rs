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

use crate::string_literal::StringLiteral;

/// Convert any `Cow<'_, str>` into an owned `Cow<'static, str>`.
///
/// Borrowed values are copied into owned strings; owned values are moved through.
#[inline(always)]
pub fn extend_cow_lifetime(cow: Cow<'_, str>) -> Cow<'static, str> {
    Cow::Owned(cow.into_owned())
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
/// This is an arena index instead of an enum. Arity values are stored in the
/// ParseArena without content deduplication:
/// - `arena.push_arity(None)` → fresh ArityIdx for an "Unknown" arity
/// - `arena.push_arity(Some(n))` → fresh ArityIdx for a "Full(n)" arity
///
/// Marshal sharing follows index identity. Literal arities that OCaml shares
/// as one constant use the arena's pre-allocated static arity indices.
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

/// OCaml `type_declaration_origin`: inline records in field and external
/// types are lifted to named declarations for type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeDeclarationOrigin {
    Declared,
    Inline_record_definition,
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
    /// An ordinary character literal (OCaml `Pconst_char {source; semantic}`):
    /// `source` is the text between the single quotes as scanned, kept for
    /// printing; `semantic` is the decoded Unicode code point.
    Char {
        source: Cow<'static, str>,
        semantic: i32,
    },
    /// An ordinary double-quoted string literal (OCaml `Pconst_string`).
    String(StringLiteral),
    /// Float constant with optional suffix.
    Float(Cow<'static, str>, Option<char>),
}

impl Constant {
    /// OCaml `Ast_helper.Const.string`: a string constant with canonical
    /// source spelling for a semantic value.
    pub fn string(semantic: &str) -> Constant {
        Constant::String(crate::string_literal::string_from_semantic(semantic))
    }

    /// OCaml `Ast_helper.Const.char`.
    pub fn char(semantic: i32) -> Constant {
        Constant::Char {
            source: Cow::Owned(crate::string_literal::encode_char_source(semantic)),
            semantic,
        }
    }
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
/// Every constructor and mutator keeps the invariant that `Some` never holds
/// an empty Vec, which `is_empty` and the derived `PartialEq` rely on.
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
                let mut v = Vec::with_capacity(1);
                v.insert(index, attr);
                self.0 = Some(Box::new(v));
            }
            Some(v) => v.insert(index, attr),
        }
    }

    /// Remove and return the attribute at the given position.
    pub fn remove(&mut self, index: usize) -> Attribute {
        let v = self.0.as_mut().expect("remove from empty attributes");
        let attr = v.remove(index);
        if v.is_empty() {
            self.0 = None;
        }
        attr
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
                a.extend(*b);
                Attributes(Some(a))
            }
        }
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
    /// Argument type (arena index). For a fixed argument this is the bare
    /// `_` it is written with, located at that `_` (what OCaml
    /// `Ast_external_process.arg_parts` types a `Parg_fixed` as).
    pub typ: CoreTypeIdx,
    /// OCaml `Parg_fixed {value; loc}`: an external argument written
    /// `@as(value) _`, whose value is fixed by the binding. `None` is
    /// `Parg_type`.
    pub fixed: Option<Box<FixedArg>>,
}

/// The payload of OCaml `Parg_fixed`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FixedArg {
    /// The fixed value as written.
    pub value: FixedValue,
    /// The location of the value: the `@as` payload.
    pub value_loc: LocIdx,
    /// The whole argument, from `@as` to `_`.
    pub loc: LocIdx,
}

/// OCaml `Parsetree.fixed_value`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum FixedValue {
    /// `@as(1)`: the integer literal's source.
    Int(StringLoc),
    /// `@as("s")`.
    String(StringLiteral),
    /// `@as(`s`)`: the source between the backquotes.
    Template(StringLoc),
    /// `@as(json`{}`)`: the JavaScript source between the backquotes.
    Json(StringLoc),
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

/// Constructor or variant arguments: the source list and the span of its
/// parentheses (parsetree.ml `Pexp_construct`/`Ppat_construct`).
pub fn ctor_args<T>(txt: Vec<T>, loc: LocIdx) -> Box<Loc<Vec<T>>> {
    Box::new(Located { txt, loc })
}

/// One payload group of a polymorphic variant tag type.
pub type VariantTypeArgs = Loc<Vec<CoreTypeIdx>>;

/// Row field in a polymorphic variant.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RowField {
    /// Tag: `\`A of T1 & T2`. Each payload group keeps the source argument
    /// list and the span of its parentheses: `#A(T1, T2)` is one group
    /// `[T1, T2]`, `#A((T1, T2))` one group `[Ptyp_tuple [T1, T2]]`
    /// (parsetree.ml `variant_type_args`).
    Rtag(Loc<Label>, Attributes, bool, Vec<VariantTypeArgs>),
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
    /// Constructor: `C`, `C(P)` or `C(P1, ..., Pn)`. The arguments are the
    /// source list, located at the argument parentheses (or the enclosing
    /// node when there are none); see parsetree.ml `Ppat_construct`.
    Ppat_construct(Loc<LidentIdx>, Box<Loc<Vec<PatIdx>>>),
    /// Variant: `#A`, `#A(P)` or `#A(P1, ..., Pn)`.
    Ppat_variant(Box<(Label, Loc<Vec<PatIdx>>)>),
    /// Record: `{l1: P1, ..., ln: Pn}`.
    /// Record: `{l1: P1, ...}`, closed flag, and an optional `...Type.t as name` rest
    /// (compiler/ml/parsetree.ml:164-168).
    Ppat_record(Box<(Vec<PatternRecordField>, ClosedFlag, Option<RecordPatRest>)>),
    /// Array: `[P1, ..., Pn]`.
    Ppat_array(Box<Vec<PatIdx>>),
    /// Dict: `dict{"k1": P1, "k2": ?P2}`.
    Ppat_dict(Box<Vec<DictPatternEntry>>),
    /// Or-pattern: `P1 | P2`.
    Ppat_or(PatIdx, PatIdx),
    /// Constraint: `(P: T)`.
    Ppat_constraint(Box<(PatIdx, CoreTypeIdx)>),
    /// Type pattern: `#tconstr`.
    Ppat_type(Loc<LidentIdx>),
    /// Variant spread: `...t`.
    Ppat_variant_spread(Loc<LidentIdx>),
    /// Unpack: `module(P)`.
    Ppat_unpack(StringLoc),
    /// Exception: `exception P`.
    Ppat_exception(PatIdx),
    /// Extension: `[%id]`.
    Ppat_extension(Box<Extension>),
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

/// An entry of a dict pattern (compiler/ml/parsetree.ml `dict_pattern_entry`):
/// `"k": P`, or `"k": ?P` when `pdp_optional`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DictPatternEntry {
    pub pdp_key: StringLoc,
    pub pdp_pattern: PatIdx,
    pub pdp_optional: bool,
}

/// An entry of a dict literal (compiler/ml/parsetree.ml `dict_entry`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DictEntry {
    /// `"k": E`
    Pdict_entry(StringLoc, ExprIdx),
    /// `...E`
    Pdict_spread(ExprIdx),
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

/// OCaml `Pexp_template {source_segments; values}`: an ordinary backquoted
/// expression. There is always one more source segment than value.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpTemplate {
    pub source_segments: Vec<StringLoc>,
    pub values: Vec<ExprIdx>,
}

/// OCaml `Pexp_raw {kind; name_loc; source}`. `name_loc` is the location of
/// `%raw` or `%ffi`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpRaw {
    pub kind: RawKind,
    pub name_loc: LocIdx,
    pub source: RawSource,
}

/// OCaml `Pstr_raw {name_loc; source; attrs}`. `name_loc` is the location of
/// `%%raw`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PstrRaw {
    pub name_loc: LocIdx,
    pub source: RawSource,
    pub attrs: Attributes,
}

/// OCaml `Parsetree.raw_kind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RawKind {
    /// `%raw`: any JavaScript expression.
    Expression,
    /// `%ffi`: a JavaScript function.
    Function,
}

/// OCaml `Parsetree.raw_source`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RawSource {
    /// `%raw("...")`: the JavaScript source, which is also the text between
    /// the quotes. The location is the string literal's.
    String(StringLoc),
    /// `%raw(`...`)`: the template source as written, from which
    /// `String_literal.decode_raw_template_source` gives the JavaScript
    /// source.
    Template(StringLoc),
}

/// OCaml `Pexp_tagged_template {tag; raw_sources; values}`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpTaggedTemplate {
    pub tag: ExprIdx,
    pub raw_sources: Vec<StringLoc>,
    pub values: Vec<ExprIdx>,
}

/// OCaml `Pexp_braces {expr; braces_loc}`: explicit braces around an
/// expression. The node's `pexp_loc` stays on the enclosed expression;
/// `braces_loc` covers the delimiters for printing.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpBraces {
    pub expr: ExprIdx,
    pub braces_loc: Location,
}

/// OCaml `Pexp_regexp {pattern; flags}`: literal source without delimiters.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PexpRegexp {
    pub pattern: String,
    pub flags: String,
}

/// Expression descriptions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExpressionDesc {
    /// Explicit braces: `{E}`.
    Pexp_braces(Box<PexpBraces>),
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
    /// Constructor: `C`, `C(E)` or `C(E1, ..., En)`, with the source argument
    /// list located at its parentheses (parsetree.ml `Pexp_construct`).
    Pexp_construct(Loc<LidentIdx>, Box<Loc<Vec<ExprIdx>>>),
    /// Variant: `#A`, `#A(E)` or `#A(E1, ..., En)`.
    Pexp_variant(Box<(Label, Loc<Vec<ExprIdx>>)>),
    /// Record: `{l1: E1, ..., ln: En}` or `{...E, l1: E1, ...}`.
    Pexp_record(Box<(Vec<ExpressionRecordField>, Option<ExprIdx>)>),
    /// Field access: `E.l`.
    Pexp_field(ExprIdx, Loc<LidentIdx>),
    /// Field set: `E.l = E'`.
    Pexp_setfield(Box<(ExprIdx, Loc<LidentIdx>, ExprIdx)>),
    /// Array: `[E1, ..., En]`.
    Pexp_array(Box<Vec<ExprIdx>>),
    /// Dict: `dict{"k1": E1, ...E2}`.
    Pexp_dict(Box<Vec<DictEntry>>),
    /// If-then-else: `if E1 { E2 } else { E3 }`.
    Pexp_ifthenelse(Box<(ExprIdx, ExprIdx, Option<ExprIdx>)>),
    /// Ternary: `E1 ? E2 : E3`.
    Pexp_ternary(Box<(ExprIdx, ExprIdx, ExprIdx)>),
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
    /// Regexp literal: `/pattern/flags`.
    Pexp_regexp(Box<PexpRegexp>),
    /// Constraint: `(E: T)`.
    Pexp_constraint(Box<(ExprIdx, CoreTypeIdx)>),
    /// Coercion: `(E :> T)`.
    Pexp_coerce(Box<(ExprIdx, Option<CoreTypeIdx>, CoreTypeIdx)>),
    /// Object property read: `obj["x"]`.
    Pexp_object_get(Box<(ExprIdx, Loc<Label>)>),
    /// Object property write: `obj["x"] = v`.
    Pexp_object_set(Box<(ExprIdx, Loc<Label>, ExprIdx)>),
    /// Object literal: `{"a": 1, "b": true}`.
    Pexp_object_literal(Box<Vec<(Loc<Label>, ExprIdx)>>),
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
    /// `%raw("...")` and `%ffi("...")`: JavaScript source.
    Pexp_raw(Box<PexpRaw>),
    /// Await: `await E`.
    Pexp_await(ExprIdx),
    /// An ordinary backquoted template: `` `a ${b}` ``.
    Pexp_template(Box<PexpTemplate>),
    /// A JavaScript tagged template: ``sql`id = ${id}` ``.
    Pexp_tagged_template(Box<PexpTaggedTemplate>),
    /// JSX element.
    Pexp_jsx_element(Box<JsxElement>),
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
    /// The `@react.component` annotation, taken out of the attributes when
    /// the binding is built (`Ast_helper.Vb.mk`).
    pub pvb_jsx_component: Option<Box<JsxComponent>>,
    /// Attributes.
    pub pvb_attributes: Attributes,
    /// Location.
    pub pvb_loc: Location,
}

/// OCaml `Parsetree.jsx_component`: a JSX component definition,
/// `@react.component`, `@jsx.component` or their `componentWithProps` forms
/// on a `let`, an `external` or a signature item. The attribute is the
/// surface syntax; this is what it means.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsxComponent {
    pub pjc_kind: JsxComponentKind,
    pub pjc_namespace: JsxComponentNamespace,
    /// The attribute's own location.
    pub pjc_loc: LocIdx,
}

/// OCaml `Parsetree.jsx_component_kind`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum JsxComponentKind {
    /// `@react.component`: the props are the labelled arguments.
    /// `@react.component(: t)` makes them share the props type `t`.
    Labelled(Option<CoreTypeIdx>),
    /// `@react.componentWithProps`: the function takes a props record.
    WithProps,
}

/// OCaml `Parsetree.jsx_component_namespace`: how the attribute was spelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum JsxComponentNamespace {
    React,
    Jsx,
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
    /// `await ME`: a dynamic import when ME is a module path, possibly
    /// constrained; elsewhere it has no effect.
    Pmod_await(ModExprIdx),
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
    /// `%%raw("...")`: JavaScript statements.
    Pstr_raw(Box<PstrRaw>),
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
    /// The `@react.component` annotation, taken out of the attributes when
    /// the description is built (`Ast_helper.Val.mk`).
    pub pval_jsx_component: Option<Box<JsxComponent>>,
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
    /// Source origin (parsetree.ml `type_declaration_origin`).
    pub ptype_origin: TypeDeclarationOrigin,
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
    /// The `@as(...)` runtime tag, taken out of the attributes when the
    /// constructor is built (OCaml `pcd_runtime_tag`).
    pub pcd_runtime_tag: Option<Located<ConstructorTag>>,
    /// Arguments.
    pub pcd_args: ConstructorArguments,
    /// Return type (arena index).
    pub pcd_res: Option<CoreTypeIdx>,
    /// Location.
    pub pcd_loc: Location,
    /// Attributes.
    pub pcd_attributes: Attributes,
}

/// OCaml `Parsetree.constructor_tag`: the literal a constructor's `@as`
/// denotes, with its source spelling.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConstructorTag {
    Pct_string(StringLiteral),
    Pct_int(String),
    Pct_float(String),
    Pct_bigint(String),
    Pct_bool(bool),
    Pct_null,
    Pct_undefined,
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
    /// The `@as("...")` rename, taken out of the attributes when the field is
    /// built (OCaml `pld_runtime_name`). The location is the attribute's own.
    pub pld_runtime_name: Option<Located<StringLiteral>>,
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

        let c = Constant::string("hello");
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
