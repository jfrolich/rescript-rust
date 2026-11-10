//! Typed Abstract Syntax Tree for ReScript.
//!
//! This module defines the typed AST produced by the type checker,
//! corresponding to OCaml's `Typedtree` module.
//!
//! Key differences from the parse tree (`Parsetree`):
//! - Every identifier has a resolved [`Path`]
//! - Every expression and pattern has a [`TypeExprRef`]
//! - Type annotations are type-checked [`CoreType`] values
//!
//! # Architecture
//!
//! The typed tree uses reference types (`TypeExprRef`) instead of owning types,
//! requiring a [`TypeContext`] for allocation. This enables efficient sharing
//! and modification during type checking.

#![allow(missing_docs)]
#![allow(non_camel_case_types)]

use crate::ident::Ident;
use crate::parse_arena::{LidentIdx, LocIdx, Located};
use crate::parser::ast::{
    Attributes, ClosedFlag, DirectionFlag, MutableFlag, OverrideFlag, PrivateFlag, RecFlag,
};
use crate::types::asttypes::ArgLabel as TypeArgLabel;
use crate::types::decl::ModuleType as DeclModuleType;
pub use crate::types::tast_arena::{
    TArgList, TCaseList, TCoreTypeIdx, TCoreTypeList, TDictList, TExpColdIdx, TExprIdx, TExprList,
    TExtIdx,
    TFieldList, TModExprIdx, TModTypeIdx, TParamList, TPatColdIdx, TPatIdx, TPatList, TSigItemList,
    TStrItemList, TValDescIdx, TVbList, TypedArena,
};
use crate::types::{
    ConstructorDescription, LabelDescription, Path, RowDesc, TypeExprRef, ValueDescription,
};
use std::sync::Arc;

/// A located value (convenience alias).
pub type Loc<T> = Located<T>;

// ============================================================================
// Constants
// ============================================================================

/// Typed constants (internal representation after parsing).
#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    /// Integer constant (matches OCaml's native int, 63-bit on 64-bit systems).
    Int(i64),
    /// Character constant (Unicode codepoint).
    Char(i32),
    /// The decoded runtime value of an ordinary string literal; source
    /// spelling has been discarded after type checking.
    String(String),
    /// Float constant (as string to preserve precision).
    Float(String),
    /// BigInt constant (sign, digits).
    BigInt(bool, String),
}

/// The only constants admitted as interval bounds by OCaml
/// `typecore.ml:1485-1506`. Keeping their payloads inline avoids making every
/// pattern large enough for two string-bearing `Constant` values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntervalBound {
    Int(i64),
    Char(i32),
}

impl IntervalBound {
    pub fn from_constant(c: Constant) -> Self {
        match c {
            Constant::Int(i) => Self::Int(i),
            Constant::Char(i) => Self::Char(i),
            _ => panic!("a typed interval bound must be an integer or character"),
        }
    }

    pub fn constant(self) -> Constant {
        match self {
            Self::Int(i) => Constant::Int(i),
            Self::Char(i) => Constant::Char(i),
        }
    }
}

// ============================================================================
// Partiality
// ============================================================================

/// Indicates whether a pattern match is exhaustive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Partial {
    /// Match is partial (not all cases covered).
    Partial,
    /// Match is total (exhaustive).
    Total,
}

// ============================================================================
// Patterns
// ============================================================================

/// A typed pattern.
#[derive(Debug, Clone)]
pub struct Pattern {
    /// Pattern description.
    pub pat_desc: PatternDesc,
    /// Source location.
    pub pat_loc: LocIdx,
    /// `pat_extra` (constraints, unpacks, etc.) and `pat_attributes`, in a
    /// side table of the [`TypedArena`]: read them with
    /// [`TypedArena::pat_extra`] and [`TypedArena::pat_attributes`].
    pub pat_cold: Option<TPatColdIdx>,
    /// Type of the pattern.
    pub pat_type: TypeExprRef,
    /// Environment at this pattern.
    pub pat_env: EnvRef,
}

/// Extra information on a pattern.
#[derive(Debug, Clone)]
pub enum PatExtra {
    /// Type constraint: `P : T`.
    Tpat_constraint(TCoreTypeIdx),
    /// Type pattern: `#tconst`.
    Tpat_type(Path, Loc<LidentIdx>),
    /// Unpack pattern: `(module P)`.
    Tpat_unpack,
}

/// Pattern description.
#[derive(Debug, Clone)]
pub enum PatternDesc {
    /// Wildcard: `_`.
    Tpat_any,

    /// Variable: `x`.
    Tpat_var(Ident, Loc<String>),

    /// Alias: `P as x`.
    Tpat_alias(TPatIdx, Ident, Loc<String>),

    /// Constant: `1`, `'a'`, `"hello"`, `1.0`.
    Tpat_constant(Constant),
    /// `Tpat_interval (lo, hi)`: an int or char range, `lo < hi`.
    Tpat_interval(IntervalBound, IntervalBound),

    /// Tuple: `(P1, ..., Pn)`.
    /// Invariant: length >= 2.
    Tpat_tuple(TPatList),

    /// Constructor: `C`, `C(P)`, `C(P1, ..., Pn)`.
    /// The description is shared like OCaml's physical `constructor_description`
    /// record, so pattern copies in exhaustiveness and matching stay cheap.
    Tpat_construct(Loc<LidentIdx>, Arc<ConstructorDescription>, TPatList),

    /// Variant: `` `A ``, `` `A(P) ``.
    Tpat_variant(String, Option<TPatIdx>, RowDescRef),

    /// Record: `{l1: P1, ..., ln: Pn}` or `{l1: P1, ..., _}`.
    /// The bool indicates whether the field is optional.
    Tpat_record(
        Vec<(Loc<LidentIdx>, Arc<LabelDescription>, TPatIdx, bool)>,
        ClosedFlag,
        Option<Box<RecordPatternRest>>,
    ),

    /// Dict: `dict{"k1": P1, ..., "kn": ?Pn}`.
    /// Entries are in source order, and their keys are distinct.
    Tpat_dict(Vec<DictPatternEntry>),

    /// Array: `[| P1, ..., Pn |]`.
    Tpat_array(TPatList),

    /// Or-pattern: `P1 | P2`.
    /// The RowDesc is Some when translating type patterns.
    Tpat_or(TPatIdx, TPatIdx, Option<Box<RowDesc>>),
}

/// An entry of a dict pattern (compiler/ml/typedtree.mli `dict_pattern_entry`).
#[derive(Debug, Clone)]
pub struct DictPatternEntry {
    pub tdp_key: Loc<String>,
    /// Matches the key's value as an option, `None` when the key is absent:
    /// `Some(P)` for `"k": P`, and `P` itself for `"k": ?P`.
    pub tdp_pattern: TPatIdx,
    /// Whether the entry is written `"k": ?P`.
    pub tdp_optional: bool,
}

/// Typed record-rest binding (compiler/ml/typedtree.ml:38-43).
#[derive(Debug, Clone)]
pub struct RecordPatternRest {
    /// Identifier bound for the rest value.
    pub rest_ident: Ident,
    /// Location passed to `enter_variable` (the value's `val_loc`).
    pub rest_loc: crate::parse_arena::LocIdx,
    /// Source name of the rest binding.
    pub rest_name: Loc<String>,
    /// Inferred record-rest type.
    pub rest_type: TypeExprRef,
    /// Runtime labels excluded from the rest object.
    pub excluded_runtime_labels: Vec<String>,
}

// ============================================================================
// Expressions
// ============================================================================

/// A typed expression.
#[derive(Debug, Clone)]
pub struct Expression {
    /// Expression description.
    pub exp_desc: ExpressionDesc,
    /// Source location.
    pub exp_loc: LocIdx,
    /// `exp_extra` (constraints, opens, newtypes, etc.) and
    /// `exp_attributes`, in a side table of the [`TypedArena`]: read them
    /// with [`TypedArena::exp_extra`] and [`TypedArena::exp_attributes`].
    pub exp_cold: Option<TExpColdIdx>,
    /// Type of the expression.
    pub exp_type: TypeExprRef,
    /// Environment at this expression.
    pub exp_env: EnvRef,
}

/// Extra information on an expression.
#[derive(Debug, Clone)]
pub enum ExpExtra {
    /// Type constraint: `E : T`.
    Texp_constraint(TCoreTypeIdx),
    /// Coercion: `(E :> T)`. `target` is T as written; `source_type` is the
    /// inferred type of E and `target_type` the type of T, both
    /// head-expanded so a consumer without a typing environment can still
    /// relate them.
    Texp_coerce {
        source_type: TypeExprRef,
        target: TCoreTypeIdx,
        target_type: TypeExprRef,
    },
    /// Open: `let open M in E`.
    Texp_open(OverrideFlag, Path, Loc<LidentIdx>, EnvRef),
    /// Newtype: `fun (type t) -> E`.
    Texp_newtype(String),
}

/// Expression description.
#[derive(Debug, Clone)]
pub enum ExpressionDesc {
    /// Identifier: `x`, `M.x`.
    Texp_ident(Path, Loc<LidentIdx>, Arc<ValueDescription>),

    /// Constant: `1`, `'a'`, `"hello"`, `1.0`.
    Texp_constant(Constant),

    /// Let binding: `let P = E in E'`.
    Texp_let(RecFlag, TVbList, TExprIdx),

    /// Function expression. Mirrors `compiler/ml/typedtree.ml`.
    Texp_function {
        params: TParamList,
        body: TExprIdx,
        /// Whether this is an async function.
        async_: bool,
    },

    /// Application: `E(E1, ..., En)`.
    /// Uses the ApplyArg representation.
    Texp_apply {
        funct: TExprIdx,
        args: TArgList,
        /// Whether this is a partial application.
        partial: bool,
        /// Whether this was transformed from JSX.
        transformed_jsx: bool,
    },

    /// Match: `switch E { | P1 => E1 | ... }`.
    /// The two case lists are (value cases, exception cases).
    Texp_match(TExprIdx, TCaseList, TCaseList, Partial),

    /// Try: `try E catch { | P1 => E1 | ... } finally E_fin`. The case list is
    /// empty when there is no catch, and then there is always a finally
    /// expression (typedtree.mli `Texp_try`).
    Texp_try(TExprIdx, TCaseList, Option<TExprIdx>),

    /// Tuple: `(E1, ..., En)`.
    Texp_tuple(TExprList),

    /// Constructor: `C`, `C(E)`, `C(E1, ..., En)`.
    Texp_construct(Loc<LidentIdx>, Arc<ConstructorDescription>, TExprList),

    /// Variant: `` `A ``, `` `A(E) ``.
    Texp_variant(String, Option<TExprIdx>),

    /// Record: `{l1: E1, ..., ln: En}` or `{...E0, l1: E1, ...}`.
    ///
    /// OCaml `Texp_record` (compiler/ml/typedtree.mli:220-238): `fields`
    /// holds only the fields the literal writes, ordered by `lbl_pos`. A field
    /// it leaves out is taken from `extended_expression` when there is one,
    /// and is otherwise an optional field set to `None`.
    Texp_record {
        fields: TFieldList,
        /// OCaml `representation`. With written fields it is their labels'
        /// `lbl_repres` (compiler/ml/typecore.ml:3058-3059, 3165-3168), read
        /// from `fields[0]`; only `{}` (typecore.ml:3060-3080) carries it.
        empty_representation: Option<Box<crate::types::RecordRepresentation>>,
        extended_expression: Option<TExprIdx>,
    },

    /// Field access: `E.l`.
    Texp_field(TExprIdx, Loc<LidentIdx>, Arc<LabelDescription>),

    /// Field mutation: `E.l = E'`.
    Texp_setfield(TExprIdx, Loc<LidentIdx>, Arc<LabelDescription>, TExprIdx),

    /// Array literal: `[E1, ..., En]`.
    Texp_array(TExprList),

    /// Dict literal: `dict{"k1": E1, ...E2}`.
    Texp_dict(TDictList),

    /// An array or list literal with spreads: the arrays or lists it
    /// concatenates, see `parser::ast_spread` (typedtree.ml `Texp_spread`).
    Texp_spread(crate::parser::ast::SpreadKind, TExprList),

    /// If-then-else: `if E1 then E2 else E3`.
    Texp_ifthenelse(TExprIdx, TExprIdx, Option<TExprIdx>),

    /// Sequence: `E1; E2`.
    Texp_sequence(TExprIdx, TExprIdx),

    /// `break` (upstream #8348). Exits the nearest enclosing loop.
    Texp_break,

    /// `continue` (upstream #8348). Skips to the next iteration of the
    /// nearest enclosing loop.
    Texp_continue,

    /// While loop: `while E1 do E2 done`.
    Texp_while(TExprIdx, TExprIdx),

    /// For loop: `for i = E1 to/downto E2 do E3 done`.
    Texp_for(Ident, TPatIdx, TExprIdx, TExprIdx, DirectionFlag, TExprIdx),

    /// For-of loop: `for pat of iterable { body }` (upstream #7887).
    /// The pattern stored is the original parser pattern (as in OCaml's
    /// `Texp_for_of of Ident.t * Parsetree.pattern * expression * expression`).
    Texp_for_of(Ident, Box<crate::parser::ast::Pattern>, TExprIdx, TExprIdx),

    /// For-await-of loop: `for await pat of asyncIterable { body }` (upstream #7887).
    Texp_for_await_of(Ident, Box<crate::parser::ast::Pattern>, TExprIdx, TExprIdx),

    /// A typed JavaScript tagged template: the typed `tag`, the exact raw
    /// segment sources (which may contain invalid escapes), and the typed
    /// interpolated values. There is always one more raw source than value.
    Texp_tagged_template {
        tag: TExprIdx,
        raw_sources: Vec<String>,
        values: TExprList,
    },

    /// A typed ordinary backquoted template: validated segments carrying
    /// source and semantic forms, and the typed interpolated values. There is
    /// always one more segment than value.
    Texp_template {
        segments: Vec<crate::string_literal::TemplateSegment>,
        values: TExprList,
    },

    /// Object property read: `E["name"]`.
    Texp_object_get(TExprIdx, Loc<String>),

    /// Object property write: `E["name"] = V`.
    Texp_object_set(TExprIdx, Loc<String>, TExprIdx),

    /// Object literal: `{"a": E, ...}`, fields in source order.
    Texp_object_literal(Vec<(Loc<String>, TExprIdx)>),

    /// Let module: `let module M = ME in E`.
    Texp_letmodule(Ident, Loc<String>, TModExprIdx, TExprIdx),

    /// Let exception: `let exception C of T in E`.
    Texp_letexception(TExtIdx, TExprIdx),

    /// Assert: `assert E`.
    Texp_assert(TExprIdx),

    /// Pack: `(module M : MT)`.
    Texp_pack(TModExprIdx),
}

// DirectionFlag and Arity are re-exported from parser::ast

/// A field a record literal writes: OCaml's
/// `Types.label_description * Longident.t loc * expression`.
/// Keep the arena port's shared label description; only written fields
/// have an entry, and their expression children are arena handles.
pub type RecordField = (Arc<LabelDescription>, Loc<LidentIdx>, TExprIdx);

/// `all_labels` (compiler/ml/translcore.ml:1020-1028): every label of the
/// record a `Texp_record` builds, the `lbl_all` of its written labels; `None`
/// for `{}`. Record typing registers that array in the `TypeContext` and
/// points every written label at it, so it always resolves.
pub fn record_all_labels(
    ctx: &crate::types::context::TypeContext,
    fields: &[RecordField],
) -> Option<Arc<Vec<LabelDescription>>> {
    let (first, _, _) = fields.first()?;
    Some(
        ctx.label_family(first.lbl_all)
            .expect("a written record label points to its registered lbl_all"),
    )
}

/// The `representation` of a `Texp_record`.
pub fn record_representation<'a>(
    fields: &'a [RecordField],
    empty_representation: Option<&'a crate::types::RecordRepresentation>,
) -> Option<&'a crate::types::RecordRepresentation> {
    fields
        .first()
        .map(|(lbl, _, _)| &lbl.lbl_repres)
        .or(empty_representation)
}

/// `fields_by_position` (compiler/ml/translcore.ml:1030-1035): each label of
/// the record with the expression the literal writes for it, if any, in
/// position order.
pub fn record_fields_by_position<'a>(
    fields: &'a [RecordField],
    labels: &'a [LabelDescription],
) -> Vec<(&'a LabelDescription, Option<&'a RecordField>)> {
    let mut written: Vec<Option<&RecordField>> = vec![None; labels.len()];
    for field in fields {
        // `written.(lbl.lbl_pos) <- Some exp`: a written label is a label of
        // the record.
        written[field.0.lbl_pos as usize] = Some(field);
    }
    labels.iter().zip(written).collect()
}

/// An argument in a function application.
#[derive(Debug, Clone)]
pub struct ApplyArg {
    /// Argument label.
    pub label: TypeArgLabel,
    /// Argument expression, or None for omitted labeled arguments.
    pub expression: Option<TExprIdx>,
}

/// A function parameter. Mirrors `compiler/ml/typedtree.ml`.
#[derive(Debug, Clone)]
pub struct FunctionParam {
    /// Source argument label.
    pub fp_lbl: TypeArgLabel,
    /// Identifier bound by generated Lambda.
    pub fp_param: Ident,
    /// Typed source pattern.
    pub fp_pat: TPatIdx,
    /// Whether the parameter pattern is exhaustive.
    pub fp_partial: Partial,
    /// Optional parameter with a default value: `fp_pat` binds the option
    /// carrier directly to `fp_param`, a fresh ident named after the label,
    /// and the user's pattern is bound by a let at the head of the body.
    pub fp_has_default: bool,
}

// ============================================================================
// Cases and Bindings
// ============================================================================

/// A case in a match expression.
#[derive(Debug, Clone)]
pub struct Case {
    /// Left-hand side pattern.
    pub c_lhs: TPatIdx,
    /// Optional guard: `when E`.
    pub c_guard: Option<TExprIdx>,
    /// Right-hand side expression.
    pub c_rhs: TExprIdx,
}

/// A value binding in a let expression.
#[derive(Debug, Clone)]
pub struct ValueBinding {
    /// Binding pattern.
    pub vb_pat: TPatIdx,
    /// Binding expression.
    pub vb_expr: TExprIdx,
    /// Attributes on the binding.
    pub vb_attributes: Attributes,
    /// Location of the binding.
    pub vb_loc: LocIdx,
}

// ============================================================================
// Type Expressions (Typed Core Types)
// ============================================================================

/// A typed core type (type expression after type checking).
#[derive(Debug, Clone)]
pub struct TypedCoreType {
    /// Type description.
    pub ctyp_desc: TypedCoreTypeDesc,
    /// Resolved type.
    pub ctyp_type: TypeExprRef,
    /// Environment at this type.
    pub ctyp_env: EnvRef,
    /// Source location.
    pub ctyp_loc: LocIdx,
    /// Attributes.
    pub ctyp_attributes: Attributes,
}

/// Arrow argument structure for Ttyp_arrow.
/// Matches OCaml's `arg = {attrs: attributes; lbl: arg_label; typ: core_type}`.
#[derive(Debug, Clone)]
pub struct ArrowArg {
    /// Attributes on the argument.
    pub attrs: Attributes,
    /// Argument label.
    pub lbl: TypeArgLabel,
    /// Argument type (boxed to prevent infinite size).
    pub typ: TCoreTypeIdx,
}

/// Typed core type description.
#[derive(Debug, Clone)]
pub enum TypedCoreTypeDesc {
    /// Type variable: `'a`.
    Ttyp_var(Option<String>),
    /// N-ary arrow type. Mirrors `compiler/ml/typedtree.ml`:
    /// `Ttyp_arrow of Parsetree.arg list * core_type`.
    Ttyp_arrow(Vec<ArrowArg>, TCoreTypeIdx),
    /// Tuple type: `(T1, ..., Tn)`.
    Ttyp_tuple(TCoreTypeList),
    /// Type constructor: `t`, `M.t`, `('a, 'b) t`.
    Ttyp_constr(Path, Loc<LidentIdx>, TCoreTypeList),
    /// Object type: `< m1: T1; ...; mn: Tn >`.
    Ttyp_object(Vec<ObjectField>, ClosedFlag),
    /// Polymorphic type: `'a 'b. T`.
    Ttyp_poly(Vec<String>, TCoreTypeIdx),
    /// Type alias: `T as 'a`.
    Ttyp_alias(TCoreTypeIdx, String),
    /// Variant type: `[< `A | `B ]`.
    Ttyp_variant(Vec<RowFieldType>, ClosedFlag, Option<Vec<String>>),
    /// Package type: `(module MT)`.
    Ttyp_package(PackageType),
}

/// An object field type.
#[derive(Debug, Clone)]
pub struct ObjectField {
    /// Field name or inherit.
    pub of_desc: ObjectFieldDesc,
    /// Field location.
    pub of_loc: LocIdx,
    /// Field attributes.
    pub of_attributes: Attributes,
}

/// Object field description.
#[derive(Debug, Clone)]
pub enum ObjectFieldDesc {
    /// Named field.
    OTtag(Loc<String>, TCoreTypeIdx),
    /// Inherited type.
    OTinherit(TCoreTypeIdx),
}

/// A row field type (for polymorphic variants).
#[derive(Debug, Clone)]
pub struct RowFieldType {
    /// Field description.
    pub rf_desc: RowFieldDesc,
    /// Field location.
    pub rf_loc: LocIdx,
    /// Field attributes.
    pub rf_attributes: Attributes,
}

/// Row field description.
#[derive(Debug, Clone)]
pub enum RowFieldDesc {
    /// Tag: `` `A `` or `` `A of T ``.
    Rtag(Loc<String>, bool, TCoreTypeList),
    /// Inherit: `T`.
    Rinherit(TCoreTypeIdx),
}

/// A package type constraint.
#[derive(Debug, Clone)]
pub struct PackageType {
    /// Module type path.
    pub pack_path: Path,
    /// Type constraints.
    pub pack_fields: Vec<(Loc<LidentIdx>, TCoreTypeIdx)>,
}

// ============================================================================
// Modules (Placeholder types)
// ============================================================================

/// A module expression (placeholder).
#[derive(Debug, Clone)]
pub struct ModuleExpr {
    /// Module description.
    pub mod_desc: ModuleExprDesc,
    /// Module location.
    pub mod_loc: LocIdx,
    /// Semantic module type (`Types.module_type` in OCaml).
    pub mod_type: DeclModuleType,
    /// Module environment.
    pub mod_env: EnvRef,
    /// Module attributes.
    pub mod_attributes: Attributes,
}

/// Module expression description (placeholder).
#[derive(Debug, Clone)]
pub enum ModuleExprDesc {
    /// Identifier.
    Tmod_ident(Path, Loc<LidentIdx>),
    /// Structure.
    Tmod_structure(Structure),
    /// Functor application.
    Tmod_apply(TModExprIdx, TModExprIdx, ModuleCoercion),
    /// Functor.
    Tmod_functor(Ident, Loc<String>, Option<TModTypeIdx>, TModExprIdx),
    /// Constraint.
    Tmod_constraint(
        TModExprIdx,
        DeclModuleType,
        ModuleTypeConstraint,
        ModuleCoercion,
    ),
    /// Unpack.
    Tmod_unpack(TExprIdx, DeclModuleType),
}

/// Module type (matches OCaml's `Typedtree.module_type`).
#[derive(Debug, Clone)]
pub struct ModuleType {
    /// Module type description.
    pub mty_desc: ModuleTypeDesc,
    /// Semantic module type (`Types.module_type` in OCaml).
    pub mty_type: DeclModuleType,
    /// Module-type environment.
    pub mty_env: EnvRef,
    /// Location.
    pub mty_loc: LocIdx,
    /// Attributes.
    pub mty_attributes: Attributes,
}

/// Module type description (matches OCaml's `Typedtree.module_type_desc`).
#[derive(Debug, Clone)]
pub enum ModuleTypeDesc {
    /// Named module type: `S` or `M.S`.
    Tmty_ident(Path, Loc<LidentIdx>),
    /// Signature: `sig ... end` / `{ ... }`.
    Tmty_signature(TypedSignature),
    /// Functor type: `functor (X : MT1) -> MT2`.
    Tmty_functor(Ident, Loc<String>, Option<TModTypeIdx>, TModTypeIdx),
    /// With constraint: `MT with ...`.
    Tmty_with(TModTypeIdx, Vec<(Path, Loc<LidentIdx>, WithConstraint)>),
    /// Typeof: `module type of ME`.
    Tmty_typeof(TModExprIdx),
    /// Alias: `(module M)`.
    Tmty_alias(Path, Loc<LidentIdx>),
}

/// With constraint (matches OCaml's `Typedtree.with_constraint`).
#[derive(Debug, Clone)]
pub enum WithConstraint {
    Twith_type(TypedTypeDeclaration),
    Twith_module(Path, Loc<LidentIdx>),
    Twith_typesubst(TypedTypeDeclaration),
    Twith_modsubst(Path, Loc<LidentIdx>),
}

/// Typed signature (matches OCaml's `Typedtree.signature`).
#[derive(Debug, Clone)]
pub struct TypedSignature {
    pub sig_items: TSigItemList,
}

/// Typed signature item (matches OCaml's `Typedtree.signature_item`).
#[derive(Debug, Clone)]
pub struct TypedSignatureItem {
    pub sig_desc: TypedSignatureItemDesc,
    pub sig_env: EnvRef,
    pub sig_loc: LocIdx,
}

/// Typed signature item description (matches OCaml's `Typedtree.signature_item_desc`).
#[derive(Debug, Clone)]
pub enum TypedSignatureItemDesc {
    Tsig_value(TValDescIdx),
    Tsig_type(RecFlag, Vec<TypedTypeDeclaration>),
    Tsig_typext(TypeExtension),
    Tsig_exception(TExtIdx),
    Tsig_module(TypedModuleDeclaration),
    Tsig_recmodule(Vec<TypedModuleDeclaration>),
    Tsig_modtype(ModuleTypeDeclaration),
    Tsig_open(OpenDeclaration),
    Tsig_include(IncludeDescription),
    Tsig_attribute(crate::parser::ast::Attribute),
}

/// Typed module declaration (matches OCaml's `Typedtree.module_declaration`).
#[derive(Debug, Clone)]
pub struct TypedModuleDeclaration {
    pub md_id: Ident,
    pub md_name: Loc<String>,
    pub md_type: TModTypeIdx,
    pub md_attributes: Attributes,
    pub md_loc: LocIdx,
}

/// Include description (for signatures, matches OCaml's `Typedtree.include_description`).
#[derive(Debug, Clone)]
pub struct IncludeDescription {
    pub incl_mod: TModTypeIdx,
    pub incl_type: Vec<crate::types::decl::SignatureItem>,
    pub incl_attributes: Attributes,
    pub incl_loc: LocIdx,
}

/// Module type constraint.
#[derive(Debug, Clone)]
pub enum ModuleTypeConstraint {
    /// Explicit signature.
    Tmodtype_explicit(TModTypeIdx),
    /// Implicit (no constraint).
    Tmodtype_implicit,
}

/// Module coercion.
#[derive(Debug, Clone)]
pub enum ModuleCoercion {
    /// No coercion needed.
    Tcoerce_none,
    /// Structural coercion.
    Tcoerce_structure(
        Vec<(usize, ModuleCoercion)>,
        Vec<(Ident, usize, ModuleCoercion)>,
        Vec<String>,
    ),
    /// Functor coercion.
    Tcoerce_functor(Box<ModuleCoercion>, Box<ModuleCoercion>),
    /// Primitive coercion.
    Tcoerce_primitive(PrimitiveCoercion),
    /// Alias coercion.
    Tcoerce_alias(EnvRef, Path, Box<ModuleCoercion>),
}

/// Primitive coercion.
#[derive(Debug, Clone)]
pub struct PrimitiveCoercion {
    /// Primitive description.
    pub pc_desc: crate::types::PrimitiveDescription,
    /// Type of the primitive (from the signature).
    pub pc_type: crate::types::TypeExprRef,
    /// Location of the primitive declaration (its `val_loc`), resolved
    /// through the compilation's `TypeContext`.
    pub pc_loc: crate::types::DeclLoc,
    /// Identifier for the primitive.
    pub pc_id: crate::ident::Ident,
}

/// A structure (module definition body).
#[derive(Debug, Clone)]
pub struct Structure {
    /// Structure items.
    pub str_items: TStrItemList,
    /// Inferred signature items for this structure.
    pub str_type: Vec<crate::types::decl::SignatureItem>,
    /// Final environment.
    pub str_final_env: EnvRef,
}

/// A structure item.
#[derive(Debug, Clone)]
pub struct StructureItem {
    /// Item description.
    pub str_desc: StructureItemDesc,
    /// Item location.
    pub str_loc: LocIdx,
    /// Item environment.
    pub str_env: EnvRef,
}

/// Structure item description.
#[derive(Debug, Clone)]
pub enum StructureItemDesc {
    /// Evaluated expression: `E`.
    Tstr_eval(TExprIdx, Attributes),
    /// Value binding: `let P = E`.
    Tstr_value(RecFlag, TVbList),
    /// Primitive declaration: `external f : t = "..."`.
    Tstr_primitive(TValDescIdx),
    /// Type declaration: `type t = ...`.
    Tstr_type(RecFlag, Vec<TypedTypeDeclaration>),
    /// Type extension: `type t += ...`.
    Tstr_typext(TypeExtension),
    /// Exception declaration: `exception C`.
    Tstr_exception(TExtIdx),
    /// Module binding: `module M = ME`.
    Tstr_module(ModuleBinding),
    /// Recursive modules: `module rec M = ...`.
    Tstr_recmodule(Vec<ModuleBinding>),
    /// Module type declaration: `module type S = MT`.
    Tstr_modtype(ModuleTypeDeclaration),
    /// Open declaration: `open M`.
    Tstr_open(OpenDeclaration),
    /// Include declaration: `include ME`.
    Tstr_include(IncludeDeclaration),
    /// Attribute: `@@attr`.
    Tstr_attribute(crate::parser::ast::Attribute),
}

// Re-export TypeDeclaration from decl for convenience (internal representation)
pub use crate::types::TypeDeclaration as InternalTypeDeclaration;

/// Typed type declaration for the typed tree.
/// Matches OCaml's Typedtree.type_declaration.
#[derive(Debug, Clone)]
pub struct TypedTypeDeclaration {
    /// Type identifier.
    pub typ_id: Ident,
    /// Type name with location.
    pub typ_name: Loc<String>,
    /// Type parameters with variance.
    pub typ_params: Vec<(TCoreTypeIdx, Variance)>,
    /// Internal type declaration for the environment.
    pub typ_type: InternalTypeDeclaration,
    /// Type constraints.
    pub typ_cstrs: Vec<(TCoreTypeIdx, TCoreTypeIdx, LocIdx)>,
    /// Type kind.
    pub typ_kind: TypedTypeKind,
    /// Private flag.
    pub typ_private: PrivateFlag,
    /// Manifest type (for type aliases).
    pub typ_manifest: Option<TCoreTypeIdx>,
    /// Location.
    pub typ_loc: LocIdx,
    /// Attributes.
    pub typ_attributes: Attributes,
}

/// Typed type kind.
#[derive(Debug, Clone)]
pub enum TypedTypeKind {
    /// Abstract type.
    Ttype_abstract,
    /// Variant type with constructors.
    Ttype_variant(Vec<TypedConstructorDeclaration>),
    /// Record type with labels.
    Ttype_record(Vec<TypedLabelDeclaration>),
    /// Open type.
    Ttype_open,
}

/// Typed constructor declaration.
#[derive(Debug, Clone)]
pub struct TypedConstructorDeclaration {
    /// Constructor identifier.
    pub cd_id: Ident,
    /// Constructor name with location.
    pub cd_name: Loc<String>,
    /// The decoded `@as` tag (OCaml `cd_runtime_tag`).
    pub cd_runtime_tag: Option<super::variant_runtime::LiteralTag>,
    /// Constructor arguments.
    pub cd_args: TypedConstructorArguments,
    /// Result type (for GADTs).
    pub cd_res: Option<TCoreTypeIdx>,
    /// Location.
    pub cd_loc: LocIdx,
    /// Attributes.
    pub cd_attributes: Attributes,
}

/// Typed constructor arguments.
#[derive(Debug, Clone)]
pub enum TypedConstructorArguments {
    /// Tuple arguments.
    Cstr_tuple(TCoreTypeList),
    /// Record arguments.
    Cstr_record(Vec<TypedLabelDeclaration>),
}

/// Typed label declaration for records.
#[derive(Debug, Clone)]
pub struct TypedLabelDeclaration {
    /// Label identifier.
    pub ld_id: Ident,
    /// Label name with location.
    pub ld_name: Loc<String>,
    /// The `@as` rename (OCaml `ld_runtime_name`).
    pub ld_runtime_name: Option<String>,
    /// Whether the label is mutable.
    pub ld_mutable: MutableFlag,
    /// Whether the label is optional.
    pub ld_optional: bool,
    /// Label type.
    pub ld_type: TCoreTypeIdx,
    /// Location.
    pub ld_loc: LocIdx,
    /// Attributes.
    pub ld_attributes: Attributes,
    /// For a label built from a `Types.label_declaration` (record spreads,
    /// `Record_type_spread.mk_lbl` in compiler/ml/record_type_spread.ml:110-121),
    /// OCaml reuses `l.ld_attributes` verbatim. That declaration may belong to
    /// another compilation unit, so its payloads are kept in portable form here
    /// and writers emit them instead of `ld_attributes`.
    pub ld_types_attributes: Option<Box<[crate::types::decl::Attribute]>>,
}

/// A type extension.
#[derive(Debug, Clone)]
pub struct TypeExtension {
    /// Extended type path.
    pub tyext_path: Path,
    /// Type parameters.
    pub tyext_params: Vec<(TCoreTypeIdx, Variance)>,
    /// Extension constructors.
    pub tyext_constructors: Vec<ExtensionConstructor>,
    /// Private flag.
    pub tyext_private: PrivateFlag,
    /// Attributes.
    pub tyext_attributes: Attributes,
}

/// Use Variance from crate::types
use crate::types::Variance;

/// A module binding.
#[derive(Debug, Clone)]
pub struct ModuleBinding {
    /// Module identifier.
    pub mb_id: Ident,
    /// Module name with location.
    pub mb_name: Loc<String>,
    /// Module expression.
    pub mb_expr: TModExprIdx,
    /// Module attributes.
    pub mb_attributes: Attributes,
    /// Location.
    pub mb_loc: LocIdx,
}

/// A module type declaration.
#[derive(Debug, Clone)]
pub struct ModuleTypeDeclaration {
    /// Module type identifier.
    pub mtd_id: Ident,
    /// Module type name with location.
    pub mtd_name: Loc<String>,
    /// Module type (None for abstract).
    pub mtd_type: Option<TModTypeIdx>,
    /// Attributes.
    pub mtd_attributes: Attributes,
    /// Location.
    pub mtd_loc: LocIdx,
}

/// An open description (matches OCaml's `open_description`).
#[derive(Debug, Clone)]
pub struct OpenDeclaration {
    /// Resolved module path.
    pub open_path: Path,
    /// Original longident as written.
    pub open_txt: Located<LidentIdx>,
    /// Open override flag.
    pub open_override: OverrideFlag,
    /// Attributes.
    pub open_attributes: Attributes,
}

/// An include declaration.
#[derive(Debug, Clone)]
pub struct IncludeDeclaration {
    /// Included module expression.
    pub incl_mod: TModExprIdx,
    /// Included module type.
    pub incl_type: Vec<crate::types::decl::SignatureItem>,
    /// Attributes.
    pub incl_attributes: Attributes,
    /// Location.
    pub incl_loc: LocIdx,
}

/// Typed value description (for `external` declarations).
/// Matches OCaml's `Typedtree.value_description`.
#[derive(Debug, Clone)]
pub struct TypedValueDescription {
    /// Identifier.
    pub val_id: Ident,
    /// Name with location.
    pub val_name: Loc<String>,
    /// Typed core type (the annotated type).
    pub val_desc: TCoreTypeIdx,
    /// Primitive names.
    pub val_prim: Option<crate::parser::ast::PrimitiveRepr>,
    /// `val_val.val_kind` (compiler/ml/typedtree.mli `value_description`):
    /// the kind `Typedecl.transl_value_decl` computed (typedecl.ml:1878-1915),
    /// including a primitive's arity from `parse_arity`.
    pub val_kind: crate::types::decl::ValueKind,
    /// Location.
    pub val_loc: LocIdx,
    /// Attributes.
    pub val_attributes: Attributes,
}

/// Extension constructor.
#[derive(Debug, Clone)]
pub struct ExtensionConstructor {
    /// Constructor identifier.
    pub ext_id: Ident,
    /// Constructor name with location.
    pub ext_name: Loc<String>,
    /// Constructor type.
    pub ext_type: crate::types::ExtensionConstructor,
    /// Constructor kind.
    pub ext_kind: ExtensionConstructorKind,
    /// Location.
    pub ext_loc: LocIdx,
    /// Attributes.
    pub ext_attributes: Attributes,
}

/// Extension constructor kind.
#[derive(Debug, Clone)]
pub enum ExtensionConstructorKind {
    /// Declaration with argument types and optional result type.
    Text_decl(ConstructorArgument, Option<TCoreTypeIdx>),
    /// Rebind to another constructor.
    Text_rebind(Path, Loc<LidentIdx>),
}

/// Constructor argument in extension declaration.
#[derive(Debug, Clone)]
pub enum ConstructorArgument {
    /// Tuple arguments.
    Cstr_tuple(TCoreTypeList),
    /// Record arguments.
    Cstr_record(Vec<LabelDeclaration>),
}

/// Label declaration in a constructor record.
#[derive(Debug, Clone)]
pub struct LabelDeclaration {
    /// Label identifier.
    pub ld_id: Ident,
    /// Label name with location.
    pub ld_name: Loc<String>,
    /// The `@as` rename (OCaml `ld_runtime_name`).
    pub ld_runtime_name: Option<String>,
    /// Whether the label is mutable.
    pub ld_mutable: MutableFlag,
    /// Whether the label is optional.
    pub ld_optional: bool,
    /// Label type.
    pub ld_type: TCoreTypeIdx,
    /// Location.
    pub ld_loc: LocIdx,
    /// Attributes.
    pub ld_attributes: Attributes,
}

// ============================================================================
// Environment and Row Reference Types
// ============================================================================

/// Reference to an environment (placeholder).
/// In the full implementation, this would be an index or reference to the Env.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvRef(pub u32);

impl EnvRef {
    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        Self(u32::try_from(idx).expect("typed env arena index exceeds u32::MAX"))
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Reference to a row description.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RowDescRef(pub u32);

// ============================================================================
// Helper Functions
// ============================================================================

impl Pattern {
    /// Create a pattern without extras or attributes; see
    /// [`TypedArena::with_pat_attributes`].
    pub fn new(desc: PatternDesc, loc: LocIdx, ty: TypeExprRef, env: EnvRef) -> Self {
        Pattern {
            pat_desc: desc,
            pat_loc: loc,
            pat_cold: None,
            pat_type: ty,
            pat_env: env,
        }
    }
}

impl Expression {
    /// Create an expression without extras or attributes; see
    /// [`TypedArena::with_exp_attributes`].
    pub fn new(desc: ExpressionDesc, loc: LocIdx, ty: TypeExprRef, env: EnvRef) -> Self {
        Expression {
            exp_desc: desc,
            exp_loc: loc,
            exp_cold: None,
            exp_type: ty,
            exp_env: env,
        }
    }
}

impl Case {
    /// Create a new case with pattern and expression (no guard).
    pub fn simple(lhs: TPatIdx, rhs: TExprIdx) -> Self {
        Case {
            c_lhs: lhs,
            c_guard: None,
            c_rhs: rhs,
        }
    }
}

impl ValueBinding {
    /// Create a new value binding.
    pub fn new(pat: TPatIdx, expr: TExprIdx, loc: LocIdx, attributes: Attributes) -> Self {
        ValueBinding {
            vb_pat: pat,
            vb_expr: expr,
            vb_attributes: attributes,
            vb_loc: loc,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_arena::ParseArena;

    #[test]
    fn test_constant() {
        let c = Constant::Int(42);
        assert_eq!(c, Constant::Int(42));

        let s = Constant::String("hello".to_string());
        assert!(matches!(s, Constant::String(_)));
    }

    #[test]
    fn test_partial() {
        assert_ne!(Partial::Partial, Partial::Total);
    }

    #[test]
    fn test_case_simple() {
        // This test just verifies the structure compiles
        // Actual construction requires type context
    }

    #[test]
    fn test_direction_flag() {
        assert_ne!(DirectionFlag::Upto, DirectionFlag::Downto);
    }

    #[test]
    fn test_arity() {
        let mut arena = ParseArena::new();
        let full2a = arena.push_arity(Some(2));
        let full2b = arena.push_arity(Some(2));
        let unknown = arena.push_arity(None);
        assert_eq!(arena.get_arity(full2a), arena.get_arity(full2b));
        assert_ne!(arena.get_arity(full2a), arena.get_arity(unknown));
    }
}

#[cfg(test)]
mod node_size_tests {
    // Typed expressions are built, moved and matched throughout typing and
    // lowering; keep rare large payloads out of line.
    #[test]
    fn typed_expression_sizes_stay_compact() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::ExpressionDesc>(), 56);
        assert_eq!(size_of::<super::Expression>(), 72);
    }

    // Module expression and module type children are arena handles.
    #[test]
    fn typed_module_nodes_stay_compact() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::ModuleExpr>(), 184);
        assert_eq!(size_of::<super::ModuleType>(), 112);
        assert_eq!(size_of::<super::ModuleTypeDesc>(), 56);
    }

    // Structure and signature items keep their large payloads (value
    // descriptions, extension constructors) behind arena handles.
    #[test]
    fn typed_items_stay_compact() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::StructureItem>(), 96);
        assert_eq!(size_of::<super::TypedSignatureItem>(), 96);
        assert_eq!(size_of::<super::TypedCoreType>(), 80);
    }

    // Sub-patterns are handles into the TypedArena, so a pattern owns no
    // boxed children; extras and attributes live in a side table.
    #[test]
    fn typed_patterns_stay_compact() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::PatternDesc>(), 56);
        assert_eq!(size_of::<super::Pattern>(), 72);
    }

    #[test]
    fn interval_bounds_preserve_constant_kinds_and_values() {
        use super::{Constant, IntervalBound};
        for constant in [Constant::Int(i64::MIN), Constant::Int(i64::MAX), Constant::Char(0x10ffff)] {
            assert_eq!(IntervalBound::from_constant(constant.clone()).constant(), constant);
        }
    }

    // Children live in the TypedArena: list-carrying nodes hold 4-byte
    // handles and 8-byte list ranges instead of inline subtrees.
    #[test]
    fn typed_list_items_stay_compact() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::Case>(), 12);
        assert_eq!(size_of::<super::ValueBinding>(), 24);
        assert_eq!(size_of::<super::FunctionParam>(), 64);
        assert_eq!(size_of::<super::ApplyArg>(), 48);
        assert_eq!(size_of::<super::RecordField>(), 24);
        assert_eq!(size_of::<super::IntervalBound>(), 16);
    }
}

/// An entry of a dict literal (compiler/ml/typedtree.mli `dict_entry`).
#[derive(Debug, Clone)]
pub enum DictEntry {
    /// `"k": E`
    Tdict_entry(Loc<String>, TExprIdx),
    /// `...E`
    Tdict_spread(TExprIdx),
}
