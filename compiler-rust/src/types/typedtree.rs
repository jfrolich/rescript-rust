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
    ArgLabel as ParserArgLabel, Arity, Attributes, ClosedFlag, DirectionFlag, MutableFlag,
    OverrideFlag, PrivateFlag, RecFlag,
};
use crate::types::asttypes::ArgLabel as TypeArgLabel;
use crate::types::decl::ModuleType as DeclModuleType;
use crate::types::{
    ConstructorDescription, LabelDescription, Path, RowDesc, TypeExprRef, ValueDescription,
};
use std::ops::Deref;
use std::sync::Arc;

/// A located value (convenience alias).
pub type Loc<T> = Located<T>;

/// Intentional Rust performance representation for sparse typedtree extras.
///
/// Most typed expressions and patterns have no extras. Store that common case
/// as `None` instead of carrying an inline empty Vec on every node; callers
/// still see slice/iterator semantics so the external typedtree shape is
/// unchanged. Do not remove this during parity cleanup unless the replacement
/// keeps the same OCaml-facing behavior and comparable memory profile.
#[derive(Debug, Clone)]
pub struct SparseExtras<T> {
    items: Option<Box<[T]>>,
}

impl<T> SparseExtras<T> {
    /// Create an empty extras list.
    pub fn new() -> Self {
        Self { items: None }
    }

    /// Create extras from a Vec, preserving order.
    pub fn from_vec(items: Vec<T>) -> Self {
        if items.is_empty() {
            Self::new()
        } else {
            Self {
                items: Some(items.into_boxed_slice()),
            }
        }
    }

    /// Append one extra item.
    pub fn push(&mut self, item: T) {
        match self.items.take() {
            None => {
                self.items = Some(vec![item].into_boxed_slice());
            }
            Some(items) => {
                let mut items = Vec::from(items);
                items.push(item);
                self.items = Some(items.into_boxed_slice());
            }
        }
    }

    /// Iterate over extras in typedtree order.
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.deref().iter()
    }

    /// Number of extras.
    pub fn len(&self) -> usize {
        self.deref().len()
    }

    /// True when there are no extras.
    pub fn is_empty(&self) -> bool {
        self.deref().is_empty()
    }

    /// Convert back to a Vec for callers that need ownership.
    pub fn into_vec(self) -> Vec<T> {
        self.items.map(Vec::from).unwrap_or_default()
    }
}

impl<T> Default for SparseExtras<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<Vec<T>> for SparseExtras<T> {
    fn from(items: Vec<T>) -> Self {
        Self::from_vec(items)
    }
}

impl<T> Deref for SparseExtras<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.items.as_deref().unwrap_or(&[])
    }
}

impl<T> IntoIterator for SparseExtras<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a, T> IntoIterator for &'a SparseExtras<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

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
    /// String constant with optional delimiter.
    String(String, Option<String>),
    /// Float constant (as string to preserve precision).
    Float(String),
    /// BigInt constant (sign, digits).
    BigInt(bool, String),
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
    /// Extra information (constraints, unpacks, etc.).
    pub pat_extra: SparseExtras<(PatExtra, LocIdx, Attributes)>,
    /// Type of the pattern.
    pub pat_type: TypeExprRef,
    /// Environment at this pattern.
    pub pat_env: EnvRef,
    /// Attributes on the pattern.
    pub pat_attributes: Attributes,
}

/// Extra information on a pattern.
#[derive(Debug, Clone)]
pub enum PatExtra {
    /// Type constraint: `P : T`.
    Tpat_constraint(TypedCoreType),
    /// Type pattern: `#tconst`.
    Tpat_type(Path, Loc<LidentIdx>),
    /// Open pattern: `M.(P)`.
    Tpat_open(Path, Loc<LidentIdx>, EnvRef),
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
    Tpat_alias(Box<Pattern>, Ident, Loc<String>),

    /// Constant: `1`, `'a'`, `"hello"`, `1.0`.
    Tpat_constant(Constant),

    /// Tuple: `(P1, ..., Pn)`.
    /// Invariant: length >= 2.
    Tpat_tuple(Vec<Pattern>),

    /// Constructor: `C`, `C(P)`, `C(P1, ..., Pn)`.
    /// The description is shared like OCaml's physical `constructor_description`
    /// record, so pattern copies in exhaustiveness and matching stay cheap.
    Tpat_construct(Loc<LidentIdx>, Arc<ConstructorDescription>, Vec<Pattern>),

    /// Variant: `` `A ``, `` `A(P) ``.
    Tpat_variant(String, Option<Box<Pattern>>, RowDescRef),

    /// Record: `{l1: P1, ..., ln: Pn}` or `{l1: P1, ..., _}`.
    /// The bool indicates whether the field is optional.
    Tpat_record(
        Vec<(Loc<LidentIdx>, Arc<LabelDescription>, Pattern, bool)>,
        ClosedFlag,
        Option<Box<RecordPatternRest>>,
    ),

    /// Array: `[| P1, ..., Pn |]`.
    Tpat_array(Vec<Pattern>),

    /// Or-pattern: `P1 | P2`.
    /// The RowDesc is Some when translating type patterns.
    Tpat_or(Box<Pattern>, Box<Pattern>, Option<Box<RowDesc>>),
}

/// Typed record-rest binding (compiler/ml/typedtree.ml:38-43).
#[derive(Debug, Clone)]
pub struct RecordPatternRest {
    /// Identifier bound for the rest value.
    pub rest_ident: Ident,
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
    /// Extra information (constraints, opens, newtypes, etc.).
    pub exp_extra: SparseExtras<(ExpExtra, LocIdx, Attributes)>,
    /// Type of the expression.
    pub exp_type: TypeExprRef,
    /// Environment at this expression.
    pub exp_env: EnvRef,
    /// Attributes on the expression.
    pub exp_attributes: Attributes,
}

/// Extra information on an expression.
#[derive(Debug, Clone)]
pub enum ExpExtra {
    /// Type constraint: `E : T`.
    Texp_constraint(TypedCoreType),
    /// Coercion: `(E :> T)`.
    Texp_coerce(TypedCoreType),
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
    Texp_let(RecFlag, Vec<ValueBinding>, Box<Expression>),

    /// Function expression. Mirrors `compiler/ml/typedtree.ml`.
    Texp_function {
        params: Vec<FunctionParam>,
        body: Box<Expression>,
        /// Whether this is an async function.
        async_: bool,
    },

    /// Application: `E(E1, ..., En)`.
    /// Uses the ApplyArg representation.
    Texp_apply {
        funct: Box<Expression>,
        args: Vec<ApplyArg>,
        /// Whether this is a partial application.
        partial: bool,
        /// Whether this was transformed from JSX.
        transformed_jsx: bool,
    },

    /// Match: `switch E { | P1 => E1 | ... }`.
    /// The two case lists are (value cases, exception cases).
    Texp_match(Box<Expression>, Vec<Case>, Vec<Case>, Partial),

    /// Try: `try E catch { | P1 => E1 | ... }`.
    Texp_try(Box<Expression>, Vec<Case>),

    /// Tuple: `(E1, ..., En)`.
    Texp_tuple(Vec<Expression>),

    /// Constructor: `C`, `C(E)`, `C(E1, ..., En)`.
    Texp_construct(Loc<LidentIdx>, Arc<ConstructorDescription>, Vec<Expression>),

    /// Variant: `` `A ``, `` `A(E) ``.
    Texp_variant(String, Option<Box<Expression>>),

    /// Record: `{l1: E1, ..., ln: En}` or `{...E0, l1: E1, ...}`.
    /// Fields are (lid, label_desc, definition, optional).
    Texp_record {
        fields: Vec<RecordField>,
        extended_expression: Option<Box<Expression>>,
    },

    /// Intentional Rust performance representation for large regular records
    /// with many omitted optional fields.
    ///
    /// OCaml compiler/ml/typecore.ml:2833-2842 stores one entry per label from
    /// the shared `lbl_all` array. Keep the same external typedtree shape by
    /// expanding in serializers, but avoid copying hundreds of label
    /// descriptions into every sparse JSX record internally. The shared
    /// `all_labels` table is part of that optimization; consumers are expected
    /// to expand it at typedtree/lambda/raw-lambda boundaries.
    ///
    /// Do not remove this during parity cleanup unless the replacement keeps
    /// the same external typedtree/lambda/JS behavior and comparable
    /// large-record performance.
    Texp_record_sparse {
        fields: Vec<RecordField>,
        all_labels: std::sync::Arc<Vec<LabelDescription>>,
        omitted_loc: LocIdx,
        extended_expression: Option<Box<Expression>>,
    },

    /// Field access: `E.l`.
    Texp_field(Box<Expression>, Loc<LidentIdx>, Arc<LabelDescription>),

    /// Field mutation: `E.l = E'`.
    Texp_setfield(
        Box<Expression>,
        Loc<LidentIdx>,
        Arc<LabelDescription>,
        Box<Expression>,
    ),

    /// Array literal: `[E1, ..., En]`.
    Texp_array(Vec<Expression>),

    /// If-then-else: `if E1 then E2 else E3`.
    Texp_ifthenelse(Box<Expression>, Box<Expression>, Option<Box<Expression>>),

    /// Sequence: `E1; E2`.
    Texp_sequence(Box<Expression>, Box<Expression>),

    /// `break` (upstream #8348). Exits the nearest enclosing loop.
    Texp_break,

    /// `continue` (upstream #8348). Skips to the next iteration of the
    /// nearest enclosing loop.
    Texp_continue,

    /// While loop: `while E1 do E2 done`.
    Texp_while(Box<Expression>, Box<Expression>),

    /// For loop: `for i = E1 to/downto E2 do E3 done`.
    Texp_for(
        Ident,
        Box<Pattern>,
        Box<Expression>,
        Box<Expression>,
        DirectionFlag,
        Box<Expression>,
    ),

    /// For-of loop: `for pat of iterable { body }` (upstream #7887).
    /// The pattern stored is the original parser pattern (as in OCaml's
    /// `Texp_for_of of Ident.t * Parsetree.pattern * expression * expression`).
    Texp_for_of(
        Ident,
        Box<crate::parser::ast::Pattern>,
        Box<Expression>,
        Box<Expression>,
    ),

    /// For-await-of loop: `for await pat of asyncIterable { body }` (upstream #7887).
    Texp_for_await_of(
        Ident,
        Box<crate::parser::ast::Pattern>,
        Box<Expression>,
        Box<Expression>,
    ),

    /// Send: `E#m` (object method call).
    Texp_send(Box<Expression>, MethKind, Option<Box<Expression>>),

    /// Let module: `let module M = ME in E`.
    Texp_letmodule(Ident, Loc<String>, Box<ModuleExpr>, Box<Expression>),

    /// Let exception: `let exception C of T in E`.
    Texp_letexception(Box<ExtensionConstructor>, Box<Expression>),

    /// Assert: `assert E`.
    Texp_assert(Box<Expression>),

    /// Pack: `(module M : MT)`.
    Texp_pack(Box<ModuleExpr>),

    /// Extension constructor: `[%extension_constructor C]`.
    Texp_extension_constructor(Loc<LidentIdx>, Path),
}

// DirectionFlag and Arity are re-exported from parser::ast

/// Method kind for object method calls.
#[derive(Debug, Clone)]
pub enum MethKind {
    /// Direct method with known type.
    Tmeth_name(String),
    /// Virtual method (looked up at runtime).
    Tmeth_val(Ident),
}

/// Record label definition in a record expression.
#[derive(Debug, Clone)]
pub enum RecordLabelDefinition {
    /// Label is kept from extended expression.
    Kept(TypeExprRef),
    /// Label is overridden with new expression.
    Overridden(Loc<LidentIdx>, Expression),
    /// Intentional Rust performance representation for an omitted optional label
    /// synthesized as `None`.
    ///
    /// OCaml compiler/ml/typecore.ml:2833-2842 materializes this as
    /// `Overridden ({loc; txt = Lident lbl.lbl_name}, option_none lbl.lbl_arg loc)`.
    /// Keep the same typedtree boundary semantics without allocating a full
    /// `Texp_construct None` expression for every sparse JSX record field.
    OmittedOptionalNone(Loc<LidentIdx>, TypeExprRef),
}

pub type RecordField = (
    Loc<LidentIdx>,
    LabelDescription,
    RecordLabelDefinition,
    bool,
);

/// An argument in a function application.
#[derive(Debug, Clone)]
pub struct ApplyArg {
    /// Argument label.
    pub label: TypeArgLabel,
    /// Argument expression, or None for omitted labeled arguments.
    pub expression: Option<Expression>,
}

/// A function parameter. Mirrors `compiler/ml/typedtree.ml`.
#[derive(Debug, Clone)]
pub struct FunctionParam {
    /// Source argument label.
    pub fp_lbl: TypeArgLabel,
    /// Identifier bound by generated Lambda.
    pub fp_param: Ident,
    /// Typed source pattern.
    pub fp_pat: Pattern,
    /// Whether the parameter pattern is exhaustive.
    pub fp_partial: Partial,
}

// ============================================================================
// Cases and Bindings
// ============================================================================

/// A case in a match expression.
#[derive(Debug, Clone)]
pub struct Case {
    /// Left-hand side pattern.
    pub c_lhs: Pattern,
    /// Optional guard: `when E`.
    pub c_guard: Option<Expression>,
    /// Right-hand side expression.
    pub c_rhs: Expression,
}

/// A value binding in a let expression.
#[derive(Debug, Clone)]
pub struct ValueBinding {
    /// Binding pattern.
    pub vb_pat: Pattern,
    /// Binding expression.
    pub vb_expr: Expression,
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
    pub typ: Box<TypedCoreType>,
}

/// Typed core type description.
#[derive(Debug, Clone)]
pub enum TypedCoreTypeDesc {
    /// Type variable: `'a`.
    Ttyp_var(Option<String>),
    /// N-ary arrow type. Mirrors `compiler/ml/typedtree.ml`:
    /// `Ttyp_arrow of Parsetree.arg list * core_type`.
    Ttyp_arrow(Vec<ArrowArg>, Box<TypedCoreType>),
    /// Tuple type: `(T1, ..., Tn)`.
    Ttyp_tuple(Vec<TypedCoreType>),
    /// Type constructor: `t`, `M.t`, `('a, 'b) t`.
    Ttyp_constr(Path, Loc<LidentIdx>, Vec<TypedCoreType>),
    /// Object type: `< m1: T1; ...; mn: Tn >`.
    Ttyp_object(Vec<ObjectField>, ClosedFlag),
    /// Polymorphic type: `'a 'b. T`.
    Ttyp_poly(Vec<String>, Box<TypedCoreType>),
    /// Type alias: `T as 'a`.
    Ttyp_alias(Box<TypedCoreType>, String),
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
    OTtag(Loc<String>, TypedCoreType),
    /// Inherited type.
    OTinherit(TypedCoreType),
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
    Rtag(Loc<String>, bool, Vec<TypedCoreType>),
    /// Inherit: `T`.
    Rinherit(TypedCoreType),
}

/// A package type constraint.
#[derive(Debug, Clone)]
pub struct PackageType {
    /// Module type path.
    pub pack_path: Path,
    /// Type constraints.
    pub pack_fields: Vec<(Loc<LidentIdx>, TypedCoreType)>,
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
    Tmod_apply(Box<ModuleExpr>, Box<ModuleExpr>, ModuleCoercion),
    /// Functor.
    Tmod_functor(Ident, Loc<String>, Option<Box<ModuleType>>, Box<ModuleExpr>),
    /// Constraint.
    Tmod_constraint(
        Box<ModuleExpr>,
        DeclModuleType,
        ModuleTypeConstraint,
        ModuleCoercion,
    ),
    /// Unpack.
    Tmod_unpack(Expression, DeclModuleType),
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

impl ModuleType {
    /// Create a new placeholder module type (for backwards compat during incremental implementation).
    pub fn placeholder() -> Self {
        Self {
            mty_desc: ModuleTypeDesc::Tmty_placeholder,
            mty_type: DeclModuleType::MtySignature(std::sync::Arc::new(vec![])),
            mty_env: EnvRef(0),
            mty_loc: LocIdx(0),
            mty_attributes: Attributes::new(),
        }
    }
}

/// Module type description (matches OCaml's `Typedtree.module_type_desc`).
#[derive(Debug, Clone)]
pub enum ModuleTypeDesc {
    /// Named module type: `S` or `M.S`.
    Tmty_ident(Path, Loc<LidentIdx>),
    /// Signature: `sig ... end` / `{ ... }`.
    Tmty_signature(TypedSignature),
    /// Functor type: `functor (X : MT1) -> MT2`.
    Tmty_functor(Ident, Loc<String>, Option<Box<ModuleType>>, Box<ModuleType>),
    /// With constraint: `MT with ...`.
    Tmty_with(Box<ModuleType>, Vec<(Path, Loc<LidentIdx>, WithConstraint)>),
    /// Typeof: `module type of ME`.
    Tmty_typeof(Box<ModuleExpr>),
    /// Alias: `(module M)`.
    Tmty_alias(Path, Loc<LidentIdx>),
    /// Placeholder for incremental implementation.
    Tmty_placeholder,
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
    pub sig_items: Vec<TypedSignatureItem>,
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
    Tsig_value(TypedValueDescription),
    Tsig_type(RecFlag, Vec<TypedTypeDeclaration>),
    Tsig_typext(TypeExtension),
    Tsig_exception(ExtensionConstructor),
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
    pub md_type: ModuleType,
    pub md_attributes: Attributes,
    pub md_loc: LocIdx,
}

/// Include description (for signatures, matches OCaml's `Typedtree.include_description`).
#[derive(Debug, Clone)]
pub struct IncludeDescription {
    pub incl_mod: ModuleType,
    pub incl_type: Vec<crate::types::decl::SignatureItem>,
    pub incl_attributes: Attributes,
    pub incl_loc: LocIdx,
}

/// Module type constraint.
#[derive(Debug, Clone)]
pub enum ModuleTypeConstraint {
    /// Explicit signature.
    Tmodtype_explicit(Box<ModuleType>),
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
    /// Location of the primitive declaration.
    pub pc_loc: crate::location::Location,
    /// Identifier for the primitive.
    pub pc_id: crate::ident::Ident,
}

/// A structure (module definition body).
#[derive(Debug, Clone)]
pub struct Structure {
    /// Structure items.
    pub str_items: Vec<StructureItem>,
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
    Tstr_eval(Expression, Attributes),
    /// Value binding: `let P = E`.
    Tstr_value(RecFlag, Vec<ValueBinding>),
    /// Primitive declaration: `external f : t = "..."`.
    Tstr_primitive(TypedValueDescription),
    /// Type declaration: `type t = ...`.
    Tstr_type(RecFlag, Vec<TypedTypeDeclaration>),
    /// Type extension: `type t += ...`.
    Tstr_typext(TypeExtension),
    /// Exception declaration: `exception C`.
    Tstr_exception(ExtensionConstructor),
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
    pub typ_params: Vec<(TypedCoreType, Variance)>,
    /// Internal type declaration for the environment.
    pub typ_type: InternalTypeDeclaration,
    /// Type constraints.
    pub typ_cstrs: Vec<(TypedCoreType, TypedCoreType, LocIdx)>,
    /// Type kind.
    pub typ_kind: TypedTypeKind,
    /// Private flag.
    pub typ_private: PrivateFlag,
    /// Manifest type (for type aliases).
    pub typ_manifest: Option<TypedCoreType>,
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
    /// Constructor arguments.
    pub cd_args: TypedConstructorArguments,
    /// Result type (for GADTs).
    pub cd_res: Option<TypedCoreType>,
    /// Location.
    pub cd_loc: LocIdx,
    /// Attributes.
    pub cd_attributes: Attributes,
}

/// Typed constructor arguments.
#[derive(Debug, Clone)]
pub enum TypedConstructorArguments {
    /// Tuple arguments.
    Cstr_tuple(Vec<TypedCoreType>),
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
    /// Whether the label is mutable.
    pub ld_mutable: MutableFlag,
    /// Whether the label is optional.
    pub ld_optional: bool,
    /// Label type.
    pub ld_type: TypedCoreType,
    /// Location.
    pub ld_loc: LocIdx,
    /// Attributes.
    pub ld_attributes: Attributes,
}

/// A type extension.
#[derive(Debug, Clone)]
pub struct TypeExtension {
    /// Extended type path.
    pub tyext_path: Path,
    /// Type parameters.
    pub tyext_params: Vec<(TypedCoreType, Variance)>,
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
    pub mb_expr: ModuleExpr,
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
    pub mtd_type: Option<ModuleType>,
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
    pub incl_mod: ModuleExpr,
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
    pub val_desc: TypedCoreType,
    /// Primitive names.
    pub val_prim: Vec<String>,
    /// Location.
    pub val_loc: LocIdx,
    /// Attributes.
    pub val_attributes: Attributes,
}

/// Signature item (placeholder).
#[derive(Debug, Clone)]
pub struct SignatureItem {
    // Placeholder
    _placeholder: (),
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
    Text_decl(ConstructorArgument, Option<TypedCoreType>),
    /// Rebind to another constructor.
    Text_rebind(Path, Loc<LidentIdx>),
}

/// Constructor argument in extension declaration.
#[derive(Debug, Clone)]
pub enum ConstructorArgument {
    /// Tuple arguments.
    Cstr_tuple(Vec<TypedCoreType>),
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
    /// Whether the label is mutable.
    pub ld_mutable: MutableFlag,
    /// Whether the label is optional.
    pub ld_optional: bool,
    /// Label type.
    pub ld_type: TypedCoreType,
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
    /// Create a new pattern with all fields.
    pub fn new(
        desc: PatternDesc,
        loc: LocIdx,
        ty: TypeExprRef,
        env: EnvRef,
        attributes: Attributes,
    ) -> Self {
        Pattern {
            pat_desc: desc,
            pat_loc: loc,
            pat_extra: SparseExtras::new(),
            pat_type: ty,
            pat_env: env,
            pat_attributes: attributes,
        }
    }

    /// Add extra information to this pattern (constraint, unpack, etc.).
    pub fn with_pat_extra(mut self, extra: PatExtra, loc: LocIdx, attrs: Attributes) -> Self {
        self.pat_extra.push((extra, loc, attrs));
        self
    }
}

impl Expression {
    /// Create a new expression with all fields.
    pub fn new(
        desc: ExpressionDesc,
        loc: LocIdx,
        ty: TypeExprRef,
        env: EnvRef,
        attributes: Attributes,
    ) -> Self {
        Expression {
            exp_desc: desc,
            exp_loc: loc,
            exp_extra: SparseExtras::new(),
            exp_type: ty,
            exp_env: env,
            exp_attributes: attributes,
        }
    }

    /// Add extra information to this expression.
    pub fn with_exp_extra(mut self, extra: ExpExtra, loc: LocIdx, attrs: Attributes) -> Self {
        self.exp_extra.push((extra, loc, attrs));
        self
    }
}

impl Case {
    /// Create a new case with pattern and expression (no guard).
    pub fn simple(lhs: Pattern, rhs: Expression) -> Self {
        Case {
            c_lhs: lhs,
            c_guard: None,
            c_rhs: rhs,
        }
    }
}

impl ValueBinding {
    /// Create a new value binding.
    pub fn new(pat: Pattern, expr: Expression, loc: LocIdx, attributes: Attributes) -> Self {
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

        let s = Constant::String("hello".to_string(), None);
        assert!(matches!(s, Constant::String(_, None)));
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
        assert_eq!(size_of::<super::ExpressionDesc>(), 72);
        assert_eq!(size_of::<super::Expression>(), 112);
    }
}
