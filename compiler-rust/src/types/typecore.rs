//! Core type checking for the ReScript compiler.
//!
//! This module provides type checking for expressions and patterns,
//! corresponding to OCaml's `Typecore` module.
//!
//! # Architecture
//!
//! Type checking is performed in a context that contains:
//! - A [`TypeContext`] for allocating type expressions
//! - An [`Env`] for looking up bindings
//! - A [`DiagnosticsContext`] for collecting errors
//!
//! The main entry points are:
//! - [`type_expression`] - type check a top-level expression
//! - [`type_pattern`] - type check a pattern
//! - [`type_binding`] - type check a let binding
//!
//! # Threading Model
//!
//! The type checker is designed for concurrent compilation:
//! - No global state - all state is in explicit contexts
//! - Each file is type-checked independently
//! - Module interfaces are loaded from cache

#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(dead_code)]

use crate::ident::Ident;
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena, StrIdx};
use crate::parser::ast::{
    ArgLabel, Attributes, Expression as ParsedExpression, Pattern as ParsedPattern, PexpApply,
    PexpFun, RecFlag,
};
use crate::parser::longident::Longident;
use crate::types::typedtree::{
    ArrowArg, Constant, EnvRef, Expression, ExpressionDesc, Pattern, PatternDesc, ValueBinding,
};
use crate::types::{Env, Path, TypeContext, TypeError, TypeExprRef, UnifyState, ValueDescription};

// ============================================================================
// Location Conversion Helpers
// ============================================================================

/// Convert a parse_arena::Located<T> to a location::Located<T> with full Location.
fn convert_located<T: Clone>(loc: &Located<T>, arena: &ParseArena) -> crate::location::Located<T> {
    crate::location::Located {
        txt: loc.txt.clone(),
        loc: arena.to_location(loc.loc),
    }
}

/// Convert a LocIdx to a Location using the arena.
fn convert_loc(loc: LocIdx, arena: &ParseArena) -> Location {
    arena.to_location(loc)
}

/// Convert a Located<StrIdx> to a Located<String> (for typedtree which uses String).
fn convert_located_stridx(loc: &Located<StrIdx>, arena: &ParseArena) -> Located<String> {
    Located {
        txt: arena.get_string(loc.txt).to_string(),
        loc: loc.loc,
    }
}

// ============================================================================
// Error Types
// ============================================================================

/// Errors that can occur during type checking.
#[derive(Debug, Clone)]
pub enum TypeCoreError {
    /// Polymorphic label in pattern.
    PolymorphicLabel(Longident),

    /// Constructor arity mismatch.
    ConstructorArityMismatch {
        name: Longident,
        expected: usize,
        provided: usize,
    },

    /// Label mismatch in record pattern.
    LabelMismatch(Longident, Vec<(TypeExprRef, TypeExprRef)>),

    /// Pattern type clash.
    PatternTypeClash(Vec<(TypeExprRef, TypeExprRef)>),

    /// Or-pattern type clash.
    OrPatternTypeClash(Ident, Vec<(TypeExprRef, TypeExprRef)>),

    /// Variable bound multiple times.
    MultiplyBoundVariable(String),

    /// Variables don't match in or-pattern.
    OrpatVars(Ident, Vec<Ident>),

    /// Expression type clash.
    ExprTypeClash {
        trace: Vec<(TypeExprRef, TypeExprRef)>,
        context: Option<TypeClashContext>,
    },

    /// Applying non-function.
    ApplyNonFunction(TypeExprRef),

    /// Wrong label in application.
    ApplyWrongLabel(ArgLabel, TypeExprRef),

    /// Label defined multiple times.
    LabelMultiplyDefined {
        label: String,
        jsx_component_info: Option<JsxPropErrorInfo>,
    },

    /// Missing labels in record.
    LabelsMissing {
        labels: Vec<String>,
        jsx_component_info: Option<JsxPropErrorInfo>,
    },

    /// Attempting to mutate immutable field.
    LabelNotMutable(Longident),

    /// Wrong name in expression.
    WrongName {
        kind: String,
        ty: TypeExprRef,
        expected: String,
        path: Path,
        name: String,
        alternatives: Vec<String>,
    },

    /// Name/type mismatch.
    NameTypeMismatch {
        kind: String,
        lid: Longident,
        expected: (Path, Path),
        alternatives: Vec<(Path, Path)>,
    },

    /// Undefined method.
    UndefinedMethod {
        ty: TypeExprRef,
        method: String,
        alternatives: Option<Vec<String>>,
    },

    /// Private type.
    PrivateType(TypeExprRef),

    /// Private label.
    PrivateLabel(Longident, TypeExprRef),

    /// Too many arguments.
    TooManyArguments(bool, TypeExprRef),

    /// Abstract wrong label.
    AbstractWrongLabel(ArgLabel, TypeExprRef),

    /// Scoping let module.
    ScopingLetModule(String, TypeExprRef),

    /// Not a variant type.
    NotAVariantType(Longident),

    /// Incoherent label order.
    IncoherentLabelOrder,

    /// Less general type.
    LessGeneral(String, Vec<(TypeExprRef, TypeExprRef)>),

    /// Modules not allowed.
    ModulesNotAllowed,

    /// Cannot infer signature.
    CannotInferSignature,

    /// Not a packed module.
    NotAPackedModule(TypeExprRef),

    /// Recursive local constraint.
    RecursiveLocalConstraint(Vec<(TypeExprRef, TypeExprRef)>),

    /// Unexpected existential.
    UnexpectedExistential,

    /// Unqualified GADT pattern.
    UnqualifiedGadtPattern(Path, String),

    /// Invalid interval pattern.
    InvalidInterval,

    /// Invalid for loop index.
    InvalidForLoopIndex,

    /// No value clauses.
    NoValueClauses,

    /// Exception pattern below toplevel.
    ExceptionPatternBelowToplevel,

    /// Inlined record escape.
    InlinedRecordEscape,

    /// Inlined record expected.
    InlinedRecordExpected,

    /// Invalid extension constructor payload.
    InvalidExtensionConstructorPayload,

    /// Not an extension constructor.
    NotAnExtensionConstructor,

    /// Literal overflow.
    LiteralOverflow(String),

    /// Unknown literal.
    UnknownLiteral(String, char),

    /// Illegal let-rec pattern.
    IllegalLetrecPat,

    /// Empty record literal.
    EmptyRecordLiteral,

    /// Uncurried arity mismatch.
    UncurriedArityMismatch {
        function_type: TypeExprRef,
        expected_arity: usize,
        provided_arity: usize,
        provided_args: Vec<ArgLabel>,
        function_name: Option<Longident>,
    },

    /// Field not optional.
    FieldNotOptional(String, TypeExprRef),

    /// Type params not supported.
    TypeParamsNotSupported(Longident),

    /// Field access on dict type.
    FieldAccessOnDictType,

    /// JSX not enabled.
    JsxNotEnabled,
}

/// Context for type clash errors.
#[derive(Debug, Clone)]
pub enum TypeClashContext {
    /// In a function call.
    FunctionCall,
    /// In a braced identifier.
    BracedIdent,
    /// In a record spread.
    RecordSpread,
    /// In an array literal.
    ArrayLiteral,
    /// In a tuple.
    Tuple,
    /// In an if expression.
    IfExpression,
    /// In a switch expression.
    SwitchExpression,
}

/// JSX prop error info.
#[derive(Debug, Clone)]
pub struct JsxPropErrorInfo {
    /// Component name.
    pub component_name: String,
    /// Props.
    pub props: Vec<String>,
}

/// Result type for type checking.
pub type TypeCoreResult<T> = Result<T, TypeCoreError>;

// ============================================================================
// Pattern Mode
// ============================================================================

/// Mode for pattern type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatternMode {
    /// Normal pattern matching.
    Normal,
    /// Inside an or-pattern.
    InsideOr,
    /// Splitting an or-pattern.
    SplittingOr,
}

/// Whether recursive arguments are allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecArg {
    /// Allowed.
    Allowed,
    /// Required.
    Required,
    /// Rejected.
    Rejected,
}

// ============================================================================
// Type Checking State
// ============================================================================

/// State for pattern type checking.
pub struct PatternState {
    /// Pattern variables collected.
    pattern_variables: Vec<PatternVariable>,
    /// Whether modules are allowed.
    allow_modules: bool,
    /// Module variables collected.
    module_variables: Vec<(crate::location::Located<String>, Location)>,
}

/// A pattern variable with its binding information.
#[derive(Debug, Clone)]
pub struct PatternVariable {
    /// The identifier.
    pub id: Ident,
    /// The type.
    pub ty: TypeExprRef,
    /// The name with location.
    pub name: crate::location::Located<String>,
    /// The location.
    pub loc: Location,
    /// Whether this is an as-variable.
    pub is_as_variable: bool,
}

impl PatternState {
    /// Create a new pattern state.
    pub fn new() -> Self {
        PatternState {
            pattern_variables: Vec::new(),
            allow_modules: false,
            module_variables: Vec::new(),
        }
    }

    /// Enter a variable into the pattern state.
    /// Takes parsed Located<StrIdx> (with LocIdx) and arena to convert to Location.
    pub fn enter_variable(
        &mut self,
        loc: LocIdx,
        name: &Located<StrIdx>,
        ty: TypeExprRef,
        is_as_variable: bool,
        is_module: bool,
        arena: &ParseArena,
    ) -> TypeCoreResult<Ident> {
        let name_str = arena.get_string(name.txt);
        // Check for duplicate binding
        if self
            .pattern_variables
            .iter()
            .any(|pv| pv.id.name() == name_str)
        {
            return Err(TypeCoreError::MultiplyBoundVariable(name_str.to_string()));
        }

        let id = Ident::create_local(name_str);
        let full_loc = arena.to_location(loc);
        let full_name = crate::location::Located {
            txt: name_str.to_string(),
            loc: arena.to_location(name.loc),
        };
        self.pattern_variables.push(PatternVariable {
            id: id.clone(),
            ty,
            name: full_name.clone(),
            loc: full_loc.clone(),
            is_as_variable,
        });

        if is_module {
            if !self.allow_modules {
                return Err(TypeCoreError::ModulesNotAllowed);
            }
            self.module_variables.push((full_name, full_loc));
        }

        Ok(id)
    }

    /// Get pattern variables sorted by name.
    pub fn sorted_pattern_variables(&self) -> Vec<&PatternVariable> {
        let mut vars: Vec<_> = self.pattern_variables.iter().collect();
        vars.sort_by(|a, b| a.id.name().cmp(b.id.name()));
        vars
    }

    /// Reset the pattern state.
    pub fn reset(&mut self, allow_modules: bool) {
        self.pattern_variables.clear();
        self.allow_modules = allow_modules;
        self.module_variables.clear();
    }
}

impl Default for PatternState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Type Checking Context
// ============================================================================

/// Context for type checking.
pub struct TypeCheckContext<'a> {
    /// Type context for allocation.
    pub type_ctx: &'a TypeContext<'a>,
    /// Parse arena for location conversion and longident allocation.
    pub arena: &'a ParseArena,
    /// Unification state.
    pub unify_state: UnifyState,
    /// Newtype level (for local type definitions).
    pub newtype_level: Option<i32>,
    /// Collected diagnostics.
    pub diagnostics: Vec<TypeCoreDiagnostic>,
    /// Used type variables within the current type expression (for sharing).
    /// Maps type variable names to their TypeExprRef, matching OCaml's used_variables.
    pub used_variables: std::collections::HashMap<String, TypeExprRef>,
    /// Bound type variables from the surrounding declaration context.
    /// This matches OCaml's typetexp `type_variables` table used by
    /// `globalize_used_variables` to link per-type-expression variables
    /// back to declaration-level parameters.
    pub type_variables: std::collections::HashMap<String, TypeExprRef>,
    /// Persistent environment for loading external modules from .cmi files.
    pub persistent_env: Option<crate::cmi::persistent_env::PersistentEnv>,
    /// Recursion depth for currently-typed `let rec` groups.
    /// Used for recursive polymorphic-variant payload fallback.
    pub recursive_let_depth: usize,
    /// Active recursive value bindings currently in scope.
    /// Used to restrict recursive polymorphic-variant payload fallback to
    /// identifiers that actually resolve to recursive bindings.
    pub active_recursive_value_ids: Vec<Ident>,
    /// Scoped toggle used by type_application for OCaml-aligned local-float
    /// instantiation in repeated argument sites.
    pub force_fresh_local_float: bool,
}

/// A diagnostic from type checking.
#[derive(Debug, Clone)]
pub struct TypeCoreDiagnostic {
    /// Location of the error.
    pub loc: Location,
    /// The error.
    pub error: TypeCoreError,
}

impl<'a> TypeCheckContext<'a> {
    /// Create a new type check context.
    pub fn new(type_ctx: &'a TypeContext<'a>, arena: &'a ParseArena) -> Self {
        TypeCheckContext {
            type_ctx,
            arena,
            unify_state: UnifyState::new(),
            newtype_level: None,
            diagnostics: Vec::new(),
            used_variables: std::collections::HashMap::new(),
            type_variables: std::collections::HashMap::new(),
            persistent_env: None,
            recursive_let_depth: 0,
            active_recursive_value_ids: Vec::new(),
            force_fresh_local_float: false,
        }
    }

    /// Set the environment for type alias expansion during unification.
    pub fn set_unify_env(&mut self, env: &Env) {
        self.unify_state.set_env(env);
    }

    /// Set the persistent environment for module loading.
    pub fn set_persistent_env(&mut self, env: crate::cmi::persistent_env::PersistentEnv) {
        self.persistent_env = Some(env);
    }

    /// Report an error.
    pub fn report_error(&mut self, loc: Location, error: TypeCoreError) {
        self.diagnostics.push(TypeCoreDiagnostic { loc, error });
    }

    /// Get the newtype level.
    pub fn get_newtype_level(&self) -> TypeCoreResult<i32> {
        self.newtype_level
            .ok_or(TypeCoreError::UnexpectedExistential)
    }

    /// Resolve a LidentIdx to a Longident reference.
    pub fn resolve_lid(&self, idx: LidentIdx) -> &Longident {
        self.arena.get_longident(idx)
    }

    /// Convert a Located<LidentIdx> to Located<Longident> by cloning the longident.
    pub fn resolve_located_lid(&self, lid: &Located<LidentIdx>) -> Located<Longident> {
        Located {
            txt: self.arena.get_longident(lid.txt).clone(),
            loc: lid.loc,
        }
    }
}

// ============================================================================
// Constants
// ============================================================================

/// Type check a constant and return its type.
pub fn type_constant(ctx: &TypeContext<'_>, env: &Env, cst: &Constant) -> TypeExprRef {
    match cst {
        Constant::Int(_) => env.type_int(ctx),
        Constant::Char(_) => env.type_char(ctx),
        Constant::String(_, _) => env.type_string(ctx),
        Constant::Float(_) => env.type_float(ctx),
        Constant::BigInt(_, _) => env.type_bigint(ctx),
    }
}

/// Convert a parsed constant to a typed constant.
pub fn convert_constant(cst: &crate::parser::ast::Constant) -> TypeCoreResult<Constant> {
    use crate::parser::ast::Constant as ParsedConstant;

    match cst {
        ParsedConstant::Integer(s, None) => {
            // Try to parse as i32
            match s.parse::<i32>() {
                Ok(n) => Ok(Constant::Int(n.into())),
                Err(_) => Err(TypeCoreError::LiteralOverflow("int".to_string())),
            }
        }
        ParsedConstant::Integer(s, Some('n')) => {
            // BigInt
            let (sign, digits) = if s.starts_with('-') {
                (false, s[1..].to_string())
            } else {
                (true, s.to_string())
            };
            Ok(Constant::BigInt(sign, digits))
        }
        ParsedConstant::Integer(i, Some(c)) => {
            Err(TypeCoreError::UnknownLiteral(i.to_string(), *c))
        }
        ParsedConstant::Char(c) => Ok(Constant::Char(*c)),
        ParsedConstant::String(s, d) => Ok(Constant::String(
            s.to_string(),
            d.as_ref().map(|x| x.to_string()),
        )),
        ParsedConstant::Float(f, None) => Ok(Constant::Float(f.to_string())),
        ParsedConstant::Float(f, Some(c)) => Err(TypeCoreError::UnknownLiteral(f.to_string(), *c)),
    }
}

// ============================================================================
// Core Type Translation
// ============================================================================

/// Convert a parser ArgLabel to a types ArgLabel (for TypeContext methods).
fn convert_arg_label_for_ctx(
    lbl: &crate::parser::ast::ArgLabel,
    arena: &ParseArena,
) -> crate::types::ArgLabel {
    match lbl {
        crate::parser::ast::ArgLabel::Nolabel => crate::types::ArgLabel::Nolabel,
        crate::parser::ast::ArgLabel::Labelled(s) => crate::types::ArgLabel::labelled(
            arena.get_string(s.txt).to_string(),
            arena.to_location(s.loc),
        ),
        crate::parser::ast::ArgLabel::Optional(s) => crate::types::ArgLabel::optional(
            arena.get_string(s.txt).to_string(),
            arena.to_location(s.loc),
        ),
    }
}

/// Translate a parsed CoreType to a TypedCoreType and its corresponding TypeExprRef.
///
/// This function converts the surface syntax type annotations into the internal
/// type representation used by the type checker.
pub fn transl_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    styp: &crate::parser::ast::CoreType,
) -> TypeCoreResult<(crate::types::typedtree::TypedCoreType, TypeExprRef)> {
    transl_type_inner(tctx, env, styp)
}

/// Inner function for type translation.
fn transl_type_inner(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    styp: &crate::parser::ast::CoreType,
) -> TypeCoreResult<(crate::types::typedtree::TypedCoreType, TypeExprRef)> {
    use crate::parser::ast::CoreTypeDesc as CTD;
    use crate::types::typedtree::{TypedCoreType, TypedCoreTypeDesc};

    let ctx = tctx.type_ctx;
    let loc = styp.ptyp_loc.clone();

    match &*styp.ptyp_desc {
        CTD::Ptyp_any => {
            // Wildcard type: create a fresh type variable
            let ty = ctx.new_var(None);
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                ctyp_type: ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, ty))
        }

        CTD::Ptyp_var(name) => {
            // Type variable: 'a
            // Look up or create a type variable with this name
            let ty = ctx.new_var(Some(name.to_string()));
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(Some(name.to_string())),
                ctyp_type: ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, ty))
        }

        CTD::Ptyp_arrow(inner) => {
            let (ref arg, ref ret_idx, ref arity) = **inner;
            // Arrow type: T1 -> T2
            let (arg_ctyp, arg_ty) =
                transl_type_inner(tctx, env, tctx.arena.get_core_type(arg.typ))?;
            let ret = tctx.arena.get_core_type(*ret_idx);
            let (ret_ctyp, ret_ty) = transl_type_inner(tctx, env, ret)?;

            // Convert Arity to Option<i32> for typed tree (matches OCaml's arity option)
            // Arity is now ArityIdx, look up the value from the arena
            let arity_opt = tctx.arena.get_arity(*arity);

            // Convert parser ArgLabel to types ArgLabel for TypeContext
            let ctx_lbl = convert_arg_label_for_ctx(&arg.lbl, tctx.arena);
            let arrow_ty = ctx.new_arrow(ctx_lbl, arg_ty, ret_ty, arity_opt);

            // Create ArrowArg structure matching OCaml's
            let arrow_arg = ArrowArg {
                attrs: arg.attrs.clone(),
                lbl: convert_arg_label_for_ctx(&arg.lbl, tctx.arena),
                typ: Box::new(arg_ctyp),
            };

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_arrow(arrow_arg, Box::new(ret_ctyp), arity_opt),
                ctyp_type: arrow_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, arrow_ty))
        }

        CTD::Ptyp_tuple(types) => {
            // Tuple type: (T1, T2, ..., Tn)
            let mut typed_types = Vec::new();
            let mut type_refs = Vec::new();

            for t in types.iter() {
                let (ctyp, ty) = transl_type_inner(tctx, env, tctx.arena.get_core_type(*t))?;
                typed_types.push(ctyp);
                type_refs.push(ty);
            }

            let tuple_ty = ctx.new_tuple(type_refs);

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_tuple(typed_types),
                ctyp_type: tuple_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, tuple_ty))
        }

        CTD::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            // Type constructor: int, string, list<'a>, etc.
            let mut typed_args = Vec::new();
            let mut arg_refs = Vec::new();

            for arg in args {
                let (ctyp, ty) = transl_type_inner(tctx, env, tctx.arena.get_core_type(*arg))?;
                typed_args.push(ctyp);
                arg_refs.push(ty);
            }

            // Create path from longident
            // Full implementation would look up the type and use its actual path
            let longident = tctx.arena.get_longident(lid.txt);
            let name = tctx.arena.get_string(longident.last_idx());
            let path = Path::pident(Ident::create_persistent(name));

            let constr_ty = ctx.new_constr(path.clone(), arg_refs);

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_constr(path, lid.clone(), typed_args),
                ctyp_type: constr_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, constr_ty))
        }

        CTD::Ptyp_alias(inner) => {
            let (ref inner_idx, ref name) = **inner;
            // Type alias: T as 'a
            let inner = tctx.arena.get_core_type(*inner_idx);
            let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, inner)?;

            // Create a type variable for the alias name and unify with inner type
            let alias_var = ctx.new_var(Some(name.to_string()));
            crate::types::unify(ctx, &mut tctx.unify_state, alias_var, inner_ty)
                .map_err(|_| TypeCoreError::PatternTypeClash(vec![(alias_var, inner_ty)]))?;

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_alias(Box::new(inner_ctyp), name.to_string()),
                ctyp_type: inner_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, inner_ty))
        }

        CTD::Ptyp_poly(inner) => {
            let (ref vars, ref body_idx) = **inner;
            // Polymorphic type: 'a 'b. T
            let var_names: Vec<String> = vars
                .iter()
                .map(|v| tctx.arena.get_string(v.txt).to_string())
                .collect();

            // Create type variables for each bound variable
            for name in &var_names {
                let _var = ctx.new_var(Some(name.clone()));
            }

            let body = tctx.arena.get_core_type(*body_idx);
            let (body_ctyp, body_ty) = transl_type_inner(tctx, env, body)?;

            let poly_ty = ctx.new_poly(body_ty, vec![]);

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(var_names, Box::new(body_ctyp)),
                ctyp_type: poly_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, poly_ty))
        }

        CTD::Ptyp_object(inner) => {
            let (ref fields, ref closed) = **inner;
            // Object type: {. name: string, age: int }
            // Simplified implementation - full version builds proper object type
            let mut typed_fields = Vec::new();

            for field in fields.iter() {
                match field {
                    crate::parser::ast::ObjectField::Otag(label, attrs, field_type) => {
                        let (field_ctyp, _field_ty) =
                            transl_type_inner(tctx, env, tctx.arena.get_core_type(*field_type))?;

                        typed_fields.push(crate::types::typedtree::ObjectField {
                            of_desc: crate::types::typedtree::ObjectFieldDesc::OTtag(
                                Located {
                                    txt: tctx.arena.get_string(label.txt).to_string(),
                                    loc: label.loc.clone(),
                                },
                                field_ctyp,
                            ),
                            of_loc: label.loc.clone(),
                            of_attributes: attrs.clone(),
                        });
                    }
                    crate::parser::ast::ObjectField::Oinherit(inherit_type) => {
                        let inherit_ct = tctx.arena.get_core_type(*inherit_type);
                        let (inherit_ctyp, _inherit_ty) = transl_type_inner(tctx, env, inherit_ct)?;
                        typed_fields.push(crate::types::typedtree::ObjectField {
                            of_desc: crate::types::typedtree::ObjectFieldDesc::OTinherit(
                                inherit_ctyp,
                            ),
                            of_loc: inherit_ct.ptyp_loc.clone(),
                            of_attributes: Attributes::new().into(),
                        });
                    }
                }
            }

            // Use a fresh type variable for the object type (simplified)
            let obj_ty = ctx.new_var(None);

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_object(typed_fields, *closed),
                ctyp_type: obj_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, obj_ty))
        }

        CTD::Ptyp_variant(inner) => {
            let (ref rows, ref closed, ref labels) = **inner;
            // Polymorphic variant type: [> `A | `B of int ]
            let mut typed_rows = Vec::new();
            let row_more = ctx.new_var(None);

            for row in rows {
                match row {
                    crate::parser::ast::RowField::Rtag(label, attrs, constant, args) => {
                        let mut typed_args = Vec::new();
                        for arg in args {
                            let (arg_ctyp, _arg_ty) =
                                transl_type_inner(tctx, env, tctx.arena.get_core_type(*arg))?;
                            typed_args.push(arg_ctyp);
                        }

                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rtag(
                                Located {
                                    txt: label.txt.to_string(),
                                    loc: label.loc.clone(),
                                },
                                *constant,
                                typed_args,
                            ),
                            rf_loc: label.loc.clone(),
                            rf_attributes: attrs.clone(),
                        });
                    }
                    crate::parser::ast::RowField::Rinherit(inherit_type) => {
                        let inherit_ct = tctx.arena.get_core_type(*inherit_type);
                        let (inherit_ctyp, _inherit_ty) = transl_type_inner(tctx, env, inherit_ct)?;
                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rinherit(inherit_ctyp),
                            rf_loc: inherit_ct.ptyp_loc.clone(),
                            rf_attributes: Attributes::new().into(),
                        });
                    }
                }
            }

            // Create variant type
            let variant_ty = row_more; // Simplified - full implementation builds row type

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_variant(
                    typed_rows,
                    *closed,
                    labels
                        .as_ref()
                        .map(|v| v.iter().map(|s| s.to_string()).collect()),
                ),
                ctyp_type: variant_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, variant_ty))
        }

        CTD::Ptyp_package(pkg_inner) => {
            let (_mod_lid, _constraints) = &**pkg_inner;
            // Package type: (module S)
            // Simplified implementation - full version handles module types
            let ty = ctx.new_var(None);

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                ctyp_type: ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, ty))
        }

        CTD::Ptyp_extension(_) => {
            // Extension type: [%ext]
            // Return a fresh type variable for now
            let ty = ctx.new_var(None);
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(None),
                ctyp_type: ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, ty))
        }
    }
}

// ============================================================================
// Pattern Type Checking
// ============================================================================

/// Type check a pattern against an expected type.
pub fn type_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
) -> TypeCoreResult<Pattern> {
    type_pattern_inner(tctx, env, pat, expected_ty, mode, state, 0)
}

/// Inner pattern type checking with explode level.
fn type_pattern_inner(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    _explode: i32,
) -> TypeCoreResult<Pattern> {
    use crate::parser::ast::PatternDesc as PD;

    let loc = pat.ppat_loc.clone();
    let ctx = tctx.type_ctx;

    match &*pat.ppat_desc {
        PD::Ppat_any => {
            // Wildcard pattern matches any type
            Ok(Pattern::new(
                PatternDesc::Tpat_any,
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_var(name) => {
            // Variable pattern
            let id = state.enter_variable(loc, name, expected_ty, false, false, tctx.arena)?;
            Ok(Pattern::new(
                PatternDesc::Tpat_var(id, convert_located_stridx(name, tctx.arena)),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_constant(cst) => {
            // Constant pattern
            let constant = convert_constant(cst)?;
            let ty = type_constant(ctx, env, &constant);

            // Unify with expected type
            unify_pattern_types(tctx, loc, ty, expected_ty)?;

            Ok(Pattern::new(
                PatternDesc::Tpat_constant(constant),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_tuple(pats) => {
            // Tuple pattern
            assert!(pats.len() >= 2, "Tuple must have at least 2 elements");

            // Create fresh type variables for each element
            let elem_types: Vec<TypeExprRef> = pats.iter().map(|_| ctx.new_var(None)).collect();

            // Create tuple type and unify
            let tuple_ty = ctx.new_tuple(elem_types.clone());
            unify_pattern_types(tctx, loc, tuple_ty, expected_ty)?;

            // Type check each element
            let mut typed_pats = Vec::new();
            for (p, ty) in pats.iter().zip(elem_types.iter()) {
                let typed_pat =
                    type_pattern_inner(tctx, env, tctx.arena.get_pat(*p), *ty, mode, state, 0)?;
                typed_pats.push(typed_pat);
            }

            Ok(Pattern::new(
                PatternDesc::Tpat_tuple(typed_pats),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_alias(inner_pat_idx, name) => {
            // Alias pattern: P as x
            let inner_pat = tctx.arena.get_pat(*inner_pat_idx);
            let typed_inner =
                type_pattern_inner(tctx, env, inner_pat, expected_ty, mode, state, 0)?;

            // Build the as-type
            let ty_var = build_as_type(ctx, env, &typed_inner)?;

            // Enter the variable with the as-type
            let id = state.enter_variable(loc, name, ty_var, true, false, tctx.arena)?;

            Ok(Pattern::new(
                PatternDesc::Tpat_alias(
                    Box::new(typed_inner),
                    id,
                    convert_located_stridx(name, tctx.arena),
                ),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_or(p1_idx, p2_idx) => {
            // Or-pattern: P1 | P2
            let inner_mode = if mode == PatternMode::SplittingOr {
                PatternMode::Normal
            } else {
                mode
            };

            // Save pattern variables before p1
            let vars_before = state.pattern_variables.len();

            // Type check first branch
            let p1 = tctx.arena.get_pat(*p1_idx);
            let typed_p1 = type_pattern_inner(tctx, env, p1, expected_ty, inner_mode, state, 0)?;

            // Save p1's variables
            let p1_vars: Vec<_> = state.pattern_variables[vars_before..].to_vec();

            // Reset for p2
            state.pattern_variables.truncate(vars_before);

            // Type check second branch
            let p2 = tctx.arena.get_pat(*p2_idx);
            let typed_p2 = type_pattern_inner(tctx, env, p2, expected_ty, inner_mode, state, 0)?;

            // Get p2's variables
            let p2_vars: Vec<_> = state.pattern_variables[vars_before..].to_vec();

            // Merge variables (they should match)
            merge_or_pattern_variables(tctx, env, loc, &p1_vars, &p2_vars)?;

            Ok(Pattern::new(
                PatternDesc::Tpat_or(Box::new(typed_p1), Box::new(typed_p2), None),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_array(pats) => {
            // Array pattern
            let elem_ty = ctx.new_var(None);
            let array_ty = env.type_array(ctx, elem_ty);
            unify_pattern_types(tctx, loc, array_ty, expected_ty)?;

            let mut typed_pats = Vec::new();
            for p in pats.iter() {
                let typed_pat =
                    type_pattern_inner(tctx, env, tctx.arena.get_pat(*p), elem_ty, mode, state, 0)?;
                typed_pats.push(typed_pat);
            }

            Ok(Pattern::new(
                PatternDesc::Tpat_array(typed_pats),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_construct(lid, arg) => {
            // Constructor pattern: Some(x), None, etc.
            type_pattern_construct(
                tctx,
                env,
                loc,
                lid,
                (*arg).map(|idx| tctx.arena.get_pat(idx)),
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_variant(inner) => {
            let (ref label, ref arg) = **inner;
            // Polymorphic variant pattern: #Red, #Blue(x)
            type_pattern_variant(
                tctx,
                env,
                loc,
                label,
                (*arg).map(|idx| tctx.arena.get_pat(idx)),
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_record(inner) => {
            let (ref fields, ref closed_flag) = **inner;
            // Record pattern: {name, age}
            type_pattern_record(
                tctx,
                env,
                loc,
                fields,
                *closed_flag,
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_constraint(inner) => {
            let (ref inner_pat_idx, ref core_type) = **inner;
            // Type constraint pattern: (x : int)
            let inner_pat = tctx.arena.get_pat(*inner_pat_idx);
            type_pattern_constraint(
                tctx,
                env,
                loc,
                inner_pat,
                tctx.arena.get_core_type(*core_type),
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_interval(inner) => {
            let (ref c1, ref c2) = **inner;
            // Interval pattern: 'a'..'z'
            type_pattern_interval(tctx, env, loc, c1, c2, expected_ty, pat)
        }

        PD::Ppat_exception(inner_pat_idx) => {
            // Exception pattern
            let inner_pat = tctx.arena.get_pat(*inner_pat_idx);
            type_pattern_exception(tctx, env, loc, inner_pat, expected_ty, mode, state, pat)
        }

        PD::Ppat_open(mod_lid, inner_pat_idx) => {
            // Local open pattern: M.(p)
            let inner_pat = tctx.arena.get_pat(*inner_pat_idx);
            type_pattern_open(
                tctx,
                env,
                loc,
                mod_lid,
                inner_pat,
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        // Remaining patterns - return wildcard for now
        PD::Ppat_type(_) | PD::Ppat_unpack(_) | PD::Ppat_extension(_) => {
            // These patterns are less common, return wildcard for now
            Ok(Pattern::new(
                PatternDesc::Tpat_any,
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }
    }
}

/// Unify pattern types, raising PatternTypeClash on error.
fn unify_pattern_types(
    tctx: &mut TypeCheckContext<'_>,
    _loc: LocIdx,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeCoreResult<()> {
    use crate::types::unify;

    match unify(tctx.type_ctx, &mut tctx.unify_state, ty1, ty2) {
        Ok(()) => Ok(()),
        Err(TypeError::Unify(_)) => Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)])),
        Err(_) => Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)])),
    }
}

/// Build the type for an as-pattern.
fn build_as_type(ctx: &TypeContext<'_>, _env: &Env, pat: &Pattern) -> TypeCoreResult<TypeExprRef> {
    match &pat.pat_desc {
        PatternDesc::Tpat_alias(inner, _, _) => build_as_type(ctx, _env, inner),
        PatternDesc::Tpat_tuple(pats) => {
            let tys: Vec<_> = pats
                .iter()
                .map(|p| build_as_type(ctx, _env, p))
                .collect::<TypeCoreResult<_>>()?;
            Ok(ctx.new_tuple(tys))
        }
        _ => Ok(pat.pat_type),
    }
}

/// Merge variables from two or-pattern branches.
fn merge_or_pattern_variables(
    tctx: &mut TypeCheckContext<'_>,
    _env: &Env,
    loc: LocIdx,
    p1_vars: &[PatternVariable],
    p2_vars: &[PatternVariable],
) -> TypeCoreResult<Vec<(Ident, Ident)>> {
    // Sort both by name
    let mut p1_sorted: Vec<_> = p1_vars.iter().collect();
    let mut p2_sorted: Vec<_> = p2_vars.iter().collect();
    p1_sorted.sort_by(|a, b| a.id.name().cmp(b.id.name()));
    p2_sorted.sort_by(|a, b| a.id.name().cmp(b.id.name()));

    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;

    while i < p1_sorted.len() && j < p2_sorted.len() {
        let v1 = p1_sorted[i];
        let v2 = p2_sorted[j];

        match v1.id.name().cmp(v2.id.name()) {
            std::cmp::Ordering::Equal => {
                // Same variable - unify types
                unify_pattern_types(tctx, loc, v1.ty, v2.ty)?;
                result.push((v1.id.clone(), v2.id.clone()));
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => {
                // v1 has no match in p2
                return Err(TypeCoreError::OrpatVars(v1.id.clone(), vec![]));
            }
            std::cmp::Ordering::Greater => {
                // v2 has no match in p1
                return Err(TypeCoreError::OrpatVars(v2.id.clone(), vec![]));
            }
        }
    }

    if i < p1_sorted.len() {
        return Err(TypeCoreError::OrpatVars(p1_sorted[i].id.clone(), vec![]));
    }
    if j < p2_sorted.len() {
        return Err(TypeCoreError::OrpatVars(p2_sorted[j].id.clone(), vec![]));
    }

    Ok(result)
}

// ============================================================================
// Pattern Type Checking Helpers
// ============================================================================

/// Type check constructor pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_construct(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    lid: &Located<crate::parse_arena::LidentIdx>,
    arg: Option<&ParsedPattern>,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    let ctx = tctx.type_ctx;

    // Look up constructor
    let lid_txt = tctx.arena.get_longident(lid.txt);
    let cstr_name = tctx.arena.get_string(lid_txt.last_idx());
    let (cstr_desc, _cstr_path) = match env.find_constructor(cstr_name) {
        Ok(desc) => (
            desc.clone(),
            Path::pident(Ident::create_persistent(cstr_name)),
        ),
        Err(_) => {
            return Err(TypeCoreError::NotAVariantType(lid_txt.clone()));
        }
    };

    // Instantiate the result type
    let result_ty = crate::types::instance(ctx, cstr_desc.cstr_res);
    unify_pattern_types(tctx, loc, result_ty, expected_ty)?;

    // Type check the argument pattern(s)
    let arg_types = &cstr_desc.cstr_args;
    let typed_args = match (arg_types.as_slice(), arg) {
        (arg_types, Some(arg_pat)) if arg_types.len() == 1 => {
            // Single argument
            let arg_ty = crate::types::instance(ctx, arg_types[0]);
            let typed_arg = type_pattern_inner(tctx, env, arg_pat, arg_ty, mode, state, 0)?;
            vec![typed_arg]
        }
        (arg_types, Some(arg_pat)) if arg_types.len() > 1 => {
            // Multiple arguments - the parser wraps them in a tuple pattern
            // Type check as a tuple, then extract individual patterns
            let tuple_tys: Vec<_> = arg_types
                .iter()
                .map(|t| crate::types::instance(ctx, *t))
                .collect();
            let tuple_ty = ctx.new_tuple(tuple_tys);
            let typed_tuple = type_pattern_inner(tctx, env, arg_pat, tuple_ty, mode, state, 0)?;
            // Extract tuple pattern elements
            match &typed_tuple.pat_desc {
                PatternDesc::Tpat_tuple(elements) => elements.clone(),
                _ => vec![typed_tuple], // Fallback if not a tuple pattern
            }
        }
        (arg_types, None) if arg_types.is_empty() => {
            // Constant constructor
            vec![]
        }
        (arg_types, None) => {
            // Constructor needs arguments but none provided
            let lid_txt = tctx.arena.get_longident(lid.txt);
            return Err(TypeCoreError::ConstructorArityMismatch {
                name: lid_txt.clone(),
                expected: arg_types.len(),
                provided: 0,
            });
        }
        (_, Some(arg_pat)) => {
            // Inlined record - type check as-is
            let typed_arg =
                type_pattern_inner(tctx, env, arg_pat, ctx.new_var(None), mode, state, 0)?;
            vec![typed_arg]
        }
    };

    Ok(Pattern::new(
        PatternDesc::Tpat_construct(lid.clone(), cstr_desc, typed_args),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check polymorphic variant pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_variant(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    label: &str,
    arg: Option<&ParsedPattern>,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    use crate::types::typedtree::RowDescRef;
    let ctx = tctx.type_ctx;

    // Type check the argument if present
    let typed_arg = if let Some(arg_pat) = arg {
        let arg_ty = ctx.new_var(None);
        let typed = type_pattern_inner(tctx, env, arg_pat, arg_ty, mode, state, 0)?;
        Some(Box::new(typed))
    } else {
        None
    };

    // For polymorphic variants, we need a row type
    // Simplified - full implementation needs proper row types
    let variant_ty = ctx.new_var(None);
    unify_pattern_types(tctx, loc, variant_ty, expected_ty)?;

    Ok(Pattern::new(
        PatternDesc::Tpat_variant(label.to_string(), typed_arg, RowDescRef(0)),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check record pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_record(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    fields: &[crate::parser::ast::PatternRecordField],
    closed_flag: crate::parser::ast::ClosedFlag,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    let ctx = tctx.type_ctx;

    // Type check each field pattern
    let mut typed_fields = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let field_ty = ctx.new_var(None);
        let typed_pat = type_pattern_inner(
            tctx,
            env,
            tctx.arena.get_pat(field.pat),
            field_ty,
            mode,
            state,
            0,
        )?;

        // Create placeholder label description
        let label_desc = crate::types::LabelDescription {
            lbl_name: tctx.resolve_lid(field.lid.txt).to_string(),
            lbl_res: expected_ty,
            lbl_arg: field_ty,
            lbl_mut: crate::types::MutableFlag::Immutable,
            lbl_optional: field.opt,
            lbl_pos: idx as i32,
            lbl_all: crate::types::LabelArrayRef(0),
            lbl_repres: crate::types::RecordRepresentation::RecordRegular,
            lbl_private: crate::types::PrivateFlag::Public,
            lbl_loc: tctx.arena.to_location(field.lid.loc),
            lbl_attributes: vec![],
        };

        typed_fields.push((field.lid.clone(), label_desc, typed_pat, field.opt));
    }

    Ok(Pattern::new(
        PatternDesc::Tpat_record(typed_fields, closed_flag),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check constraint pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_constraint(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_pat: &ParsedPattern,
    core_type: &crate::parser::ast::CoreType,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    // Translate the type constraint
    let (typed_ctype, ctype_ty) = transl_type(tctx, env, core_type)?;

    // Unify the constraint type with the expected type
    if crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, expected_ty, ctype_ty).is_err() {
        return Err(TypeCoreError::PatternTypeClash(vec![(
            expected_ty,
            ctype_ty,
        )]));
    }

    // Type check the inner pattern with the constraint type
    let typed_inner = type_pattern_inner(tctx, env, inner_pat, ctype_ty, mode, state, 0)?;

    // Return the inner pattern with constraint in pat_extra
    Ok(typed_inner.with_pat_extra(
        crate::types::typedtree::PatExtra::Tpat_constraint(typed_ctype),
        loc.clone(),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check interval pattern.
fn type_pattern_interval(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    c1: &crate::parser::ast::Constant,
    c2: &crate::parser::ast::Constant,
    expected_ty: TypeExprRef,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    let ctx = tctx.type_ctx;

    // Convert constants
    let constant1 = convert_constant(c1)?;
    let constant2 = convert_constant(c2)?;

    // Get type of first constant (both should have same type)
    let const_ty = type_constant(ctx, env, &constant1);
    unify_pattern_types(tctx, loc, const_ty, expected_ty)?;

    // Validate that both constants are of the same type (char or int)
    match (&constant1, &constant2) {
        (Constant::Char(_), Constant::Char(_)) => {}
        (Constant::Int(_), Constant::Int(_)) => {}
        _ => return Err(TypeCoreError::InvalidInterval),
    }

    // Interval patterns are desugared to or-patterns in the typed tree
    // For simplicity, we represent as two constant patterns in an or-pattern
    let p1 = Pattern::new(
        PatternDesc::Tpat_constant(constant1),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        Attributes::new(),
    );
    let p2 = Pattern::new(
        PatternDesc::Tpat_constant(constant2),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        Attributes::new(),
    );

    Ok(Pattern::new(
        PatternDesc::Tpat_or(Box::new(p1), Box::new(p2), None),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check exception pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_exception(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_pat: &ParsedPattern,
    _expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    let ctx = tctx.type_ctx;

    // Exception patterns match the exn type
    let exn_ty = ctx.new_constr(Path::pident(Ident::create_persistent("exn")), vec![]);

    // Type check the inner pattern against exn
    let typed_inner = type_pattern_inner(tctx, env, inner_pat, exn_ty, mode, state, 0)?;

    // Exception patterns have a special representation
    // For now, just return the inner pattern (simplified)
    Ok(Pattern::new(
        typed_inner.pat_desc,
        loc.clone(),
        exn_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

/// Type check local open pattern.
#[allow(clippy::too_many_arguments)]
fn type_pattern_open(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    mod_lid: &Located<crate::parse_arena::LidentIdx>,
    inner_pat: &ParsedPattern,
    expected_ty: TypeExprRef,
    mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    // For now, just type check the inner pattern without opening the module
    // Full implementation would look up the module and extend the environment
    let typed_inner = type_pattern_inner(tctx, env, inner_pat, expected_ty, mode, state, 0)?;

    // Create the open pattern
    let mod_lid_txt = tctx.arena.get_longident(mod_lid.txt);
    let mod_name = tctx.arena.get_string(mod_lid_txt.last_idx());
    let _mod_path = Path::pident(Ident::create_persistent(mod_name));

    Ok(Pattern::new(
        PatternDesc::Tpat_or(Box::new(typed_inner.clone()), Box::new(typed_inner), None),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        pat.ppat_attributes.clone(),
    ))
}

// ============================================================================
// Expression Type Checking
// ============================================================================

/// Type check an expression against an expected type.
pub fn type_expect<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    expr: &ParsedExpression,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
) -> TypeCoreResult<Expression> {
    use crate::parser::ast::ExpressionDesc as ED;

    let loc = expr.pexp_loc.clone();
    let ctx = tctx.type_ctx;

    match &*expr.pexp_desc {
        ED::Pexp_ident(lid) => {
            // Identifier expression
            let longident = tctx.resolve_lid(lid.txt);
            let (path, desc) = env.lookup_value_by_lid(longident, tctx.arena, tctx.type_ctx)?;

            // Instantiate the type
            let ty = crate::types::instance(ctx, desc.val_type);

            // Unify with expected type
            unify_expression_types(tctx, loc, ty, expected_ty, context)?;

            Ok(Expression::new(
                ExpressionDesc::Texp_ident(path, lid.clone(), desc),
                loc,
                ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_constant(cst) => {
            // Constant expression
            let constant = convert_constant(cst)?;
            let ty = type_constant(ctx, env, &constant);

            // Unify with expected type
            unify_expression_types(tctx, loc, ty, expected_ty, context)?;

            Ok(Expression::new(
                ExpressionDesc::Texp_constant(constant),
                loc,
                ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_tuple(exprs) => {
            // Tuple expression
            assert!(exprs.len() >= 2, "Tuple must have at least 2 elements");

            // Create fresh type variables for each element
            let elem_types: Vec<TypeExprRef> = exprs.iter().map(|_| ctx.new_var(None)).collect();

            // Create tuple type and unify
            let tuple_ty = ctx.new_tuple(elem_types.clone());
            unify_expression_types(tctx, loc, tuple_ty, expected_ty, context)?;

            // Type check each element
            let mut typed_exprs = Vec::new();
            for (e, ty) in exprs.iter().zip(elem_types.iter()) {
                let typed_expr = type_expect(tctx, env, tctx.arena.get_expr(*e), *ty, None)?;
                typed_exprs.push(typed_expr);
            }

            Ok(Expression::new(
                ExpressionDesc::Texp_tuple(typed_exprs),
                loc,
                tuple_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body_idx) = **inner;
            // Let expression
            let (typed_bindings, new_env) = type_let_bindings(tctx, env, *rec_flag, bindings)?;

            // Type check body in extended environment
            let body = tctx.arena.get_expr(*body_idx);
            let typed_body = type_expect(tctx, &new_env, body, expected_ty, None)?;
            let body_type = typed_body.exp_type;

            Ok(Expression::new(
                ExpressionDesc::Texp_let(*rec_flag, typed_bindings, Box::new(typed_body)),
                loc,
                body_type,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_sequence(e1_idx, e2_idx) => {
            // Sequence expression: e1; e2
            // e1 should have type unit
            let unit_ty = env.type_unit(ctx);
            let e1 = tctx.arena.get_expr(*e1_idx);
            let typed_e1 = type_expect(tctx, env, e1, unit_ty, None)?;

            // e2 has the expected type
            let e2 = tctx.arena.get_expr(*e2_idx);
            let typed_e2 = type_expect(tctx, env, e2, expected_ty, None)?;
            let e2_type = typed_e2.exp_type;

            Ok(Expression::new(
                ExpressionDesc::Texp_sequence(Box::new(typed_e1), Box::new(typed_e2)),
                loc,
                e2_type,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_ifthenelse(inner) => {
            let (ref cond_idx, ref then_idx, ref else_idx) = **inner;
            // If expression
            let bool_ty = env.type_bool(ctx);

            // Condition should be bool
            let cond = tctx.arena.get_expr(*cond_idx);
            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;

            // Then branch has expected type
            let then_branch = tctx.arena.get_expr(*then_idx);
            let typed_then = type_expect(tctx, env, then_branch, expected_ty, None)?;

            // Else branch, if present
            let typed_else = if let Some(else_idx) = else_idx {
                let else_branch = tctx.arena.get_expr(*else_idx);
                let typed_else = type_expect(tctx, env, else_branch, expected_ty, None)?;
                Some(Box::new(typed_else))
            } else {
                // No else branch - result type should be unit
                let unit_ty = env.type_unit(ctx);
                unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;
                None
            };

            Ok(Expression::new(
                ExpressionDesc::Texp_ifthenelse(
                    Box::new(typed_cond),
                    Box::new(typed_then),
                    typed_else,
                ),
                loc,
                expected_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_while(cond_idx, body_idx) => {
            // While loop
            let bool_ty = env.type_bool(ctx);
            let unit_ty = env.type_unit(ctx);

            let cond = tctx.arena.get_expr(*cond_idx);
            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;
            let body = tctx.arena.get_expr(*body_idx);
            let typed_body = type_expect(tctx, env, body, unit_ty, None)?;

            // While loop has type unit
            unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;

            Ok(Expression::new(
                ExpressionDesc::Texp_while(Box::new(typed_cond), Box::new(typed_body)),
                loc,
                unit_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_assert(e_idx) => {
            // Assert expression
            let bool_ty = env.type_bool(ctx);
            let unit_ty = env.type_unit(ctx);

            let e = tctx.arena.get_expr(*e_idx);
            let typed_e = type_expect(tctx, env, e, bool_ty, None)?;

            // Assert has type unit
            unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;

            Ok(Expression::new(
                ExpressionDesc::Texp_assert(Box::new(typed_e)),
                loc,
                unit_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_array(exprs) => {
            // Array expression
            let elem_ty = ctx.new_var(None);
            let array_ty = env.type_array(ctx, elem_ty);

            unify_expression_types(tctx, loc, array_ty, expected_ty, context)?;

            let mut typed_exprs = Vec::new();
            for e in exprs.iter() {
                let typed_e = type_expect(
                    tctx,
                    env,
                    tctx.arena.get_expr(*e),
                    elem_ty,
                    Some(TypeClashContext::ArrayLiteral),
                )?;
                typed_exprs.push(typed_e);
            }

            Ok(Expression::new(
                ExpressionDesc::Texp_array(typed_exprs),
                loc,
                array_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ref partial,
                ref transformed_jsx,
            } = **inner;
            // Function application
            let funct_expr = tctx.arena.get_expr(*funct);
            type_application(
                tctx,
                env,
                loc,
                funct_expr,
                args,
                *partial,
                *transformed_jsx,
                expected_ty,
                context,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_match(inner) => {
            let (ref scrutinee_idx, ref cases) = **inner;
            // Match expression
            let scrutinee = tctx.arena.get_expr(*scrutinee_idx);
            type_match(
                tctx,
                env,
                loc,
                scrutinee,
                cases,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_try(inner) => {
            let (ref body_idx, ref handlers) = **inner;
            // Try expression
            let body = tctx.arena.get_expr(*body_idx);
            type_try(
                tctx,
                env,
                loc,
                body,
                handlers,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_fun(inner) => {
            let PexpFun {
                ref arg_label,
                ref default,
                ref lhs,
                ref rhs,
                ref arity,
                ref is_async,
            } = **inner;
            // Function expression
            let default_expr = (*default).map(|idx| tctx.arena.get_expr(idx));
            let lhs_pat = tctx.arena.get_pat(*lhs);
            let rhs_expr = tctx.arena.get_expr(*rhs);
            type_function(
                tctx,
                env,
                loc,
                arg_label,
                default_expr,
                lhs_pat,
                rhs_expr,
                arity.clone(),
                *is_async,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_for(inner) => {
            let (ref pat, ref start_idx, ref end_idx, ref direction, ref body_idx) = **inner;
            // For loop
            let pat_ref = tctx.arena.get_pat(*pat);
            let start_expr = tctx.arena.get_expr(*start_idx);
            let end_expr = tctx.arena.get_expr(*end_idx);
            let body = tctx.arena.get_expr(*body_idx);
            type_for(
                tctx,
                env,
                loc,
                pat_ref,
                start_expr,
                end_expr,
                *direction,
                body,
                expected_ty,
                context,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_construct(lid, arg) => {
            // Constructor application
            type_construct(
                tctx,
                env,
                loc,
                lid,
                (*arg).map(|idx| tctx.arena.get_expr(idx)),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_variant(inner) => {
            let (ref label, ref arg) = **inner;
            // Polymorphic variant
            type_variant(
                tctx,
                env,
                loc,
                label,
                (*arg).map(|idx| tctx.arena.get_expr(idx)),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_record(inner) => {
            let (ref fields, ref base) = **inner;
            // Record expression
            type_record(
                tctx,
                env,
                loc,
                fields,
                (*base).map(|idx| tctx.arena.get_expr(idx)),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_field(record_expr_idx, field_lid) => {
            // Field access
            let record_expr = tctx.arena.get_expr(*record_expr_idx);
            type_field(
                tctx,
                env,
                loc,
                record_expr,
                field_lid,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_setfield(inner) => {
            let (ref record_expr_idx, ref field_lid, ref new_value_idx) = **inner;
            // Field assignment
            let record_expr = tctx.arena.get_expr(*record_expr_idx);
            let new_value = tctx.arena.get_expr(*new_value_idx);
            type_setfield(
                tctx,
                env,
                loc,
                record_expr,
                field_lid,
                new_value,
                expected_ty,
                context,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_constraint(inner) => {
            let (ref inner_expr_idx, ref core_type) = **inner;
            // Type constraint
            let inner_expr = tctx.arena.get_expr(*inner_expr_idx);
            let core_type_ref = tctx.arena.get_core_type(*core_type);
            type_constraint(
                tctx,
                env,
                loc,
                inner_expr,
                core_type_ref,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_coerce(inner) => {
            let (ref inner_expr_idx, ref opt_from_type, ref to_type) = **inner;
            // Type coercion: (E :> T) or (E : T1 :> T2)
            let inner_expr = tctx.arena.get_expr(*inner_expr_idx);
            let to_type_ref = tctx.arena.get_core_type(*to_type);
            let opt_from_type_ref = opt_from_type.map(|idx| tctx.arena.get_core_type(idx));
            type_coerce(
                tctx,
                env,
                loc,
                inner_expr,
                opt_from_type_ref,
                to_type_ref,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_open(inner) => {
            let (ref _override_flag, ref lid, ref body_idx) = **inner;
            // Open expression: M.{ E } or open M; E
            let body = tctx.arena.get_expr(*body_idx);
            type_open(
                tctx,
                env,
                loc,
                lid,
                body,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_newtype(inner) => {
            let (ref name, ref body_idx) = **inner;
            // Newtype expression: (type t) => E
            let body = tctx.arena.get_expr(*body_idx);
            type_newtype(
                tctx,
                env,
                loc,
                name,
                body,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_await(inner_expr_idx) => {
            // Await expression: await E
            let inner_expr = tctx.arena.get_expr(*inner_expr_idx);
            type_await(
                tctx,
                env,
                loc,
                inner_expr,
                expected_ty,
                context,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_send(inner) => {
            let (ref obj_expr_idx, ref method) = **inner;
            // Method send: E#m
            let obj_expr = tctx.arena.get_expr(*obj_expr_idx);
            type_send(
                tctx,
                env,
                loc,
                obj_expr,
                method,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_letexception(inner) => {
            let (ref ext_constr, ref body_idx) = **inner;
            // Let exception: { exception C; E }
            let body = tctx.arena.get_expr(*body_idx);
            type_letexception(
                tctx,
                env,
                loc,
                ext_constr,
                body,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_extension(extension) => {
            // Extension: [%id]
            type_extension_expr(
                tctx,
                env,
                loc,
                extension,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_letmodule(inner) => {
            let (ref name, ref module_expr, ref body_idx) = **inner;
            // Let module: { module M = ME; E }
            let module_expr_ref = tctx.arena.get_mod_expr(*module_expr);
            let body = tctx.arena.get_expr(*body_idx);
            type_letmodule(
                tctx,
                env,
                loc,
                name,
                module_expr_ref,
                body,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_pack(module_expr_idx) => {
            // Pack: module(ME)
            let module_expr = tctx.arena.get_mod_expr(*module_expr_idx);
            type_pack(
                tctx,
                env,
                loc,
                module_expr,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_jsx_element(jsx_element) => {
            // JSX element - typically transformed before type checking
            type_jsx_element(
                tctx,
                env,
                loc,
                jsx_element,
                expected_ty,
                &expr.pexp_attributes,
            )
        }
    }
}

/// Unify expression types, raising ExprTypeClash on error.
fn unify_expression_types(
    tctx: &mut TypeCheckContext<'_>,
    _loc: LocIdx,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
    context: Option<TypeClashContext>,
) -> TypeCoreResult<()> {
    use crate::types::unify;

    match unify(tctx.type_ctx, &mut tctx.unify_state, ty1, ty2) {
        Ok(()) => Ok(()),
        Err(_) => Err(TypeCoreError::ExprTypeClash {
            trace: vec![(ty1, ty2)],
            context,
        }),
    }
}

// ============================================================================
// Expression Type Checking Helpers
// ============================================================================

/// Type check function application.
#[allow(clippy::too_many_arguments)]
fn type_application(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    funct: &ParsedExpression,
    args: &[(ArgLabel, crate::parse_arena::ExprIdx)],
    _partial: bool,
    _transformed_jsx: bool,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::ApplyArg;

    let ctx = tctx.type_ctx;

    // Type check the function
    let funct_ty = ctx.new_var(None);
    let typed_funct = type_expect(tctx, env, funct, funct_ty, None)?;

    // Get the function's type after any unification
    let mut current_ty = tctx.type_ctx.repr(typed_funct.exp_type);

    // Type check arguments, extracting/building arrow types as we go
    let mut typed_args = Vec::new();
    for (label, arg_expr_idx) in args.iter() {
        // Try to extract argument type from current function type
        let (arg_ty, ret_ty) = match crate::types::split_arrow(ctx, current_ty) {
            Some((arg, ret)) => (arg, ret),
            None => {
                // Not a function type yet - create arrow type
                let arg_ty = ctx.new_var(None);
                let ret_ty = ctx.new_var(None);
                let arrow_ty = ctx.new_arrow_simple(arg_ty, ret_ty);
                unify_expression_types(tctx, loc, current_ty, arrow_ty, None)?;
                (arg_ty, ret_ty)
            }
        };

        // Type check the argument
        let arg_expr = tctx.arena.get_expr(*arg_expr_idx);
        let typed_arg = type_expect(
            tctx,
            env,
            arg_expr,
            arg_ty,
            Some(TypeClashContext::FunctionCall),
        )?;
        typed_args.push(ApplyArg {
            label: convert_arg_label_for_ctx(label, tctx.arena),
            expression: Some(typed_arg),
        });

        // Move to return type for next argument
        current_ty = ret_ty;
    }

    // The final current_ty is the result type
    let result_ty = current_ty;

    // Unify result with expected type
    unify_expression_types(tctx, loc, result_ty, expected_ty, context)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_apply {
            funct: Box::new(typed_funct),
            args: typed_args,
            partial: false,
            transformed_jsx: false,
        },
        loc.clone(),
        result_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check match expression.
fn type_match(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    scrutinee: &ParsedExpression,
    cases: &[crate::parser::ast::Case],
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::Partial;

    let ctx = tctx.type_ctx;

    // Type the scrutinee
    let scrutinee_ty = ctx.new_var(None);
    let typed_scrutinee = type_expect(tctx, env, scrutinee, scrutinee_ty, None)?;

    // Type check each case
    let mut typed_cases = Vec::new();
    for case in cases {
        let typed_case = type_case(tctx, env, case, scrutinee_ty, expected_ty)?;
        typed_cases.push(typed_case);
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_match(
            Box::new(typed_scrutinee),
            typed_cases,
            vec![],         // No exception cases for now
            Partial::Total, // Assume total for now
        ),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check a single case.
fn type_case(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    case: &crate::parser::ast::Case,
    scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
) -> TypeCoreResult<crate::types::typedtree::Case> {
    let mut state = PatternState::new();

    // Type check the pattern
    let typed_pat = type_pattern(
        tctx,
        env,
        tctx.arena.get_pat(case.pc_lhs),
        scrutinee_ty,
        PatternMode::Normal,
        &mut state,
    )?;

    // Extend environment with pattern bindings
    let mut case_env = env.clone();
    for pv in &state.pattern_variables {
        let desc = ValueDescription {
            val_type: pv.ty,
            val_kind: crate::types::ValueKind::ValReg,
            val_loc: pv.loc.clone(),
            val_attributes: vec![],
            val_path: None,
        };
        case_env.add_value(pv.id.clone(), desc);
    }

    // Type check the guard if present
    let typed_guard = if let Some(guard) = &case.pc_guard {
        let bool_ty = env.type_bool(tctx.type_ctx);
        Some(type_expect(
            tctx,
            &case_env,
            tctx.arena.get_expr(*guard),
            bool_ty,
            None,
        )?)
    } else {
        None
    };

    // Type check the body
    let typed_body = type_expect(
        tctx,
        &case_env,
        tctx.arena.get_expr(case.pc_rhs),
        body_ty,
        None,
    )?;

    Ok(crate::types::typedtree::Case {
        c_lhs: typed_pat,
        c_guard: typed_guard,
        c_rhs: typed_body,
    })
}

/// Type check try expression.
fn type_try(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    body: &ParsedExpression,
    handlers: &[crate::parser::ast::Case],
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // Type check the body with expected type
    let typed_body = type_expect(tctx, env, body, expected_ty, None)?;

    // Type check each handler
    // Exception type (exn)
    let exn_ty = ctx.new_constr(Path::pident(Ident::create_persistent("exn")), vec![]);

    let mut typed_handlers = Vec::new();
    for handler in handlers {
        let typed_case = type_case(tctx, env, handler, exn_ty, expected_ty)?;
        typed_handlers.push(typed_case);
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_try(Box::new(typed_body), typed_handlers),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check function expression.
#[allow(clippy::too_many_arguments)]
fn type_function(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    arg_label: &ArgLabel,
    default: Option<&ParsedExpression>,
    param: &ParsedPattern,
    body: &ParsedExpression,
    arity: crate::parser::ast::Arity,
    _is_async: bool,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::{Case, FunctionParam, FunctionParamPattern, Partial};

    let ctx = tctx.type_ctx;

    // Create type for parameter
    let param_ty = ctx.new_var(None);
    let return_ty = ctx.new_var(None);

    // Convert arity to Option<i32> for the arrow type
    // Arity is now ArityIdx, look up from arena
    let arity_opt = tctx.arena.get_arity(arity);

    // Build function type with arity and label
    let ctx_label = convert_arg_label_for_ctx(arg_label, tctx.arena);
    let func_ty = ctx.new_arrow(ctx_label, param_ty, return_ty, arity_opt);
    unify_expression_types(tctx, loc, func_ty, expected_ty, None)?;

    // Type check parameter pattern
    let mut state = PatternState::new();
    let typed_param = type_pattern(tctx, env, param, param_ty, PatternMode::Normal, &mut state)?;

    // Type check default expression if present
    let typed_default = if let Some(default_expr) = default {
        Some(Box::new(type_expect(
            tctx,
            env,
            default_expr,
            param_ty,
            None,
        )?))
    } else {
        None
    };

    // Extend environment with parameter binding
    let mut body_env = env.clone();
    for pv in &state.pattern_variables {
        let desc = ValueDescription {
            val_type: pv.ty,
            val_kind: crate::types::ValueKind::ValReg,
            val_loc: pv.loc.clone(),
            val_attributes: vec![],
            val_path: None,
        };
        body_env.add_value(pv.id.clone(), desc);
    }

    // Type check body
    let typed_body = type_expect(tctx, &body_env, body, return_ty, None)?;

    // Build function parameter
    let fp = FunctionParam {
        label: arg_label.clone(),
        default: typed_default,
        pat: FunctionParamPattern::Simple(typed_param.clone()),
    };

    // Build single case for the body
    let cases = vec![Case {
        c_lhs: typed_param,
        c_guard: None,
        c_rhs: typed_body,
    }];

    Ok(Expression::new(
        ExpressionDesc::Texp_function {
            params: vec![fp],
            body: cases,
            partial: Partial::Total,
            arity,
            async_: false,
        },
        loc.clone(),
        func_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check for loop.
#[allow(clippy::too_many_arguments)]
fn type_for(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    pat: &ParsedPattern,
    start_expr: &ParsedExpression,
    end_expr: &ParsedExpression,
    direction: crate::parser::ast::DirectionFlag,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;
    let int_ty = env.type_int(ctx);
    let unit_ty = env.type_unit(ctx);

    // Type check bounds
    let typed_start = type_expect(tctx, env, start_expr, int_ty, None)?;
    let typed_end = type_expect(tctx, env, end_expr, int_ty, None)?;

    // Type check pattern (must be variable binding an int)
    let mut state = PatternState::new();
    let typed_pat = type_pattern(tctx, env, pat, int_ty, PatternMode::Normal, &mut state)?;

    // The loop variable
    let loop_var_id = if state.pattern_variables.len() == 1 {
        state.pattern_variables[0].id.clone()
    } else {
        return Err(TypeCoreError::InvalidForLoopIndex);
    };

    // Extend environment with loop variable
    let mut body_env = env.clone();
    for pv in &state.pattern_variables {
        let desc = ValueDescription {
            val_type: pv.ty,
            val_kind: crate::types::ValueKind::ValReg,
            val_loc: pv.loc.clone(),
            val_attributes: vec![],
            val_path: None,
        };
        body_env.add_value(pv.id.clone(), desc);
    }

    // Type check body (should be unit)
    let typed_body = type_expect(tctx, &body_env, body, unit_ty, None)?;

    // For loop has type unit
    unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_for(
            loop_var_id,
            Box::new(typed_pat),
            Box::new(typed_start),
            Box::new(typed_end),
            direction,
            Box::new(typed_body),
        ),
        loc.clone(),
        unit_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check constructor application.
fn type_construct(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    lid: &Located<LidentIdx>,
    arg: Option<&ParsedExpression>,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;
    let longident = tctx.resolve_lid(lid.txt);

    // Look up constructor
    let cstr_name = tctx.arena.get_string(longident.last_idx());
    let (_cstr_path, cstr_desc) = match env.find_constructor(cstr_name) {
        Ok(desc) => (
            Path::pident(Ident::create_persistent(cstr_name)),
            desc.clone(),
        ),
        Err(_) => {
            return Err(TypeCoreError::NotAVariantType(longident.clone()));
        }
    };

    // Get the result type (instantiate if polymorphic)
    let result_ty = crate::types::instance(ctx, cstr_desc.cstr_res);
    unify_expression_types(tctx, loc, result_ty, expected_ty, None)?;

    // Type check arguments
    let arg_types = &cstr_desc.cstr_args;
    let typed_args = match (arg_types.as_slice(), arg) {
        (arg_types, Some(arg_expr)) if arg_types.len() == 1 => {
            // Single argument
            let arg_ty = crate::types::instance(ctx, arg_types[0]);
            let typed_arg = type_expect(tctx, env, arg_expr, arg_ty, None)?;
            vec![typed_arg]
        }
        (arg_types, Some(arg_expr)) if arg_types.len() > 1 => {
            // Multiple arguments - the parser wraps them in a tuple
            // Type check as a tuple, then extract individual elements
            let instantiated_arg_types: Vec<_> = arg_types
                .iter()
                .map(|t| crate::types::instance(ctx, *t))
                .collect();
            let tuple_ty = ctx.new_tuple(instantiated_arg_types);
            let typed_tuple = type_expect(tctx, env, arg_expr, tuple_ty, None)?;
            // Extract tuple elements
            match &typed_tuple.exp_desc {
                ExpressionDesc::Texp_tuple(elements) => elements.clone(),
                _ => vec![typed_tuple], // Fallback if not a tuple
            }
        }
        (arg_types, None) if arg_types.is_empty() => {
            // Constant constructor with no arguments
            vec![]
        }
        (arg_types, None) => {
            // Constructor needs arguments but none provided
            let longident = tctx.resolve_lid(lid.txt);
            return Err(TypeCoreError::ConstructorArityMismatch {
                name: longident.clone(),
                expected: arg_types.len(),
                provided: 0,
            });
        }
        (_, Some(arg_expr)) => {
            // Inlined record - type check the expression
            let typed_arg = type_expect(tctx, env, arg_expr, ctx.new_var(None), None)?;
            vec![typed_arg]
        }
    };

    Ok(Expression::new(
        ExpressionDesc::Texp_construct(lid.clone(), cstr_desc, typed_args),
        loc.clone(),
        result_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check polymorphic variant.
fn type_variant(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    label: &str,
    arg: Option<&ParsedExpression>,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // Type check argument if present
    let typed_arg = if let Some(arg_expr) = arg {
        let arg_ty = ctx.new_var(None);
        let typed = type_expect(tctx, env, arg_expr, arg_ty, None)?;
        Some(Box::new(typed))
    } else {
        None
    };

    // For polymorphic variants, create a row type
    // This is simplified - full implementation needs row types
    let variant_ty = ctx.new_var(None);
    unify_expression_types(tctx, loc, variant_ty, expected_ty, None)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_variant(label.to_string(), typed_arg),
        loc.clone(),
        variant_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check record expression.
fn type_record(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    fields: &[crate::parser::ast::ExpressionRecordField],
    base: Option<&ParsedExpression>,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::RecordLabelDefinition;

    let ctx = tctx.type_ctx;

    // Type check base expression if present
    let typed_base = if let Some(base_expr) = base {
        let base_ty = ctx.new_var(None);
        let typed = type_expect(tctx, env, base_expr, base_ty, None)?;
        // Unify base type with expected
        unify_expression_types(
            tctx,
            loc,
            base_ty,
            expected_ty,
            Some(TypeClashContext::RecordSpread),
        )?;
        Some(typed)
    } else {
        None
    };

    // Type check each field
    let mut typed_fields = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        // Type check the field expression
        let field_ty = ctx.new_var(None);
        let typed_expr = type_expect(tctx, env, tctx.arena.get_expr(field.expr), field_ty, None)?;

        // Create a placeholder label description
        let label_desc = crate::types::LabelDescription {
            lbl_name: tctx.resolve_lid(field.lid.txt).to_string(),
            lbl_res: expected_ty,
            lbl_arg: field_ty,
            lbl_mut: crate::types::MutableFlag::Immutable,
            lbl_optional: field.opt,
            lbl_pos: idx as i32,
            lbl_all: crate::types::LabelArrayRef(0), // Placeholder
            lbl_repres: crate::types::RecordRepresentation::RecordRegular,
            lbl_private: crate::types::PrivateFlag::Public,
            lbl_loc: tctx.arena.to_location(field.lid.loc),
            lbl_attributes: vec![],
        };

        typed_fields.push((
            field.lid.clone(),
            label_desc,
            RecordLabelDefinition::Overridden(field.lid.clone(), typed_expr),
            field.opt,
        ));
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_record {
            fields: typed_fields,
            extended_expression: typed_base.map(Box::new),
        },
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check field access.
fn type_field(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    record_expr: &ParsedExpression,
    field_lid: &Located<LidentIdx>,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // Type check the record expression
    let record_ty = ctx.new_var(None);
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;

    // Look up the field - for now just create placeholder
    let field_ty = ctx.new_var(None);
    unify_expression_types(tctx, loc, field_ty, expected_ty, None)?;

    // Create placeholder label description
    let label_desc = crate::types::LabelDescription {
        lbl_name: tctx.resolve_lid(field_lid.txt).to_string(),
        lbl_res: record_ty,
        lbl_arg: field_ty,
        lbl_mut: crate::types::MutableFlag::Immutable,
        lbl_optional: false,
        lbl_pos: 0,
        lbl_all: crate::types::LabelArrayRef(0),
        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
        lbl_private: crate::types::PrivateFlag::Public,
        lbl_loc: tctx.arena.to_location(field_lid.loc),
        lbl_attributes: vec![],
    };

    Ok(Expression::new(
        ExpressionDesc::Texp_field(Box::new(typed_record), field_lid.clone(), label_desc),
        loc,
        field_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check field assignment.
#[allow(clippy::too_many_arguments)]
fn type_setfield(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    record_expr: &ParsedExpression,
    field_lid: &Located<LidentIdx>,
    new_value: &ParsedExpression,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;
    let unit_ty = env.type_unit(ctx);

    // Type check the record expression
    let record_ty = ctx.new_var(None);
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;

    // Get field type
    let field_ty = ctx.new_var(None);

    // Type check the new value
    let typed_value = type_expect(tctx, env, new_value, field_ty, None)?;

    // setfield has type unit
    unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;

    // Create placeholder label description
    let label_desc = crate::types::LabelDescription {
        lbl_name: tctx.resolve_lid(field_lid.txt).to_string(),
        lbl_res: record_ty,
        lbl_arg: field_ty,
        lbl_mut: crate::types::MutableFlag::Mutable,
        lbl_optional: false,
        lbl_pos: 0,
        lbl_all: crate::types::LabelArrayRef(0),
        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
        lbl_private: crate::types::PrivateFlag::Public,
        lbl_loc: tctx.arena.to_location(field_lid.loc),
        lbl_attributes: vec![],
    };

    Ok(Expression::new(
        ExpressionDesc::Texp_setfield(
            Box::new(typed_record),
            field_lid.clone(),
            label_desc,
            Box::new(typed_value),
        ),
        loc,
        unit_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check type constraint.
fn type_constraint(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_expr: &ParsedExpression,
    core_type: &crate::parser::ast::CoreType,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Translate the type constraint
    let (typed_ctype, ctype_ty) = transl_type(tctx, env, core_type)?;

    // Unify the constraint type with the expected type
    if crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, expected_ty, ctype_ty).is_err() {
        return Err(TypeCoreError::ExprTypeClash {
            trace: vec![(expected_ty, ctype_ty)],
            context: None,
        });
    }

    // Type check the inner expression with the constraint type
    let typed_inner = type_expect(tctx, env, inner_expr, ctype_ty, None)?;

    // Return the inner expression with the constraint as exp_extra
    Ok(typed_inner.with_exp_extra(
        crate::types::typedtree::ExpExtra::Texp_constraint(typed_ctype),
        loc.clone(),
        attributes.to_vec().into(),
    ))
}

/// Type check type coercion.
#[allow(clippy::too_many_arguments)]
fn type_coerce(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_expr: &ParsedExpression,
    opt_from_type: Option<&crate::parser::ast::CoreType>,
    to_type: &crate::parser::ast::CoreType,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Translate the target type
    let (to_typed_ctype, to_ty) = transl_type(tctx, env, to_type)?;

    // Unify the target type with the expected type
    if crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, expected_ty, to_ty).is_err() {
        return Err(TypeCoreError::ExprTypeClash {
            trace: vec![(expected_ty, to_ty)],
            context: None,
        });
    }

    // If there's a from type, translate and check it
    let (opt_from_typed, from_ty) = if let Some(from_type) = opt_from_type {
        let (from_typed_ctype, from_ty) = transl_type(tctx, env, from_type)?;
        (Some(from_typed_ctype), from_ty)
    } else {
        // No explicit from type, infer it from the expression
        let from_ty = tctx.type_ctx.new_var(None);
        (None, from_ty)
    };

    // Type check the inner expression with the from type
    let typed_inner = type_expect(tctx, env, inner_expr, from_ty, None)?;

    // Return the inner expression with the coercion as exp_extra
    Ok(typed_inner.with_exp_extra(
        crate::types::typedtree::ExpExtra::Texp_coerce(to_typed_ctype),
        loc.clone(),
        attributes.to_vec().into(),
    ))
}

/// Type check open expression.
fn type_open(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    lid: &Located<LidentIdx>,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Look up the module and extend the environment with its exports
    // For now, we just type check the body in the current environment
    // Full implementation would open the module's bindings into scope
    let _ = lid; // TODO: Open the module's bindings (use tctx.resolve_lid(lid.txt) when needed)

    // Type check the body expression
    let typed_body = type_expect(tctx, env, body, expected_ty, None)?;

    // Return expression with open in exp_extra
    // For now, return the body directly since we don't have full module support
    Ok(Expression::new(
        typed_body.exp_desc,
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check newtype expression.
fn type_newtype(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    name: &Located<StrIdx>,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Create a new abstract type for the newtype
    let ctx = tctx.type_ctx;
    let name_str = tctx.arena.get_string(name.txt).to_string();

    // Create an abstract type that will be bound to the name
    let new_type_var = ctx.new_var(Some(name_str.clone()));

    // Extend environment with the new type (simplified - full implementation
    // would create a proper type declaration)
    let _ = new_type_var; // Used to create the abstract type binding

    // Type check the body with the newtype in scope
    let typed_body = type_expect(tctx, env, body, expected_ty, None)?;

    // Return expression with newtype in exp_extra
    Ok(typed_body.with_exp_extra(
        crate::types::typedtree::ExpExtra::Texp_newtype(name_str),
        loc.clone(),
        attributes.to_vec().into(),
    ))
}

/// Type check await expression.
#[allow(clippy::too_many_arguments)]
fn type_await(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_expr: &ParsedExpression,
    expected_ty: TypeExprRef,
    _context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // For await, the inner expression should be a Promise<T>
    // and the result type is T
    // For simplicity, we just type check the inner expression with expected type
    // Full implementation would handle Promise type constructor

    // Type check the inner expression
    let typed_inner = type_expect(tctx, env, inner_expr, expected_ty, None)?;

    // Return the expression - await just unwraps the promise
    // In JavaScript, this is a runtime operation
    Ok(Expression::new(
        ExpressionDesc::Texp_apply {
            funct: Box::new(typed_inner),
            args: vec![], // Await is a special form, not a regular application
            partial: false,
            transformed_jsx: false,
        },
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check method send.
fn type_send(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    obj_expr: &ParsedExpression,
    method: &Located<std::borrow::Cow<'static, str>>,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // The object should have an object type with the method
    let obj_ty = ctx.new_var(None);
    let typed_obj = type_expect(tctx, env, obj_expr, obj_ty, None)?;

    // For now, allow any method call and use the expected type as result
    // Full implementation would look up the method in the object type
    Ok(Expression::new(
        ExpressionDesc::Texp_send(
            Box::new(typed_obj),
            crate::types::typedtree::MethKind::Tmeth_name(method.txt.to_string()),
            None,
        ),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check let exception.
fn type_letexception(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    _ext_constr: &crate::parser::ast::ExtensionConstructor,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Register the exception constructor in the environment
    // For now, just type check the body
    // Full implementation would add the exception to the environment

    let typed_body = type_expect(tctx, env, body, expected_ty, None)?;

    // Return the body expression
    // Full implementation would wrap in Texp_letexception
    Ok(Expression::new(
        typed_body.exp_desc,
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check extension expression.
fn type_extension_expr(
    tctx: &mut TypeCheckContext<'_>,
    _env: &Env,
    loc: LocIdx,
    _extension: &crate::parser::ast::Extension,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Extensions are handled by the preprocessor or raise an error
    // For type checking, treat as an opaque value of the expected type
    let _ = tctx; // May be used for error reporting in full implementation

    Ok(Expression::new(
        ExpressionDesc::Texp_constant(Constant::Int(0)), // Placeholder
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check let module expression.
#[allow(clippy::too_many_arguments)]
fn type_letmodule(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    _name: &Located<StrIdx>,
    _module_expr: &crate::parser::ast::ModuleExpr,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Let module introduces a local module binding
    // Full implementation would:
    // 1. Type check the module expression
    // 2. Add the module to the environment
    // 3. Type check the body in the extended environment

    // For now, just type check the body
    let typed_body = type_expect(tctx, env, body, expected_ty, None)?;

    Ok(Expression::new(
        typed_body.exp_desc,
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check pack expression (first-class module).
fn type_pack(
    tctx: &mut TypeCheckContext<'_>,
    _env: &Env,
    loc: LocIdx,
    _module_expr: &crate::parser::ast::ModuleExpr,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Pack creates a first-class module value
    // Full implementation would:
    // 1. Type check the module expression
    // 2. Create a package type from the module type

    // For now, return a placeholder with the expected type
    let placeholder_lid = tctx.arena.placeholder_located(loc);

    Ok(Expression::new(
        ExpressionDesc::Texp_pack(Box::new(crate::types::typedtree::ModuleExpr {
            mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_ident(
                crate::types::Path::pident(Ident::create_local("placeholder")),
                placeholder_lid,
            ),
            mod_loc: loc,
            mod_type: crate::types::typedtree::ModuleType::placeholder(),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new().into(),
        })),
        loc,
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check JSX element.
fn type_jsx_element(
    tctx: &mut TypeCheckContext<'_>,
    _env: &Env,
    loc: LocIdx,
    _jsx_element: &crate::parser::ast::JsxElement,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // JSX elements are typically transformed to function calls before type checking
    // by the JSX PPX. If we encounter one here, we create a placeholder.
    //
    // In a full implementation, this would:
    // 1. Look up the component (lowercase = intrinsic, uppercase = component)
    // 2. Type check props
    // 3. Type check children
    // 4. Return appropriate React element type

    let _ = tctx; // May be used for JSX type checking

    // For now, return a placeholder with the expected type
    // Real JSX handling would create Texp_apply calls
    Ok(Expression::new(
        ExpressionDesc::Texp_constant(Constant::Int(0)), // Placeholder
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check let bindings.
fn type_let_bindings(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeCoreResult<(Vec<ValueBinding>, Env)> {
    let ctx = tctx.type_ctx;

    // Begin a new definition level
    ctx.begin_def();

    // Create type variables for all bindings
    let binding_types: Vec<TypeExprRef> = bindings.iter().map(|_| ctx.new_var(None)).collect();

    // For recursive bindings, extend environment first
    let typing_env = if rec_flag == RecFlag::Recursive {
        let mut new_env = env.clone();
        for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
            if let crate::parser::ast::PatternDesc::Ppat_var(name) =
                &*tctx.arena.get_pat(binding.pvb_pat).ppat_desc
            {
                let id = Ident::create_local(tctx.arena.get_string(name.txt));
                let desc = ValueDescription {
                    val_type: *ty,
                    val_kind: crate::types::ValueKind::ValReg,
                    val_loc: tctx.arena.to_location(binding.pvb_loc),
                    val_attributes: vec![],
                    val_path: None,
                };
                new_env.add_value(id, desc);
            }
        }
        new_env
    } else {
        env.clone()
    };

    // Type check each binding
    let mut typed_bindings = Vec::new();
    let mut state = PatternState::new();

    for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
        state.reset(false);

        // Type check pattern
        let typed_pat = type_pattern(
            tctx,
            &typing_env,
            tctx.arena.get_pat(binding.pvb_pat),
            *ty,
            PatternMode::Normal,
            &mut state,
        )?;

        // Type check expression
        let typed_expr = type_expect(
            tctx,
            &typing_env,
            tctx.arena.get_expr(binding.pvb_expr),
            *ty,
            None,
        )?;

        typed_bindings.push(ValueBinding::new(
            typed_pat,
            typed_expr,
            binding.pvb_loc.clone(),
            binding.pvb_attributes.clone(),
        ));
    }

    // End definition level
    ctx.end_def();

    // Generalize types
    for ty in &binding_types {
        crate::types::generalize(ctx, *ty);
    }

    // Build final environment
    let mut new_env = env.clone();
    for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
        for pv in &state.pattern_variables {
            let desc = ValueDescription {
                val_type: *ty,
                val_kind: crate::types::ValueKind::ValReg,
                val_loc: tctx.arena.to_location(binding.pvb_loc),
                val_attributes: vec![],
                val_path: None,
            };
            new_env.add_value(pv.id.clone(), desc);
        }
    }

    Ok((typed_bindings, new_env))
}

// ============================================================================
// Top-Level Entry Points
// ============================================================================

/// Type check a top-level expression.
pub fn type_expression<'a>(
    type_ctx: &'a TypeContext<'a>,
    arena: &'a ParseArena,
    env: &Env,
    expr: &ParsedExpression,
) -> TypeCoreResult<Expression> {
    let mut tctx = TypeCheckContext::new(type_ctx, arena);

    // Begin a definition scope
    type_ctx.begin_def();

    // Type with a fresh variable
    let expected_ty = type_ctx.new_var(None);
    let typed_expr = type_expect(&mut tctx, env, expr, expected_ty, None)?;

    // End definition scope
    type_ctx.end_def();

    // Generalize the type
    crate::types::generalize(type_ctx, typed_expr.exp_type);

    Ok(typed_expr)
}

/// Type check a top-level binding.
pub fn type_binding<'a>(
    type_ctx: &'a TypeContext<'a>,
    arena: &'a ParseArena,
    env: &Env,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeCoreResult<(Vec<ValueBinding>, Env)> {
    let mut tctx = TypeCheckContext::new(type_ctx, arena);
    type_let_bindings(&mut tctx, env, rec_flag, bindings)
}

// ============================================================================
// Environment Extensions for Built-in Types
// ============================================================================

impl Env {
    /// Get the int type.
    pub fn type_int(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        // In a real implementation, this would look up the predef type
        ctx.new_constr(Path::pident(Ident::create_persistent("int")), vec![])
    }

    /// Get the char type.
    pub fn type_char(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("char")), vec![])
    }

    /// Get the string type.
    pub fn type_string(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("string")), vec![])
    }

    /// Get the float type.
    pub fn type_float(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("float")), vec![])
    }

    /// Get the bigint type.
    pub fn type_bigint(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("bigint")), vec![])
    }

    /// Get the unit type.
    pub fn type_unit(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("unit")), vec![])
    }

    /// Get the bool type.
    pub fn type_bool(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        ctx.new_constr(Path::pident(Ident::create_persistent("bool")), vec![])
    }

    /// Get the array type.
    pub fn type_array(&self, ctx: &TypeContext<'_>, elem_ty: TypeExprRef) -> TypeExprRef {
        ctx.new_constr(
            Path::pident(Ident::create_persistent("array")),
            vec![elem_ty],
        )
    }

    /// Get the option type.
    pub fn type_option(&self, ctx: &TypeContext<'_>, elem_ty: TypeExprRef) -> TypeExprRef {
        ctx.new_constr(
            Path::pident(Ident::create_persistent("option")),
            vec![elem_ty],
        )
    }

    /// Look up a value by longident.
    /// Properly resolves StrIdx through the arena to get actual identifier names.
    pub fn lookup_value_by_lid<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> TypeCoreResult<(Path, ValueDescription)> {
        match lid {
            Longident::Lident(idx) => {
                let name = arena.get_string(*idx);
                match self.find_value_with_id(name) {
                    Ok((id, desc)) => {
                        let path = desc
                            .val_path
                            .clone()
                            .unwrap_or_else(|| Path::pident(id.clone()));
                        Ok((path, desc.clone()))
                    }
                    Err(_) => Err(TypeCoreError::UndefinedMethod {
                        ty: TypeExprRef(0),
                        method: name.to_string(),
                        alternatives: None,
                    }),
                }
            }
            Longident::Ldot(prefix, idx) => {
                let value_name = arena.get_string(*idx);

                // Resolve the module prefix to get a signature and path.
                let lid_str = Self::longident_to_string(lid, arena);
                if let Some((mod_path, sig)) = self.resolve_module_lid(prefix, arena, ctx) {
                    // Search for the value in the signature.
                    // Signature lookup must respect shadowing order:
                    // later items in a structure/signature shadow earlier ones.
                    for sig_item in sig.iter().rev() {
                        if let crate::types::decl::SignatureItem::SigValue(id, vd) = sig_item {
                            if id.name() == value_name {
                                let path = Path::pdot(mod_path.clone(), value_name.to_string());
                                return Ok((path, vd.clone()));
                            }
                        }
                    }
                    return Err(TypeCoreError::UndefinedMethod {
                        ty: TypeExprRef(0),
                        method: lid_str,
                        alternatives: None,
                    });
                }

                // Fallback: try looking up as a flattened value in the local env.
                match self.find_value_with_id(value_name) {
                    Ok((id, desc)) => {
                        let path = desc
                            .val_path
                            .clone()
                            .unwrap_or_else(|| Path::pident(id.clone()));
                        Ok((path, desc.clone()))
                    }
                    Err(_) => Err(TypeCoreError::UndefinedMethod {
                        ty: TypeExprRef(0),
                        method: lid_str,
                        alternatives: None,
                    }),
                }
            }
            Longident::Lapply(_, _) => Err(TypeCoreError::UndefinedMethod {
                ty: TypeExprRef(0),
                method: "(functor application)".to_string(),
                alternatives: None,
            }),
        }
    }

    /// Convert a longident to a human-readable string for error messages.
    fn longident_to_string(lid: &Longident, arena: &crate::parse_arena::ParseArena) -> String {
        match lid {
            Longident::Lident(idx) => arena.get_string(*idx).to_string(),
            Longident::Ldot(prefix, idx) => {
                let prefix_str = Self::longident_to_string(prefix, arena);
                format!("{}.{}", prefix_str, arena.get_string(*idx))
            }
            Longident::Lapply(f, a) => {
                format!(
                    "{}({})",
                    Self::longident_to_string(f, arena),
                    Self::longident_to_string(a, arena)
                )
            }
        }
    }

    /// Resolve a module longident to its signature and path.
    pub(crate) fn resolve_module_lid<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        self.resolve_module_lid_impl(lid, arena, ctx, true)
    }

    /// Resolve a module longident without mutating type paths inside the returned signature.
    #[allow(dead_code)]
    fn resolve_module_lid_raw<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        self.resolve_module_lid_impl(lid, arena, ctx, false)
    }

    /// Resolve a module longident to path+signature, optionally applying
    /// rewrite/substitution to contained type paths.
    fn resolve_module_lid_impl<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        ctx: &'b crate::types::context::TypeContext<'b>,
        apply_subst: bool,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        match lid {
            Longident::Lident(mod_idx) => {
                let mod_name = arena.get_string(*mod_idx);
                // Try local environment
                if let Ok((mod_id, md)) = self.find_module_with_id(mod_name) {
                    let result = self.resolve_module_type(&md.md_type, ctx);
                    if let Some((sig, _resolved_name)) = result {
                        let path = Path::pident(mod_id.clone());
                        let has_type_or_module_defs = sig.iter().any(|item| {
                            matches!(
                                item,
                                crate::types::decl::SignatureItem::SigType(..)
                                    | crate::types::decl::SignatureItem::SigModule(..)
                                    | crate::types::decl::SignatureItem::SigModtype(..)
                            )
                        });
                        let needs_copy = apply_subst
                            && (has_type_or_module_defs || _resolved_name.is_some());
                        let sig = if needs_copy {
                            copy_lookup_signature_for_subst(&sig, ctx)
                        } else {
                            sig
                        };
                        return Some((path, sig));
                    }
                }
                None
            }
            Longident::Ldot(prefix, submod_idx) => {
                let submod_name = arena.get_string(*submod_idx);
                // Recursively resolve the prefix to get a signature
                if let Some((parent_path, parent_sig)) =
                    self.resolve_module_lid_impl(prefix, arena, ctx, apply_subst)
                {
                    // Search for the sub-module in the parent's signature
                    for sig_item in &parent_sig {
                        if let crate::types::decl::SignatureItem::SigModule(id, sub_md, _) =
                            sig_item
                        {
                            if id.name() == submod_name {
                                let sub_path = Path::pdot(parent_path, submod_name.to_string());
                                let result =
                                    self.resolve_module_type(&sub_md.md_type, ctx);
                                if let Some((sig, _resolved_name)) = result {
                                    let sig = if apply_subst {
                                        copy_lookup_signature_for_subst(&sig, ctx)
                                    } else {
                                        sig
                                    };
                                    return Some((sub_path, sig));
                                }
                                return None;
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Resolve a module type to a signature, following aliases.
    /// Returns (signature, Option<resolved_module_name>) where resolved_module_name is Some
    /// when an alias was followed (so the caller can rewrite paths).
    fn resolve_module_type<'b>(
        &self,
        mty: &crate::types::decl::ModuleType,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(crate::types::decl::Signature, Option<String>)> {
        use std::collections::HashSet;

        fn resolve_module_type_inner<'b>(
            env: &Env,
            mty: &crate::types::decl::ModuleType,
            ctx: &'b crate::types::context::TypeContext<'b>,
            visiting: &mut HashSet<Path>,
        ) -> Option<(crate::types::decl::Signature, Option<String>)> {
            match mty {
                crate::types::decl::ModuleType::MtySignature(sig) => Some((sig.clone(), None)),
                crate::types::decl::ModuleType::MtyAlias(_, path) => {
                    resolve_path(env, path, ctx, visiting)
                }
                crate::types::decl::ModuleType::MtyIdent(path) => {
                    resolve_modtype_path(env, path, ctx, visiting)
                        .or_else(|| resolve_path(env, path, ctx, visiting))
                }
                _ => None,
            }
        }

        fn resolve_modtype_path<'b>(
            env: &Env,
            path: &Path,
            ctx: &'b crate::types::context::TypeContext<'b>,
            visiting: &mut HashSet<Path>,
        ) -> Option<(crate::types::decl::Signature, Option<String>)> {
            use crate::types::decl::SignatureItem;

            if !visiting.insert(path.clone()) {
                return None;
            }

            let result = match path {
                Path::Pident(id) => {
                    let modtype_name = id.name();
                    match env.find_modtype(modtype_name) {
                        Ok(mtd) => mtd.mtd_type.as_ref().and_then(|mty| {
                            resolve_module_type_inner(env, mty, ctx, visiting)
                        }),
                        Err(_) => None,
                    }
                }
                Path::Pdot(parent, modtype_name, _) => {
                    let (parent_sig, _resolved_name) =
                        match resolve_path(env, parent, ctx, visiting) {
                            Some(x) => x,
                            None => {
                                visiting.remove(path);
                                return None;
                            }
                        };
                    parent_sig.iter().find_map(|sig_item| {
                        if let SignatureItem::SigModtype(id, mtd) = sig_item {
                            if id.name() == modtype_name.as_str() {
                                return mtd.mtd_type.as_ref().and_then(|mty| {
                                    resolve_module_type_inner(env, mty, ctx, visiting)
                                });
                            }
                        }
                        None
                    })
                }
                Path::Papply(_, _) => None,
            };

            visiting.remove(path);
            result
        }

        fn resolve_path<'b>(
            env: &Env,
            path: &Path,
            ctx: &'b crate::types::context::TypeContext<'b>,
            visiting: &mut HashSet<Path>,
        ) -> Option<(crate::types::decl::Signature, Option<String>)> {
            use crate::types::decl::SignatureItem;
            if !visiting.insert(path.clone()) {
                return None;
            }

            match path {
                Path::Pident(id) => {
                    let mod_name = id.name();
                    if let Ok(md) = env.find_module(mod_name) {
                        let result =
                            resolve_module_type_inner(env, &md.md_type, ctx, visiting);
                        visiting.remove(path);
                        return result;
                    }
                    visiting.remove(path);
                    None
                }
                Path::Pdot(parent, submod_name, _) => {
                    let (parent_sig, _resolved_name) =
                        match resolve_path(env, parent, ctx, visiting) {
                            Some(x) => x,
                            None => {
                                visiting.remove(path);
                                return None;
                            }
                        };
                    for sig_item in &parent_sig {
                        if let SignatureItem::SigModule(id, sub_md, _) = sig_item {
                            if id.name() == submod_name.as_str() {
                                let result = resolve_module_type_inner(
                                    env,
                                    &sub_md.md_type,
                                    ctx,
                                    visiting,
                                );
                                visiting.remove(path);
                                return result;
                            }
                        }
                    }
                    visiting.remove(path);
                    None
                }
                Path::Papply(_, _) => {
                    visiting.remove(path);
                    None
                }
            }
        }

        let mut visiting = HashSet::new();
        resolve_module_type_inner(self, mty, ctx, &mut visiting)
    }
}

// ============================================================================
// Copy helpers for lookup signature (deep copy with sharing cache)
// ============================================================================

fn copy_lookup_type_expr(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    use crate::types::type_expr::{RowDesc, RowField, TypeDesc};

    let ty = ctx.repr(ty);
    if let Some(&copied) = cache.get(&ty) {
        return copied;
    }

    let level = ctx.get_level(ty);
    let placeholder = ctx.new_var(None);
    ctx.set_level(placeholder, level);
    cache.insert(ty, placeholder);

    let copied = {
        let desc = ctx.get_desc(ty).clone();
        match desc {
            TypeDesc::Tvar(name) => {
                let t = ctx.new_var(name);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tarrow {
                arg, ret, arity, ..
            } => {
                let copied_arg = copy_lookup_type_expr(ctx, arg.typ, cache);
                let copied_ret = copy_lookup_type_expr(ctx, ret, cache);
                let t = ctx.new_arrow(arg.lbl, copied_arg, copied_ret, arity);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Ttuple(types) => {
                let copied_items = types
                    .iter()
                    .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                    .collect();
                let t = ctx.new_tuple(copied_items);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tconstr { path, args, .. } => {
                let copied_args = args
                    .iter()
                    .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                    .collect();
                let t = ctx.new_constr(path, copied_args);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tobject { fields, name } => {
                let copied_fields = copy_lookup_type_expr(ctx, fields, cache);
                let copied_name = name.map(|(path, args)| {
                    (
                        path,
                        args.into_iter()
                            .map(|t| copy_lookup_type_expr(ctx, t, cache))
                            .collect(),
                    )
                });
                let t = ctx.new_type(TypeDesc::Tobject {
                    fields: copied_fields,
                    name: copied_name,
                });
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => {
                let copied_typ = copy_lookup_type_expr(ctx, typ, cache);
                let copied_rest = copy_lookup_type_expr(ctx, rest, cache);
                let t = ctx.new_type(TypeDesc::Tfield {
                    name,
                    kind,
                    typ: copied_typ,
                    rest: copied_rest,
                });
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tnil => {
                let t = ctx.new_type(TypeDesc::Tnil);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tlink(target) => copy_lookup_type_expr(ctx, target, cache),
            TypeDesc::Tsubst(target) => {
                let copied_target = copy_lookup_type_expr(ctx, target, cache);
                let t = ctx.new_type(TypeDesc::Tsubst(copied_target));
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tvariant(row) => {
                let copied_row = RowDesc {
                    row_fields: row
                        .row_fields
                        .iter()
                        .map(|(label, field)| {
                            let copied_field = match field {
                                RowField::Rpresent(Some(ty)) => {
                                    RowField::Rpresent(Some(copy_lookup_type_expr(ctx, *ty, cache)))
                                }
                                RowField::Reither {
                                    constant,
                                    types,
                                    matched,
                                    link,
                                } => RowField::Reither {
                                    constant: *constant,
                                    types: types
                                        .iter()
                                        .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                                        .collect(),
                                    matched: *matched,
                                    link: *link,
                                },
                                other => other.clone(),
                            };
                            (label.clone(), copied_field)
                        })
                        .collect(),
                    row_more: copy_lookup_type_expr(ctx, row.row_more, cache),
                    row_closed: row.row_closed,
                    row_fixed: row.row_fixed,
                    row_name: row.row_name.as_ref().map(|(path, args)| {
                        (
                            path.clone(),
                            args.iter()
                                .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                                .collect(),
                        )
                    }),
                };
                let t = ctx.new_variant(copied_row);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tunivar(name) => {
                let t = ctx.new_type(TypeDesc::Tunivar(name));
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tpoly { body, vars } => {
                let copied_body = copy_lookup_type_expr(ctx, body, cache);
                let copied_vars = vars
                    .iter()
                    .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                    .collect();
                let t = ctx.new_poly(copied_body, copied_vars);
                ctx.set_level(t, level);
                t
            }
            TypeDesc::Tpackage { path, lids, args } => {
                let copied_args = args
                    .iter()
                    .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                    .collect();
                let t = ctx.new_type(TypeDesc::Tpackage {
                    path,
                    lids,
                    args: copied_args,
                });
                ctx.set_level(t, level);
                t
            }
        }
    };

    ctx.set_desc(placeholder, crate::types::type_expr::TypeDesc::Tlink(copied));
    cache.insert(ty, copied);
    copied
}

fn copy_lookup_constructor_args(
    args: &crate::types::decl::ConstructorArguments,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ConstructorArguments {
    match args {
        crate::types::decl::ConstructorArguments::CstrTuple(items) => {
            crate::types::decl::ConstructorArguments::CstrTuple(
                items
                    .iter()
                    .map(|t| copy_lookup_type_expr(ctx, *t, cache))
                    .collect(),
            )
        }
        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
            crate::types::decl::ConstructorArguments::CstrRecord(
                labels
                    .iter()
                    .map(|label| crate::types::decl::LabelDeclaration {
                        ld_id: label.ld_id.clone(),
                        ld_mutable: label.ld_mutable.clone(),
                        ld_optional: label.ld_optional,
                        ld_type: copy_lookup_type_expr(ctx, label.ld_type, cache),
                        ld_loc: label.ld_loc.clone(),
                        ld_attributes: label.ld_attributes.clone(),
                    })
                    .collect(),
            )
        }
    }
}

fn copy_lookup_type_kind(
    kind: &crate::types::decl::TypeKind,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeKind {
    match kind {
        crate::types::decl::TypeKind::TypeAbstract => crate::types::decl::TypeKind::TypeAbstract,
        crate::types::decl::TypeKind::TypeOpen => crate::types::decl::TypeKind::TypeOpen,
        crate::types::decl::TypeKind::TypeRecord(labels, repr) => {
            crate::types::decl::TypeKind::TypeRecord(
                labels
                    .iter()
                    .map(|label| crate::types::decl::LabelDeclaration {
                        ld_id: label.ld_id.clone(),
                        ld_mutable: label.ld_mutable.clone(),
                        ld_optional: label.ld_optional,
                        ld_type: copy_lookup_type_expr(ctx, label.ld_type, cache),
                        ld_loc: label.ld_loc.clone(),
                        ld_attributes: label.ld_attributes.clone(),
                    })
                    .collect(),
                repr.clone(),
            )
        }
        crate::types::decl::TypeKind::TypeVariant(constructors) => {
            crate::types::decl::TypeKind::TypeVariant(
                constructors
                    .iter()
                    .map(|constructor| crate::types::decl::ConstructorDeclaration {
                        cd_id: constructor.cd_id.clone(),
                        cd_args: copy_lookup_constructor_args(&constructor.cd_args, ctx, cache),
                        cd_res: constructor
                            .cd_res
                            .map(|t| copy_lookup_type_expr(ctx, t, cache)),
                        cd_loc: constructor.cd_loc.clone(),
                        cd_attributes: constructor.cd_attributes.clone(),
                    })
                    .collect(),
            )
        }
    }
}

fn copy_lookup_type_inlined(
    inlined: &crate::types::decl::TypeInlinedType,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeInlinedType {
    match inlined {
        crate::types::decl::TypeInlinedType::Record { type_name, labels } => {
            crate::types::decl::TypeInlinedType::Record {
                type_name: type_name.clone(),
                labels: labels
                    .iter()
                    .map(|label| crate::types::decl::LabelDeclaration {
                        ld_id: label.ld_id.clone(),
                        ld_mutable: label.ld_mutable.clone(),
                        ld_optional: label.ld_optional,
                        ld_type: copy_lookup_type_expr(ctx, label.ld_type, cache),
                        ld_loc: label.ld_loc.clone(),
                        ld_attributes: label.ld_attributes.clone(),
                    })
                    .collect(),
            }
        }
    }
}

fn copy_lookup_type_decl(
    decl: &crate::types::decl::TypeDeclaration,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::TypeDeclaration {
    crate::types::decl::TypeDeclaration {
        type_params: decl
            .type_params
            .iter()
            .map(|t| copy_lookup_type_expr(ctx, *t, cache))
            .collect(),
        type_arity: decl.type_arity,
        type_kind: copy_lookup_type_kind(&decl.type_kind, ctx, cache),
        type_private: decl.type_private,
        type_manifest: decl
            .type_manifest
            .map(|t| copy_lookup_type_expr(ctx, t, cache)),
        type_variance: decl.type_variance.clone(),
        type_newtype_level: decl.type_newtype_level,
        type_loc: decl.type_loc.clone(),
        type_attributes: decl.type_attributes.clone(),
        type_immediate: decl.type_immediate,
        type_unboxed: decl.type_unboxed,
        type_inlined_types: decl
            .type_inlined_types
            .iter()
            .map(|inlined| copy_lookup_type_inlined(inlined, ctx, cache))
            .collect(),
        type_path: decl.type_path.clone(),
    }
}

fn copy_lookup_extension_constructor(
    ext: &crate::types::decl::ExtensionConstructor,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ExtensionConstructor {
    crate::types::decl::ExtensionConstructor {
        ext_type_path: ext.ext_type_path.clone(),
        ext_type_params: ext
            .ext_type_params
            .iter()
            .map(|t| copy_lookup_type_expr(ctx, *t, cache))
            .collect(),
        ext_args: copy_lookup_constructor_args(&ext.ext_args, ctx, cache),
        ext_ret_type: ext
            .ext_ret_type
            .map(|t| copy_lookup_type_expr(ctx, t, cache)),
        ext_private: ext.ext_private,
        ext_loc: ext.ext_loc.clone(),
        ext_attributes: ext.ext_attributes.clone(),
        ext_is_exception: ext.ext_is_exception,
    }
}

fn copy_lookup_module_type(
    module_type: &crate::types::decl::ModuleType,
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::ModuleType {
    match module_type {
        crate::types::decl::ModuleType::MtyIdent(path) => {
            crate::types::decl::ModuleType::MtyIdent(path.clone())
        }
        crate::types::decl::ModuleType::MtyAlias(alias, path) => {
            crate::types::decl::ModuleType::MtyAlias(*alias, path.clone())
        }
        crate::types::decl::ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => crate::types::decl::ModuleType::MtyFunctor {
            param: param.clone(),
            param_type: param_type
                .as_ref()
                .map(|inner| Box::new(copy_lookup_module_type(inner, ctx, cache))),
            result: Box::new(copy_lookup_module_type(result, ctx, cache)),
        },
        crate::types::decl::ModuleType::MtySignature(sig_items) => {
            crate::types::decl::ModuleType::MtySignature(copy_lookup_signature(
                sig_items, ctx, cache,
            ))
        }
    }
}

fn copy_lookup_signature(
    sig_items: &[crate::types::decl::SignatureItem],
    ctx: &TypeContext<'_>,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::decl::Signature {
    sig_items
        .iter()
        .map(|item| match item {
            crate::types::decl::SignatureItem::SigValue(id, desc) => {
                crate::types::decl::SignatureItem::SigValue(
                    id.clone(),
                    crate::types::decl::ValueDescription {
                        val_type: copy_lookup_type_expr(ctx, desc.val_type, cache),
                        val_kind: desc.val_kind.clone(),
                        val_loc: desc.val_loc.clone(),
                        val_attributes: desc.val_attributes.clone(),
                        val_path: desc.val_path.clone(),
                    },
                )
            }
            crate::types::decl::SignatureItem::SigType(id, decl, rec_status) => {
                crate::types::decl::SignatureItem::SigType(
                    id.clone(),
                    copy_lookup_type_decl(decl, ctx, cache),
                    *rec_status,
                )
            }
            crate::types::decl::SignatureItem::SigTypext(id, ext, ext_status) => {
                crate::types::decl::SignatureItem::SigTypext(
                    id.clone(),
                    copy_lookup_extension_constructor(ext, ctx, cache),
                    *ext_status,
                )
            }
            crate::types::decl::SignatureItem::SigModule(id, md, rec_status) => {
                crate::types::decl::SignatureItem::SigModule(
                    id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: copy_lookup_module_type(&md.md_type, ctx, cache),
                        md_attributes: md.md_attributes.clone(),
                        md_loc: md.md_loc.clone(),
                        md_path: md.md_path.clone(),
                    },
                    *rec_status,
                )
            }
            crate::types::decl::SignatureItem::SigModtype(id, mtd) => {
                crate::types::decl::SignatureItem::SigModtype(
                    id.clone(),
                    crate::types::decl::ModtypeDeclaration {
                        mtd_type: mtd
                            .mtd_type
                            .as_ref()
                            .map(|mty| copy_lookup_module_type(mty, ctx, cache)),
                        mtd_attributes: mtd.mtd_attributes.clone(),
                        mtd_loc: mtd.mtd_loc.clone(),
                    },
                )
            }
            crate::types::decl::SignatureItem::SigClass => {
                crate::types::decl::SignatureItem::SigClass
            }
            crate::types::decl::SignatureItem::SigClassType => {
                crate::types::decl::SignatureItem::SigClassType
            }
        })
        .collect()
}

fn copy_lookup_signature_for_subst(
    sig_items: &[crate::types::decl::SignatureItem],
    ctx: &TypeContext<'_>,
) -> crate::types::decl::Signature {
    let mut cache = std::collections::HashMap::new();
    copy_lookup_signature(sig_items, ctx, &mut cache)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use std::borrow::Cow;

    #[test]
    fn test_convert_constant_int() {
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("42"), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(42));
    }

    #[test]
    fn test_convert_constant_overflow() {
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("99999999999999999"), None);
        let result = convert_constant(&cst);
        assert!(matches!(result, Err(TypeCoreError::LiteralOverflow(_))));
    }

    #[test]
    fn test_convert_constant_string() {
        let cst = crate::parser::ast::Constant::String(Cow::Borrowed("hello"), None);
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::String(s, None) if s == "hello"));
    }

    #[test]
    fn test_convert_constant_bigint() {
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("12345"), Some('n'));
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::BigInt(true, d) if d == "12345"));
    }

    #[test]
    fn test_type_constant() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let env = crate::types::initial_env(&ctx);

        let cst = Constant::Int(42);
        let ty = type_constant(&ctx, &env, &cst);
        // Check that we got a valid type (can get its description)
        let desc = ctx.get_desc(ty);
        assert!(matches!(&*desc, crate::types::TypeDesc::Tconstr { .. }));
    }

    #[test]
    fn test_pattern_state_enter_variable() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let _env = crate::types::initial_env(&ctx);
        let mut state = PatternState::new();

        let mut arena = ParseArena::new();
        let loc = LocIdx::none();
        let ty = ctx.new_var(None);
        let x_idx = arena.intern("x");
        let name = Located { txt: x_idx, loc };

        let id = state.enter_variable(loc, &name, ty, false, false, &arena);
        assert!(id.is_ok());

        // Duplicate should fail
        let id2 = state.enter_variable(loc, &name, ty, false, false, &arena);
        assert!(matches!(id2, Err(TypeCoreError::MultiplyBoundVariable(_))));
    }

    #[test]
    fn test_type_check_context_creation() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let arena = ParseArena::new();
        let tctx = TypeCheckContext::new(&ctx, &arena);

        assert!(tctx.newtype_level.is_none());
        assert!(tctx.diagnostics.is_empty());
    }

    #[test]
    fn test_env_type_constructors() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let env = crate::types::initial_env(&ctx);

        let int_ty = env.type_int(&ctx);
        let bool_ty = env.type_bool(&ctx);
        let string_ty = env.type_string(&ctx);

        // All should be valid Tconstr types
        assert!(matches!(
            &*ctx.get_desc(int_ty),
            crate::types::TypeDesc::Tconstr { .. }
        ));
        assert!(matches!(
            &*ctx.get_desc(bool_ty),
            crate::types::TypeDesc::Tconstr { .. }
        ));
        assert!(matches!(
            &*ctx.get_desc(string_ty),
            crate::types::TypeDesc::Tconstr { .. }
        ));

        // Array type with element type
        let elem_ty = ctx.new_var(None);
        let array_ty = env.type_array(&ctx, elem_ty);
        assert!(matches!(
            &*ctx.get_desc(array_ty),
            crate::types::TypeDesc::Tconstr { .. }
        ));
    }
}
