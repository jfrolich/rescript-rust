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

use std::collections::HashMap;
use crate::ident::Ident;
use crate::location::Location;
use crate::parse_arena::{LidentIdx, Located, LocIdx, ParseArena, StrIdx};
use crate::parser::ast::{
    ArgLabel, Expression as ParsedExpression, Pattern as ParsedPattern, RecFlag,
};
use crate::parser::longident::Longident;
use crate::types::typedtree::{
    ArrowArg, Constant, EnvRef, Expression, ExpressionDesc, Pattern, PatternDesc, ValueBinding,
};
use crate::types::{Env, Path, TypeContext, TypeDesc, TypeError, TypeExprRef, UnifyState, ValueDescription};

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

    /// Other error (catch-all for module type checking errors propagated from typemod).
    Other(String),
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
    pub used_variables: HashMap<String, TypeExprRef>,
    /// Persistent environment for loading external modules from .cmi files.
    pub persistent_env: Option<crate::cmi::persistent_env::PersistentEnv>,
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
            used_variables: HashMap::new(),
            persistent_env: None,
        }
    }

    /// Set the environment for type alias expansion during unification.
    /// Should be called before type-checking each structure item so the
    /// unifier can expand type aliases when paths don't match.
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

    /// Get the last component name of a Longident as a string.
    /// For `Lident("int")` returns `"int"`, for `Ldot(_, "bar")` returns `"bar"`.
    pub fn longident_last_name(&self, lid: &Longident) -> String {
        self.arena.get_string(lid.last_idx()).to_string()
    }

    /// Get the full dotted name of a Longident as a string.
    /// For `Lident("int")` returns `"int"`, for `Ldot(Lident("Foo"), "bar")` returns `"Foo.bar"`.
    pub fn longident_to_string(&self, lid: &Longident) -> String {
        match lid {
            Longident::Lident(idx) => self.arena.get_string(*idx).to_string(),
            Longident::Ldot(prefix, idx) => {
                format!("{}.{}", self.longident_to_string(prefix), self.arena.get_string(*idx))
            }
            Longident::Lapply(a, b) => {
                format!("{}({})", self.longident_to_string(a), self.longident_to_string(b))
            }
        }
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

/// Parse an integer literal string, handling underscores and 0x/0o/0b prefixes.
/// Returns the value as i64, or None if it can't be parsed.
fn parse_int_literal(s: &str) -> Option<i64> {
    let stripped: String = s.chars().filter(|c| *c != '_').collect();
    let (negative, digits) = if stripped.starts_with('-') {
        (true, &stripped[1..])
    } else {
        (false, &stripped[..])
    };
    let abs_val = if digits.starts_with("0x") || digits.starts_with("0X") {
        i64::from_str_radix(&digits[2..], 16).ok()?
    } else if digits.starts_with("0o") || digits.starts_with("0O") {
        i64::from_str_radix(&digits[2..], 8).ok()?
    } else if digits.starts_with("0b") || digits.starts_with("0B") {
        i64::from_str_radix(&digits[2..], 2).ok()?
    } else {
        digits.parse::<i64>().ok()?
    };
    if negative { Some(-abs_val) } else { Some(abs_val) }
}

/// Convert a parsed constant to a typed constant.
pub fn convert_constant(cst: &crate::parser::ast::Constant) -> TypeCoreResult<Constant> {
    use crate::parser::ast::Constant as ParsedConstant;

    match cst {
        ParsedConstant::Integer(s, None) => {
            // Parse integer literal, handling underscores and 0x/0o/0b prefixes.
            // OCaml's native int is 63-bit, so large literals succeed there.
            // We parse as i64 and wrap to i32 to match JavaScript semantics.
            match parse_int_literal(s) {
                Some(n) => Ok(Constant::Int(n as i32)),
                None => Err(TypeCoreError::LiteralOverflow("int".to_string())),
            }
        }
        ParsedConstant::Integer(s, Some('n')) => {
            // BigInt - strip leading zeros to match OCaml behavior
            let (sign, raw_digits) = if s.starts_with('-') {
                (false, &s[1..])
            } else {
                (true, s.as_str())
            };
            let digits = raw_digits.trim_start_matches('0');
            let digits = if digits.is_empty() { "0" } else { digits };
            Ok(Constant::BigInt(sign, digits.to_string()))
        }
        ParsedConstant::Integer(i, Some(c)) => Err(TypeCoreError::UnknownLiteral(i.clone(), *c)),
        ParsedConstant::Char(c) => Ok(Constant::Char(*c)),
        ParsedConstant::String(s, d) => {
            // Transform "js" delimiter to "*j" to match OCaml's escaped form
            let delim = match d {
                Some(d) if d == "js" => Some("*j".to_string()),
                other => other.clone(),
            };
            Ok(Constant::String(s.clone(), delim))
        }
        ParsedConstant::Float(f, None) => Ok(Constant::Float(f.clone())),
        ParsedConstant::Float(f, Some(c)) => Err(TypeCoreError::UnknownLiteral(f.clone(), *c)),
    }
}

// ============================================================================
// Core Type Translation
// ============================================================================

/// Convert a parser ArgLabel to a types ArgLabel (for TypeContext methods).
fn convert_arg_label_for_ctx(lbl: &crate::parser::ast::ArgLabel, arena: &ParseArena) -> crate::types::ArgLabel {
    match lbl {
        crate::parser::ast::ArgLabel::Nolabel => crate::types::ArgLabel::Nolabel,
        crate::parser::ast::ArgLabel::Labelled(s) => {
            crate::types::ArgLabel::labelled(arena.get_string(s.txt).to_string(), arena.to_location(s.loc))
        }
        crate::parser::ast::ArgLabel::Optional(s) => {
            crate::types::ArgLabel::optional(arena.get_string(s.txt).to_string(), arena.to_location(s.loc))
        }
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
    // Reset used_variables for each top-level type translation (matches OCaml's transl_simple_type)
    tctx.used_variables.clear();
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

    match &styp.ptyp_desc {
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
            // Look up existing or create a new type variable with this name.
            // Matches OCaml's used_variables table to ensure sharing within a type expression.
            let ty = if let Some(&existing) = tctx.used_variables.get(name) {
                existing
            } else {
                let v = ctx.new_var(Some(name.clone()));
                tctx.used_variables.insert(name.clone(), v);
                v
            };
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(Some(name.clone())),
                ctyp_type: ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, ty))
        }

        CTD::Ptyp_arrow { arg, ret, arity } => {
            // Arrow type: T1 -> T2
            let (arg_ctyp, arg_ty) = transl_type_inner(tctx, env, &arg.typ)?;
            let (ret_ctyp, ret_ty) = transl_type_inner(tctx, env, ret)?;

            // Convert Arity to Option<i32> for typed tree (matches OCaml's arity option)
            // Arity is now ArityIdx, look up the value from the arena
            let arity_opt = tctx.arena.get_arity(*arity);

            // Like OCaml: wrap optional argument types in option
            let arg_ty = if arg.lbl.is_optional() {
                ctx.new_constr(
                    crate::types::Path::pident(crate::ident::Ident::create_persistent("option")),
                    vec![arg_ty],
                )
            } else {
                arg_ty
            };

            // Convert parser ArgLabel to types ArgLabel for TypeContext
            let ctx_lbl = convert_arg_label_for_ctx(&arg.lbl, tctx.arena);
            let arrow_ty = ctx.new_arrow(ctx_lbl, arg_ty, ret_ty, arity_opt);

            // Create ArrowArg structure matching OCaml's
            let arrow_arg = ArrowArg {
                attrs: arg.attrs.clone(),
                lbl: arg.lbl.clone(),
                typ: Box::new(arg_ctyp),
            };

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_arrow(
                    arrow_arg,
                    Box::new(ret_ctyp),
                    arity_opt,
                ),
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

            for t in types {
                let (ctyp, ty) = transl_type_inner(tctx, env, t)?;
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

        CTD::Ptyp_constr(lid, args) => {
            // Type constructor: int, string, list<'a>, etc.
            let mut typed_args = Vec::new();
            let mut arg_refs = Vec::new();

            for arg in args {
                let (ctyp, ty) = transl_type_inner(tctx, env, arg)?;
                typed_args.push(ctyp);
                arg_refs.push(ty);
            }

            // Look up the type in the environment to get the canonical path.
            // This matches OCaml's Typetexp.transl_type_aux which calls
            // Env.lookup_type to get the actual Path.t from the environment,
            // ensuring predef types like int/string/unit use persistent idents
            // that match the initial_env types and CMI-loaded types.
            let longident = tctx.arena.get_longident(lid.txt);
            let path = match longident {
                crate::parser::longident::Longident::Lident(name_idx) => {
                    let name = tctx.arena.get_string(*name_idx);
                    match env.find_type_with_id(name) {
                        Ok((id, decl)) => {
                            // Use qualified type_path if available (from opened modules)
                            decl.type_path.clone().unwrap_or_else(|| Path::pident(id.clone()))
                        }
                        Err(_) => {
                            // Type not found in env - fall back to creating from longident
                            Path::from_longident(longident, |idx| tctx.arena.get_string(idx))
                        }
                    }
                }
                crate::parser::longident::Longident::Ldot(_prefix, _name_idx) => {
                    // For qualified paths like Module.t, construct from longident
                    // but try to resolve the module path through the env
                    Path::from_longident(longident, |idx| tctx.arena.get_string(idx))
                }
                _ => Path::from_longident(longident, |idx| tctx.arena.get_string(idx)),
            };

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

        CTD::Ptyp_alias(inner, name) => {
            // Type alias: T as 'a
            let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, inner)?;

            // Create a type variable for the alias name and unify with inner type
            let alias_var = ctx.new_var(Some(name.clone()));
            crate::types::unify(ctx, &mut tctx.unify_state, alias_var, inner_ty)
                .map_err(|_| TypeCoreError::PatternTypeClash(vec![(alias_var, inner_ty)]))?;

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_alias(Box::new(inner_ctyp), name.clone()),
                ctyp_type: inner_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, inner_ty))
        }

        CTD::Ptyp_poly(vars, body) => {
            // Polymorphic type: 'a 'b. T
            let var_names: Vec<String> = vars.iter().map(|v| tctx.arena.get_string(v.txt).to_string()).collect();

            // Create type variables for each bound variable
            for name in &var_names {
                let _var = ctx.new_var(Some(name.clone()));
            }

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

        CTD::Ptyp_object(fields, closed) => {
            // Object type: {. name: string, age: int }
            // Build proper Tobject(Tfield(..., Tfield(..., Tnil))) type chain
            let mut typed_fields = Vec::new();
            // Collect (name, field_type) pairs for building the Tfield chain
            let mut field_entries: Vec<(String, TypeExprRef)> = Vec::new();

            for field in fields.iter() {
                match field {
                    crate::parser::ast::ObjectField::Otag(label, attrs, field_type) => {
                        // OCaml uses transl_poly_type which wraps in Ptyp_poly([], t)
                        // via force_poly. We simulate this by translating the type
                        // and wrapping both core type and type in poly.
                        let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, field_type)?;

                        // Wrap core type in Ttyp_poly([], inner)
                        let poly_ty = ctx.new_poly(inner_ty, vec![]);
                        let poly_ctyp = TypedCoreType {
                            ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vec![], Box::new(inner_ctyp)),
                            ctyp_type: poly_ty,
                            ctyp_env: EnvRef(0),
                            ctyp_loc: field_type.ptyp_loc.clone(),
                            ctyp_attributes: vec![],
                        };

                        let field_name = tctx.arena.get_string(label.txt).to_string();
                        field_entries.push((field_name.clone(), poly_ty));

                        typed_fields.push(crate::types::typedtree::ObjectField {
                            of_desc: crate::types::typedtree::ObjectFieldDesc::OTtag(
                                Located {
                                    txt: field_name,
                                    loc: label.loc.clone(),
                                },
                                poly_ctyp,
                            ),
                            of_loc: label.loc.clone(),
                            of_attributes: attrs.clone(),
                        });
                    }
                    crate::parser::ast::ObjectField::Oinherit(inherit_type) => {
                        let (inherit_ctyp, _inherit_ty) =
                            transl_type_inner(tctx, env, inherit_type)?;
                        typed_fields.push(crate::types::typedtree::ObjectField {
                            of_desc: crate::types::typedtree::ObjectFieldDesc::OTinherit(
                                inherit_ctyp,
                            ),
                            of_loc: inherit_type.ptyp_loc.clone(),
                            of_attributes: vec![],
                        });
                    }
                }
            }

            // Build the Tfield chain terminated by Tnil (closed) or Tvar (open)
            let ty_init = match closed {
                crate::parser::ast::ClosedFlag::Closed => ctx.new_type(TypeDesc::Tnil),
                crate::parser::ast::ClosedFlag::Open => ctx.new_var(None),
            };
            // Sort fields alphabetically to match OCaml's Hashtbl.fold order
            // (OCaml collects fields into a hash table then folds, producing
            // hash-bucket order which for small tables with short keys is alphabetical)
            field_entries.sort_by(|a, b| a.0.cmp(&b.0));
            // Fold fields into Tfield chain
            let fields_ty = field_entries.iter().fold(ty_init, |rest, (name, field_ty)| {
                ctx.new_type(TypeDesc::Tfield {
                    name: name.clone(),
                    kind: crate::types::type_expr::FieldKind::Fpresent,
                    typ: *field_ty,
                    rest,
                })
            });
            // Wrap in Tobject
            let obj_ty = ctx.new_type(TypeDesc::Tobject {
                fields: fields_ty,
                name: None,
            });

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_object(typed_fields, *closed),
                ctyp_type: obj_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, obj_ty))
        }

        CTD::Ptyp_variant(rows, closed, labels) => {
            // Polymorphic variant type: [> `A | `B of int ]
            let mut typed_rows = Vec::new();
            let row_more = ctx.new_var(None);

            for row in rows {
                match row {
                    crate::parser::ast::RowField::Rtag(label, attrs, constant, args) => {
                        let mut typed_args = Vec::new();
                        for arg in args {
                            let (arg_ctyp, _arg_ty) = transl_type_inner(tctx, env, arg)?;
                            typed_args.push(arg_ctyp);
                        }

                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rtag(
                                Located {
                                    txt: label.txt.clone(),
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
                        let (inherit_ctyp, _inherit_ty) =
                            transl_type_inner(tctx, env, inherit_type)?;
                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rinherit(inherit_ctyp),
                            rf_loc: inherit_type.ptyp_loc.clone(),
                            rf_attributes: vec![],
                        });
                    }
                }
            }

            // Create variant type
            let variant_ty = row_more; // Simplified - full implementation builds row type

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_variant(typed_rows, *closed, labels.clone()),
                ctyp_type: variant_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, variant_ty))
        }

        CTD::Ptyp_package((_mod_lid, _constraints)) => {
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

    match &pat.ppat_desc {
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
                let typed_pat = type_pattern_inner(tctx, env, p, *ty, mode, state, 0)?;
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

        PD::Ppat_alias(inner_pat, name) => {
            // Alias pattern: P as x
            let typed_inner =
                type_pattern_inner(tctx, env, inner_pat, expected_ty, mode, state, 0)?;

            // Build the as-type
            let ty_var = build_as_type(ctx, env, &typed_inner)?;

            // Enter the variable with the as-type
            let id = state.enter_variable(loc, name, ty_var, true, false, tctx.arena)?;

            Ok(Pattern::new(
                PatternDesc::Tpat_alias(Box::new(typed_inner), id, convert_located_stridx(name, tctx.arena)),
                loc,
                expected_ty,
                EnvRef(0),
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_or(p1, p2) => {
            // Or-pattern: P1 | P2
            let inner_mode = if mode == PatternMode::SplittingOr {
                PatternMode::Normal
            } else {
                mode
            };

            // Save pattern variables before p1
            let vars_before = state.pattern_variables.len();

            // Type check first branch
            let typed_p1 = type_pattern_inner(tctx, env, p1, expected_ty, inner_mode, state, 0)?;

            // Save p1's variables
            let p1_vars: Vec<_> = state.pattern_variables[vars_before..].to_vec();

            // Reset for p2
            state.pattern_variables.truncate(vars_before);

            // Type check second branch
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
            for p in pats {
                let typed_pat = type_pattern_inner(tctx, env, p, elem_ty, mode, state, 0)?;
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
                arg.as_ref().map(|p| p.as_ref()),
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_variant(label, arg) => {
            // Polymorphic variant pattern: #Red, #Blue(x)
            type_pattern_variant(
                tctx,
                env,
                loc,
                label,
                arg.as_ref().map(|p| p.as_ref()),
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_record(fields, closed_flag) => {
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

        PD::Ppat_constraint(inner_pat, core_type) => {
            // Type constraint pattern: (x : int)
            type_pattern_constraint(
                tctx,
                env,
                loc,
                inner_pat,
                core_type,
                expected_ty,
                mode,
                state,
                pat,
            )
        }

        PD::Ppat_interval(c1, c2) => {
            // Interval pattern: 'a'..'z'
            type_pattern_interval(tctx, env, loc, c1, c2, expected_ty, pat)
        }

        PD::Ppat_exception(inner_pat) => {
            // Exception pattern
            type_pattern_exception(tctx, env, loc, inner_pat, expected_ty, mode, state, pat)
        }

        PD::Ppat_open(mod_lid, inner_pat) => {
            // Local open pattern: M.(p)
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

    // Look up constructor with disambiguation following OCaml's approach:
    // 1. For module-qualified constructors (Ldot), use direct module lookup
    // 2. For unqualified constructors (Lident), use disambiguation considering expected type
    let lid_txt = tctx.arena.get_longident(lid.txt);
    let lid_name = tctx.longident_last_name(lid_txt);
    let is_qualified = matches!(lid_txt, Longident::Ldot(..));
    let (cstr_desc, _cstr_path) = if is_qualified {
        // Module-qualified: use direct lookup
        match lookup_constructor_in_module(lid_txt, tctx.arena, env, &mut tctx.persistent_env, tctx.type_ctx) {
            Some((path, desc)) => (desc, path),
            None => {
                match env.find_constructor(&lid_name) {
                    Ok(desc) => (
                        desc.clone(),
                        Path::pident(Ident::create_persistent(lid_name)),
                    ),
                    Err(_) => return Err(TypeCoreError::NotAVariantType(lid_txt.clone())),
                }
            }
        }
    } else {
        // Unqualified: use disambiguation with expected type
        match disambiguate_constructor(&lid_name, expected_ty, env, &mut tctx.persistent_env, tctx.type_ctx) {
            Some((path, desc)) => (desc, path),
            None => {
                match lookup_constructor_in_module(lid_txt, tctx.arena, env, &mut tctx.persistent_env, tctx.type_ctx) {
                    Some((path, desc)) => (desc, path),
                    None => return Err(TypeCoreError::NotAVariantType(lid_txt.clone())),
                }
            }
        }
    };

    // Instantiate constructor: creates fresh type variables shared between
    // cstr_res and cstr_args, matching OCaml's Ctype.instance_constructor
    let (inst_arg_types, result_ty) = crate::types::instance_constructor(ctx, &cstr_desc);
    unify_pattern_types(tctx, loc, result_ty, expected_ty)?;

    // Type check the argument pattern(s)
    let typed_args = match (inst_arg_types.as_slice(), arg) {
        (arg_types, Some(arg_pat)) if arg_types.len() == 1 => {
            // Single argument
            let typed_arg = type_pattern_inner(tctx, env, arg_pat, arg_types[0], mode, state, 0)?;
            vec![typed_arg]
        }
        (arg_types, Some(arg_pat)) if arg_types.len() > 1 => {
            // Multiple arguments - check if the pattern is a wildcard or tuple
            match &arg_pat.ppat_desc {
                crate::parser::ast::PatternDesc::Ppat_any => {
                    // OCaml replicates Ppat_any for each constructor arg
                    let mut args = Vec::new();
                    for &arg_ty in arg_types {
                        let typed_arg = type_pattern_inner(tctx, env, arg_pat, arg_ty, mode, state, 0)?;
                        args.push(typed_arg);
                    }
                    args
                }
                _ => {
                    // Tuple pattern - extract individual elements
                    let tuple_ty = ctx.new_tuple(arg_types.to_vec());
                    let typed_tuple = type_pattern_inner(tctx, env, arg_pat, tuple_ty, mode, state, 0)?;
                    match &typed_tuple.pat_desc {
                        PatternDesc::Tpat_tuple(elements) => elements.clone(),
                        _ => vec![typed_tuple],
                    }
                }
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
        let field_name = tctx.longident_last_name(tctx.resolve_lid(field.lid.txt));

        // Create fresh type variable for the field
        let field_ty = ctx.new_var(None);

        // Try to look up the label from the environment for type info
        let label_desc = if let Ok(env_label) = env.find_label(&field_name) {
            let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, env_label);
            // Best-effort unification to propagate type info
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, expected_ty);
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_arg, field_ty);
            crate::types::LabelDescription {
                lbl_name: env_label.lbl_name.clone(),
                lbl_res: expected_ty,
                lbl_arg: field_ty,
                lbl_mut: env_label.lbl_mut.clone(),
                lbl_optional: env_label.lbl_optional,
                lbl_pos: env_label.lbl_pos,
                lbl_all: env_label.lbl_all,
                lbl_repres: env_label.lbl_repres.clone(),
                lbl_private: env_label.lbl_private.clone(),
                lbl_loc: env_label.lbl_loc.clone(),
                lbl_attributes: env_label.lbl_attributes.clone(),
            }
        } else {
            crate::types::LabelDescription {
                lbl_name: field_name,
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
            }
        };

        let typed_pat = type_pattern_inner(tctx, env, &field.pat, field_ty, mode, state, 0)?;
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

    // OCaml converts Tpat_var to Tpat_alias(Tpat_any, id, name) for constraint patterns
    // (separate = true always in Ppat_constraint case)
    let typed_inner = match typed_inner.pat_desc.clone() {
        crate::types::typedtree::PatternDesc::Tpat_var(id, name) => {
            let any_pat = Pattern {
                pat_desc: crate::types::typedtree::PatternDesc::Tpat_any,
                pat_loc: typed_inner.pat_loc.clone(),
                pat_extra: vec![],
                pat_type: ctype_ty,
                pat_env: typed_inner.pat_env,
                pat_attributes: vec![],
            };
            Pattern {
                pat_desc: crate::types::typedtree::PatternDesc::Tpat_alias(
                    Box::new(any_pat),
                    id,
                    name,
                ),
                pat_type: ctype_ty,
                ..typed_inner
            }
        }
        _ => typed_inner,
    };

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
        vec![],
    );
    let p2 = Pattern::new(
        PatternDesc::Tpat_constant(constant2),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        vec![],
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
    let _mod_path = Path::pident(Ident::create_persistent(tctx.longident_last_name(mod_lid_txt)));

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

    match &expr.pexp_desc {
        ED::Pexp_ident(lid) => {
            // Identifier expression
            let longident = tctx.arena.get_longident(lid.txt);
            let (path, desc) = env.lookup_value_by_lid(longident, tctx.arena, &mut tctx.persistent_env, tctx.type_ctx)?;

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
                let typed_expr = type_expect(tctx, env, e, *ty, None)?;
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

        ED::Pexp_let(rec_flag, bindings, body) => {
            // Let expression
            let (typed_bindings, new_env) = type_let_bindings(tctx, env, *rec_flag, bindings)?;

            // Type check body in extended environment
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

        ED::Pexp_sequence(e1, e2) => {
            // Sequence expression: e1; e2
            // e1 should have type unit
            let unit_ty = env.type_unit(ctx);
            let typed_e1 = type_expect(tctx, env, e1, unit_ty, None)?;

            // e2 has the expected type
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

        ED::Pexp_ifthenelse(cond, then_branch, else_branch) => {
            // If expression
            let bool_ty = env.type_bool(ctx);

            // Condition should be bool
            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;

            // Then branch has expected type
            let typed_then = type_expect(tctx, env, then_branch, expected_ty, None)?;

            // Else branch, if present
            let typed_else = if let Some(else_branch) = else_branch {
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

        ED::Pexp_while(cond, body) => {
            // While loop
            let bool_ty = env.type_bool(ctx);
            let unit_ty = env.type_unit(ctx);

            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;
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

        ED::Pexp_assert(e) => {
            // Assert expression
            let bool_ty = env.type_bool(ctx);

            let typed_e = type_expect(tctx, env, e, bool_ty, None)?;

            // assert(false) has the expected type (polymorphic), others have type unit
            let exp_type = match &typed_e.exp_desc {
                ExpressionDesc::Texp_construct(_, cd, _) if cd.cstr_name == "false" => {
                    expected_ty
                }
                _ => {
                    let unit_ty = env.type_unit(ctx);
                    unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;
                    unit_ty
                }
            };

            Ok(Expression::new(
                ExpressionDesc::Texp_assert(Box::new(typed_e)),
                loc,
                exp_type,
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
            for e in exprs {
                let typed_e =
                    type_expect(tctx, env, e, elem_ty, Some(TypeClashContext::ArrayLiteral))?;
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

        ED::Pexp_apply {
            funct,
            args,
            partial,
            transformed_jsx,
        } => {
            // Function application
            type_application(
                tctx,
                env,
                loc,
                funct,
                args,
                *partial,
                *transformed_jsx,
                expected_ty,
                context,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_match(scrutinee, cases) => {
            // Match expression
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

        ED::Pexp_try(body, handlers) => {
            // Try expression
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

        ED::Pexp_fun {
            arg_label,
            default,
            lhs,
            rhs,
            arity,
            is_async,
        } => {
            // Function expression
            type_function(
                tctx,
                env,
                loc,
                arg_label,
                default.as_ref().map(|e| e.as_ref()),
                lhs,
                rhs,
                arity.clone(),
                *is_async,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_for(pat, start_expr, end_expr, direction, body) => {
            // For loop
            type_for(
                tctx,
                env,
                loc,
                pat,
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
                arg.as_ref().map(|e| e.as_ref()),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_variant(label, arg) => {
            // Polymorphic variant
            type_variant(
                tctx,
                env,
                loc,
                label,
                arg.as_ref().map(|e| e.as_ref()),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_record(fields, base) => {
            // Record expression
            type_record(
                tctx,
                env,
                loc,
                fields,
                base.as_ref().map(|e| e.as_ref()),
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_field(record_expr, field_lid) => {
            // Field access
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

        ED::Pexp_setfield(record_expr, field_lid, new_value) => {
            // Field assignment
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

        ED::Pexp_constraint(inner_expr, core_type) => {
            // Type constraint
            type_constraint(
                tctx,
                env,
                loc,
                inner_expr,
                core_type,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_coerce(inner_expr, opt_from_type, to_type) => {
            // Type coercion: (E :> T) or (E : T1 :> T2)
            type_coerce(
                tctx,
                env,
                loc,
                inner_expr,
                opt_from_type.as_ref(),
                to_type,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_open(_override_flag, lid, body) => {
            // Open expression: M.{ E } or open M; E
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

        ED::Pexp_newtype(name, body) => {
            // Newtype expression: (type t) => E
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

        ED::Pexp_await(inner_expr) => {
            // Await expression: await E
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

        ED::Pexp_send(obj_expr, method) => {
            // Method send: E#m
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

        ED::Pexp_letexception(ext_constr, body) => {
            // Let exception: { exception C; E }
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

        ED::Pexp_letmodule(name, module_expr, body) => {
            // Let module: { module M = ME; E }
            type_letmodule(
                tctx,
                env,
                loc,
                name,
                module_expr,
                body,
                expected_ty,
                &expr.pexp_attributes,
            )
        }

        ED::Pexp_pack(module_expr) => {
            // Pack: module(ME)
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
        Err(_e) => {
            if std::env::var("DEBUG_TYPECLASH").is_ok() {
                let d1 = tctx.type_ctx.get_desc(tctx.type_ctx.repr(ty1));
                let d2 = tctx.type_ctx.get_desc(tctx.type_ctx.repr(ty2));
                eprintln!("TYPECLASH: {:?} vs {:?} ctx={:?}", &*d1, &*d2, context);
            }
            Err(TypeCoreError::ExprTypeClash {
                trace: vec![(ty1, ty2)],
                context,
            })
        }
    }
}


// ============================================================================
// Expression Type Checking Helpers
// ============================================================================

/// Type check function application.
#[allow(clippy::too_many_arguments)]
/// Unified ops form (unary or binary).
#[derive(Clone, Copy, PartialEq)]
enum UnifiedOpForm {
    Unary,
    Binary,
}

/// Check if a path (by name) is a unified op, returning its form.
fn get_unified_op_form(path_name: &str) -> Option<UnifiedOpForm> {
    match path_name {
        // Binary unified ops (matching OCaml's unified_ops.ml)
        "Pervasives.+" | "Pervasives.-" | "Pervasives.*" | "Pervasives./"
        | "Pervasives.%" | "Pervasives.mod" | "Pervasives.**"
        | "Pervasives.<<" | "Pervasives.>>" | "Pervasives.>>>"
        | "Pervasives.|||" | "Pervasives.^^^" | "Pervasives.&&&" => {
            Some(UnifiedOpForm::Binary)
        }
        // Unary unified ops
        "Pervasives.~+" | "Pervasives.~-" | "Pervasives.~~~" => {
            Some(UnifiedOpForm::Unary)
        }
        _ => None,
    }
}

/// Check if a resolved type is a Tconstr matching a specific type name.
fn is_type_named(ctx: &TypeContext<'_>, ty: TypeExprRef, name: &str) -> bool {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } if args.is_empty() => {
            match path {
                Path::Pident(id) => id.name() == name,
                _ => false,
            }
        }
        _ => false,
    }
}

/// Translate unified ops: specialized type-checking for polymorphic operators.
///
/// This matches OCaml's `translate_unified_ops` in typecore.ml.
/// Unified ops like `+`, `-`, `*`, etc. are polymorphic in Pervasives
/// (type `('a, 'a) => 'a`) but get specialized based on the argument types.
/// The default fallback is `int`.
///
/// Crucially, this does NOT unify the operator's polymorphic type with the
/// concrete arg/result types, so the operator expression keeps its
/// polymorphic instance type (with shared Tvars and cycles in sexp output).
fn translate_unified_ops(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    typed_funct: &Expression,
    args: &[(ArgLabel, ParsedExpression)],
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> Option<TypeCoreResult<Expression>> {
    use crate::types::typedtree::ApplyArg;

    // Check if the function is a unified op
    let path_name = match &typed_funct.exp_desc {
        ExpressionDesc::Texp_ident(path, _, _) => path.name(),
        _ => return None,
    };

    let form = match get_unified_op_form(&path_name) {
        Some(f) => f,
        None => return None,
    };

    let ctx = tctx.type_ctx;

    match form {
        UnifiedOpForm::Binary if args.len() == 2 => {
            // Type check LHS and RHS independently (not against function type)
            let lhs_ty = ctx.new_var(None);
            let lhs_result = type_expect(tctx, env, &args[0].1, lhs_ty, None);
            let lhs = match lhs_result {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };
            let lhs_type = ctx.repr(lhs.exp_type);

            let rhs_ty = ctx.new_var(None);
            let rhs_result = type_expect(tctx, env, &args[1].1, rhs_ty, None);
            let rhs = match rhs_result {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };
            let rhs_type = ctx.repr(rhs.exp_type);

            // Determine the concrete type using unified ops rules:
            // Rule 1: If LHS is a known primitive type, use it
            // Rule 2: If RHS is a known primitive type, use it
            // Rule 3: Default to int
            let concrete_type_name = if is_type_named(ctx, lhs_type, "int") {
                "int"
            } else if is_type_named(ctx, lhs_type, "float") {
                "float"
            } else if is_type_named(ctx, lhs_type, "bigint") {
                "bigint"
            } else if is_type_named(ctx, lhs_type, "string") {
                "string"
            } else if is_type_named(ctx, rhs_type, "int") {
                "int"
            } else if is_type_named(ctx, rhs_type, "float") {
                "float"
            } else if is_type_named(ctx, rhs_type, "bigint") {
                "bigint"
            } else if is_type_named(ctx, rhs_type, "string") {
                "string"
            } else {
                // Default fallback to int
                "int"
            };

            // Create SEPARATE concrete type nodes for each position.
            // OCaml's type_expect calls instance() on the expected type, creating
            // fresh copies each time. We simulate this by creating separate nodes.
            let make_concrete = || ctx.new_constr(
                Path::pident(Ident::create_persistent(concrete_type_name)),
                vec![],
            );

            // Unify LHS with a fresh concrete type
            let lhs_concrete = make_concrete();
            if let Err(e) = unify_expression_types(tctx, loc, lhs.exp_type, lhs_concrete, None) {
                return Some(Err(e));
            }
            // Re-type RHS with a fresh concrete type (matching OCaml which calls type_expect)
            let rhs_concrete = make_concrete();
            let rhs = match type_expect(tctx, env, &args[1].1, rhs_concrete, None) {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };

            // Result type is a fresh concrete type
            let result_ty = make_concrete();

            // Unify result with expected type
            if let Err(e) = unify_expression_types(tctx, loc, result_ty, expected_ty, context) {
                return Some(Err(e));
            }

            let typed_args = vec![
                ApplyArg {
                    label: args[0].0.clone(),
                    expression: lhs,
                },
                ApplyArg {
                    label: args[1].0.clone(),
                    expression: rhs,
                },
            ];

            Some(Ok(Expression::new(
                ExpressionDesc::Texp_apply {
                    funct: Box::new(typed_funct.clone()),
                    args: typed_args,
                    partial: false,
                    transformed_jsx: false,
                },
                loc.clone(),
                result_ty,
                EnvRef(0),
                attributes.to_vec(),
            )))
        }
        UnifiedOpForm::Unary if args.len() == 1 => {
            // Type check the argument independently
            let arg_ty = ctx.new_var(None);
            let arg_result = type_expect(tctx, env, &args[0].1, arg_ty, None);
            let arg = match arg_result {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };
            let arg_type = ctx.repr(arg.exp_type);

            // Determine the concrete type
            let concrete_type_name = if is_type_named(ctx, arg_type, "int") {
                "int"
            } else if is_type_named(ctx, arg_type, "float") {
                "float"
            } else if is_type_named(ctx, arg_type, "bigint") {
                "bigint"
            } else {
                "int" // Default fallback
            };

            let concrete_ty = ctx.new_constr(
                Path::pident(Ident::create_persistent(concrete_type_name)),
                vec![],
            );

            // Unify arg with concrete type
            if let Err(e) = unify_expression_types(tctx, loc, arg.exp_type, concrete_ty, None) {
                return Some(Err(e));
            }

            // Result type
            let result_ty = ctx.new_constr(
                Path::pident(Ident::create_persistent(concrete_type_name)),
                vec![],
            );

            if let Err(e) = unify_expression_types(tctx, loc, result_ty, expected_ty, context) {
                return Some(Err(e));
            }

            let typed_args = vec![ApplyArg {
                label: args[0].0.clone(),
                expression: arg,
            }];

            Some(Ok(Expression::new(
                ExpressionDesc::Texp_apply {
                    funct: Box::new(typed_funct.clone()),
                    args: typed_args,
                    partial: false,
                    transformed_jsx: false,
                },
                loc.clone(),
                result_ty,
                EnvRef(0),
                attributes.to_vec(),
            )))
        }
        _ => None, // Wrong number of args for the form
    }
}

fn type_application(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    funct: &ParsedExpression,
    args: &[(ArgLabel, ParsedExpression)],
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

    // Try unified ops dispatch first (matching OCaml's translate_unified_ops)
    if let Some(result) = translate_unified_ops(
        tctx, env, loc, &typed_funct, args, expected_ty, context.clone(), attributes,
    ) {
        return result;
    }

    // Normal application: get the function's type after any unification
    let mut current_ty = tctx.type_ctx.repr(typed_funct.exp_type);

    // Check if function type is a Tvar (force_tvar case in OCaml).
    // In ReScript, all applications are total/uncurried, so when the function's type
    // is a type variable, we set the arity to the number of arguments.
    let force_tvar = matches!(&*tctx.type_ctx.get_desc(current_ty), TypeDesc::Tvar(_));
    let top_arity: Option<i32> = if force_tvar {
        Some(args.len() as i32)
    } else {
        // Check existing arity from function type
        match &*tctx.type_ctx.get_desc(current_ty) {
            TypeDesc::Tarrow { arity, .. } => *arity,
            _ => None,
        }
    };

    // Type check arguments, extracting/building arrow types as we go
    let mut typed_args = Vec::new();
    for (label, arg_expr) in args.iter() {
        // Skip optional parameters when the call-site provides a Nolabel argument.
        // This handles cases like f(~x: int=?, unit) called as f(()) where the
        // optional ~x parameter should be implicitly None.
        loop {
            let (fn_label, arg_ty, ret_ty) = match crate::types::ctype::split_arrow_with_label(ctx, current_ty) {
                Some((lbl, arg, ret)) => (Some(lbl), arg, ret),
                None => {
                    // Not a function type yet - create arrow type with arity
                    let arg_ty = ctx.new_var(None);
                    let ret_ty = ctx.new_var(None);
                    let arrow_ty = ctx.new_arrow(crate::types::ArgLabel::Nolabel, arg_ty, ret_ty, top_arity);
                    unify_expression_types(tctx, loc, current_ty, arrow_ty, None)?;
                    (None, arg_ty, ret_ty)
                }
            };

            let fn_param_is_optional = fn_label.as_ref().map_or(false, |l| l.is_optional());
            let call_is_optional = label.is_optional();

            // Check if the labels match (considering that Optional("x") matches Labelled("x"))
            let labels_match = match (&fn_label, label) {
                (Some(fn_lbl), call_lbl) => {
                    match (fn_lbl.label_name(), call_lbl.name_idx()) {
                        (Some(fn_name), Some(call_idx)) => fn_name == tctx.arena.get_string(call_idx),
                        (None, None) => true, // both Nolabel
                        _ => false,
                    }
                }
                (None, call_lbl) => call_lbl.is_nolabel(),
            };

            // Skip optional parameters when:
            // 1. The function expects an optional param and call-site provides Nolabel, OR
            // 2. The function expects an optional param and call-site provides a different label
            // In both cases, the optional parameter gets None implicitly.
            if fn_param_is_optional && !labels_match {
                current_ty = ret_ty;
                continue;
            }

            // Handle optional parameter wrapping:
            // When the function parameter is Optional but the call-site passes a concrete
            // value (Labelled, not Optional), unwrap option<T> to T for type checking.
            let effective_arg_ty = if fn_param_is_optional && !call_is_optional {
                // Unwrap option<T> to get T for type checking the concrete argument
                crate::types::ctype::extract_option_type(ctx, arg_ty).unwrap_or(arg_ty)
            } else {
                arg_ty
            };

            // Type check the argument
            let typed_arg = type_expect(
                tctx,
                env,
                arg_expr,
                effective_arg_ty,
                Some(TypeClashContext::FunctionCall),
            )?;
            typed_args.push(ApplyArg {
                label: label.clone(),
                expression: typed_arg,
            });

            // Move to return type for next argument
            current_ty = ret_ty;
            break;
        }
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
        attributes.to_vec(),
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
        attributes.to_vec(),
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
        &case.pc_lhs,
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
        Some(type_expect(tctx, &case_env, guard, bool_ty, None)?)
    } else {
        None
    };

    // Type check the body
    let typed_body = type_expect(tctx, &case_env, &case.pc_rhs, body_ty, None)?;

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
        attributes.to_vec(),
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
        attributes.to_vec(),
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
        attributes.to_vec(),
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
    let longident = tctx.resolve_lid(lid.txt).clone();

    // Look up constructor with disambiguation following OCaml's approach:
    // 1. For module-qualified constructors (Ldot), use direct module lookup
    // 2. For unqualified constructors (Lident), use disambiguation considering expected type
    let lid_name = tctx.longident_last_name(&longident);
    let is_qualified = matches!(longident, Longident::Ldot(..));
    let (_cstr_path, cstr_desc) = if is_qualified {
        // Module-qualified: use direct lookup
        match lookup_constructor_in_module(&longident, tctx.arena, env, &mut tctx.persistent_env, tctx.type_ctx) {
            Some((path, desc)) => (path, desc),
            None => {
                match env.find_constructor(&lid_name) {
                    Ok(desc) => (
                        Path::pident(Ident::create_persistent(lid_name)),
                        desc.clone(),
                    ),
                    Err(_) => return Err(TypeCoreError::NotAVariantType(longident)),
                }
            }
        }
    } else {
        // Unqualified: use disambiguation with expected type
        match disambiguate_constructor(&lid_name, expected_ty, env, &mut tctx.persistent_env, tctx.type_ctx) {
            Some((path, desc)) => (path, desc),
            None => {
                match lookup_constructor_in_module(&longident, tctx.arena, env, &mut tctx.persistent_env, tctx.type_ctx) {
                    Some((path, desc)) => (path, desc),
                    None => return Err(TypeCoreError::NotAVariantType(longident)),
                }
            }
        }
    };

    // Instantiate constructor: creates fresh type variables shared between
    // cstr_res and cstr_args, matching OCaml's Ctype.instance_constructor
    let (inst_arg_types, result_ty) = crate::types::instance_constructor(ctx, &cstr_desc);
    unify_expression_types(tctx, loc, result_ty, expected_ty, None)?;

    // Type check arguments
    let typed_args = match (inst_arg_types.as_slice(), arg) {
        (arg_types, Some(arg_expr)) if arg_types.len() == 1 => {
            // Single argument
            let typed_arg = type_expect(tctx, env, arg_expr, arg_types[0], None)?;
            vec![typed_arg]
        }
        (arg_types, Some(arg_expr)) if arg_types.len() > 1 => {
            // Multiple arguments - the parser wraps them in a tuple
            let tuple_ty = ctx.new_tuple(arg_types.to_vec());
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
        attributes.to_vec(),
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
        attributes.to_vec(),
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

    // Track which field positions we've seen (for missing optional field detection)
    let mut seen_positions = std::collections::HashSet::new();
    let mut has_optional = false;

    // Type check each field
    let mut typed_fields = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let field_name = tctx.longident_last_name(tctx.resolve_lid(field.lid.txt));

        // Check if this field is optional (from env or parser)
        let is_optional = if let Ok(env_label) = env.find_label(&field_name) {
            env_label.lbl_optional
        } else {
            field.opt
        };

        // Type check the field expression with a fresh type variable
        let field_ty = ctx.new_var(None);
        let typed_expr = type_expect(tctx, env, &field.expr, field_ty, None)?;

        // For optional fields, create the option type for unification with lbl_arg
        let lbl_arg_ty = if is_optional {
            env.type_option(ctx, field_ty)
        } else {
            field_ty
        };

        // Build label description - use env info if available, otherwise placeholder
        let label_desc = if let Ok(env_label) = env.find_label(&field_name) {
            // Instantiate the label type to resolve type names
            let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, env_label);
            // Best-effort unification to propagate type info
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, expected_ty);
            // For optional fields, unify option<field_ty> with ty_arg (which is option<T>)
            // For non-optional fields, unify field_ty with ty_arg (which is T)
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, lbl_arg_ty, ty_arg);
            if env_label.lbl_optional {
                has_optional = true;
            }
            seen_positions.insert(env_label.lbl_pos);
            crate::types::LabelDescription {
                lbl_name: env_label.lbl_name.clone(),
                lbl_res: expected_ty,
                lbl_arg: lbl_arg_ty,
                lbl_mut: env_label.lbl_mut.clone(),
                lbl_optional: env_label.lbl_optional,
                lbl_pos: env_label.lbl_pos,
                lbl_all: env_label.lbl_all,
                lbl_repres: env_label.lbl_repres.clone(),
                lbl_private: env_label.lbl_private.clone(),
                lbl_loc: env_label.lbl_loc.clone(),
                lbl_attributes: env_label.lbl_attributes.clone(),
            }
        } else {
            if field.opt {
                has_optional = true;
            }
            crate::types::LabelDescription {
                lbl_name: field_name,
                lbl_res: expected_ty,
                lbl_arg: lbl_arg_ty,
                lbl_mut: crate::types::MutableFlag::Immutable,
                lbl_optional: field.opt,
                lbl_pos: idx as i32,
                lbl_all: crate::types::LabelArrayRef(0),
                lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                lbl_private: crate::types::PrivateFlag::Public,
                lbl_loc: tctx.arena.to_location(field.lid.loc),
                lbl_attributes: vec![],
            }
        };

        // If field is optional, wrap the typed expression in Some(...)
        // Matching OCaml's process_optional_label behavior
        let (final_expr, final_desc) = if label_desc.lbl_optional {
            let option_ty = lbl_arg_ty; // Already option<T>
            let some_cstr = make_some_constructor(ctx, option_ty);
            let some_lid = Located { txt: tctx.arena.some_lid(), loc };
            let wrapped = Expression::new(
                ExpressionDesc::Texp_construct(some_lid.clone(), some_cstr, vec![typed_expr]),
                loc,
                option_ty,
                EnvRef(0),
                vec![],
            );
            let mut desc = label_desc;
            desc.lbl_optional = false; // Mark as required after wrapping
            (wrapped, desc)
        } else {
            (typed_expr, label_desc)
        };

        typed_fields.push((
            field.lid.clone(),
            final_desc,
            RecordLabelDefinition::Overridden(field.lid.clone(), final_expr),
        ));
    }

    // Add missing optional fields as None
    // Matching OCaml's label_definitions logic (typecore.ml line 2663-2679)
    if has_optional && typed_base.is_none() {
        if let Some(all_labels) = get_record_labels(ctx, env, expected_ty) {
            for (lbl_idx, label_decl) in all_labels.iter().enumerate() {
                let lbl_pos = lbl_idx as i32;
                if label_decl.ld_optional && !seen_positions.contains(&lbl_pos) {
                    // This optional field was not provided - synthesize None
                    // lbl_arg/ld_type for optional fields is already option<T>
                    // (typemod.rs wraps optional label types during type declaration)
                    let lbl_name = label_decl.ld_id.name().to_string();
                    let option_ty = if let Ok(env_label) = env.find_label(&lbl_name) {
                        let (ta, tr) = crate::types::ctype::instance_label(ctx, env_label);
                        let _ = crate::types::unify(ctx, &mut tctx.unify_state, tr, expected_ty);
                        ta // Already option<T>
                    } else {
                        crate::types::instance(ctx, label_decl.ld_type) // Already option<T>
                    };
                    let none_cstr = make_none_constructor(ctx, option_ty);
                    let none_lid = Located { txt: tctx.arena.none_lid(), loc };
                    let none_expr = Expression::new(
                        ExpressionDesc::Texp_construct(none_lid.clone(), none_cstr, vec![]),
                        loc,
                        option_ty,
                        EnvRef(0),
                        vec![],
                    );

                    let label_desc = crate::types::LabelDescription {
                        lbl_name: lbl_name.clone(),
                        lbl_res: expected_ty,
                        lbl_arg: option_ty,
                        lbl_mut: crate::types::MutableFlag::Immutable,
                        lbl_optional: false, // Required after desugaring
                        lbl_pos,
                        lbl_all: crate::types::LabelArrayRef(0),
                        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                        lbl_private: crate::types::PrivateFlag::Public,
                        lbl_loc: crate::location::Location::none(),
                        lbl_attributes: vec![],
                    };

                    let field_lid = Located { txt: tctx.arena.placeholder_lid(), loc };
                    typed_fields.push((
                        field_lid.clone(),
                        label_desc,
                        RecordLabelDefinition::Overridden(
                            Located { txt: tctx.arena.placeholder_lid(), loc },
                            none_expr,
                        ),
                    ));
                }
            }
        }
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_record {
            fields: typed_fields,
            extended_expression: typed_base.map(Box::new),
        },
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
    ))
}

/// Create a ConstructorDescription for the `Some` constructor.
fn make_some_constructor(ctx: &TypeContext<'_>, option_ty: TypeExprRef) -> crate::types::ConstructorDescription {
    crate::types::ConstructorDescription {
        cstr_name: "Some".to_string(),
        cstr_res: option_ty,
        cstr_existentials: vec![],
        cstr_args: vec![ctx.new_var(None)], // The inner type
        cstr_arity: 1,
        cstr_tag: crate::types::ConstructorTag::CstrBlock(0),
        cstr_consts: 1,
        cstr_nonconsts: 1,
        cstr_generalized: false,
        cstr_private: crate::types::PrivateFlag::Public,
        cstr_loc: crate::location::Location::none(),
        cstr_attributes: vec![],
        cstr_inlined: None,
    }
}

/// Create a ConstructorDescription for the `None` constructor.
fn make_none_constructor(_ctx: &TypeContext<'_>, option_ty: TypeExprRef) -> crate::types::ConstructorDescription {
    crate::types::ConstructorDescription {
        cstr_name: "None".to_string(),
        cstr_res: option_ty,
        cstr_existentials: vec![],
        cstr_args: vec![],
        cstr_arity: 0,
        cstr_tag: crate::types::ConstructorTag::CstrConstant(0),
        cstr_consts: 1,
        cstr_nonconsts: 1,
        cstr_generalized: false,
        cstr_private: crate::types::PrivateFlag::Public,
        cstr_loc: crate::location::Location::none(),
        cstr_attributes: vec![],
        cstr_inlined: None,
    }
}

/// Get all label declarations for a record type from the environment.
fn get_record_labels(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<Vec<crate::types::decl::LabelDeclaration>> {
    let repr = ctx.repr(ty);
    let desc = ctx.get_desc(repr);
    if let crate::types::TypeDesc::Tconstr { ref path, .. } = *desc {
        if let Ok(type_decl) = env.lookup_type(path) {
            if let crate::types::TypeKind::TypeRecord(ref labels, _) = type_decl.type_kind {
                return Some(labels.clone());
            }
        }
    }
    None
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

    let field_name = tctx.longident_last_name(tctx.resolve_lid(field_lid.txt));

    // Following OCaml's type_label_access pattern:
    // 1. Type the record expression first (with unconstrained type)
    // 2. Use the expression's type to disambiguate the label
    let record_ty = ctx.new_var(None);
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;
    let ty_exp = typed_record.exp_type;

    let field_ty = ctx.new_var(None);
    let _ = crate::types::unify(ctx, &mut tctx.unify_state, field_ty, expected_ty);

    // Disambiguate label: use the record expression's type to find the right label
    let env_label = disambiguate_label(&field_name, ty_exp, env, ctx);

    let label_desc = if let Some(env_label) = env_label {
        let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
        // Unify label's result type with the record's type
        let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, record_ty);
        // Unify label's arg type with the field type
        let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_arg, field_ty);
        crate::types::LabelDescription {
            lbl_name: env_label.lbl_name.clone(),
            lbl_res: record_ty,
            lbl_arg: field_ty,
            lbl_mut: env_label.lbl_mut.clone(),
            lbl_optional: env_label.lbl_optional,
            lbl_pos: env_label.lbl_pos,
            lbl_all: env_label.lbl_all,
            lbl_repres: env_label.lbl_repres.clone(),
            lbl_private: env_label.lbl_private.clone(),
            lbl_loc: env_label.lbl_loc.clone(),
            lbl_attributes: env_label.lbl_attributes.clone(),
        }
    } else {
        crate::types::LabelDescription {
            lbl_name: field_name,
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
        }
    };

    // Unify the record expression's type with the record type
    unify_expression_types(tctx, loc, ty_exp, record_ty, None)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_field(Box::new(typed_record), field_lid.clone(), label_desc),
        loc,
        field_ty,
        EnvRef(0),
        attributes.to_vec(),
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
    let field_name = tctx.longident_last_name(tctx.resolve_lid(field_lid.txt));

    // Create fresh type variables for the record and field
    let record_ty = ctx.new_var(None);
    let field_ty = ctx.new_var(None);

    // Try to look up the label from the environment for type info
    let label_desc = if let Ok(env_label) = env.find_label(&field_name) {
        let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, env_label);
        // Best-effort unification to propagate type info
        let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_arg, field_ty);
        let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, record_ty);
        crate::types::LabelDescription {
            lbl_name: env_label.lbl_name.clone(),
            lbl_res: record_ty,
            lbl_arg: field_ty,
            lbl_mut: env_label.lbl_mut.clone(),
            lbl_optional: env_label.lbl_optional,
            lbl_pos: env_label.lbl_pos,
            lbl_all: env_label.lbl_all,
            lbl_repres: env_label.lbl_repres.clone(),
            lbl_private: env_label.lbl_private.clone(),
            lbl_loc: env_label.lbl_loc.clone(),
            lbl_attributes: env_label.lbl_attributes.clone(),
        }
    } else {
        crate::types::LabelDescription {
            lbl_name: field_name,
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
        }
    };

    // Type check the record expression with the proper record type
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;

    // Type check the new value with the proper field type
    let typed_value = type_expect(tctx, env, new_value, field_ty, None)?;

    // setfield has type unit
    unify_expression_types(tctx, loc, expected_ty, unit_ty, context)?;

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
        attributes.to_vec(),
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
        attributes.to_vec(),
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
    let (_opt_from_typed, from_ty) = if let Some(from_type) = opt_from_type {
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
    // The expression type becomes the target type after coercion
    let mut result = typed_inner.with_exp_extra(
        crate::types::typedtree::ExpExtra::Texp_coerce(to_typed_ctype),
        loc.clone(),
        attributes.to_vec(),
    );
    result.exp_type = to_ty;
    Ok(result)
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
    // Open the module's bindings into scope for the body
    let open_lid = tctx.arena.get_longident(lid.txt);
    let mut open_env = env.clone();

    // Resolve the module longident and open its signature
    let path = crate::types::typemod::path_from_longident(open_lid, |idx| tctx.arena.get_string(idx));
    let mod_type = crate::types::typemod::lookup_module_type_by_lid(
        open_lid, tctx.arena, env, &mut tctx.persistent_env, tctx.type_ctx,
    );
    if let Some(ref mty) = mod_type {
        let sig = crate::types::typemod::resolve_mod_type_to_sig(
            mty, &mut tctx.persistent_env, tctx.type_ctx,
        );
        if let Some(ref sig_items) = sig {
            crate::cmi::persistent_env::add_signature_to_env(
                sig_items, &path, &mut open_env, tctx.type_ctx, true,
            );
        }
    }

    // Type check the body expression in the extended environment
    let typed_body = type_expect(tctx, &open_env, body, expected_ty, None)?;

    // Return expression with open in exp_extra
    Ok(Expression::new(
        typed_body.exp_desc,
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
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
        attributes.to_vec(),
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
        attributes.to_vec(),
    ))
}

/// Type check method send.
fn type_send(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    obj_expr: &ParsedExpression,
    method: &Located<String>,
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
            crate::types::typedtree::MethKind::Tmeth_name(method.txt.clone()),
            None,
        ),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
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
        attributes.to_vec(),
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
        attributes.to_vec(),
    ))
}

/// Type check let module expression.
#[allow(clippy::too_many_arguments)]
fn type_letmodule(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    name: &Located<StrIdx>,
    module_expr: &crate::parser::ast::ModuleExpr,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let arena = tctx.arena;
    let mod_name_str = arena.get_string(name.txt).to_string();
    let mod_id = Ident::create_local(&mod_name_str);

    // Type check the module expression and build its signature for the env
    let (typed_mod, mod_sig) = match &module_expr.pmod_desc {
        crate::parser::ast::ModuleExprDesc::Pmod_structure(items) => {
            let (structure, _inner_env) = crate::types::typemod::type_structure(tctx, env, arena, items)
                .map_err(|e| TypeCoreError::Other(format!("letmodule: {e:?}")))?;

            // Build a signature from the typed structure items
            let sig_items = build_signature_from_structure(&structure);

            let md = crate::types::typedtree::ModuleExpr {
                mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_structure(structure),
                mod_loc: module_expr.pmod_loc,
                mod_type: crate::types::typedtree::ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: vec![],
            };
            (md, crate::types::decl::ModuleType::MtySignature(sig_items))
        }
        _ => {
            let md = crate::types::typemod::type_module_expr(tctx, env, arena, module_expr)
                .map_err(|e| TypeCoreError::Other(format!("letmodule: {e:?}")))?;
            // Try to extract module type from typed expression, or look it up for idents
            let mod_sig = crate::types::typemod::extract_module_type_from_mod_expr_pub(&md)
                .or_else(|| {
                    // For module aliases (Pmod_ident), look up the module's type
                    if let crate::parser::ast::ModuleExprDesc::Pmod_ident(lid) = &module_expr.pmod_desc {
                        let longident = arena.get_longident(lid.txt);
                        crate::types::typemod::lookup_module_type_by_lid(
                            longident, arena, env, &mut tctx.persistent_env, tctx.type_ctx,
                        )
                    } else {
                        None
                    }
                })
                .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
            (md, mod_sig)
        }
    };

    // Add the module to the environment so the body can access M.value
    let mut body_env = env.clone();
    let md_decl = crate::types::decl::ModuleDeclaration {
        md_type: mod_sig,
        md_attributes: vec![],
        md_loc: crate::location::Location::none(),
    };
    body_env.add_module(mod_id.clone(), md_decl);

    // Type check the body in the extended environment
    let typed_body = type_expect(tctx, &body_env, body, expected_ty, None)?;

    Ok(Expression::new(
        crate::types::typedtree::ExpressionDesc::Texp_letmodule(
            mod_id,
            Located { txt: mod_name_str.clone(), loc: name.loc },
            Box::new(typed_mod),
            Box::new(typed_body),
        ),
        loc,
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
    ))
}

/// Extract value signature items from a binding pattern (for building signatures from structures).
fn extract_sig_values_from_binding_pattern(
    pat: &crate::types::typedtree::Pattern,
    ty: TypeExprRef,
    sig: &mut Vec<crate::types::decl::SignatureItem>,
) {
    use crate::types::typedtree::PatternDesc;
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            sig.push(crate::types::decl::SignatureItem::SigValue(
                id.clone(),
                crate::types::decl::ValueDescription {
                    val_type: ty,
                    val_kind: crate::types::decl::ValueKind::ValReg,
                    val_loc: crate::location::Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                },
            ));
        }
        PatternDesc::Tpat_alias(inner, id, _) => {
            sig.push(crate::types::decl::SignatureItem::SigValue(
                id.clone(),
                crate::types::decl::ValueDescription {
                    val_type: ty,
                    val_kind: crate::types::decl::ValueKind::ValReg,
                    val_loc: crate::location::Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                },
            ));
            // Also extract from the inner pattern
            extract_sig_values_from_binding_pattern(inner, ty, sig);
        }
        PatternDesc::Tpat_tuple(pats) => {
            for p in pats {
                extract_sig_values_from_binding_pattern(p, p.pat_type, sig);
            }
        }
        _ => {}
    }
}

/// Build a signature from typed structure items.
fn build_signature_from_structure(structure: &crate::types::typedtree::Structure) -> Vec<crate::types::decl::SignatureItem> {
    use crate::types::typedtree::StructureItemDesc;
    let mut sig = Vec::new();
    for item in &structure.str_items {
        match &item.str_desc {
            StructureItemDesc::Tstr_primitive(tvd) => {
                let vd = crate::types::decl::ValueDescription {
                    val_type: tvd.val_desc.ctyp_type,
                    val_kind: crate::types::decl::ValueKind::ValPrim(
                        crate::types::decl::PrimitiveDescription {
                            prim_name: tvd.val_prim.first().cloned().unwrap_or_default(),
                            prim_arity: 1,
                            prim_native_name: String::new(),
                            prim_native_float: false,
                        }
                    ),
                    val_loc: crate::location::Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                };
                sig.push(crate::types::decl::SignatureItem::SigValue(tvd.val_id.clone(), vd));
            }
            StructureItemDesc::Tstr_value(_rec, bindings) => {
                for binding in bindings {
                    extract_sig_values_from_binding_pattern(&binding.vb_pat, binding.vb_expr.exp_type, &mut sig);
                }
            }
            StructureItemDesc::Tstr_module(mb) => {
                let inner_mty = crate::types::typemod::extract_module_type_from_mod_expr_pub(&mb.mb_expr)
                    .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
                sig.push(crate::types::decl::SignatureItem::SigModule(
                    mb.mb_id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: inner_mty,
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                    },
                    crate::types::decl::RecStatus::TrecNot,
                ));
            }
            StructureItemDesc::Tstr_type(rec_flag, decls) => {
                let rec_status = match rec_flag {
                    crate::parser::ast::RecFlag::Recursive => crate::types::decl::RecStatus::TrecFirst,
                    crate::parser::ast::RecFlag::Nonrecursive => crate::types::decl::RecStatus::TrecNot,
                };
                for decl in decls {
                    sig.push(crate::types::decl::SignatureItem::SigType(
                        decl.typ_id.clone(),
                        decl.typ_type.clone(),
                        rec_status,
                    ));
                }
            }
            StructureItemDesc::Tstr_exception(ext_cstr) => {
                sig.push(crate::types::decl::SignatureItem::SigTypext(
                    ext_cstr.ext_id.clone(),
                    ext_cstr.ext_type.clone(),
                    crate::types::decl::ExtStatus::TextException,
                ));
            }
            StructureItemDesc::Tstr_typext(type_ext) => {
                for ext_cstr in &type_ext.tyext_constructors {
                    sig.push(crate::types::decl::SignatureItem::SigTypext(
                        ext_cstr.ext_id.clone(),
                        ext_cstr.ext_type.clone(),
                        crate::types::decl::ExtStatus::TextFirst,
                    ));
                }
            }
            _ => {}
        }
    }
    sig
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
            mod_attributes: vec![],
        })),
        loc,
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
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
        attributes.to_vec(),
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
            if let crate::parser::ast::PatternDesc::Ppat_var(name) = &binding.pvb_pat.ppat_desc {
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

    // Type check each binding, collecting pattern variables per binding
    let mut typed_bindings = Vec::new();
    let mut state = PatternState::new();
    let mut all_pattern_vars: Vec<Vec<PatternVariable>> = Vec::new();

    for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
        state.reset(false);

        // Type check pattern
        let typed_pat = type_pattern(
            tctx,
            &typing_env,
            &binding.pvb_pat,
            *ty,
            PatternMode::Normal,
            &mut state,
        )?;

        // Type check expression
        let typed_expr = type_expect(tctx, &typing_env, &binding.pvb_expr, *ty, None)?;

        typed_bindings.push(ValueBinding::new(
            typed_pat,
            typed_expr,
            binding.pvb_loc.clone(),
            binding.pvb_attributes.clone(),
        ));

        // Save pattern variables from this binding
        all_pattern_vars.push(state.pattern_variables.clone());
    }

    // End definition level
    ctx.end_def();

    // Generalize types
    for ty in &binding_types {
        crate::types::generalize(ctx, *ty);
    }

    // Build final environment from all collected pattern variables
    let mut new_env = env.clone();
    for pvars in all_pattern_vars.iter() {
        for pv in pvars {
            let desc = ValueDescription {
                val_type: pv.ty,
                val_kind: crate::types::ValueKind::ValReg,
                val_loc: crate::location::Location::none(),
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
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    expr: &ParsedExpression,
) -> TypeCoreResult<Expression> {
    let type_ctx = tctx.type_ctx;

    // Begin a definition scope
    type_ctx.begin_def();

    // Type with a fresh variable
    let expected_ty = type_ctx.new_var(None);
    let typed_expr = type_expect(tctx, env, expr, expected_ty, None)?;

    // Try to unify with unit (matching OCaml's Bs_toplevel_expression_unit warning behavior)
    // This resolves unresolved type variables to unit for statement-level expressions
    let unit_ty = env.type_unit(type_ctx);
    let _ = crate::types::unify(type_ctx, &mut tctx.unify_state, typed_expr.exp_type, unit_ty);

    // End definition scope
    type_ctx.end_def();

    // Generalize the type
    crate::types::generalize(type_ctx, typed_expr.exp_type);

    Ok(typed_expr)
}

/// Type check a top-level binding.
pub fn type_binding<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeCoreResult<(Vec<ValueBinding>, Env)> {
    type_let_bindings(tctx, env, rec_flag, bindings)
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
    pub fn lookup_value_by_lid<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> TypeCoreResult<(Path, ValueDescription)> {
        match lid {
            Longident::Lident(idx) => {
                let name = arena.get_string(*idx);
                match self.find_value_with_id(name) {
                    Ok((id, desc)) => {
                        let path = desc.val_path.clone().unwrap_or_else(|| Path::pident(id.clone()));
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
                // Resolve the module prefix to get a signature and path
                let lid_str = Self::longident_to_string(lid, arena);
                if let Some((mod_path, sig)) = self.resolve_module_lid(prefix, arena, pers_env, ctx) {
                    // Search for the value in the signature
                    for sig_item in &sig {
                        if let crate::types::decl::SignatureItem::SigValue(id, vd) = sig_item {
                            if id.name() == value_name {
                                let path = Path::pdot(mod_path, value_name.to_string());
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
                // Fallback: try looking up as a flattened value in the local env
                match self.find_value_with_id(value_name) {
                    Ok((id, desc)) => {
                        let path = desc.val_path.clone().unwrap_or_else(|| Path::pident(id.clone()));
                        Ok((path, desc.clone()))
                    }
                    Err(_) => Err(TypeCoreError::UndefinedMethod {
                        ty: TypeExprRef(0),
                        method: lid_str,
                        alternatives: None,
                    }),
                }
            }
            Longident::Lapply(_, _) => {
                Err(TypeCoreError::UndefinedMethod {
                    ty: TypeExprRef(0),
                    method: "(functor application)".to_string(),
                    alternatives: None,
                })
            }
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
                format!("{}({})", Self::longident_to_string(f, arena), Self::longident_to_string(a, arena))
            }
        }
    }

    /// Resolve a module longident to its signature and path.
    /// Handles nested module paths like Belt.Array by recursively resolving.
    fn resolve_module_lid<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        match lid {
            Longident::Lident(mod_idx) => {
                let mod_name = arena.get_string(*mod_idx);
                // First try local environment
                if let Ok(md) = self.find_module(mod_name) {
                    let sig = Self::resolve_module_type(&md.md_type, pers_env, ctx);
                    if let Some(sig) = sig {
                        return Some((Path::pident(Ident::create_local(mod_name)), sig));
                    }
                }
                // Then try persistent environment (external modules)
                if let Some(pers) = pers_env.as_mut() {
                    if let Some(ps) = pers.find_pers_struct(mod_name, ctx) {
                        let sig = ps.ps_sig.clone();
                        return Some((Path::pident(Ident::create_persistent(mod_name)), sig));
                    }
                }
                None
            }
            Longident::Ldot(prefix, submod_idx) => {
                let submod_name = arena.get_string(*submod_idx);
                // Recursively resolve the prefix to get a signature
                if let Some((parent_path, parent_sig)) = self.resolve_module_lid(prefix, arena, pers_env, ctx) {
                    // Search for the sub-module in the parent's signature
                    for sig_item in &parent_sig {
                        if let crate::types::decl::SignatureItem::SigModule(id, sub_md, _) = sig_item {
                            if id.name() == submod_name {
                                let sub_path = Path::pdot(parent_path, submod_name.to_string());
                                let sub_sig = Self::resolve_module_type(&sub_md.md_type, pers_env, ctx);
                                if let Some(sig) = sub_sig {
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

    /// Resolve a module type to a signature, following aliases and loading from persistent env.
    fn resolve_module_type<'b>(
        mty: &crate::types::decl::ModuleType,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<crate::types::decl::Signature> {
        match mty {
            crate::types::decl::ModuleType::MtySignature(sig) => Some(sig.clone()),
            crate::types::decl::ModuleType::MtyAlias(_, path) |
            crate::types::decl::ModuleType::MtyIdent(path) => {
                // Follow the alias: extract the module name from the path
                let mod_name = match path {
                    Path::Pident(id) => id.name().to_string(),
                    Path::Pdot(_, name, _) => name.clone(),
                    _ => return None,
                };
                if let Some(pers) = pers_env.as_mut() {
                    if let Some(ps) = pers.find_pers_struct(&mod_name, ctx) {
                        return Some(ps.ps_sig.clone());
                    }
                }
                None
            }
            _ => None,
        }
    }
}

/// Look up a constructor in a module-qualified path (e.g., Nullable.Value).
/// For Ldot paths, resolves the module and searches its type declarations.
fn lookup_constructor_in_module<'b>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    use crate::parser::longident::Longident;
    use crate::types::decl::SignatureItem;
    match lid {
        Longident::Ldot(module_lid, cstr_idx) => {
            let cstr_name = arena.get_string(*cstr_idx);
            // Resolve the module prefix to get its signature
            let (_mod_path, sig) = env.resolve_module_lid(module_lid, arena, pers_env, ctx)?;
            // Search the signature for type declarations that contain the constructor
            for sig_item in &sig {
                if let SignatureItem::SigType(_id, type_decl, _rec) = sig_item {
                    if let crate::types::TypeKind::TypeVariant(ref constrs) = type_decl.type_kind {
                        let num_consts = constrs.iter()
                            .filter(|c| matches!(c.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && c.cd_res.is_none())
                            .count() as i32;
                        let num_nonconsts = constrs.len() as i32 - num_consts;
                        let mut const_idx = 0i32;
                        let mut block_idx = 0i32;
                        for cd in constrs {
                            let is_constant = matches!(cd.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && cd.cd_res.is_none();
                            if cd.cd_id.name() == cstr_name {
                                let tag = if is_constant {
                                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                                } else {
                                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                                };
                                let (cstr_args, cstr_arity) = match &cd.cd_args {
                                    crate::types::ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
                                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                                        let args: Vec<_> = labels.iter().map(|l| l.ld_type).collect();
                                        let arity = args.len() as i32;
                                        (args, arity)
                                    }
                                };
                                let cstr_res = cd.cd_res.unwrap_or_else(|| {
                                    ctx.new_generic_constr(
                                        Path::pident(_id.clone()),
                                        type_decl.type_params.clone(),
                                    )
                                });
                                let desc = crate::types::decl::ConstructorDescription {
                                    cstr_name: cstr_name.to_string(),
                                    cstr_res,
                                    cstr_existentials: vec![],
                                    cstr_args,
                                    cstr_arity,
                                    cstr_tag: tag,
                                    cstr_consts: num_consts,
                                    cstr_nonconsts: num_nonconsts,
                                    cstr_generalized: false,
                                    cstr_private: crate::types::PrivateFlag::Public,
                                    cstr_loc: crate::location::Location::none(),
                                    cstr_attributes: vec![],
                                    cstr_inlined: None,
                                };
                                let path = Path::pident(Ident::create_persistent(cstr_name));
                                return Some((path, desc));
                            }
                            if is_constant { const_idx += 1; } else { block_idx += 1; }
                        }
                    }
                }
                // Also search SigTypext for exception/extension constructors
                if let SignatureItem::SigTypext(id, ext, _status) = sig_item {
                    if id.name() == cstr_name {
                        let (cstr_args, cstr_arity) = match &ext.ext_args {
                            crate::types::ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
                            crate::types::ConstructorArguments::CstrRecord(labels) => {
                                let args: Vec<_> = labels.iter().map(|l| l.ld_type).collect();
                                let arity = args.len() as i32;
                                (args, arity)
                            }
                        };
                        let cstr_res = ctx.new_generic_constr(ext.ext_type_path.clone(), ext.ext_type_params.clone());
                        let ext_path = Path::pident(Ident::create_persistent(cstr_name));
                        let desc = crate::types::decl::ConstructorDescription {
                            cstr_name: cstr_name.to_string(),
                            cstr_res,
                            cstr_existentials: vec![],
                            cstr_args,
                            cstr_arity,
                            cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(ext_path.clone()),
                            cstr_consts: 0,
                            cstr_nonconsts: 0,
                            cstr_generalized: false,
                            cstr_private: crate::types::PrivateFlag::Public,
                            cstr_loc: crate::location::Location::none(),
                            cstr_attributes: vec![],
                            cstr_inlined: None,
                        };
                        return Some((ext_path, desc));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract the type path from a type expression if it's a concrete type constructor.
/// Follows repr/Tlink chains, and for abstract types tries to expand through aliases.
/// Returns the path from the Tconstr if found.
fn extract_type_path_from_expected<'a>(
    expected_ty: TypeExprRef,
    env: &Env,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<Path> {
    let ty = ctx.repr(expected_ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, .. } => {
            // Check if this is a concrete (non-abstract) type
            if let Some(decl) = lookup_type_decl_for_path(path, env, ctx) {
                match &decl.type_kind {
                    crate::types::TypeKind::TypeAbstract => {
                        // Abstract type - try to expand through manifest
                        if let Some(manifest) = decl.type_manifest {
                            drop(desc);
                            return extract_type_path_from_expected(manifest, env, ctx);
                        }
                        None
                    }
                    _ => Some(path.clone()),
                }
            } else {
                // Can't find decl, but the path might still work for matching
                Some(path.clone())
            }
        }
        _ => None,
    }
}

/// Disambiguate a constructor by name, considering both the environment and
/// the expected type. Follows OCaml's disambiguate pattern:
/// 1. Try to extract the concrete variant type from expected_ty
/// 2. Find all constructors with the given name in the env
/// 3. If we have a type path from expected_ty, prefer the constructor matching that type
/// 4. Otherwise fall back to the most recent constructor in scope
fn disambiguate_constructor<'a>(
    cstr_name: &str,
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    // Step 1: Try to extract the variant type path from the expected type
    let opath = extract_type_path_from_expected(expected_ty, env, ctx);

    // Step 2: Find all constructors with this name
    let all_constrs = env.find_all_constructors(cstr_name);

    if all_constrs.is_empty() {
        // No constructors found in env - try type-directed lookup
        return lookup_constructor_by_expected_type(cstr_name, expected_ty, env, pers_env, ctx);
    }

    // Step 3: If we have a target type path, try to disambiguate
    if let Some(ref target_path) = opath {
        // Look for a constructor whose result type matches the expected type's path
        for cstr in &all_constrs {
            let cstr_ty = ctx.repr(cstr.cstr_res);
            let cstr_desc = ctx.get_desc(cstr_ty);
            if let TypeDesc::Tconstr { path: cstr_path, .. } = &*cstr_desc {
                if cstr_path.same(target_path) {
                    let path = Path::pident(Ident::create_persistent(cstr_name));
                    return Some((path, (*cstr).clone()));
                }
            }
        }
        // No constructor in env matched the expected type - try type-directed lookup
        // (the type might be defined in another module loaded from CMI)
        if let Some(result) = lookup_constructor_by_expected_type(cstr_name, expected_ty, env, pers_env, ctx) {
            return Some(result);
        }
    }

    // Step 4: Fall back to the most recent constructor (last in the list = most recently added)
    let cstr = all_constrs.last().unwrap();
    let path = Path::pident(Ident::create_persistent(cstr_name));
    Some((path, (*cstr).clone()))
}

/// Disambiguate a label by name, considering the record expression's type.
/// Follows OCaml's Label.disambiguate pattern:
/// 1. Get all labels with the given name from the env
/// 2. Extract the type path from the record expression's type
/// 3. If we have a type path, prefer the label from that type
/// 4. Otherwise fall back to the most recent label in scope
fn disambiguate_label<'a>(
    label_name: &str,
    record_ty: TypeExprRef,
    env: &Env,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    // Extract type path from the record expression's type
    let opath = extract_type_path_from_expected(record_ty, env, ctx);

    // Find all labels with this name
    let all_labels = env.find_all_labels(label_name);

    if all_labels.is_empty() {
        return None;
    }

    // If we have a target type path, try to disambiguate
    if let Some(ref target_path) = opath {
        for label in &all_labels {
            let lbl_ty = ctx.repr(label.lbl_res);
            let lbl_desc = ctx.get_desc(lbl_ty);
            if let TypeDesc::Tconstr { path: lbl_path, .. } = &*lbl_desc {
                if lbl_path.same(target_path) {
                    return Some((*label).clone());
                }
            }
        }
    }

    // Fall back to the most recent label (last in the list)
    all_labels.last().map(|l| (*l).clone())
}

/// Type-directed constructor disambiguation.
///
/// When a constructor like `A` is used without qualification and is not found
/// in the local env, look at the expected type to find which type defines it.
/// For example, if the expected type is `M.t` and `M.t` is defined as `A | B(int)`,
/// we can resolve the unqualified `A` constructor.
fn lookup_constructor_by_expected_type<'b>(
    cstr_name: &str,
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    let expected_ty = ctx.repr(expected_ty);
    let desc = ctx.get_desc(expected_ty);

    let type_path = match &*desc {
        TypeDesc::Tconstr { path, .. } => path.clone(),
        _ => return None,
    };
    drop(desc);

    // Look up the type declaration
    let type_decl = lookup_type_decl_for_path(&type_path, env, ctx)?;

    // Check if it's a variant type with a matching constructor
    if let crate::types::TypeKind::TypeVariant(ref constrs) = type_decl.type_kind {
        let num_consts = constrs.iter()
            .filter(|c| matches!(c.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && c.cd_res.is_none())
            .count() as i32;
        let num_nonconsts = constrs.len() as i32 - num_consts;
        let mut const_idx = 0i32;
        let mut block_idx = 0i32;
        for cd in constrs {
            let is_constant = matches!(cd.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && cd.cd_res.is_none();
            if cd.cd_id.name() == cstr_name {
                let tag = if is_constant {
                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                } else {
                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                };
                let (cstr_args, cstr_arity) = match &cd.cd_args {
                    crate::types::ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                        let args: Vec<_> = labels.iter().map(|l| l.ld_type).collect();
                        let arity = args.len() as i32;
                        (args, arity)
                    }
                };
                // Use the type path's head ident for the result type
                let type_path_ident = match &type_path {
                    Path::Pident(id) => id.clone(),
                    Path::Pdot(_, name, _) => Ident::create_persistent(name.as_str()),
                    _ => return None,
                };
                let cstr_res = cd.cd_res.unwrap_or_else(|| {
                    ctx.new_generic_constr(
                        Path::pident(type_path_ident),
                        type_decl.type_params.clone(),
                    )
                });
                let desc = crate::types::decl::ConstructorDescription {
                    cstr_name: cstr_name.to_string(),
                    cstr_res,
                    cstr_existentials: vec![],
                    cstr_args,
                    cstr_arity,
                    cstr_tag: tag,
                    cstr_consts: num_consts,
                    cstr_nonconsts: num_nonconsts,
                    cstr_generalized: false,
                    cstr_private: crate::types::PrivateFlag::Public,
                    cstr_loc: crate::location::Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: None,
                };
                let path = Path::pident(Ident::create_persistent(cstr_name));
                return Some((path, desc));
            }
            if is_constant { const_idx += 1; } else { block_idx += 1; }
        }
    }
    None
}

/// Look up a type declaration for a given path.
/// Tries env first, then the global type stores.
fn lookup_type_decl_for_path<'a>(
    type_path: &Path,
    env: &Env,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::decl::TypeDeclaration> {
    // Try env.lookup_type first
    if let Ok(decl) = env.lookup_type(type_path) {
        return Some(decl.clone());
    }

    // Try stamp-based lookup
    if let Path::Pident(id) = type_path {
        if id.stamp() != 0 {
            if let Some(decl) = ctx.find_type_decl_by_stamp(id.stamp()) {
                return Some(decl.clone());
            }
        }
    }

    // Try path-based lookup for Pdot paths
    if let Path::Pdot(parent, type_name, _) = type_path {
        let path_name = type_path.name();
        if let Some(decl) = ctx.find_type_decl_by_path(&path_name) {
            return Some(decl.clone());
        }

        // Try resolving the module alias: Pdot(Pident(Nullable/9), "t")
        // -> look up "Nullable" module in env -> if it's MtyAlias(Stdlib_Nullable)
        // -> look up "Stdlib_Nullable.t" in the path store or try CMI resolution
        if let Path::Pident(parent_id) = parent.as_ref() {
            // Use name-based lookup since stamp in type path may differ from env
            if let Ok(md) = env.find_module(parent_id.name()) {
                use crate::types::decl::ModuleType;
                match &md.md_type {
                    ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                        let resolved_path = Path::pdot(alias_path.clone(), type_name.as_str());
                        if let Some(decl) = ctx.find_type_decl_by_path(&resolved_path.name()) {
                            return Some(decl.clone());
                        }
                        if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, &resolved_path) {
                            return Some(decl);
                        }
                    }
                    ModuleType::MtySignature(sig) => {
                        for item in sig {
                            if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item {
                                if id.name() == type_name.as_str() {
                                    return Some(decl.clone());
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Try resolving through modules (loading CMI files on demand)
        if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, type_path) {
            return Some(decl);
        }

        // Try Stdlib alias patterns as fallback
        if let Path::Pident(parent_id) = parent.as_ref() {
            let flat_name = format!("Stdlib_{}.{}", parent_id.name(), type_name);
            if let Some(decl) = ctx.find_type_decl_by_path(&flat_name) {
                return Some(decl.clone());
            }
            let stdlib_path = format!("Stdlib.{}.{}", parent_id.name(), type_name);
            if let Some(decl) = ctx.find_type_decl_by_path(&stdlib_path) {
                return Some(decl.clone());
            }
            // Try loading CMI directly by module name
            let direct_path = Path::pdot(
                Path::Pident(Ident::create_persistent(parent_id.name())),
                type_name.as_str(),
            );
            if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, &direct_path) {
                return Some(decl);
            }
        }
    }

    // Try name-based lookup
    let name = type_path.head_name();
    if let Some(decl) = ctx.find_type_decl(name) {
        return Some(decl.clone());
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;

    #[test]
    fn test_convert_constant_int() {
        let cst = crate::parser::ast::Constant::Integer("42".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(42));
    }

    #[test]
    fn test_convert_constant_overflow_wraps() {
        // Values that fit in i64 but not i32 should wrap to i32
        let cst = crate::parser::ast::Constant::Integer("99999999999999999".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(99999999999999999_i64 as i32));
    }

    #[test]
    fn test_convert_constant_overflow_too_large() {
        // Values that don't fit in i64 should still error
        let cst = crate::parser::ast::Constant::Integer("99999999999999999999999".to_string(), None);
        let result = convert_constant(&cst);
        assert!(matches!(result, Err(TypeCoreError::LiteralOverflow(_))));
    }

    #[test]
    fn test_convert_constant_underscores() {
        let cst = crate::parser::ast::Constant::Integer("949_460_645_006".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(949_460_645_006_i64 as i32));
    }

    #[test]
    fn test_convert_constant_hex() {
        let cst = crate::parser::ast::Constant::Integer("0xffff_ffff".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(0xffff_ffff_i64 as i32));
    }

    #[test]
    fn test_convert_constant_string() {
        let cst = crate::parser::ast::Constant::String("hello".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::String(s, None) if s == "hello"));
    }

    #[test]
    fn test_convert_constant_bigint() {
        let cst = crate::parser::ast::Constant::Integer("12345".to_string(), Some('n'));
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

        let arena = ParseArena::new();
        let loc = LocIdx::none();
        let ty = ctx.new_var(None);
        let name = Located {
            txt: "x".to_string(),
            loc,
        };

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
