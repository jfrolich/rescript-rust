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
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena, PosIdx, StrIdx};
use crate::parser::ast::{
    ArgLabel, Attributes, Expression as ParsedExpression, Pattern as ParsedPattern, PexpApply,
    PexpFun, RecFlag,
};
use crate::parser::longident::Longident;
use crate::types::typedtree::{
    ArrowArg, Constant, EnvRef, Expression, ExpressionDesc, Pattern, PatternDesc, ValueBinding,
};
use crate::types::{
    Env, Path, TypeContext, TypeDesc, TypeError, TypeExprRef, UnifyState, ValueDescription,
};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

const DICT_PATTERN_ATTRIBUTE: &str = "res.dictPattern";
const DICT_MAGIC_FIELD_NAME: &str = "dictValuesType";
const DICT_TYPE_NAME: &str = "dict";
const PAT_VARIANT_SPREAD_ATTRIBUTE: &str = "res.patVariantSpread";
const PAT_FROM_VARIANT_SPREAD_ATTRIBUTE: &str = "res.patFromVariantSpread";

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        if x > (isize::MAX as usize / 2) {
            break;
        }
        x *= 2;
    }
    x
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h.wrapping_mul(5).wrapping_add(0xe6546b64)
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

fn ocaml_hashtbl_hash_string(s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut h = 0u32;
    let mut i = 0usize;

    while i + 4 <= len {
        let w = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, w);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut w = 0u32;
        if rem >= 3 {
            w |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            w |= (bytes[i + 1] as u32) << 8;
        }
        w |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, w);
    }

    h ^= len as u32;
    ocaml_hash_final_mix(h) & 0x3fff_ffff
}

/// Match OCaml `Hashtbl.create 17` + `Hashtbl.fold` traversal order.
fn ocaml_hashtbl_fold_order(labels: &[String]) -> Vec<String> {
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); ocaml_hashtbl_power_2_above(16, 17)];
    let mut size = 0usize;

    for (entry_idx, label) in labels.iter().enumerate() {
        let bucket_idx = (ocaml_hashtbl_hash_string(label) as usize) & (buckets.len() - 1);
        buckets[bucket_idx].insert(0, entry_idx);
        size += 1;

        if size > (buckets.len() << 1) {
            let mut new_buckets = vec![Vec::new(); buckets.len() * 2];
            for bucket in &buckets {
                for &idx in bucket {
                    let new_idx = (ocaml_hashtbl_hash_string(&labels[idx]) as usize)
                        & (new_buckets.len() - 1);
                    new_buckets[new_idx].push(idx);
                }
            }
            buckets = new_buckets;
        }
    }

    let mut ordered = Vec::with_capacity(labels.len());
    for bucket in &buckets {
        for &idx in bucket {
            ordered.push(labels[idx].clone());
        }
    }
    ordered
}

/// Match OCaml `Hashtbl.replace` + `Hashtbl.fold` behavior for string keys.
fn ocaml_hashtbl_replace_fold_order(entries: &[String]) -> Vec<String> {
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); ocaml_hashtbl_power_2_above(16, 17)];
    let mut size = 0usize;

    for (entry_idx, entry) in entries.iter().enumerate() {
        let bucket_idx = (ocaml_hashtbl_hash_string(entry) as usize) & (buckets.len() - 1);
        if let Some(existing_pos) = buckets[bucket_idx]
            .iter()
            .position(|&idx| entries[idx] == *entry)
        {
            buckets[bucket_idx].remove(existing_pos);
            size -= 1;
        }
        buckets[bucket_idx].insert(0, entry_idx);
        size += 1;

        if size > (buckets.len() << 1) {
            let mut new_buckets = vec![Vec::new(); buckets.len() * 2];
            for bucket in &buckets {
                for &idx in bucket {
                    let new_idx =
                        (ocaml_hashtbl_hash_string(&entries[idx]) as usize) & (new_buckets.len() - 1);
                    new_buckets[new_idx].insert(0, idx);
                }
            }
            buckets = new_buckets;
        }
    }

    let mut ordered = Vec::with_capacity(size);
    for bucket in &buckets {
        for &idx in bucket {
            ordered.push(entries[idx].clone());
        }
    }
    ordered
}

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

fn find_loc_idx_by_bounds(arena: &ParseArena, start: PosIdx, end: PosIdx) -> Option<LocIdx> {
    let mut fallback = None;
    for (idx, loc) in arena.locations().iter().enumerate() {
        if loc.loc_start == start && loc.loc_end == end {
            let found = LocIdx(idx as u32);
            if loc.loc_ghost {
                return Some(found);
            }
            if fallback.is_none() {
                fallback = Some(found);
            }
        }
    }
    fallback
}

/// Convert a Located<StrIdx> to a Located<String> (for typedtree which uses String).
fn convert_located_stridx(loc: &Located<StrIdx>, arena: &ParseArena) -> Located<String> {
    Located {
        txt: arena.get_string(loc.txt).to_string(),
        loc: loc.loc,
    }
}

fn has_dict_pattern_attribute(arena: &ParseArena, attrs: &[crate::parser::ast::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == DICT_PATTERN_ATTRIBUTE)
}

fn is_dict_type_path(path: &Path) -> bool {
    // Must match the predef dict type exactly (Pident with persistent stamp),
    // not any user-defined type that happens to be named "dict".
    // OCaml uses `Path.same tpath Predef.path_dict` which compares stamps.
    match path {
        Path::Pident(id) => id.stamp() == 0 && id.name() == DICT_TYPE_NAME,
        _ => false,
    }
}

fn resolve_package_modtype_path<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    lid: &Longident,
) -> Path {
    crate::types::typemod::lookup_modtype_path_by_lid(
        lid,
        tctx.arena,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    )
    .unwrap_or_else(|| crate::types::typemod::path_from_longident(lid, |idx| tctx.arena.get_string(idx)))
}

/// Match OCaml polymorphic compare over `Longident.t`:
/// constructor order `Lident < Ldot < Lapply`, then recursive field compare.
fn compare_longident(arena: &ParseArena, left: &Longident, right: &Longident) -> Ordering {
    match (left, right) {
        (Longident::Lident(left_name), Longident::Lident(right_name)) => {
            arena.get_string(*left_name).cmp(arena.get_string(*right_name))
        }
        (Longident::Lident(_), _) => Ordering::Less,
        (_, Longident::Lident(_)) => Ordering::Greater,
        (Longident::Ldot(left_prefix, left_name), Longident::Ldot(right_prefix, right_name)) => {
            let prefix_cmp = compare_longident(arena, left_prefix, right_prefix);
            if prefix_cmp != Ordering::Equal {
                prefix_cmp
            } else {
                arena.get_string(*left_name).cmp(arena.get_string(*right_name))
            }
        }
        (Longident::Ldot(_, _), _) => Ordering::Less,
        (_, Longident::Ldot(_, _)) => Ordering::Greater,
        (Longident::Lapply(left_functor, left_arg), Longident::Lapply(right_functor, right_arg)) => {
            let functor_cmp = compare_longident(arena, left_functor, right_functor);
            if functor_cmp != Ordering::Equal {
                functor_cmp
            } else {
                compare_longident(arena, left_arg, right_arg)
            }
        }
    }
}

fn inline_record_type_params(
    ctx: &TypeContext<'_>,
    parent_type_params: &[TypeExprRef],
    labels: &[crate::types::LabelDeclaration],
) -> Vec<TypeExprRef> {
    parent_type_params
        .iter()
        .copied()
        .filter(|param| {
            labels
                .iter()
                .any(|label| crate::types::ctype::deep_occur(ctx, *param, label.ld_type))
        })
        .collect()
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
    module_variables: Vec<(crate::parse_arena::Located<String>, Location)>,
}

/// A pattern variable with its binding information.
#[derive(Debug, Clone)]
pub struct PatternVariable {
    /// The identifier.
    pub id: Ident,
    /// The type.
    pub ty: TypeExprRef,
    /// Original parser location index for this binding.
    pub loc_idx: LocIdx,
    /// The name with location.
    pub name: crate::parse_arena::Located<String>,
    /// The location.
    pub loc: Location,
    /// Whether this is an as-variable.
    pub is_as_variable: bool,
    /// Whether this variable is bound as an unpacked module.
    pub is_module: bool,
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
        let full_name = crate::parse_arena::Located {
            txt: name_str.to_string(),
            loc: name.loc,
        };
        self.pattern_variables.push(PatternVariable {
            id: id.clone(),
            ty,
            loc_idx: loc,
            name: full_name.clone(),
            loc: full_loc.clone(),
            is_as_variable,
            is_module,
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
    /// Bound type variables from the surrounding declaration context.
    /// This matches OCaml's typetexp `type_variables` table used by
    /// `globalize_used_variables` to link per-type-expression variables
    /// back to declaration-level parameters.
    pub type_variables: HashMap<String, TypeExprRef>,
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
    /// When inside Pexp_constraint, the GENERIC constraint type. Used by
    /// type_match_cases_batch_non_gadt to create fresh instances per case
    /// body, matching OCaml's behavior where ty_res is generic.
    pub generic_constraint_body_ty: Option<TypeExprRef>,
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
            type_variables: HashMap::new(),
            recursive_let_depth: 0,
            active_recursive_value_ids: Vec::new(),
            persistent_env: None,
            force_fresh_local_float: false,
            generic_constraint_body_ty: None,
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

    /// Match OCaml Typetexp.reset_type_variables:
    /// clear declaration-level type variable bindings and reset global level.
    pub fn reset_type_variables(&mut self) {
        self.type_ctx.reset_global_level();
        self.type_variables.clear();
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
                format!(
                    "{}.{}",
                    self.longident_to_string(prefix),
                    self.arena.get_string(*idx)
                )
            }
            Longident::Lapply(a, b) => {
                format!(
                    "{}({})",
                    self.longident_to_string(a),
                    self.longident_to_string(b)
                )
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
    let ty = match cst {
        // Match OCaml typecore.ml type_constant: instance_def Predef.type_*
        // so each constant occurrence gets its own instantiated node.
        Constant::Int(_) => crate::types::instance(ctx, env.type_int(ctx)),
        Constant::Char(_) => crate::types::instance(ctx, env.type_char(ctx)),
        Constant::String(_, _) => crate::types::instance(ctx, env.type_string(ctx)),
        Constant::Float(_) => crate::types::instance(ctx, env.type_float(ctx)),
        Constant::BigInt(_, _) => crate::types::instance(ctx, env.type_bigint(ctx)),
    };
    if std::env::var_os("RUST_DEBUG_CONST_LEVELS").is_some() {
        let repr = ctx.repr(ty);
        let kind = match cst {
            Constant::Int(_) => "int",
            Constant::Char(_) => "char",
            Constant::String(_, _) => "string",
            Constant::Float(_) => "float",
            Constant::BigInt(_, _) => "bigint",
        };
        eprintln!(
            "[const-level] kind={} ty={} level={} desc={:?}",
            kind,
            repr.0,
            ctx.get_level(repr),
            &*ctx.get_desc(repr)
        );
    }
    ty
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
    if negative {
        Some(-abs_val)
    } else {
        Some(abs_val)
    }
}

/// Parse a bigint literal string following OCaml Bigint_utils.parse_bigint:
/// - keep sign separately as a bool (true for positive, false for negative)
/// - remove `_` separators
/// - remove leading zeros only when followed by decimal digits
/// - preserve non-decimal heads like `00x1` (after `_` removal)
fn parse_bigint_literal(s: &str) -> (bool, String) {
    fn remove_leading_sign(s: &str) -> (bool, &str) {
        if s.is_empty() {
            (false, s)
        } else if let Some(rest) = s.strip_prefix('-') {
            (false, rest)
        } else if let Some(rest) = s.strip_prefix('+') {
            (true, rest)
        } else {
            (true, s)
        }
    }

    fn remove_leading_zeros(s: &str) -> String {
        // OCaml removes separators before any zero/sign logic.
        let without_underscores: String = s.chars().filter(|c| *c != '_').collect();
        let starts_with_minus = without_underscores.starts_with('-');
        let without_sign = without_underscores
            .strip_prefix('-')
            .or_else(|| without_underscores.strip_prefix('+'))
            .unwrap_or(&without_underscores);

        let processed = if without_sign.is_empty() {
            String::new()
        } else {
            let bytes = without_sign.as_bytes();
            let mut idx = 0usize;
            while idx < bytes.len() && bytes[idx] == b'0' {
                idx += 1;
            }
            if idx >= bytes.len() {
                "0".to_string()
            } else if bytes[idx].is_ascii_digit() {
                without_sign[idx..].to_string()
            } else {
                without_sign.to_string()
            }
        };

        if starts_with_minus {
            format!("-{processed}")
        } else {
            processed
        }
    }

    let (sign, digits) = remove_leading_sign(s);
    (sign, remove_leading_zeros(digits))
}

/// Wrap an i64 value to simulate OCaml's native int (63-bit on 64-bit systems).
/// OCaml's int wraps around at 2^62, so values outside [-2^62, 2^62-1] are wrapped.
/// This matches OCaml's int_of_string behavior for large integer literals.
fn wrap_to_ocaml_int(n: i64) -> i64 {
    // OCaml's native int on 64-bit is 63 bits: range is [-2^62, 2^62-1]
    // The wrapping is equivalent to: ((n + 2^62) mod 2^63) - 2^62
    let half = 1i64 << 62; // 2^62 = 4611686018427387904
    let modulus = 1i128 << 63; // 2^63 as i128 to avoid overflow
    let shifted = (n as i128) + (half as i128);
    let wrapped = shifted.rem_euclid(modulus);
    (wrapped - half as i128) as i64
}

/// Convert a parsed constant to a typed constant.
pub fn convert_constant(cst: &crate::parser::ast::Constant) -> TypeCoreResult<Constant> {
    use crate::parser::ast::Constant as ParsedConstant;

    match cst {
        ParsedConstant::Integer(s, None) => {
            // Parse integer literal, handling underscores and 0x/0o/0b prefixes.
            // OCaml's native int is 63-bit on 64-bit systems. We parse as i64
            // and simulate 63-bit wrapping to match OCaml's int_of_string behavior.
            match parse_int_literal(s) {
                Some(n) => Ok(Constant::Int(wrap_to_ocaml_int(n))),
                None => Err(TypeCoreError::LiteralOverflow("int".to_string())),
            }
        }
        ParsedConstant::Integer(s, Some('n')) => {
            let (sign, digits) = parse_bigint_literal(s);
            Ok(Constant::BigInt(sign, digits))
        }
        ParsedConstant::Integer(i, Some(c)) => {
            Err(TypeCoreError::UnknownLiteral(i.to_string(), *c))
        }
        ParsedConstant::Char(c) => Ok(Constant::Char(*c)),
        ParsedConstant::String(s, d) => {
            // Transform "js" delimiter to "*j" to match OCaml's escaped form
            let delim = d.as_ref().map(|x| {
                if x.as_ref() == "js" {
                    "*j".to_string()
                } else {
                    x.to_string()
                }
            });
            Ok(Constant::String(s.to_string(), delim))
        }
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

fn collect_named_type_vars_from_core_type(
    ctyp: &crate::types::typedtree::TypedCoreType,
    out: &mut HashMap<String, TypeExprRef>,
) {
    use crate::types::typedtree::{ObjectFieldDesc, RowFieldDesc, TypedCoreTypeDesc};

    match &ctyp.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_var(Some(name)) => {
            out.entry(name.clone()).or_insert(ctyp.ctyp_type);
        }
        TypedCoreTypeDesc::Ttyp_var(None) => {}
        TypedCoreTypeDesc::Ttyp_arrow(arg, ret, _) => {
            collect_named_type_vars_from_core_type(&arg.typ, out);
            collect_named_type_vars_from_core_type(ret, out);
        }
        TypedCoreTypeDesc::Ttyp_tuple(items) | TypedCoreTypeDesc::Ttyp_constr(_, _, items) => {
            for item in items {
                collect_named_type_vars_from_core_type(item, out);
            }
        }
        TypedCoreTypeDesc::Ttyp_object(fields, _) => {
            for field in fields {
                match &field.of_desc {
                    ObjectFieldDesc::OTtag(_, ty) | ObjectFieldDesc::OTinherit(ty) => {
                        collect_named_type_vars_from_core_type(ty, out);
                    }
                }
            }
        }
        TypedCoreTypeDesc::Ttyp_poly(_, body) | TypedCoreTypeDesc::Ttyp_alias(body, _) => {
            collect_named_type_vars_from_core_type(body, out);
        }
        TypedCoreTypeDesc::Ttyp_variant(rows, _, _) => {
            for row in rows {
                match &row.rf_desc {
                    RowFieldDesc::Rtag(_, _, tys) => {
                        for ty in tys {
                            collect_named_type_vars_from_core_type(ty, out);
                        }
                    }
                    RowFieldDesc::Rinherit(ty) => {
                        collect_named_type_vars_from_core_type(ty, out);
                    }
                }
            }
        }
        TypedCoreTypeDesc::Ttyp_package(pack) => {
            for (_, ty) in &pack.pack_fields {
                collect_named_type_vars_from_core_type(ty, out);
            }
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
    transl_type_delayed(tctx, env, styp, false)
}

/// Translate a type with delayed globalization (matching OCaml's
/// transl_simple_type_delayed). When `globalize` is true, we route used
/// variables through fresh global variables before linking them in
/// `type_variables`; this matches typetexp's delayed force path.
pub fn transl_type_delayed(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    styp: &crate::parser::ast::CoreType,
    globalize: bool,
) -> TypeCoreResult<(crate::types::typedtree::TypedCoreType, TypeExprRef)> {
    // Reset used_variables for each top-level type translation (matches OCaml's transl_simple_type)
    tctx.used_variables.clear();
    let translated = transl_type_inner(tctx, env, styp)?;

    // Match OCaml typetexp `globalize_used_variables`: link variables seen in
    // this type expression back to declaration-level variables and register
    // new names for later constraints in the same typing scope.
    if !tctx.used_variables.is_empty() {
        let used_vars: Vec<(String, TypeExprRef)> = tctx
            .used_variables
            .iter()
            .map(|(name, ty)| (name.clone(), *ty))
            .collect();
        for (name, used_ty) in used_vars {
            let ctx = tctx.type_ctx;
            if globalize {
                // OCaml typetexp.ml globalize_used_variables:
                //   v = new_global_var (); unify v used_ty;
                // and then unify v with either an existing table binding or a
                // fresh table entry (v2 = new_global_var ()).
                let lowered_ty = {
                    let v = ctx.new_global_var(None);
                    let _ = crate::types::unify(ctx, &mut tctx.unify_state, v, used_ty);
                    v
                };
                if let Some(bound_ty) = tctx.type_variables.get(&name).copied() {
                    if std::env::var_os("RUST_DEBUG_TYPE_VAR_GLOBALIZE").is_some()
                        && (name == "key" || name == "id" || name == "self" || name == "a")
                    {
                        let used_repr = ctx.repr(lowered_ty);
                        let bound_repr = ctx.repr(bound_ty);
                        eprintln!(
                            "[type-var-globalize] name={} used={} bound={} globalize={}",
                            name, used_repr.0, bound_repr.0, globalize
                        );
                    }
                    let _ = crate::types::unify(ctx, &mut tctx.unify_state, lowered_ty, bound_ty);
                } else {
                    let bound_ty = ctx.new_global_var(None);
                    if std::env::var_os("RUST_DEBUG_TYPE_VAR_GLOBALIZE").is_some()
                        && (name == "key" || name == "id" || name == "self" || name == "a")
                    {
                        let used_repr = ctx.repr(lowered_ty);
                        let bound_repr = ctx.repr(bound_ty);
                        eprintln!(
                            "[type-var-globalize] name={} used={} bound={} globalize={}",
                            name, used_repr.0, bound_repr.0, globalize
                        );
                    }
                    let _ = crate::types::unify(ctx, &mut tctx.unify_state, lowered_ty, bound_ty);
                    tctx.type_variables.insert(name, bound_ty);
                }
            } else if let Some(bound_ty) = tctx.type_variables.get(&name).copied() {
                if std::env::var_os("RUST_DEBUG_TYPE_VAR_GLOBALIZE").is_some()
                    && (name == "key" || name == "id" || name == "self" || name == "a")
                {
                    let used_repr = ctx.repr(used_ty);
                    let bound_repr = ctx.repr(bound_ty);
                    eprintln!(
                        "[type-var-globalize] name={} used={} bound={} globalize={}",
                        name, used_repr.0, bound_repr.0, globalize
                    );
                }
                let _ = crate::types::unify(ctx, &mut tctx.unify_state, used_ty, bound_ty);
            } else {
                if std::env::var_os("RUST_DEBUG_TYPE_VAR_GLOBALIZE").is_some()
                    && (name == "key" || name == "id" || name == "self" || name == "a")
                {
                    let used_repr = ctx.repr(used_ty);
                    eprintln!(
                        "[type-var-globalize] name={} used={} bound=<none> globalize={}",
                        name, used_repr.0, globalize
                    );
                }
                tctx.type_variables.insert(name, used_ty);
            }
        }
    }

    tctx.used_variables.clear();
    Ok(translated)
}

fn path_from_longident_persistent(lid: &Longident, arena: &ParseArena) -> Path {
    match lid {
        Longident::Lident(name_idx) => {
            Path::pident(Ident::create_persistent(arena.get_string(*name_idx)))
        }
        Longident::Ldot(prefix, name_idx) => {
            let prefix_path = path_from_longident_persistent(prefix, arena);
            Path::pdot(prefix_path, arena.get_string(*name_idx))
        }
        Longident::Lapply(functor, arg) => {
            let funct = path_from_longident_persistent(functor, arena);
            let arg = path_from_longident_persistent(arg, arena);
            Path::papply(funct, arg)
        }
    }
}

fn resolve_type_constructor_path(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    lid: &Longident,
) -> (Path, Option<crate::types::decl::TypeDeclaration>) {
    use crate::types::decl::SignatureItem;

    match lid {
        Longident::Lident(name_idx) => {
            let name = tctx.arena.get_string(*name_idx);
            match env.find_type_with_origin(name) {
                Ok((id, decl, is_local)) => {
                    // Match OCaml's IdTbl.find_name behavior:
                    // - Local/included bindings (tbl.current): return Pident(id)
                    // - Opened bindings (tbl.opened): return the decl's type_path
                    //   (which is the qualified Pdot path from the opened module)
                    let path = if is_local {
                        Path::pident(id.clone())
                    } else {
                        decl.type_path
                            .clone()
                            .unwrap_or_else(|| Path::pident(id.clone()))
                    };
                    (path, Some(decl.clone()))
                }
                Err(_) => {
                    (Path::pident(Ident::create_persistent(name)), None)
                }
            }
        }
        Longident::Ldot(prefix, name_idx) => {
            let type_name = tctx.arena.get_string(*name_idx);

            // Match OCaml typetexp.ml find_component:
            // `Longident.Ldot (Longident.Lident "*predef*", s)` is looked up as
            // plain `Lident s` in the initial safe environment.
            if let Longident::Lident(prefix_idx) = prefix.as_ref() {
                if tctx.arena.get_string(*prefix_idx) == "*predef*" {
                    let predef_path = Path::pident(Ident::create_persistent(type_name));
                    let predef_decl = env.lookup_type(&predef_path).ok().cloned();
                    return (predef_path, predef_decl);
                }
            }

            if let Some((mod_path, sig)) = env.resolve_module_lid(
                prefix,
                tctx.arena,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                for item in &sig {
                    if let SignatureItem::SigType(id, decl, _) = item {
                        if id.name() == type_name {
                            if std::env::var_os("RUST_DEBUG_ORD_T_DECL").is_some()
                                && type_name == "t"
                                && matches!(prefix.as_ref(), Longident::Lident(prefix_idx) if tctx.arena.get_string(*prefix_idx) == "Ord")
                            {
                                let manifest_desc = decl.type_manifest.map(|m| {
                                    let r = tctx.type_ctx.repr(m);
                                    let d = tctx.type_ctx.get_desc(r);
                                    match &*d {
                                        crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
                                            format!("Tconstr({})@{}", path.name(), r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tvar(_) => {
                                            format!("Tvar@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tunivar(_) => {
                                            format!("Tunivar@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tarrow { .. } => {
                                            format!("Tarrow@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Ttuple(_) => {
                                            format!("Ttuple@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tlink(t) => {
                                            format!("Tlink({})@{}", tctx.type_ctx.repr(*t).0, r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tsubst(t) => {
                                            format!("Tsubst({})@{}", tctx.type_ctx.repr(*t).0, r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tobject { .. } => {
                                            format!("Tobject@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tfield { .. } => {
                                            format!("Tfield@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tnil => {
                                            format!("Tnil@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tvariant(_) => {
                                            format!("Tvariant@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tpoly { .. } => {
                                            format!("Tpoly@{}", r.0)
                                        }
                                        crate::types::type_expr::TypeDesc::Tpackage { .. } => {
                                            format!("Tpackage@{}", r.0)
                                        }
                                    }
                                });
                                eprintln!(
                                    "[ord-t-decl] mod_path={} type_path={:?} manifest={:?} kind={:?}",
                                    mod_path.name(),
                                    decl.type_path.as_ref().map(|p| p.name()),
                                    manifest_desc,
                                    decl.type_kind
                                );
                            }
                            return (
                                Path::pdot(mod_path.clone(), type_name.to_string()),
                                Some(decl.clone()),
                            );
                        }
                    }
                }
                return (Path::pdot(mod_path, type_name.to_string()), None);
            }
            (path_from_longident_persistent(lid, tctx.arena), None)
        }
        Longident::Lapply(_, _) => (path_from_longident_persistent(lid, tctx.arena), None),
    }
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
            // Ptyp_var is ONLY for type variables (e.g., 'a in ReScript).
            // Locally abstract types (type a) are handled by Ptyp_constr,
            // not Ptyp_var. OCaml's typetexp only looks up type variables
            // (used_variables/TyVarEnv), not the type environment, for Ptyp_var.
            let name_str = name.to_string();
            let ty = if let Some(&existing) = tctx.used_variables.get(&name_str) {
                crate::types::instance(ctx, existing)
            } else {
                let v = ctx.new_var(Some(name_str.clone()));
                tctx.used_variables.insert(name_str.clone(), v);
                v
            };
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_var(Some(name_str)),
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
            let arrow_ty = ctx.new_arrow(ctx_lbl.clone(), arg_ty, ret_ty, arity_opt);

            // Create ArrowArg structure matching OCaml's
            let arrow_arg = ArrowArg {
                attrs: arg.attrs.clone(),
                lbl: ctx_lbl,
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
            let longident = tctx.arena.get_longident(lid.txt);
            let (path, type_decl) = resolve_type_constructor_path(tctx, env, longident);

            let mut parsed_args: Vec<_> = args
                .iter()
                .map(|arg| tctx.arena.get_core_type(*arg).clone())
                .collect();
            if let Some(decl) = &type_decl {
                // Match OCaml Typetexp: `t<_>` for arity>1 expands `_` to all params.
                if parsed_args.len() == 1
                    && matches!(&*parsed_args[0].ptyp_desc, CTD::Ptyp_any)
                    && decl.type_arity > 1
                {
                    parsed_args = vec![parsed_args[0].clone(); decl.type_arity as usize];
                }
            }

            let mut typed_args = Vec::new();
            let mut arg_refs = Vec::new();

            for arg in &parsed_args {
                let (ctyp, ty) = transl_type_inner(tctx, env, arg)?;
                typed_args.push(ctyp);
                arg_refs.push(ty);
            }

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
            let name_str = name.to_string();
            let inner = tctx.arena.get_core_type(*inner_idx);

            // Match OCaml Typetexp.transl_type_aux Ptyp_alias:
            // - reuse an existing alias binding via `instance` when present
            // - otherwise register a fresh alias in used_variables *before*
            //   translating the inner type, then instantiate and name its proxy.
            let existing_alias = tctx.used_variables.get(&name_str).copied();

            let (inner_ctyp, alias_ty) = if let Some(existing_alias) = existing_alias {
                let alias_ty = crate::types::instance(ctx, existing_alias);
                let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, inner)?;
                crate::types::unify(ctx, &mut tctx.unify_state, alias_ty, inner_ty)
                    .map_err(|_| TypeCoreError::PatternTypeClash(vec![(alias_ty, inner_ty)]))?;
                (inner_ctyp, inner_ty)
            } else {
                let alias_ty = ctx.new_var(None);
                tctx.used_variables.insert(name_str.clone(), alias_ty);

                let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, inner)?;

                // Keep compile coverage for recursive self-alias object types
                // (for example `type x = {...} as 'self`) until unify_var-style
                // recursive alias handling is fully ported.
                if crate::types::occurs(ctx, alias_ty, inner_ty) {
                    tctx.used_variables.remove(&name_str);
                    let fallback_alias_ty = ctx.new_var(Some(name_str.clone()));
                    crate::types::unify(ctx, &mut tctx.unify_state, fallback_alias_ty, inner_ty)
                        .map_err(|_| {
                            TypeCoreError::PatternTypeClash(vec![(fallback_alias_ty, inner_ty)])
                        })?;
                    (inner_ctyp, inner_ty)
                } else {
                    crate::types::unify(ctx, &mut tctx.unify_state, alias_ty, inner_ty)
                        .map_err(|_| TypeCoreError::PatternTypeClash(vec![(alias_ty, inner_ty)]))?;

                    let instantiated = crate::types::instance(ctx, alias_ty);
                    let proxy = crate::types::btype::proxy(ctx, instantiated);
                    let rename_desc = {
                        let proxy_desc = ctx.get_desc(proxy);
                        match &*proxy_desc {
                            TypeDesc::Tvar(None) => Some(TypeDesc::Tvar(Some(name_str.clone()))),
                            TypeDesc::Tunivar(None) => {
                                Some(TypeDesc::Tunivar(Some(name_str.clone())))
                            }
                            _ => None,
                        }
                    };
                    if let Some(desc) = rename_desc {
                        ctx.set_desc(proxy, desc);
                    }
                    (inner_ctyp, instantiated)
                }
            };

            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_alias(Box::new(inner_ctyp), name_str),
                ctyp_type: alias_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, alias_ty))
        }

        CTD::Ptyp_poly(inner) => {
            let (ref vars, ref body_idx) = **inner;
            // Polymorphic type: 'a 'b. T
            // OCaml typetexp.ml Ptyp_poly: creates univars, translates body,
            // generalizes, then converts Tvar→Tunivar for bound variables.
            let var_names: Vec<String> = vars
                .iter()
                .map(|v| tctx.arena.get_string(v.txt).to_string())
                .collect();

            ctx.begin_def();

            // Create type variables for each bound variable and register them
            // in used_variables so body translation connects to these nodes.
            // OCaml: new_univars = List.map (fun name -> (name, newvar ~name ())) vars
            let new_univars: Vec<(String, TypeExprRef)> = var_names
                .iter()
                .map(|name| {
                    let v = ctx.new_var(Some(name.clone()));
                    (name.clone(), v)
                })
                .collect();

            // Save old univar state and prepend new ones
            // OCaml: univars := new_univars @ !univars
            let old_used: Vec<(String, TypeExprRef)> = new_univars
                .iter()
                .filter_map(|(name, _)| {
                    tctx.used_variables.get(name).map(|v| (name.clone(), *v))
                })
                .collect();
            for (name, var) in &new_univars {
                tctx.used_variables.insert(name.clone(), *var);
            }

            let body = tctx.arena.get_core_type(*body_idx);
            let (body_ctyp, body_ty) = transl_type_inner(tctx, env, body)?;

            // Restore old used_variables for the poly variable names
            for (name, old_var) in &old_used {
                tctx.used_variables.insert(name.clone(), *old_var);
            }
            for (name, _) in &new_univars {
                if !old_used.iter().any(|(n, _)| n == name) {
                    tctx.used_variables.remove(name);
                }
            }

            ctx.end_def();
            crate::types::ctype::generalize(ctx, body_ty);

            // OCaml: for each poly variable that deeply occurs in the body and is
            // at generic level, change Tvar→Tunivar (universalize)
            let mut ty_list = Vec::new();
            for (_name, ty1) in new_univars.iter().rev() {
                let v = crate::types::btype::proxy(ctx, *ty1);
                if crate::types::ctype::deep_occur(ctx, v, body_ty) {
                    // Extract the name and check level before calling set_desc
                    // to avoid RefCell borrow conflict
                    let uni_name = {
                        let desc = ctx.get_desc(v);
                        match &*desc {
                            TypeDesc::Tvar(name) if ctx.get_level(v) == crate::types::type_expr::GENERIC_LEVEL => {
                                Some(name.clone())
                            }
                            _ => None,
                        }
                    };
                    if let Some(name) = uni_name {
                        ctx.set_desc(v, TypeDesc::Tunivar(name));
                        ty_list.push(v);
                    }
                }
            }
            ty_list.reverse();

            let poly_ty = ctx.new_poly(body_ty, ty_list);

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
            // Build proper Tobject(Tfield(..., Tfield(..., Tnil))) type chain
            let mut typed_fields = Vec::new();
            // Match OCaml Typetexp.transl_fields: collect unique fields in a
            // hashtable, then iterate in Hashtbl.fold order.
            let mut field_entries: HashMap<String, TypeExprRef> = HashMap::new();
            let mut field_insertions: Vec<String> = Vec::new();

            fn add_object_field(
                field_entries: &mut HashMap<String, TypeExprRef>,
                field_insertions: &mut Vec<String>,
                field_name: String,
                field_type: TypeExprRef,
            ) {
                if !field_entries.contains_key(&field_name) {
                    field_insertions.push(field_name.clone());
                    field_entries.insert(field_name, field_type);
                }
            }

            for field in fields.iter() {
                match field {
                    crate::parser::ast::ObjectField::Otag(label, attrs, field_type) => {
                        let field_ct = tctx.arena.get_core_type(*field_type);
                        // OCaml uses transl_poly_type which applies force_poly before
                        // translation: if already Ptyp_poly, translate as-is; otherwise
                        // wrap in Ptyp_poly([], t) first. We check post-translation.
                        let (inner_ctyp, inner_ty) = transl_type_inner(tctx, env, field_ct)?;

                        // Apply force_poly: if already Ttyp_poly, don't double-wrap
                        let (poly_ctyp, poly_ty) = match &inner_ctyp.ctyp_desc {
                            TypedCoreTypeDesc::Ttyp_poly(_, _) => (inner_ctyp, inner_ty),
                            _ => {
                                let poly_ty = ctx.new_poly(inner_ty, vec![]);
                                let poly_ctyp = TypedCoreType {
                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vec![], Box::new(inner_ctyp)),
                                    ctyp_type: poly_ty,
                                    ctyp_env: EnvRef(0),
                                    ctyp_loc: field_ct.ptyp_loc,
                                    ctyp_attributes: Attributes::new(),
                                };
                                (poly_ctyp, poly_ty)
                            }
                        };

                        let field_name = tctx.arena.get_string(label.txt).to_string();
                        add_object_field(
                            &mut field_entries,
                            &mut field_insertions,
                            field_name.clone(),
                            poly_ty,
                        );

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
                        let inherit_ct = tctx.arena.get_core_type(*inherit_type);
                        let (inherit_ctyp, inherit_ty) =
                            transl_type_inner(tctx, env, inherit_ct)?;

                        // Extract fields from the inherited type (OCaml's typetexp.ml lines 597-617).
                        // expand_head resolves type aliases/constructors to get the underlying object type.
                        let expanded = crate::types::ctype::expand_head(ctx, env, inherit_ty);
                        let expanded_desc = ctx.get_desc(expanded);
                        if let TypeDesc::Tobject {
                            fields: obj_fields, ..
                        } = &*expanded_desc
                        {
                            // Walk the Tfield chain and add each field to field_entries
                            let mut current_field = *obj_fields;
                            loop {
                                let fd = ctx.get_desc(ctx.repr(current_field));
                                match &*fd {
                                    TypeDesc::Tfield {
                                        name, typ, rest, ..
                                    } => {
                                        add_object_field(
                                            &mut field_entries,
                                            &mut field_insertions,
                                            name.clone(),
                                            *typ,
                                        );
                                        current_field = *rest;
                                    }
                                    TypeDesc::Tnil => break,
                                    _ => break,
                                }
                            }
                        }
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

            // Build the Tfield chain terminated by Tnil (closed) or Tvar (open)
            let ty_init = match closed {
                crate::parser::ast::ClosedFlag::Closed => ctx.new_type(TypeDesc::Tnil),
                crate::parser::ast::ClosedFlag::Open => ctx.new_var(None),
            };
            let mut ordered_field_names = ocaml_hashtbl_fold_order(&field_insertions);
            // OCaml transl_fields uses:
            //   fields = Hashtbl.fold (fun s ty l -> (s, ty) :: l) ...
            // followed by List.fold_left building Tfield(..., acc).
            // `ocaml_hashtbl_fold_order` returns traversal order, so reverse it to
            // match the intermediate Hashtbl.fold list before the left fold.
            ordered_field_names.reverse();
            let field_entries = ordered_field_names
                .into_iter()
                .filter_map(|name| field_entries.remove(&name).map(|ty| (name, ty)))
                .collect::<Vec<_>>();
            // Fold fields into Tfield chain
            let fields_ty = field_entries
                .iter()
                .fold(ty_init, |rest, (name, field_ty)| {
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

        CTD::Ptyp_variant(inner) => {
            let (ref rows, ref closed, ref labels) = **inner;
            // Polymorphic variant type: [> `A | `B of int ]
            let mut typed_rows = Vec::new();
            let mut row_name: Option<(Path, Vec<TypeExprRef>)> = None;
            let mut row_field_map: HashMap<String, crate::types::type_expr::RowField> =
                HashMap::new();
            let mut row_field_insertions: Vec<String> = Vec::new();

            fn add_row_field(
                row_field_map: &mut HashMap<String, crate::types::type_expr::RowField>,
                row_field_insertions: &mut Vec<String>,
                label: String,
                field: crate::types::type_expr::RowField,
            ) {
                if !row_field_map.contains_key(&label) {
                    row_field_insertions.push(label.clone());
                    row_field_map.insert(label, field);
                }
            }

            for row in rows {
                match row {
                    crate::parser::ast::RowField::Rtag(label, attrs, constant, args) => {
                        let mut typed_args = Vec::new();
                        let mut arg_types = Vec::new();
                        for arg in args {
                            let arg_ct = tctx.arena.get_core_type(*arg);
                            let (arg_ctyp, arg_ty) = transl_type_inner(tctx, env, arg_ct)?;
                            typed_args.push(arg_ctyp);
                            arg_types.push(arg_ty);
                        }

                        row_name = None;

                        let is_reither = labels.as_ref().is_some_and(|present| {
                            !present.iter().any(|present_lbl| present_lbl == &label.txt)
                        });
                        let row_field = if is_reither {
                            crate::types::type_expr::RowField::Reither {
                                constant: *constant,
                                types: arg_types,
                                matched: false,
                                link: ctx.alloc_row_field(None),
                            }
                        } else {
                            match typed_args.first() {
                                None => crate::types::type_expr::RowField::Rpresent(None),
                                Some(first) => crate::types::type_expr::RowField::Rpresent(Some(
                                    first.ctyp_type,
                                )),
                            }
                        };
                        add_row_field(
                            &mut row_field_map,
                            &mut row_field_insertions,
                            label.txt.to_string(),
                            row_field,
                        );

                        let typed_label = Located {
                            txt: label.txt.to_string(),
                            loc: label.loc.clone(),
                        };

                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rtag(
                                typed_label,
                                *constant,
                                typed_args,
                            ),
                            rf_loc: label.loc.clone(),
                            rf_attributes: attrs.clone(),
                        });
                    }
                    crate::parser::ast::RowField::Rinherit(inherit_type) => {
                        let inherit_ct = tctx.arena.get_core_type(*inherit_type);
                        let (inherit_ctyp, inherit_ty) = transl_type_inner(tctx, env, inherit_ct)?;

                        let inherit_ty_repr = ctx.repr(inherit_ty);
                        let inherit_name = match &*ctx.get_desc(inherit_ty_repr) {
                            TypeDesc::Tconstr { path, args, .. } => {
                                Some((path.clone(), args.clone()))
                            }
                            _ => None,
                        };
                        if row_field_map.is_empty() {
                            row_name = inherit_name;
                        } else {
                            row_name = None;
                        }

                        let expanded = crate::types::ctype::expand_head(ctx, env, inherit_ty);
                        let inherited_fields = {
                            let expanded_desc = ctx.get_desc(expanded);
                            match &*expanded_desc {
                                TypeDesc::Tvariant(row_desc)
                                    if crate::types::btype::static_row(ctx, row_desc) =>
                                {
                                    Some(crate::types::btype::row_repr(ctx, row_desc).row_fields)
                                }
                                _ => None,
                            }
                        };
                        if let Some(fields) = inherited_fields {
                            for (label_name, inherited_field) in fields {
                                let is_reither = labels.as_ref().is_some_and(|present| {
                                    !present.iter().any(|lbl| lbl == &label_name)
                                });
                                let resolved_field = if is_reither {
                                    match inherited_field {
                                        crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
                                            crate::types::type_expr::RowField::Reither {
                                                constant: false,
                                                types: vec![ty],
                                                matched: false,
                                                link: ctx.alloc_row_field(None),
                                            }
                                        }
                                        crate::types::type_expr::RowField::Rpresent(None) => {
                                            crate::types::type_expr::RowField::Reither {
                                                constant: true,
                                                types: vec![],
                                                matched: false,
                                                link: ctx.alloc_row_field(None),
                                            }
                                        }
                                        _ => inherited_field,
                                    }
                                } else {
                                    inherited_field
                                };
                                add_row_field(
                                    &mut row_field_map,
                                    &mut row_field_insertions,
                                    label_name,
                                    resolved_field,
                                );
                            }
                        }
                        typed_rows.push(crate::types::typedtree::RowFieldType {
                            rf_desc: crate::types::typedtree::RowFieldDesc::Rinherit(inherit_ctyp),
                            rf_loc: inherit_ct.ptyp_loc.clone(),
                            rf_attributes: Attributes::new().into(),
                        });
                    }
                }
            }

            // OCaml's Ptyp_variant uses Hashtbl.fold to collect fields,
            // which produces a hash-determined order. Match this always
            // (OCaml does not condition on attributes).
            let ordered_labels = ocaml_hashtbl_fold_order(&row_field_insertions);
            let row_fields = ordered_labels
                .into_iter()
                .filter_map(|label| row_field_map.remove(&label).map(|field| (label, field)))
                .collect::<Vec<_>>();
            let row_closed = *closed == crate::parser::ast::ClosedFlag::Closed;
            // Keep an explicit row variable for now to avoid over-constraining
            // polymorphic variant aliases in downstream application typing.
            let row_more = ctx.new_var(None);
            let variant_ty = ctx.new_variant(crate::types::type_expr::RowDesc {
                row_fields,
                row_more,
                row_closed,
                row_fixed: false,
                row_name,
            });

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

        CTD::Ptyp_package(inner) => {
            let (mod_lid, constraints) = &**inner;
            // Package type: (module S with type t = T)
            let longident = tctx.resolve_lid(mod_lid.txt).clone();
            let pack_path = resolve_package_modtype_path(tctx, env, &longident);

            // Match OCaml Typetexp.create_package_mty:
            // - sort constraints by longident
            // - reject duplicate constrained type names
            let mut sorted_constraints: Vec<_> = constraints
                .iter()
                .map(|(field_lid, field_ty)| {
                    (tctx.resolve_lid(field_lid.txt).clone(), field_lid, field_ty)
                })
                .collect();
            sorted_constraints.sort_by(|(left, _, _), (right, _, _)| {
                compare_longident(tctx.arena, left, right)
            });

            for pair in sorted_constraints.windows(2) {
                if compare_longident(tctx.arena, &pair[0].0, &pair[1].0) == Ordering::Equal {
                    return Err(TypeCoreError::Other(format!(
                        "multiple constraints on type {}",
                        tctx.longident_to_string(&pair[0].0)
                    )));
                }
            }

            let mut typed_fields = Vec::with_capacity(sorted_constraints.len());
            let mut lids = Vec::with_capacity(sorted_constraints.len());
            let mut args = Vec::with_capacity(sorted_constraints.len());
            for (_, field_lid, field_ty) in sorted_constraints {
                let (typed_field_ty, field_type_ref) =
                    transl_type_inner(tctx, env, tctx.arena.get_core_type(*field_ty))?;
                typed_fields.push((field_lid.clone(), typed_field_ty));
                lids.push(tctx.resolve_lid(field_lid.txt).clone());
                args.push(field_type_ref);
            }

            let package_ty = ctx.new_type(TypeDesc::Tpackage {
                path: pack_path.clone(),
                lids,
                args,
            });
            let ctyp = TypedCoreType {
                ctyp_desc: TypedCoreTypeDesc::Ttyp_package(crate::types::typedtree::PackageType {
                    pack_path,
                    pack_txt: mod_lid.clone(),
                    pack_fields: typed_fields,
                }),
                ctyp_type: package_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, package_ty))
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

fn has_res_pat_variant_spread_attribute(
    arena: &ParseArena,
    attrs: &[crate::parser::ast::Attribute],
) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == PAT_VARIANT_SPREAD_ATTRIBUTE)
}

fn find_existing_lident_idx(arena: &ParseArena, name: &str) -> Option<LidentIdx> {
    for idx in (0..arena.longident_count()).rev() {
        let lid_idx = LidentIdx(idx as u32);
        if let Longident::Lident(str_idx) = arena.get_longident(lid_idx) {
            if arena.get_string(*str_idx) == name {
                return Some(lid_idx);
            }
        }
    }
    None
}

fn find_existing_longident_idx(arena: &ParseArena, target: &Longident) -> Option<LidentIdx> {
    for idx in (0..arena.longident_count()).rev() {
        let lid_idx = LidentIdx(idx as u32);
        if arena.get_longident(lid_idx) == target {
            return Some(lid_idx);
        }
    }
    None
}

/// Build an or-pattern from a poly variant type definition.
/// Matches OCaml typecore.ml:537-609 `build_or_pat`.
///
/// Given a type like `type myvariant = [#Tag1(int) | #Tag2(bool)]`,
/// this creates a `Tpat_or(Tpat_variant("Tag1", _), Tpat_variant("Tag2", _))` pattern
/// with Reither fields in the row type.
fn build_or_pat(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    lid: &Located<LidentIdx>,
) -> TypeCoreResult<(Path, Pattern, TypeExprRef)> {
    use crate::types::type_expr::{RowDesc, RowField, RowFieldRef};
    use crate::types::typedtree::RowDescRef;
    let ctx = tctx.type_ctx;
    let lid_txt = tctx.resolve_lid(lid.txt).clone();

    // Step 1: Find the type declaration and get the path
    let spread_ct = crate::parser::ast::CoreType {
        ptyp_desc: Box::new(crate::parser::ast::CoreTypeDesc::Ptyp_constr(Box::new((
            *lid,
            vec![],
        )))),
        ptyp_loc: lid.loc,
        ptyp_attributes: Attributes::new(),
    };
    let (_, spread_ty_ref) = transl_type(tctx, env, &spread_ct)?;
    let spread_ty = ctx.repr(spread_ty_ref);
    let spread_ty_desc = ctx.get_desc(spread_ty);
    let (path, args) = match &*spread_ty_desc {
        TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
        _ => return Err(TypeCoreError::NotAVariantType(lid_txt)),
    };
    drop(spread_ty_desc);

    // Step 2: Create fresh type variables for type params and expand to get the variant row
    // OCaml: let tyl = List.map (fun _ -> newvar()) decl.type_params
    // OCaml: let ty = expand_head env (newty (Tconstr(path, tyl, ref Mnil)))
    // We already have spread_ty_ref from transl_type which should be Tconstr(path, args)
    // Expand it to get the Tvariant
    let expanded = crate::types::ctype::expand_head(ctx, env, spread_ty_ref);
    let expanded_desc = ctx.get_desc(expanded);
    let row0 = match &*expanded_desc {
        TypeDesc::Tvariant(row) if crate::types::btype::static_row(ctx, row) => {
            crate::types::btype::row_repr(ctx, row)
        }
        _ => return Err(TypeCoreError::NotAVariantType(lid_txt)),
    };
    drop(expanded_desc);

    // Step 3: Build patterns and new row fields from the existing row fields
    // OCaml creates Reither fields for each Rpresent field
    let mut pats: Vec<(String, Option<Box<Pattern>>)> = Vec::new();
    let mut fields: Vec<(String, RowField)> = Vec::new();

    for (label, field) in &row0.row_fields {
        match crate::types::btype::row_field_repr(ctx, field) {
            RowField::Rpresent(None) => {
                pats.push((label.clone(), None));
                fields.push((
                    label.clone(),
                    RowField::Reither {
                        constant: true,
                        types: vec![],
                        matched: true,
                        link: ctx.alloc_row_field(None),
                    },
                ));
            }
            RowField::Rpresent(Some(ty)) => {
                let arg_pat = Pattern::new(
                    PatternDesc::Tpat_any,
                    LocIdx::none(),
                    ty,
                    EnvRef(0),
                    Attributes::new(),
                );
                pats.push((label.clone(), Some(Box::new(arg_pat))));
                fields.push((
                    label.clone(),
                    RowField::Reither {
                        constant: false,
                        types: vec![ty],
                        matched: true,
                        link: ctx.alloc_row_field(None),
                    },
                ));
            }
            _ => {
                // Skip Reither and Rabsent fields
            }
        }
    }

    if pats.is_empty() {
        return Err(TypeCoreError::NotAVariantType(lid_txt));
    }

    // Step 4: Create the variant type for the patterns
    let row = RowDesc {
        row_fields: fields,
        row_more: ctx.new_var(None),
        row_closed: false,
        row_fixed: false,
        row_name: Some((path.clone(), args)),
    };
    let ty = ctx.new_variant(row);

    // Step 5: Create Tpat_variant for each pattern
    // OCaml's fold_left builds pats with :: prepend, implicitly reversing them.
    // We must reverse to match OCaml's order in the or-pattern chain.
    pats.reverse();
    let ghost_loc = loc.clone(); // OCaml uses ghost location
    let typed_pats: Vec<Pattern> = pats
        .into_iter()
        .map(|(label, arg)| {
            Pattern::new(
                PatternDesc::Tpat_variant(label, arg, RowDescRef(0)),
                ghost_loc.clone(),
                ty,
                EnvRef(0),
                Attributes::new(),
            )
        })
        .collect();

    // Step 6: Fold into Tpat_or chain
    // OCaml: List.fold_left (fun pat pat0 -> {pat_desc = Tpat_or(pat0, pat, Some row0)}) pat pats
    let mut iter = typed_pats.into_iter();
    let first = iter.next().unwrap();
    let or_pat = iter.fold(first, |acc, pat0| {
        Pattern::new(
            PatternDesc::Tpat_or(Box::new(pat0), Box::new(acc), None),
            ghost_loc.clone(),
            ty,
            EnvRef(0),
            Attributes::new(),
        )
    });

    // Set the location to the original pattern location
    let result = Pattern {
        pat_loc: loc,
        ..or_pat
    };

    Ok((path, result, ty))
}

fn extract_type_from_pat_variant_spread(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    lid: &Located<LidentIdx>,
) -> TypeCoreResult<(Path, Vec<crate::types::ConstructorDeclaration>, TypeExprRef)> {
    let ctx = tctx.type_ctx;
    let lid_txt = tctx.resolve_lid(lid.txt).clone();
    let spread_ct = crate::parser::ast::CoreType {
        ptyp_desc: Box::new(crate::parser::ast::CoreTypeDesc::Ptyp_constr(Box::new((
            *lid,
            vec![],
        )))),
        ptyp_loc: lid.loc,
        ptyp_attributes: Attributes::new(),
    };

    let (_, spread_ty_ref) = transl_type(tctx, env, &spread_ct)?;
    let spread_ty = ctx.repr(spread_ty_ref);
    let spread_ty_desc = ctx.get_desc(spread_ty);
    let (spread_path, spread_args) = match &*spread_ty_desc {
        TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
        _ => return Err(TypeCoreError::NotAVariantType(lid_txt)),
    };
    drop(spread_ty_desc);

    let Some(type_decl) =
        lookup_type_decl_for_path(&spread_path, env, &mut tctx.persistent_env, ctx)
    else {
        return Err(TypeCoreError::NotAVariantType(lid_txt));
    };
    if !spread_args.is_empty() || !type_decl.type_params.is_empty() {
        return Err(TypeCoreError::NotAVariantType(lid_txt));
    }

    let constructors = match &type_decl.type_kind {
        crate::types::TypeKind::TypeVariant(cstrs) => cstrs.clone(),
        _ => return Err(TypeCoreError::NotAVariantType(lid_txt)),
    };
    let spread_ty = ctx.new_generic_constr(spread_path.clone(), vec![]);

    Ok((spread_path, constructors, spread_ty))
}

fn build_ppat_or_for_variant_spread(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
    _expected_ty: TypeExprRef,
) -> TypeCoreResult<Option<(ParsedPattern, TypeExprRef)>> {
    let crate::parser::ast::PatternDesc::Ppat_type(lident) = &*pat.ppat_desc else {
        return Ok(None);
    };
    if !has_res_pat_variant_spread_attribute(tctx.arena, &pat.ppat_attributes) {
        return Ok(None);
    }

    let (_path, constructors, spread_ty) = extract_type_from_pat_variant_spread(tctx, env, lident)?;
    debug_assert_eq!(
        tctx.arena
            .get_string(tctx.arena.pat_from_variant_spread_attr_str()),
        PAT_FROM_VARIANT_SPREAD_ATTRIBUTE
    );
    let pat_from_variant_spread_attr = (
        Located::mknoloc(tctx.arena.pat_from_variant_spread_attr_str()),
        crate::parser::ast::Payload::PStr(Box::new(vec![])),
    );
    let arena_ptr = tctx.arena as *const ParseArena as *mut ParseArena;
    let mut synthetic_pattern_idxs = Vec::with_capacity(constructors.len());
    for cstr in constructors {
        let cstr_name = cstr.cd_id.name();
        let Some(cstr_lid_idx) = find_existing_lident_idx(tctx.arena, cstr_name) else {
            return Err(TypeCoreError::NotAVariantType(
                tctx.resolve_lid(lident.txt).clone(),
            ));
        };
        let cstr_lid = Located {
            txt: cstr_lid_idx,
            loc: lident.loc,
        };
        let cstr_arg = match cstr.cd_args {
            crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty() => None,
            _ => Some(unsafe {
                (*arena_ptr).push_pat(ParsedPattern {
                ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_any),
                ppat_loc: LocIdx::none(),
                ppat_attributes: Attributes::new(),
                })
            }),
        };
        let parsed = ParsedPattern {
            ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_construct(cstr_lid, cstr_arg)),
            ppat_loc: lident.loc,
            ppat_attributes: vec![pat_from_variant_spread_attr.clone()].into(),
        };
        synthetic_pattern_idxs.push(unsafe { (*arena_ptr).push_pat(parsed) });
    }

    synthetic_pattern_idxs.reverse();
    let expanded_pattern = match synthetic_pattern_idxs.into_iter().reduce(|lhs, rhs| {
        unsafe { (*arena_ptr).push_pat(ParsedPattern {
            ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_or(lhs, rhs)),
            ppat_loc: LocIdx::none(),
            ppat_attributes: Attributes::new(),
        }) }
    }) {
        Some(pattern) => tctx.arena.get_pat(pattern).clone(),
        None => pat.clone(),
    };

    Ok(Some((expanded_pattern, spread_ty)))
}

fn maybe_expand_variant_spread_in_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
    expected_ty: TypeExprRef,
) -> TypeCoreResult<Option<ParsedPattern>> {
    if !matches!(&*pat.ppat_desc, crate::parser::ast::PatternDesc::Ppat_type(_)) {
        return Ok(None);
    }
    if !has_res_pat_variant_spread_attribute(tctx.arena, &pat.ppat_attributes) {
        return Ok(None);
    }

    Ok(
        build_ppat_or_for_variant_spread(tctx, env, pat, expected_ty)?
            .map(|(expanded, _)| expanded),
    )
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
    // Match OCaml's type_pat: set newtype_level for GADT existential support
    let old_newtype_level = tctx.newtype_level;
    tctx.newtype_level = Some(tctx.type_ctx.current_level());
    let result = type_pattern_inner(tctx, env, pat, expected_ty, mode, state, 0);
    tctx.newtype_level = old_newtype_level;
    result
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

    let expanded_pat = maybe_expand_variant_spread_in_pattern(tctx, env, pat, expected_ty)?;
    let pat = expanded_pat.as_ref().unwrap_or(pat);
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

            if std::env::var_os("RUST_DEBUG_TUPLE_PAT").is_some() {
                let full_loc = tctx.arena.to_location(loc);
                if full_loc.loc_start.line >= 1098 && full_loc.loc_start.line <= 1110 {
                    let expected_repr = ctx.repr(expected_ty);
                    let tuple_repr = ctx.repr(tuple_ty);
                    let elem_dump: Vec<String> = elem_types
                        .iter()
                        .map(|ty| {
                            let r = ctx.repr(*ty);
                            format!("{}@{}", r.0, ctx.get_level(r))
                        })
                        .collect();
                    eprintln!(
                        "[rust-tuple-pat] stage=after_unify loc={}:{} expected={}@{} tuple={}@{} elems=[{}]",
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        expected_repr.0,
                        ctx.get_level(expected_repr),
                        tuple_repr.0,
                        ctx.get_level(tuple_repr),
                        elem_dump.join(",")
                    );
                }
            }

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
            let (expanded_inner, override_type_from_variant_spread) =
                if matches!(&*inner_pat.ppat_desc, PD::Ppat_type(_))
                    && has_res_pat_variant_spread_attribute(tctx.arena, &inner_pat.ppat_attributes)
                {
                    match build_ppat_or_for_variant_spread(tctx, env, inner_pat, expected_ty)? {
                        Some((expanded, spread_ty)) => (Some(expanded), Some(spread_ty)),
                        None => (None, None),
                    }
                } else {
                    (None, None)
                };
            let inner_pat = expanded_inner.as_ref().unwrap_or(inner_pat);

            let typed_inner =
                type_pattern_inner(tctx, env, inner_pat, expected_ty, mode, state, 0)?;

            // Build the as-type.
            // OCaml wraps in begin_def/end_def/generalize (typecore.ml:1288-1295).
            // For non-private constructors, build_as_type creates fresh types at
            // the elevated level, which then get generalized. For private constructors,
            // build_as_type returns pat.pat_type which is at the caller's level —
            // the actual generalization comes from type_cases' propagation cycle.
            let ctx = tctx.type_ctx;
            ctx.begin_def();
            let ty_var = match override_type_from_variant_spread {
                Some(ty) => ty,
                None => build_as_type(tctx, env, &typed_inner)?,
            };
            ctx.end_def();
            crate::types::ctype::generalize(ctx, ty_var);

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
            let inner_pat = tctx.arena.get_pat(*inner_pat_idx);
            let core_ty = tctx.arena.get_core_type(*core_type);

            // OCaml typecore.ml:1249-1274: Special case for Ppat_constraint(Ppat_var, Ptyp_poly)
            // Uses instance_poly ~keep_names:true to preserve type variable names.
            if let (
                PD::Ppat_var(name),
                crate::parser::ast::CoreTypeDesc::Ptyp_poly(_),
            ) = (&*inner_pat.ppat_desc, &*core_ty.ptyp_desc)
            {
                type_pattern_constraint_poly_var(
                    tctx, env, loc, inner_pat, *name, core_ty, expected_ty, mode, state, pat,
                )
            } else {
                type_pattern_constraint(
                    tctx, env, loc, inner_pat, core_ty, expected_ty, mode, state, pat,
                )
            }
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

        PD::Ppat_unpack(name) => {
            // Module unpack pattern: module(M)
            let id = state.enter_variable(loc, name, expected_ty, false, true, tctx.arena)?;
            let typed_pat = Pattern::new(
                PatternDesc::Tpat_var(id, convert_located_stridx(name, tctx.arena)),
                loc,
                expected_ty,
                EnvRef(0),
                Attributes::new(),
            );
            Ok(typed_pat.with_pat_extra(
                crate::types::typedtree::PatExtra::Tpat_unpack,
                loc,
                pat.ppat_attributes.clone(),
            ))
        }

        PD::Ppat_type(lid) => {
            // Poly variant type pattern: #type or used for #...spread
            // OCaml typecore.ml:1663-1671: build_or_pat expands into Tpat_variant or-patterns
            let (path, or_pat, ty) = build_or_pat(tctx, env, loc.clone(), lid)?;
            unify_pattern_types(tctx, loc.clone(), ty, expected_ty)?;
            let result = Pattern {
                pat_extra: vec![(
                    crate::types::typedtree::PatExtra::Tpat_type(path, *lid),
                    loc,
                    pat.ppat_attributes.clone(),
                )],
                ..or_pat
            };
            Ok(result)
        }

        PD::Ppat_extension(_) => {
            // Extension patterns - return wildcard for now
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
    loc: LocIdx,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeCoreResult<()> {
    use crate::types::unify;

    let debug_pattern_unify = std::env::var_os("RUST_DEBUG_PATTERN_UNIFY").is_some();

    if debug_pattern_unify {
        let summarize = |ty: TypeExprRef| {
            let raw_desc = tctx.type_ctx.get_desc(ty);
            let raw_head = match &*raw_desc {
                TypeDesc::Tlink(t) => format!("raw=Tlink->#{}", tctx.type_ctx.repr(*t).0),
                TypeDesc::Tsubst(t) => {
                    format!("raw=Tsubst->#{}", tctx.type_ctx.repr(*t).0)
                }
                TypeDesc::Tvariant(_) => "raw=Tvariant".to_string(),
                TypeDesc::Tconstr { path, .. } => format!("raw=Tconstr({})", path.name()),
                TypeDesc::Tvar(_) => "raw=Tvar".to_string(),
                TypeDesc::Tunivar(_) => "raw=Tunivar".to_string(),
                TypeDesc::Tarrow { .. } => "raw=Tarrow".to_string(),
                TypeDesc::Ttuple(_) => "raw=Ttuple".to_string(),
                TypeDesc::Tobject { .. } => "raw=Tobject".to_string(),
                TypeDesc::Tfield { .. } => "raw=Tfield".to_string(),
                TypeDesc::Tnil => "raw=Tnil".to_string(),
                TypeDesc::Tpoly { .. } => "raw=Tpoly".to_string(),
                TypeDesc::Tpackage { .. } => "raw=Tpackage".to_string(),
            };
            drop(raw_desc);
            let repr = tctx.type_ctx.repr(ty);
            let desc = tctx.type_ctx.get_desc(repr);
            match &*desc {
                TypeDesc::Tvariant(row) => {
                    let row = crate::types::btype::row_repr(tctx.type_ctx, row);
                    let field_summary = row
                        .row_fields
                        .iter()
                        .map(|(label, field)| {
                            let rf = crate::types::btype::row_field_repr(tctx.type_ctx, field);
                            let kind = match rf {
                                crate::types::type_expr::RowField::Rabsent => "Rabsent".to_string(),
                                crate::types::type_expr::RowField::Rpresent(None) => {
                                    "Rpresent(None)".to_string()
                                }
                                crate::types::type_expr::RowField::Rpresent(Some(arg)) => {
                                    format!("Rpresent(Some#{})", tctx.type_ctx.repr(arg).0)
                                }
                                crate::types::type_expr::RowField::Reither {
                                    constant,
                                    matched,
                                    types,
                                    ..
                                } => format!("Reither(c={},m={},n={})", constant, matched, types.len()),
                            };
                            format!("{}={}", label, kind)
                        })
                        .collect::<Vec<_>>()
                        .join(";");
                    format!(
                        "#{}->#{} {} Tvariant(closed={},fixed={},more=#{},fields=[{}])",
                        ty.0,
                        repr.0,
                        raw_head,
                        row.row_closed,
                        row.row_fixed,
                        tctx.type_ctx.repr(row.row_more).0,
                        field_summary
                    )
                }
                _ => format!("#{}->#{} {}", ty.0, repr.0, raw_head),
            }
        };
        let full_loc = tctx.arena.to_location(loc);
        eprintln!(
            "[pattern-unify-start] loc={}:{} ty1={} ty2={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            summarize(ty1),
            summarize(ty2)
        );
    }

    match unify(tctx.type_ctx, &mut tctx.unify_state, ty1, ty2) {
        Ok(()) => Ok(()),
        Err(TypeError::Unify(_)) => {
            if debug_pattern_unify {
                let summarize = |ty: TypeExprRef| {
                    let raw_desc = tctx.type_ctx.get_desc(ty);
                    let raw_head = match &*raw_desc {
                        TypeDesc::Tlink(t) => format!("raw=Tlink->#{}", tctx.type_ctx.repr(*t).0),
                        TypeDesc::Tsubst(t) => {
                            format!("raw=Tsubst->#{}", tctx.type_ctx.repr(*t).0)
                        }
                        TypeDesc::Tvariant(_) => "raw=Tvariant".to_string(),
                        TypeDesc::Tconstr { path, .. } => format!("raw=Tconstr({})", path.name()),
                        TypeDesc::Tvar(_) => "raw=Tvar".to_string(),
                        TypeDesc::Tunivar(_) => "raw=Tunivar".to_string(),
                        TypeDesc::Tarrow { .. } => "raw=Tarrow".to_string(),
                        TypeDesc::Ttuple(_) => "raw=Ttuple".to_string(),
                        TypeDesc::Tobject { .. } => "raw=Tobject".to_string(),
                        TypeDesc::Tfield { .. } => "raw=Tfield".to_string(),
                        TypeDesc::Tnil => "raw=Tnil".to_string(),
                        TypeDesc::Tpoly { .. } => "raw=Tpoly".to_string(),
                        TypeDesc::Tpackage { .. } => "raw=Tpackage".to_string(),
                    };
                    drop(raw_desc);
                    let repr = tctx.type_ctx.repr(ty);
                    let desc = tctx.type_ctx.get_desc(repr);
                    match &*desc {
                        TypeDesc::Tconstr { path, args, .. } => {
                            format!(
                                "#{}->#{} {} {}(args={})",
                                ty.0,
                                repr.0,
                                raw_head,
                                path.name(),
                                args.len()
                            )
                        }
                        TypeDesc::Tarrow { .. } => {
                            format!("#{}->#{} {} Tarrow", ty.0, repr.0, raw_head)
                        }
                        TypeDesc::Tvar(_) => format!("#{}->#{} {} Tvar", ty.0, repr.0, raw_head),
                        TypeDesc::Tunivar(_) => {
                            format!("#{}->#{} {} Tunivar", ty.0, repr.0, raw_head)
                        }
                        TypeDesc::Tlink(t) => format!(
                            "#{}->#{} {} Tlink->{}",
                            ty.0,
                            repr.0,
                            raw_head,
                            tctx.type_ctx.repr(*t).0
                        ),
                        TypeDesc::Tsubst(t) => format!(
                            "#{}->#{} {} Tsubst->{}",
                            ty.0,
                            repr.0,
                            raw_head,
                            tctx.type_ctx.repr(*t).0
                        ),
                        TypeDesc::Ttuple(ts) => {
                            format!("#{}->#{} {} Ttuple({})", ty.0, repr.0, raw_head, ts.len())
                        }
                        TypeDesc::Tobject { .. } => {
                            format!("#{}->#{} {} Tobject", ty.0, repr.0, raw_head)
                        }
                        TypeDesc::Tfield { .. } => {
                            format!("#{}->#{} {} Tfield", ty.0, repr.0, raw_head)
                        }
                        TypeDesc::Tnil => format!("#{}->#{} {} Tnil", ty.0, repr.0, raw_head),
                        TypeDesc::Tvariant(row) => {
                            let row = crate::types::btype::row_repr(tctx.type_ctx, row);
                            let field_summary = row
                                .row_fields
                                .iter()
                                .map(|(label, field)| {
                                    let rf = crate::types::btype::row_field_repr(tctx.type_ctx, field);
                                    let kind = match rf {
                                        crate::types::type_expr::RowField::Rabsent => "Rabsent".to_string(),
                                        crate::types::type_expr::RowField::Rpresent(None) => {
                                            "Rpresent(None)".to_string()
                                        }
                                        crate::types::type_expr::RowField::Rpresent(Some(arg)) => {
                                            format!("Rpresent(Some#{})", tctx.type_ctx.repr(arg).0)
                                        }
                                        crate::types::type_expr::RowField::Reither {
                                            constant,
                                            matched,
                                            types,
                                            ..
                                        } => format!(
                                            "Reither(c={},m={},n={})",
                                            constant,
                                            matched,
                                            types.len()
                                        ),
                                    };
                                    format!("{}={}", label, kind)
                                })
                                .collect::<Vec<_>>()
                                .join(";");
                            format!(
                                "#{}->#{} {} Tvariant(closed={},fixed={},more=#{},fields=[{}])",
                                ty.0,
                                repr.0,
                                raw_head,
                                row.row_closed,
                                row.row_fixed,
                                tctx.type_ctx.repr(row.row_more).0,
                                field_summary
                            )
                        }
                        TypeDesc::Tpoly { .. } => {
                            format!("#{}->#{} {} Tpoly", ty.0, repr.0, raw_head)
                        }
                        TypeDesc::Tpackage { .. } => {
                            format!("#{}->#{} {} Tpackage", ty.0, repr.0, raw_head)
                        }
                    }
                };
                let full_loc = tctx.arena.to_location(loc);
                eprintln!(
                    "[pattern-unify-fail] loc={}:{} ty1={} ty2={}",
                    full_loc.loc_start.line,
                    full_loc.loc_start.column(),
                    summarize(ty1),
                    summarize(ty2)
                );
            }
            Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)]))
        },
        Err(_) => Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)])),
    }
}

/// GADT-mode pattern unification: enables generate_equations and assume_injective
/// so that abstract newtypes can receive type equations. Matches OCaml's
/// unify_pat_types_gadt which calls unify_gadt.
fn unify_pattern_types_gadt(
    tctx: &mut TypeCheckContext<'_>,
    _loc: LocIdx,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeCoreResult<()> {
    use crate::types::unify;

    // Save old state
    let old_generate = tctx.unify_state.generate_equations;
    let old_injective = tctx.unify_state.assume_injective;
    let old_mode = tctx.unify_state.mode;

    // Set GADT mode
    tctx.unify_state.generate_equations = true;
    tctx.unify_state.assume_injective = true;
    tctx.unify_state.mode = crate::types::UnifyMode::Pattern;

    let result = unify(tctx.type_ctx, &mut tctx.unify_state, ty1, ty2);

    // Restore old state
    tctx.unify_state.generate_equations = old_generate;
    tctx.unify_state.assume_injective = old_injective;
    tctx.unify_state.mode = old_mode;

    match result {
        Ok(()) => Ok(()),
        Err(TypeError::Unify(_)) => {
            Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)]))
        },
        Err(_) => Err(TypeCoreError::PatternTypeClash(vec![(ty1, ty2)])),
    }
}

fn row_field_contains_tunivar(
    ctx: &TypeContext<'_>,
    env: &Env,
    field: &crate::types::type_expr::RowField,
    seen: &mut HashSet<TypeExprRef>,
) -> bool {
    match field {
        crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
            type_contains_tunivar(ctx, env, *ty, seen)
        }
        crate::types::type_expr::RowField::Reither { types, .. } => types
            .iter()
            .copied()
            .any(|ty| type_contains_tunivar(ctx, env, ty, seen)),
        _ => false,
    }
}

fn type_contains_tunivar(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    seen: &mut HashSet<TypeExprRef>,
) -> bool {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return false;
    }

    match &*ctx.get_desc(ty) {
        TypeDesc::Tunivar(_) => true,
        TypeDesc::Tvar(_) | TypeDesc::Tnil => false,
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            type_contains_tunivar(ctx, env, *target, seen)
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            type_contains_tunivar(ctx, env, arg.typ, seen)
                || type_contains_tunivar(ctx, env, *ret, seen)
        }
        TypeDesc::Ttuple(types) => types
            .iter()
            .copied()
            .any(|ty| type_contains_tunivar(ctx, env, ty, seen)),
        TypeDesc::Tconstr { path, args, .. } => {
            is_local_abstract_type_path(ctx, env, path)
                || args
                    .iter()
                    .copied()
                    .any(|ty| type_contains_tunivar(ctx, env, ty, seen))
        }
        TypeDesc::Tobject { fields, name } => {
            type_contains_tunivar(ctx, env, *fields, seen)
                || name.as_ref().is_some_and(|(_, args)| {
                    args.iter()
                        .copied()
                        .any(|ty| type_contains_tunivar(ctx, env, ty, seen))
                })
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            type_contains_tunivar(ctx, env, *typ, seen)
                || type_contains_tunivar(ctx, env, *rest, seen)
        }
        TypeDesc::Tvariant(row) => {
            type_contains_tunivar(ctx, env, row.row_more, seen)
                || row
                    .row_fields
                    .iter()
                    .any(|(_, field)| row_field_contains_tunivar(ctx, env, field, seen))
                || row.row_name.as_ref().is_some_and(|(_, args)| {
                    args.iter()
                        .copied()
                        .any(|ty| type_contains_tunivar(ctx, env, ty, seen))
                })
        }
        TypeDesc::Tpoly { body, vars } => {
            type_contains_tunivar(ctx, env, *body, seen)
                || vars
                    .iter()
                    .copied()
                    .any(|ty| type_contains_tunivar(ctx, env, ty, seen))
        }
        TypeDesc::Tpackage { args, .. } => args
            .iter()
            .copied()
            .any(|ty| type_contains_tunivar(ctx, env, ty, seen)),
    }
}

fn copy_case_row_field(
    ctx: &TypeContext<'_>,
    env: &Env,
    field: &crate::types::type_expr::RowField,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::type_expr::RowField {
    match field {
        crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
            crate::types::type_expr::RowField::Rpresent(Some(copy_case_type(ctx, env, *ty, cache)))
        }
        crate::types::type_expr::RowField::Rpresent(None) => {
            crate::types::type_expr::RowField::Rpresent(None)
        }
        crate::types::type_expr::RowField::Reither {
            constant,
            types,
            matched,
            link,
        } => crate::types::type_expr::RowField::Reither {
            constant: *constant,
            types: types
                .iter()
                .copied()
                .map(|ty| copy_case_type(ctx, env, ty, cache))
                .collect(),
            matched: *matched,
            link: *link,
        },
        crate::types::type_expr::RowField::Rabsent => crate::types::type_expr::RowField::Rabsent,
    }
}

fn copy_case_row(
    ctx: &TypeContext<'_>,
    env: &Env,
    row: &crate::types::type_expr::RowDesc,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> crate::types::type_expr::RowDesc {
    crate::types::type_expr::RowDesc {
        row_fields: row
            .row_fields
            .iter()
            .map(|(label, field)| (label.clone(), copy_case_row_field(ctx, env, field, cache)))
            .collect(),
        row_more: copy_case_type(ctx, env, row.row_more, cache),
        row_closed: row.row_closed,
        row_fixed: row.row_fixed,
        row_name: row.row_name.as_ref().map(|(path, args)| {
            (
                path.clone(),
                args.iter()
                    .copied()
                    .map(|ty| copy_case_type(ctx, env, ty, cache))
                    .collect(),
            )
        }),
    }
}

fn is_local_abstract_type_path(ctx: &TypeContext<'_>, env: &Env, path: &Path) -> bool {
    let is_local_abstract = |decl: &crate::types::TypeDeclaration| {
        decl.type_newtype_level.is_some()
            && decl.type_manifest.is_none()
            && matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
    };

    if let Ok(decl) = env.lookup_type(path) {
        if is_local_abstract(decl) {
            return true;
        }
    }
    if let Path::Pident(id) = path {
        if let Some(decl) = ctx.find_type_decl_by_stamp(id.stamp()) {
            if is_local_abstract(&decl) {
                return true;
            }
        }
    }
    false
}

fn copy_case_type(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);
    if let Some(&cached) = cache.get(&ty) {
        return cached;
    }

    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            copy_case_type(ctx, env, *target, cache)
        }
        TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => {
            let fresh = ctx.new_var(name.clone());
            cache.insert(ty, fresh);
            fresh
        }
        TypeDesc::Tarrow {
            arg,
            ret,
            commutable,
            arity,
        } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_arg = crate::types::type_expr::TypeArg {
                lbl: arg.lbl.clone(),
                typ: copy_case_type(ctx, env, arg.typ, cache),
            };
            let copied_ret = copy_case_type(ctx, env, *ret, cache);
            ctx.set_desc(
                placeholder,
                TypeDesc::Tarrow {
                    arg: copied_arg,
                    ret: copied_ret,
                    commutable: commutable.clone(),
                    arity: *arity,
                },
            );
            placeholder
        }
        TypeDesc::Ttuple(types) => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied = types
                .iter()
                .copied()
                .map(|t| copy_case_type(ctx, env, t, cache))
                .collect();
            ctx.set_desc(placeholder, TypeDesc::Ttuple(copied));
            placeholder
        }
        TypeDesc::Tconstr { path, args, .. } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_args = args
                .iter()
                .copied()
                .map(|t| copy_case_type(ctx, env, t, cache))
                .collect();
            ctx.set_desc(
                placeholder,
                TypeDesc::Tconstr {
                    path: path.clone(),
                    args: copied_args,
                    abbrev: crate::types::type_expr::AbbrevMemoRef::nil(),
                },
            );
            placeholder
        }
        TypeDesc::Tobject { fields, name } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_fields = copy_case_type(ctx, env, *fields, cache);
            let copied_name = name.as_ref().map(|(path, args)| {
                (
                    path.clone(),
                    args.iter()
                        .copied()
                        .map(|t| copy_case_type(ctx, env, t, cache))
                        .collect(),
                )
            });
            ctx.set_desc(
                placeholder,
                TypeDesc::Tobject {
                    fields: copied_fields,
                    name: copied_name,
                },
            );
            placeholder
        }
        TypeDesc::Tfield {
            name,
            kind,
            typ,
            rest,
        } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_typ = copy_case_type(ctx, env, *typ, cache);
            let copied_rest = copy_case_type(ctx, env, *rest, cache);
            ctx.set_desc(
                placeholder,
                TypeDesc::Tfield {
                    name: name.clone(),
                    kind: kind.clone(),
                    typ: copied_typ,
                    rest: copied_rest,
                },
            );
            placeholder
        }
        TypeDesc::Tnil => {
            let copied = ctx.new_type(TypeDesc::Tnil);
            cache.insert(ty, copied);
            copied
        }
        TypeDesc::Tvariant(row) => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_row = copy_case_row(ctx, env, row, cache);
            ctx.set_desc(placeholder, TypeDesc::Tvariant(copied_row));
            placeholder
        }
        TypeDesc::Tpoly { body, vars } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_body = copy_case_type(ctx, env, *body, cache);
            let copied_vars = vars
                .iter()
                .copied()
                .map(|v| copy_case_type(ctx, env, v, cache))
                .collect();
            ctx.set_desc(
                placeholder,
                TypeDesc::Tpoly {
                    body: copied_body,
                    vars: copied_vars,
                },
            );
            placeholder
        }
        TypeDesc::Tpackage { path, lids, args } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let copied_args = args
                .iter()
                .copied()
                .map(|t| copy_case_type(ctx, env, t, cache))
                .collect();
            ctx.set_desc(
                placeholder,
                TypeDesc::Tpackage {
                    path: path.clone(),
                    lids: lids.clone(),
                    args: copied_args,
                },
            );
            placeholder
        }
    }
}

fn refine_record_as_type_label(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    whole_pat: &Pattern,
    record_ty: TypeExprRef,
    label_desc: &crate::types::LabelDescription,
    field_pat: Option<&Pattern>,
) -> TypeCoreResult<()> {
    let ctx = tctx.type_ctx;
    let (_poly_vars, ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, false, label_desc);
    unify_pattern_types(tctx, whole_pat.pat_loc, record_ty, ty_res)?;

    let lbl_arg_repr = ctx.repr(label_desc.lbl_arg);
    let lbl_arg_desc = ctx.get_desc(lbl_arg_repr);
    let arg_is_poly = matches!(&*lbl_arg_desc, TypeDesc::Tpoly { .. });
    drop(lbl_arg_desc);

    let refinable = label_desc.lbl_mut == crate::types::asttypes::MutableFlag::Immutable
        && field_pat.is_some()
        && !arg_is_poly;
    if refinable {
        let field_pat = field_pat.unwrap();
        let field_as_ty = build_as_type(tctx, env, field_pat)?;
        unify_pattern_types(tctx, field_pat.pat_loc, field_as_ty, ty_arg)?;
    } else {
        let (_poly_vars2, ty_arg2, ty_res2) = crate::types::ctype::instance_label(ctx, false, label_desc);
        unify_pattern_types(tctx, whole_pat.pat_loc, ty_arg, ty_arg2)?;
        unify_pattern_types(tctx, whole_pat.pat_loc, record_ty, ty_res2)?;
    }
    Ok(())
}

/// Build the type for an as-pattern.
fn build_as_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &Pattern,
) -> TypeCoreResult<TypeExprRef> {
    let ctx = tctx.type_ctx;
    match &pat.pat_desc {
        PatternDesc::Tpat_alias(inner, _, _) => build_as_type(tctx, env, inner),
        PatternDesc::Tpat_tuple(pats) => {
            let tys: Vec<_> = pats
                .iter()
                .map(|p| build_as_type(tctx, env, p))
                .collect::<TypeCoreResult<_>>()?;
            Ok(ctx.new_tuple(tys))
        }
        PatternDesc::Tpat_construct(_, cstr, args) => {
            let keep = cstr.cstr_private == crate::types::PrivateFlag::Private
                || !cstr.cstr_existentials.is_empty();
            if keep {
                Ok(pat.pat_type)
            } else {
                let arg_as_tys: Vec<_> = args
                    .iter()
                    .map(|arg| build_as_type(tctx, env, arg))
                    .collect::<TypeCoreResult<_>>()?;
                let (inst_arg_tys, ty_res) = crate::types::instance_constructor(ctx, cstr);
                for ((arg_pat, arg_as_ty), inst_arg_ty) in
                    args.iter().zip(arg_as_tys.iter()).zip(inst_arg_tys.iter())
                {
                    unify_pattern_types(tctx, arg_pat.pat_loc, *arg_as_ty, *inst_arg_ty)?;
                }
                Ok(ty_res)
            }
        }
        PatternDesc::Tpat_record(fields, _closed) => {
            let first_label = fields.first().map(|(_, lbl, _, _)| lbl);
            if first_label
                .is_some_and(|lbl| lbl.lbl_private == crate::types::PrivateFlag::Private)
            {
                Ok(pat.pat_type)
            } else {
                // OCaml build_as_type for records creates a fresh record type variable,
                // then refines it through each label's instantiated arg/res types.
                let ty = ctx.new_var(None);
                let present_fields_by_pos: std::collections::HashMap<i32, &Pattern> = fields
                    .iter()
                    .map(|(_lid, label_desc, field_pat, _optional)| (label_desc.lbl_pos, field_pat))
                    .collect();

                let all_labels = get_record_labels(ctx, env, &mut tctx.persistent_env, pat.pat_type)
                    .or_else(|| {
                        first_label.and_then(|lbl| {
                            get_record_labels(ctx, env, &mut tctx.persistent_env, lbl.lbl_res)
                        })
                    });

                if let Some(label_decls) = all_labels {
                    for (idx, label_decl) in label_decls.iter().enumerate() {
                        let label_name = label_decl.ld_id.name().to_string();
                        // Match OCaml build_as_type record refinement: keep the selected
                        // record declaration shape, do not re-disambiguate labels by name.
                        // Re-disambiguating through env with a fresh `ty` can pick labels
                        // from unrelated record types that happen to share field names.
                        let decl_label = crate::types::LabelDescription {
                            lbl_name: label_name,
                            lbl_res: ty,
                            lbl_arg: crate::types::instance(ctx, label_decl.ld_type),
                            lbl_mut: label_decl.ld_mutable.clone(),
                            lbl_optional: label_decl.ld_optional,
                            lbl_pos: idx as i32,
                            lbl_all: crate::types::LabelArrayRef(0),
                            lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                            lbl_private: crate::types::PrivateFlag::Public,
                            lbl_loc: label_decl.ld_loc.clone(),
                            lbl_attributes: label_decl.ld_attributes.clone(),
                        };
                        let field_pat = present_fields_by_pos.get(&(idx as i32)).copied();
                        refine_record_as_type_label(tctx, env, pat, ty, &decl_label, field_pat)?;
                    }
                } else {
                    for (_lid, label_desc, _field_pat, _optional) in fields.iter() {
                        let field_pat = present_fields_by_pos.get(&label_desc.lbl_pos).copied();
                        refine_record_as_type_label(tctx, env, pat, ty, label_desc, field_pat)?;
                    }
                }
                Ok(ty)
            }
        }
        PatternDesc::Tpat_variant(label, opt_arg, _) => {
            // OCaml typecore.ml:488-498: create single-field open row with Rpresent
            let opt_ty = match opt_arg {
                Some(p) => Some(build_as_type(tctx, env, p)?),
                None => None,
            };
            let row = crate::types::type_expr::RowDesc {
                row_fields: vec![(label.clone(), crate::types::type_expr::RowField::Rpresent(opt_ty))],
                row_more: ctx.new_var(None),
                row_name: None,
                row_fixed: false,
                row_closed: false,
            };
            Ok(ctx.new_variant(row))
        }
        PatternDesc::Tpat_or(p1, p2, opt_row) => {
            // OCaml typecore.ml:526-534
            match opt_row {
                None => {
                    let ty1 = build_as_type(tctx, env, p1)?;
                    let ty2 = build_as_type(tctx, env, p2)?;
                    unify_pattern_types(tctx, p2.pat_loc, ty2, ty1)?;
                    Ok(ty1)
                }
                Some(row) => {
                    // Open the row: set row_closed=false and fresh row_more
                    let row = crate::types::btype::row_repr(ctx, row);
                    let mut new_row = row;
                    new_row.row_closed = false;
                    new_row.row_more = ctx.new_var(None);
                    Ok(ctx.new_variant(new_row))
                }
            }
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
    let debug_expected_ty = || {
        let expected_repr = ctx.repr(expected_ty);
        let expected_desc = ctx.get_desc(expected_repr);
        match &*expected_desc {
            TypeDesc::Tconstr { path, .. } => {
                format!("Tconstr({})@{}", path.name(), expected_repr.0)
            }
            TypeDesc::Tvar(name) => format!("Tvar({name:?})@{}", expected_repr.0),
            TypeDesc::Tlink(inner) => format!("Tlink({})@{}", inner.0, expected_repr.0),
            TypeDesc::Tarrow { .. } => format!("Tarrow@{}", expected_repr.0),
            TypeDesc::Ttuple(_) => format!("Ttuple@{}", expected_repr.0),
            TypeDesc::Tobject { .. } => format!("Tobject@{}", expected_repr.0),
            TypeDesc::Tfield { .. } => format!("Tfield@{}", expected_repr.0),
            TypeDesc::Tnil => format!("Tnil@{}", expected_repr.0),
            TypeDesc::Tvariant(_) => format!("Tvariant@{}", expected_repr.0),
            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})@{}", expected_repr.0),
            TypeDesc::Tpoly { .. } => format!("Tpoly@{}", expected_repr.0),
            TypeDesc::Tpackage { .. } => format!("Tpackage@{}", expected_repr.0),
            TypeDesc::Tsubst(_) => format!("Tsubst@{}", expected_repr.0),
        }
    };

    // Look up constructor with disambiguation following OCaml's approach:
    // 1. For module-qualified constructors (Ldot), use direct module lookup
    // 2. For unqualified constructors (Lident), use disambiguation considering expected type
    let lid_txt = tctx.arena.get_longident(lid.txt);
    let lid_name = tctx.longident_last_name(lid_txt);
    let is_qualified = matches!(lid_txt, Longident::Ldot(..));
    let (cstr_desc, _cstr_path) = if is_qualified {
        if let Some((path, desc)) =
            lookup_predef_option_constructor(lid_txt, tctx.arena, env, tctx.type_ctx)
        {
            (desc, path)
        } else {
            let module_candidates = lookup_constructors_in_module(
                lid_txt,
                tctx.arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            );
            if let Some((path, desc)) = disambiguate_constructor_candidates(
                &module_candidates,
                expected_ty,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                (desc, path)
            } else {
                match env.find_constructor(&lid_name) {
                    Ok(desc) => (
                        desc.clone(),
                        Path::pident(Ident::create_persistent(&lid_name)),
                    ),
                    Err(_) => {
                        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
                            eprintln!(
                                "[type-pattern-cstr] unresolved name={} qualified=true stage=env.find_constructor expected={}",
                                lid_name,
                                debug_expected_ty()
                            );
                        }
                        return Err(TypeCoreError::NotAVariantType(lid_txt.clone()));
                    }
                }
            }
        }
    } else {
        // Unqualified: use disambiguation with expected type
        match disambiguate_constructor(
            &lid_name,
            expected_ty,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        ) {
            Some((path, desc)) => (desc, path),
            None => {
                match lookup_constructor_in_module(
                    lid_txt,
                    tctx.arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                ) {
                    Some((path, desc)) => (desc, path),
                    None => {
                        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
                            eprintln!(
                                "[type-pattern-cstr] unresolved name={} qualified=false stage=module-fallback expected={}",
                                lid_name,
                                debug_expected_ty()
                            );
                        }
                        return Err(TypeCoreError::NotAVariantType(lid_txt.clone()));
                    }
                }
            }
        }
    };

    // Instantiate constructor: creates fresh type variables shared between
    // cstr_res and cstr_args, matching OCaml's Ctype.instance_constructor.
    // For GADT constructors with existentials, process them in pattern context.
    let (inst_arg_types, result_ty) = if !cstr_desc.cstr_existentials.is_empty() {
        if let Some(newtype_lev) = tctx.newtype_level {
            let mut env_mut = env.clone();
            let result = crate::types::instance_constructor_in_pattern(
                ctx, &mut env_mut, newtype_lev, &cstr_desc,
            );
            // Note: env_mut has the new abstract types added, but since env is
            // immutable here, the abstract types are only visible through the
            // local_constraints (for GADT equation checking).
            result
        } else {
            crate::types::instance_constructor(ctx, &cstr_desc)
        }
    } else {
        crate::types::instance_constructor(ctx, &cstr_desc)
    };
    // PR#7214: use GADT unification only for generalized constructors
    // (not for toplevel lets or inside 'or' patterns)
    if cstr_desc.cstr_generalized && mode != PatternMode::SplittingOr {
        unify_pattern_types_gadt(tctx, loc, result_ty, expected_ty)?;
    } else {
        unify_pattern_types(tctx, loc, result_ty, expected_ty)?;
    }

    // Type check the argument pattern(s)
    let typed_args = match (inst_arg_types.as_slice(), arg) {
        (arg_types, Some(arg_pat)) if arg_types.len() == 1 => {
            // Single argument
            let typed_arg = type_pattern_inner(tctx, env, arg_pat, arg_types[0], mode, state, 0)?;
            vec![typed_arg]
        }
        (arg_types, Some(arg_pat)) if arg_types.len() > 1 => {
            // Multiple arguments - check if the pattern is a wildcard or tuple
            match &*arg_pat.ppat_desc {
                crate::parser::ast::PatternDesc::Ppat_any => {
                    // OCaml replicates Ppat_any for each constructor arg
                    let mut args = Vec::new();
                    for &arg_ty in arg_types {
                        let typed_arg =
                            type_pattern_inner(tctx, env, arg_pat, arg_ty, mode, state, 0)?;
                        args.push(typed_arg);
                    }
                    args
                }
                _ => {
                    // Tuple pattern - extract individual elements
                    let tuple_ty = ctx.new_tuple(arg_types.to_vec());
                    let typed_tuple =
                        type_pattern_inner(tctx, env, arg_pat, tuple_ty, mode, state, 0)?;
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

    // Match OCaml typecore.ml Ppat_variant:
    // - always build a single-tag row with Reither
    // - use `constant = (arg is None)`
    // - thread payload type into the row when present
    let arg_ty = arg.map(|_| ctx.new_var(None));
    let mut row_arg_types = Vec::new();
    if let Some(ty) = arg_ty {
        row_arg_types.push(ty);
    }
    let variant_ty = ctx.new_variant(crate::types::type_expr::RowDesc {
        row_fields: vec![(
            label.to_string(),
            crate::types::type_expr::RowField::Reither {
                constant: arg.is_none(),
                types: row_arg_types,
                matched: true,
                link: ctx.alloc_row_field(None),
            },
        )],
        row_more: ctx.new_var(None),
        row_closed: false,
        row_fixed: false,
        row_name: None,
    });
    unify_pattern_types(tctx, loc, variant_ty, expected_ty)?;

    let typed_arg = match (arg, arg_ty) {
        (Some(arg_pat), Some(arg_ty)) => Some(Box::new(type_pattern_inner(
            tctx, env, arg_pat, arg_ty, mode, state, 0,
        )?)),
        _ => None,
    };

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
    let debug_pattern_record = std::env::var_os("RUST_DEBUG_PATTERN_RECORD").is_some();
    let summarize_ty = |ty: TypeExprRef| -> String {
        let repr = ctx.repr(ty);
        let desc = ctx.get_desc(repr);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let args = args
                    .iter()
                    .map(|arg| ctx.repr(*arg).0.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{}#{}({})", path.name(), repr.0, args)
            }
            TypeDesc::Tvar(_) => format!("Tvar#{}", repr.0),
            TypeDesc::Tunivar(_) => format!("Tunivar#{}", repr.0),
            TypeDesc::Tlink(t) => format!("Tlink#{}->{}", repr.0, ctx.repr(*t).0),
            _ => format!("other#{}", repr.0),
        }
    };
    let has_dict_pattern_attr = has_dict_pattern_attribute(tctx.arena, &pat.ppat_attributes);
    let field_names: Vec<String> = fields
        .iter()
        .map(|field| tctx.longident_last_name(tctx.resolve_lid(field.lid.txt)))
        .collect();
    let closed_record = matches!(closed_flag, crate::parser::ast::ClosedFlag::Closed);
    // OCaml record patterns allow omitted fields even when syntactically closed;
    // `Closed` vs `Open` affects warning behavior, not candidate type matching.
    let match_record_fields_strictly = false;

    // OCaml: dict patterns are forced to type dict<'a>, independent of expected_ty shape.
    // This enables field-label disambiguation through the dict magic field.
    let record_ty = if has_dict_pattern_attr {
        ctx.new_constr(
            Path::pident(Ident::create_persistent(DICT_TYPE_NAME)),
            vec![ctx.new_var(None)],
        )
    } else {
        expected_ty
    };
    let disambiguation_ty = if has_dict_pattern_attr {
        // Dict patterns should not be steered by regular record label
        // disambiguation (`id`, `name`, ...). Field patterns are typed against
        // the dict payload itself.
        record_ty
    } else {
        select_record_type_for_fields(
            ctx,
            env,
            &mut tctx.persistent_env,
            &field_names,
            record_ty,
            None,
            match_record_fields_strictly,
        )
        .unwrap_or(record_ty)
    };
    let dict_field_ty = if has_dict_pattern_attr {
        let repr = ctx.repr(record_ty);
        let desc = ctx.get_desc(repr);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } if is_dict_type_path(path) && args.len() == 1 => {
                Some(args[0])
            }
            _ => Some(ctx.new_var(None)),
        }
    } else {
        None
    };
    if debug_pattern_record {
        let full_loc = tctx.arena.to_location(loc);
        eprintln!(
            "[pat-record] loc={}:{} fields={:?} expected={} record={} disamb={} closed={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            field_names,
            summarize_ty(expected_ty),
            summarize_ty(record_ty),
            summarize_ty(disambiguation_ty),
            closed_record
        );
    }

    // Type check each field pattern
    let mut typed_fields = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let resolved_lid = tctx.resolve_lid(field.lid.txt).clone();
        let field_name = tctx.longident_last_name(&resolved_lid);

        // Create fresh type variable for the field
        let base_field_ty = dict_field_ty.unwrap_or_else(|| ctx.new_var(None));
        let field_ty = if has_dict_pattern_attr && field.opt {
            env.type_option(ctx, base_field_ty)
        } else {
            base_field_ty
        };

        // Try to look up the label from the environment for type info
        let disambiguated = if has_dict_pattern_attr {
            None
        } else {
            disambiguate_label_for_record_fields(
                &field_name,
                disambiguation_ty,
                &field_names,
                match_record_fields_strictly,
                env,
                &mut tctx.persistent_env,
                ctx,
            )
            .or_else(|| {
                lookup_label_by_lid(
                    &resolved_lid,
                    tctx.arena,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                )
            })
        };
        if debug_pattern_record {
            let full_loc = tctx.arena.to_location(field.lid.loc);
            let chosen = disambiguated
                .as_ref()
                .map(|label| {
                    format!(
                        "{}@{} res={}",
                        label.lbl_name,
                        label.lbl_pos,
                        summarize_ty(label.lbl_res)
                    )
                })
                .unwrap_or_else(|| "<none>".to_string());
            eprintln!(
                "[pat-record] field loc={}:{} name={} chosen={}",
                full_loc.loc_start.line,
                full_loc.loc_start.column(),
                field_name,
                chosen
            );
        }

        let label_desc = if let Some(env_label) = disambiguated {
                let (_poly_vars, ty_arg, ty_res) =
                    crate::types::ctype::instance_label(ctx, false, &env_label);
                // Best-effort unification to propagate type info
                let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, record_ty);
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
                    lbl_optional: field.opt,
                    lbl_pos: idx as i32,
                    lbl_all: crate::types::LabelArrayRef(0),
                    lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                    lbl_private: crate::types::PrivateFlag::Public,
                    lbl_loc: tctx.arena.to_location(field.lid.loc),
                    lbl_attributes: vec![],
                }
            };

        // process_optional_label: if the label is optional and the user did NOT write '?',
        // wrap the pattern in Some(...) before type checking.
        // This matches OCaml's typecore.ml process_optional_label behavior.
        let parsed_pat = tctx.arena.get_pat(field.pat);
        let typed_pat = if label_desc.lbl_optional && !field.opt {
            // field_ty is option<T> — extract T to type-check the inner pattern
            let inner_ty = crate::types::ctype::extract_option_type(ctx, field_ty)
                .unwrap_or(field_ty);
            let typed_inner = type_pattern_inner(tctx, env, parsed_pat, inner_ty, mode, state, 0)?;
            // Wrap in Tpat_construct("Some", [typed_inner]) with type option<T>
            let some_lid = Located { txt: tctx.arena.some_lid(), loc: parsed_pat.ppat_loc };
            let some_cstr = make_some_constructor(ctx, field_ty);
            Pattern::new(
                PatternDesc::Tpat_construct(some_lid, some_cstr, vec![typed_inner]),
                parsed_pat.ppat_loc,
                field_ty,
                EnvRef(0),
                Attributes::new(),
            )
        } else {
            type_pattern_inner(tctx, env, parsed_pat, field_ty, mode, state, 0)?
        };
        typed_fields.push((field.lid.clone(), label_desc, typed_pat, field.opt));
    }

    // OCaml unifies the inferred record type with the pattern expected type.
    unify_pattern_types(tctx, loc, record_ty, expected_ty)?;

    // Invariant: records are sorted in the typed tree (by label position)
    // Matches OCaml typecore.ml: List.sort (fun (_, lbl1, _, _) (_, lbl2, _, _) -> compare lbl1.lbl_pos lbl2.lbl_pos)
    typed_fields.sort_by_key(|(_, label_desc, _, _)| label_desc.lbl_pos);

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
    let ctx = tctx.type_ctx;

    // Match OCaml typecore.ml Ppat_constraint flow:
    // begin_def; transl_simple_type_delayed; end_def; generalize_structure;
    // then use two independent instances (constraint ty and inner-pattern ty).
    ctx.begin_def();
    let (typed_ctype, ctype_ty) = transl_type_delayed(tctx, env, core_type, true)?;
    ctx.end_def();
    let var_level = ctx.current_level();
    crate::types::generalize_structure(ctx, var_level, ctype_ty);

    let constraint_ty = crate::types::instance(ctx, ctype_ty);
    let inner_expected_ty = crate::types::instance(ctx, ctype_ty);

    unify_pattern_types(tctx, loc, constraint_ty, expected_ty)?;

    let typed_inner = type_pattern_inner(tctx, env, inner_pat, inner_expected_ty, mode, state, 0)?;

    // OCaml uses inner pattern attributes for Tpat_constraint extra.
    let constraint_extra = (
        crate::types::typedtree::PatExtra::Tpat_constraint(typed_ctype),
        loc.clone(),
        inner_pat.ppat_attributes.clone(),
    );

    // OCaml converts Tpat_var to Tpat_alias(Tpat_any, id, name) and replaces extras.
    // OCaml: {p with pat_desc = Tpat_any; pat_attributes = []} — keeps p.pat_type
    // which is expected_ty' (the second instance of the constraint type).
    let typed_inner = match typed_inner.pat_desc.clone() {
        crate::types::typedtree::PatternDesc::Tpat_var(id, name) => {
            // Use typed_inner.pat_type (= inner_expected_ty, instance 2)
            // to match OCaml's {p with pat_desc = Tpat_any} behavior.
            let any_pat = Pattern {
                pat_desc: crate::types::typedtree::PatternDesc::Tpat_any,
                pat_attributes: Attributes::new(),
                pat_type: typed_inner.pat_type,
                ..typed_inner.clone()
            };
            Pattern {
                pat_desc: crate::types::typedtree::PatternDesc::Tpat_alias(
                    Box::new(any_pat),
                    id,
                    name,
                ),
                pat_type: constraint_ty,
                pat_extra: vec![constraint_extra],
                ..typed_inner
            }
        }
        _ => {
            let mut typed_inner = typed_inner;
            typed_inner.pat_type = constraint_ty;
            let mut extras = Vec::with_capacity(typed_inner.pat_extra.len() + 1);
            extras.push(constraint_extra);
            extras.extend(typed_inner.pat_extra.into_iter());
            typed_inner.pat_extra = extras;
            typed_inner
        }
    };

    Ok(typed_inner)
}

/// Type check constraint pattern: Ppat_constraint(Ppat_var, Ptyp_poly).
/// OCaml typecore.ml:1249-1274: explicitly polymorphic type annotation.
/// Uses instance_poly ~keep_names:true to preserve type variable names.
#[allow(clippy::too_many_arguments)]
fn type_pattern_constraint_poly_var(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    inner_pat: &ParsedPattern,
    name: crate::parser::ast::StringLoc,
    core_type: &crate::parser::ast::CoreType,
    expected_ty: TypeExprRef,
    _mode: PatternMode,
    state: &mut PatternState,
    pat: &ParsedPattern,
) -> TypeCoreResult<Pattern> {
    let ctx = tctx.type_ctx;

    // OCaml: lloc = inner_pat.ppat_loc (used for unify and enter_variable)
    let lloc = inner_pat.ppat_loc;

    // OCaml: let cty, force = Typetexp.transl_simple_type_delayed !env sty in
    let (typed_ctype, ctype_ty) = transl_type_delayed(tctx, env, core_type, true)?;

    // OCaml: unify_pat_types lloc !env ty expected_ty
    unify_pattern_types(tctx, lloc, ctype_ty, expected_ty)?;

    // OCaml: match ty.desc with Tpoly(body, tyl) -> ...
    let ctype_repr = ctx.repr(ctype_ty);
    let ctype_desc = ctx.get_desc(ctype_repr);
    match &*ctype_desc {
        TypeDesc::Tpoly { body, vars } => {
            let body = *body;
            let vars: Vec<TypeExprRef> = vars.clone();
            drop(ctype_desc);

            // OCaml: begin_def (); let _, ty' = instance_poly ~keep_names:true false tyl body in end_def (); generalize ty'
            ctx.begin_def();
            let (_inst_vars, ty_prime) =
                crate::types::ctype::instance_poly(ctx, true, false, &vars, body);
            ctx.end_def();
            crate::types::ctype::generalize(ctx, ty_prime);

            // OCaml: let id = enter_variable lloc name ty' in
            let id = state.enter_variable(lloc, &name, ty_prime, false, false, tctx.arena)?;

            // OCaml: pat_desc = Tpat_var(id, name); pat_type = ty (the Tpoly type)
            // pat_extra = [(Tpat_constraint cty, loc, sp.ppat_attributes)]
            let constraint_extra = (
                crate::types::typedtree::PatExtra::Tpat_constraint(typed_ctype),
                loc.clone(),
                pat.ppat_attributes.clone(),
            );

            Ok(Pattern {
                pat_desc: PatternDesc::Tpat_var(id, convert_located_stridx(&name, tctx.arena)),
                pat_loc: lloc,
                pat_type: ctype_ty,
                pat_env: EnvRef(0),
                pat_attributes: Attributes::new(),
                pat_extra: vec![constraint_extra],
            })
        }
        _ => {
            drop(ctype_desc);
            // Fallback: shouldn't happen for Ptyp_poly but be safe
            type_pattern_constraint(
                tctx, env, loc, inner_pat, core_type, expected_ty, _mode, state, pat,
            )
        }
    }
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

    // Interval patterns are desugared to or-patterns in the typed tree.
    // OCaml expands the full range into a nested Tpat_or tree of individual constants.
    let (start_val, end_val) = match (&constant1, &constant2) {
        (Constant::Char(c1), Constant::Char(c2)) => (*c1, *c2),
        (Constant::Int(i1), Constant::Int(i2)) => (*i1 as i32, *i2 as i32),
        _ => return Err(TypeCoreError::InvalidInterval),
    };

    let make_const = |val: i32| -> Constant {
        if matches!(constant1, Constant::Char(_)) {
            Constant::Char(val)
        } else {
            Constant::Int(val as i64)
        }
    };

    // Build all constant patterns for the range
    let mut patterns: Vec<Pattern> = (start_val..=end_val)
        .map(|val| {
            Pattern::new(
                PatternDesc::Tpat_constant(make_const(val)),
                loc.clone(),
                expected_ty,
                EnvRef(0),
                Attributes::new(),
            )
        })
        .collect();

    // Build right-associative nested Tpat_or tree
    let mut result = patterns.pop().unwrap();
    while let Some(pat_left) = patterns.pop() {
        result = Pattern::new(
            PatternDesc::Tpat_or(Box::new(pat_left), Box::new(result), None),
            loc.clone(),
            expected_ty,
            EnvRef(0),
            Attributes::new(),
        );
    }

    result.pat_attributes = pat.ppat_attributes.clone();

    Ok(result)
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
    let exn_ty = crate::types::ctype::instance(ctx, ctx.predef_exn());

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
    let _mod_path = Path::pident(Ident::create_persistent(
        tctx.longident_last_name(mod_lid_txt),
    ));

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

fn type_exp<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    expr: &ParsedExpression,
    context: Option<TypeClashContext>,
) -> TypeCoreResult<Expression> {
    let expected_ty = tctx.type_ctx.new_var(None);
    type_expect(tctx, env, expr, expected_ty, context)
}

/// Match OCaml `type_statement`:
/// begin_def; type_exp; end_def; expand_head(exp_type); unify with unit.
fn type_statement<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    expr: &ParsedExpression,
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;
    ctx.begin_def();
    let typed = type_exp(tctx, env, expr, None)?;
    ctx.end_def();

    // Keep OCaml side effects from `expand_head env exp.exp_type`:
    // this drives abbreviation memo/env synchronization in statement typing.
    let _ = crate::types::ctype::expand_head(ctx, env, typed.exp_type);

    let expected_ty = env.type_unit(ctx);
    unify_expression_types(tctx, typed.exp_loc, typed.exp_type, expected_ty, None)?;
    Ok(typed)
}

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
    // Keep alias expansion aligned with the current typing environment.
    // OCaml passes `env` through all Ctype operations; in Rust we update the
    // unify-state snapshot on each type_expect entry.
    tctx.set_unify_env(env);

    match &*expr.pexp_desc {
        ED::Pexp_ident(lid) => {
            // Identifier expression
            let longident = tctx.arena.get_longident(lid.txt);
            let (path, desc) = env.lookup_value_by_lid(
                longident,
                tctx.arena,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )?;

            let ty = crate::types::instance(ctx, desc.val_type);
            if std::env::var_os("RUST_DEBUG_IDENT_LEVELS").is_some() {
                let path_name = path.name();
                if path_name == "foo1"
                    || path_name == "React.string"
                    || path_name == "ReactDOM.someElement"
                    || path_name == "pt"
                    || path_name == "st"
                    || path_name == "dir"
                    || path_name == "make_player"
                    || path_name == "make_enemy"
                    || path_name == "p1"
                    || path_name == "p2"
                    || path_name == "v0"
                    || path_name == "v1"
                    || path_name == "v3"
                    || path_name == "img"
                    || path_name == "empty"
                    || path_name == "Js.Undefined.empty"
                    || path_name == "f"
                    || path_name == "v"
                    || path_name == "add"
                    || path_name == "Js.String2.substrAtMost"
                    || path_name == "Js.String2.lastIndexOfFrom"
                    || path_name == "basicComponent"
                    || path_name == "React.jsx"
                    || path_name == "ComponentWithOptionalProps.make"
                    || path_name == "Spice.stringToJson"
                    || path_name == "Spice.stringFromJson"
                    || path_name == "setActive"
                    || path_name == "merge2"
                {
                    let val_ty = ctx.repr(desc.val_type);
                    let inst_ty = ctx.repr(ty);
                    let val_desc = ctx.get_desc(val_ty);
                    let inst_desc = ctx.get_desc(inst_ty);
                    let val_args = match &*val_desc {
                        TypeDesc::Tconstr { args, .. } => Some(args.clone()),
                        _ => None,
                    };
                    let inst_args = match &*inst_desc {
                        TypeDesc::Tconstr { args, .. } => Some(args.clone()),
                        _ => None,
                    };
                    let summarize = |d: &TypeDesc| match d {
                        TypeDesc::Tconstr { path, args, .. } => {
                            format!("Tconstr({},args={})", path.name(), args.len())
                        }
                        TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                        TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                        TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                        TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                        TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                        TypeDesc::Tobject { .. } => "Tobject".to_string(),
                        TypeDesc::Tfield { .. } => "Tfield".to_string(),
                        TypeDesc::Tnil => "Tnil".to_string(),
                        TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                        TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                        TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                    };
                    eprintln!(
                        "[ident-level] path={} val_id={} val_level={} val_desc={} inst_id={} inst_level={} inst_desc={}",
                        path_name,
                        val_ty.0,
                        ctx.get_level(val_ty),
                        summarize(&val_desc),
                        inst_ty.0,
                        ctx.get_level(inst_ty),
                        summarize(&inst_desc),
                    );
                    if let Some(args) = val_args {
                        let parts: Vec<String> = args
                            .iter()
                            .map(|a| {
                                let r = ctx.repr(*a);
                                format!("{}@{}", r.0, ctx.get_level(r))
                            })
                            .collect();
                        eprintln!("[ident-level] path={} val_args={}", path_name, parts.join(","));
                    }
                    if let Some(args) = inst_args {
                        let parts: Vec<String> = args
                            .iter()
                            .map(|a| {
                                let r = ctx.repr(*a);
                                format!("{}@{}", r.0, ctx.get_level(r))
                            })
                            .collect();
                        eprintln!(
                            "[ident-level] path={} inst_args={}",
                            path_name,
                            parts.join(",")
                        );
                    }
                    if let TypeDesc::Tarrow { arg, ret, .. } = &*val_desc {
                        let arg_r = ctx.repr(arg.typ);
                        let ret_r = ctx.repr(*ret);
                        eprintln!(
                            "[ident-level] path={} val_arrow arg={}@{} ret={}@{}",
                            path_name,
                            arg_r.0,
                            ctx.get_level(arg_r),
                            ret_r.0,
                            ctx.get_level(ret_r)
                        );
                        if path_name == "merge2" {
                            let dump_tconstr_args =
                                |label: &str, ty: TypeExprRef, ctx: &TypeContext<'_>| {
                                    let ty = ctx.repr(ty);
                                    let desc = ctx.get_desc(ty);
                                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                                        let args_dump = args
                                            .iter()
                                            .map(|a| {
                                                let ar = ctx.repr(*a);
                                                format!("{}@{}", ar.0, ctx.get_level(ar))
                                            })
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        eprintln!(
                                            "[ident-level] path=merge2 {}={}#{}@{}({})",
                                            label,
                                            path.name(),
                                            ty.0,
                                            ctx.get_level(ty),
                                            args_dump
                                        );
                                    } else {
                                        eprintln!(
                                            "[ident-level] path=merge2 {}=non-constr#{}@{}",
                                            label,
                                            ty.0,
                                            ctx.get_level(ty)
                                        );
                                    }
                                };
                            dump_tconstr_args("val_arg", arg_r, ctx);
                            dump_tconstr_args("val_ret", ret_r, ctx);
                            if let TypeDesc::Tarrow { arg, ret, .. } = &*ctx.get_desc(ret_r) {
                                dump_tconstr_args("val_ret_arg", ctx.repr(arg.typ), ctx);
                                dump_tconstr_args("val_ret_ret", ctx.repr(*ret), ctx);
                            }
                            if let Ok(decl) =
                                env.lookup_type(&Path::pident(crate::ident::Ident::create_local("t")))
                            {
                                let params = decl
                                    .type_params
                                    .iter()
                                    .map(|p| {
                                        let pr = ctx.repr(*p);
                                        format!("{}@{}", pr.0, ctx.get_level(pr))
                                    })
                                    .collect::<Vec<_>>()
                                    .join(",");
                                eprintln!("[ident-level] path=merge2 decl_t_params={}", params);
                            }
                        }
                        if path_name == "Js.String2.substrAtMost"
                            || path_name == "Js.String2.lastIndexOfFrom"
                            || path_name == "f"
                        {
                            let mut chain = vec![format!("arg:{}@{}", arg_r.0, ctx.get_level(arg_r))];
                            let mut cursor = ret_r;
                            for _ in 0..8 {
                                let cursor_desc = ctx.get_desc(cursor);
                                match &*cursor_desc {
                                    TypeDesc::Tarrow { arg, ret, .. } => {
                                        let a = ctx.repr(arg.typ);
                                        let r = ctx.repr(*ret);
                                        chain.push(format!("arg:{}@{}", a.0, ctx.get_level(a)));
                                        cursor = r;
                                    }
                                    TypeDesc::Tconstr { path, args, .. } => {
                                        let args_summary = args
                                            .iter()
                                            .map(|t| {
                                                let t = ctx.repr(*t);
                                                format!("{}@{}", t.0, ctx.get_level(t))
                                            })
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        chain.push(format!(
                                            "ret:{}#{}@{}({})",
                                            path.name(),
                                            cursor.0,
                                            ctx.get_level(cursor),
                                            args_summary
                                        ));
                                        break;
                                    }
                                    other => {
                                        chain.push(format!("ret:{:?}", other));
                                        break;
                                    }
                                }
                            }
                            eprintln!(
                                "[ident-level] path={} val_arrow_chain {}",
                                path_name,
                                chain.join(" -> ")
                            );
                        }
                        if path_name == "basicComponent" {
                            let ret_desc = ctx.get_desc(ret_r);
                            if let TypeDesc::Tconstr { path, args, .. } = &*ret_desc {
                                let parts: Vec<String> = args
                                    .iter()
                                    .map(|t| {
                                        let t = ctx.repr(*t);
                                        format!("{}@{}", t.0, ctx.get_level(t))
                                    })
                                    .collect();
                                eprintln!(
                                    "[ident-level] path=basicComponent val_ret={} args={}",
                                    path.name(),
                                    parts.join(",")
                                );
                            }
                        }
                    }
                    if let TypeDesc::Tarrow { arg, ret, .. } = &*inst_desc {
                        let arg_r = ctx.repr(arg.typ);
                        let ret_r = ctx.repr(*ret);
                        eprintln!(
                            "[ident-level] path={} inst_arrow arg={}@{} ret={}@{}",
                            path_name,
                            arg_r.0,
                            ctx.get_level(arg_r),
                            ret_r.0,
                            ctx.get_level(ret_r)
                        );
                        if path_name == "merge2" {
                            let dump_tconstr_args =
                                |label: &str, ty: TypeExprRef, ctx: &TypeContext<'_>| {
                                    let ty = ctx.repr(ty);
                                    let desc = ctx.get_desc(ty);
                                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                                        let args_dump = args
                                            .iter()
                                            .map(|a| {
                                                let ar = ctx.repr(*a);
                                                format!("{}@{}", ar.0, ctx.get_level(ar))
                                            })
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        eprintln!(
                                            "[ident-level] path=merge2 {}={}#{}@{}({})",
                                            label,
                                            path.name(),
                                            ty.0,
                                            ctx.get_level(ty),
                                            args_dump
                                        );
                                    } else {
                                        eprintln!(
                                            "[ident-level] path=merge2 {}=non-constr#{}@{}",
                                            label,
                                            ty.0,
                                            ctx.get_level(ty)
                                        );
                                    }
                                };
                            dump_tconstr_args("inst_arg", arg_r, ctx);
                            dump_tconstr_args("inst_ret", ret_r, ctx);
                            if let TypeDesc::Tarrow { arg, ret, .. } = &*ctx.get_desc(ret_r) {
                                dump_tconstr_args("inst_ret_arg", ctx.repr(arg.typ), ctx);
                                dump_tconstr_args("inst_ret_ret", ctx.repr(*ret), ctx);
                            }
                            if let Ok(decl) =
                                env.lookup_type(&Path::pident(crate::ident::Ident::create_local("t")))
                            {
                                let params = decl
                                    .type_params
                                    .iter()
                                    .map(|p| {
                                        let pr = ctx.repr(*p);
                                        format!("{}@{}", pr.0, ctx.get_level(pr))
                                    })
                                    .collect::<Vec<_>>()
                                    .join(",");
                                eprintln!("[ident-level] path=merge2 decl_t_params={}", params);
                            }
                        }
                        if path_name == "Js.String2.substrAtMost"
                            || path_name == "Js.String2.lastIndexOfFrom"
                            || path_name == "f"
                        {
                            let mut chain = vec![format!("arg:{}@{}", arg_r.0, ctx.get_level(arg_r))];
                            let mut cursor = ret_r;
                            for _ in 0..8 {
                                let cursor_desc = ctx.get_desc(cursor);
                                match &*cursor_desc {
                                    TypeDesc::Tarrow { arg, ret, .. } => {
                                        let a = ctx.repr(arg.typ);
                                        let r = ctx.repr(*ret);
                                        chain.push(format!("arg:{}@{}", a.0, ctx.get_level(a)));
                                        cursor = r;
                                    }
                                    TypeDesc::Tconstr { path, args, .. } => {
                                        let args_summary = args
                                            .iter()
                                            .map(|t| {
                                                let t = ctx.repr(*t);
                                                format!("{}@{}", t.0, ctx.get_level(t))
                                            })
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        chain.push(format!(
                                            "ret:{}#{}@{}({})",
                                            path.name(),
                                            cursor.0,
                                            ctx.get_level(cursor),
                                            args_summary
                                        ));
                                        break;
                                    }
                                    other => {
                                        chain.push(format!("ret:{:?}", other));
                                        break;
                                    }
                                }
                            }
                            eprintln!(
                                "[ident-level] path={} inst_arrow_chain {}",
                                path_name,
                                chain.join(" -> ")
                            );
                        }
                        if path_name == "basicComponent" {
                            let ret_desc = ctx.get_desc(ret_r);
                            if let TypeDesc::Tconstr { path, args, .. } = &*ret_desc {
                                let parts: Vec<String> = args
                                    .iter()
                                    .map(|t| {
                                        let t = ctx.repr(*t);
                                        format!("{}@{}", t.0, ctx.get_level(t))
                                    })
                                    .collect();
                                eprintln!(
                                    "[ident-level] path=basicComponent inst_ret={} args={}",
                                    path.name(),
                                    parts.join(",")
                                );
                            }
                        }
                    }
                }
            }
            if std::env::var_os("RUST_DEBUG_IDENT_LEVELS").is_some() {
                let path_name = path.name();
                if path_name == "N.minimum"
                    || path_name == "N.maximum"
                    || path_name == "v"
                    || path_name == "N.fromArray"
                    || path_name == "N.eq"
                    || path_name == "A.makeBy"
                    || path_name == "img"
                    || path_name == "dd"
                    || path_name == "merge2"
                {
                    let val_ty = ctx.repr(desc.val_type);
                    let inst_ty = ctx.repr(ty);
                    eprintln!(
                        "[ident-level] path={} val_id={} val_level={} inst_id={} inst_level={}",
                        path_name,
                        val_ty.0,
                        ctx.get_level(val_ty),
                        inst_ty.0,
                        ctx.get_level(inst_ty),
                    );
                }
            }
            if std::env::var_os("RUST_DEBUG_IDENT_TRACE").is_some() {
                let path_name = path.name();
                if path_name == "N.fromArray"
                    || path_name == "A.makeBy"
                    || path_name == "N.eq"
                    || path_name == "dd"
                    || path_name == "Ord.compare"
                    || path_name == "x"
                    || path_name == "v"
                    || path_name == "X.forEach"
                    || path_name == "X.i"
                    || path_name == "basicComponent"
                    || path_name == "React.jsx"
                    || path_name == "ComponentWithOptionalProps.make"
                    || path_name == "merge2"
                {
                    let val_ty = ctx.repr(desc.val_type);
                    let inst_ty = ctx.repr(ty);
                    let expected_repr = ctx.repr(expected_ty);
                    let summarize = |ty: TypeExprRef| {
                        let desc = ctx.get_desc(ty);
                        match &*desc {
                            TypeDesc::Tconstr { path, args, .. } => {
                                format!("Tconstr({},args={})", path.name(), args.len())
                            }
                            TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                            TypeDesc::Tvar(_) => "Tvar".to_string(),
                            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                            TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                            TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                            TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                            TypeDesc::Tobject { .. } => "Tobject".to_string(),
                            TypeDesc::Tfield { .. } => "Tfield".to_string(),
                            TypeDesc::Tnil => "Tnil".to_string(),
                            TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                            TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                            TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                        }
                    };
                    let full_loc = tctx.arena.to_location(loc);
                    let simple_memo = ctx.get_abbrev_memo(ctx.simple_abbrevs_memo());
                    eprintln!(
                        "[ident-trace] path={} loc={}:{} env_id={} val_ty={}({}) inst_ty={}({}) expected_ty={}({}) simple={:?}",
                        path_name,
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        env.id(),
                        val_ty.0,
                        summarize(val_ty),
                        inst_ty.0,
                        summarize(inst_ty),
                        expected_repr.0,
                        summarize(expected_repr),
                        simple_memo
                    );
                    if path_name == "X.forEach" {
                        let describe = |ty: TypeExprRef| -> String {
                            let ty = ctx.repr(ty);
                            let desc = ctx.get_desc(ty);
                            match &*desc {
                                TypeDesc::Tconstr { path, args, .. } => {
                                    let args = args
                                        .iter()
                                        .map(|a| ctx.repr(*a).0.to_string())
                                        .collect::<Vec<_>>()
                                        .join(",");
                                    format!("{}#{}({})", path.name(), ty.0, args)
                                }
                                TypeDesc::Tarrow { arg, ret, .. } => {
                                    format!("arrow#{}({}->{})", ty.0, ctx.repr(arg.typ).0, ctx.repr(*ret).0)
                                }
                                TypeDesc::Tvar(_) => format!("tvar#{}", ty.0),
                                TypeDesc::Tlink(t) => format!("tlink#{}->{}", ty.0, ctx.repr(*t).0),
                                _ => format!("other#{}", ty.0),
                            }
                        };
                        let val1 = ctx.repr(desc.val_type);
                        let inst1 = ctx.repr(ty);
                        let val_desc = ctx.get_desc(val1);
                        if let TypeDesc::Tarrow { arg, ret, .. } = &*val_desc {
                            let ret = ctx.repr(*ret);
                            let ret_desc = ctx.get_desc(ret);
                            if let TypeDesc::Tarrow { arg: arg2, ret: ret2, .. } = &*ret_desc {
                                eprintln!(
                                    "[ident-trace-x-foreach] val a1={} a2={} r2={} desc_a1={} desc_a2={}",
                                    ctx.repr(arg.typ).0,
                                    ctx.repr(arg2.typ).0,
                                    ctx.repr(*ret2).0,
                                    describe(arg.typ),
                                    describe(arg2.typ),
                                );
                                let a1_desc = ctx.get_desc(ctx.repr(arg.typ));
                                if let TypeDesc::Tconstr { args, .. } = &*a1_desc {
                                    if let Some(first) = args.first() {
                                        eprintln!(
                                            "[ident-trace-x-foreach] val a1_inner={}",
                                            describe(*first)
                                        );
                                    }
                                }
                                let a2_desc = ctx.get_desc(ctx.repr(arg2.typ));
                                if let TypeDesc::Tconstr { args, .. } = &*a2_desc {
                                    if let Some(first) = args.first() {
                                        eprintln!(
                                            "[ident-trace-x-foreach] val a2_inner={}",
                                            describe(*first)
                                        );
                                    }
                                }
                            }
                        }
                        let inst_desc = ctx.get_desc(inst1);
                        if let TypeDesc::Tarrow { arg, ret, .. } = &*inst_desc {
                            let ret = ctx.repr(*ret);
                            let ret_desc = ctx.get_desc(ret);
                            if let TypeDesc::Tarrow { arg: arg2, ret: ret2, .. } = &*ret_desc {
                                eprintln!(
                                    "[ident-trace-x-foreach] inst a1={} a2={} r2={} desc_a1={} desc_a2={}",
                                    ctx.repr(arg.typ).0,
                                    ctx.repr(arg2.typ).0,
                                    ctx.repr(*ret2).0,
                                    describe(arg.typ),
                                    describe(arg2.typ),
                                );
                                let a1_desc = ctx.get_desc(ctx.repr(arg.typ));
                                if let TypeDesc::Tconstr { args, .. } = &*a1_desc {
                                    if let Some(first) = args.first() {
                                        eprintln!(
                                            "[ident-trace-x-foreach] inst a1_inner={}",
                                            describe(*first)
                                        );
                                    }
                                }
                                let a2_desc = ctx.get_desc(ctx.repr(arg2.typ));
                                if let TypeDesc::Tconstr { args, .. } = &*a2_desc {
                                    if let Some(first) = args.first() {
                                        eprintln!(
                                            "[ident-trace-x-foreach] inst a2_inner={}",
                                            describe(*first)
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            rue_unify(tctx, loc, ty, expected_ty, context)?;

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

            let debug_unknown_const = std::env::var_os("RUST_DEBUG_UNKNOWN_CONST").is_some()
                && matches!(&constant, Constant::String(s, _) if s == "Unknown");
            if debug_unknown_const {
                let ty_repr = ctx.repr(ty);
                let expected_repr = ctx.repr(expected_ty);
                let summarize = |t: TypeExprRef| {
                    let d = ctx.get_desc(t);
                    match &*d {
                        TypeDesc::Tconstr { path, abbrev, .. } => {
                            format!(
                                "Tconstr({}) abbrev={:?} memo={:?}",
                                path.name(),
                                abbrev,
                                ctx.get_abbrev_memo(*abbrev)
                            )
                        }
                        TypeDesc::Tlink(target) => format!("Tlink({})", ctx.repr(*target).0),
                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                        TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                        TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                        TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                        TypeDesc::Tobject { .. } => "Tobject".to_string(),
                        TypeDesc::Tfield { .. } => "Tfield".to_string(),
                        TypeDesc::Tnil => "Tnil".to_string(),
                        TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                        TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                        TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                        TypeDesc::Tsubst(target) => format!("Tsubst({})", ctx.repr(*target).0),
                    }
                };
                eprintln!(
                    "[unknown-const] stage=before_unify ty={}@{} {} expected={}@{} {}",
                    ty_repr.0,
                    ctx.get_level(ty_repr),
                    summarize(ty_repr),
                    expected_repr.0,
                    ctx.get_level(expected_repr),
                    summarize(expected_repr)
                );
            }

            // OCaml: rue { ... exp_type = type_constant cst; ... }
            rue_unify(tctx, loc, ty, expected_ty, context)?;

            if debug_unknown_const {
                let ty_repr = ctx.repr(ty);
                let expected_repr = ctx.repr(expected_ty);
                eprintln!(
                    "[unknown-const] stage=after_unify ty={}@{} expected={}@{}",
                    ty_repr.0,
                    ctx.get_level(ty_repr),
                    expected_repr.0,
                    ctx.get_level(expected_repr)
                );
            }

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

            // Create tuple type and unify (instance generic expected_ty to avoid corruption)
            let tuple_ty = ctx.new_tuple(elem_types.clone());
            let eff_expected = instance_if_generic(ctx, expected_ty);
            unify_expression_types(tctx, loc, tuple_ty, eff_expected, context.clone())?;

            // Type check each element
            let mut typed_exprs = Vec::new();
            for (e, ty) in exprs.iter().zip(elem_types.iter()) {
                let typed_expr = type_expect(tctx, env, tctx.arena.get_expr(*e), *ty, None)?;
                typed_exprs.push(typed_expr);
            }

            // Keep sharing: create fresh Ttuple from sub-expression types
            // (matches OCaml: exp_type = newty (Ttuple (List.map (fun e -> e.exp_type) expl)))
            let result_ty =
                ctx.new_tuple(typed_exprs.iter().map(|e| e.exp_type).collect());
            Ok(Expression::new(
                ExpressionDesc::Texp_tuple(typed_exprs),
                loc,
                result_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body_idx) = **inner;
            // Let expression
            // OCaml does NOT reset typetexp.type_variables for local Pexp_let.
            // reset_type_variables happens at top-level expression/binding entry.
            let (typed_bindings, new_env, unpacks) =
                type_let_bindings(tctx, env, *rec_flag, bindings)?;

            // Type check body in extended environment
            let body = tctx.arena.get_expr(*body_idx);
            let typed_body = type_expect(tctx, &new_env, body, expected_ty, None)?;
            let typed_body = wrap_module_unpacks_in_expression(
                tctx,
                &new_env,
                typed_body,
                &unpacks,
                body.pexp_loc,
            );
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
            let e1 = tctx.arena.get_expr(*e1_idx);
            let typed_e1 = type_statement(tctx, env, e1)?;

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
            let bool_ty = ctx.predef_bool();

            // Condition should be bool
            let cond = tctx.arena.get_expr(*cond_idx);
            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;
            let then_branch = tctx.arena.get_expr(*then_idx);
            let else_branch = else_idx.map(|idx| tctx.arena.get_expr(idx));

            match else_branch {
                Some(else_branch) => {
                    // OCaml keeps sharing by unifying else with then.exp_type.
                    let typed_then = type_expect(tctx, env, then_branch, expected_ty, None)?;
                    let typed_else = type_expect(tctx, env, else_branch, expected_ty, None)?;
                    unify_expression_types(
                        tctx,
                        loc,
                        typed_else.exp_type,
                        typed_then.exp_type,
                        context,
                    )?;
                    let then_exp_type = typed_then.exp_type;

                    Ok(Expression::new(
                        ExpressionDesc::Texp_ifthenelse(
                            Box::new(typed_cond),
                            Box::new(typed_then),
                            Some(Box::new(typed_else)),
                        ),
                        loc,
                        then_exp_type,
                        EnvRef(0),
                        expr.pexp_attributes.clone(),
                    ))
                }
                None => {
                    // OCaml: rue { ... exp_type = ifso.exp_type; ... }
                    // Match OCaml typecore.ml: type the `then` branch against
                    // Predef.type_unit (generic singleton), not instance_def.
                    let unit_ty = ctx.predef_unit();
                    let typed_then = type_expect(tctx, env, then_branch, unit_ty, None)?;
                    let then_exp_type = typed_then.exp_type;
                    rue_unify(tctx, loc, then_exp_type, expected_ty, context)?;

                    Ok(Expression::new(
                        ExpressionDesc::Texp_ifthenelse(
                            Box::new(typed_cond),
                            Box::new(typed_then),
                            None,
                        ),
                        loc,
                        then_exp_type,
                        EnvRef(0),
                        expr.pexp_attributes.clone(),
                    ))
                }
            }
        }

        ED::Pexp_while(cond_idx, body_idx) => {
            // While loop
            // OCaml passes Predef.type_bool/unit to type_expect; rue instances each.
            // Use separate unit types for body and result (matching OCaml's rue pattern).
            let bool_ty = ctx.predef_bool();

            let cond = tctx.arena.get_expr(*cond_idx);
            let typed_cond = type_expect(tctx, env, cond, bool_ty, None)?;
            let body = tctx.arena.get_expr(*body_idx);
            let typed_body = type_statement(tctx, env, body)?;

            // OCaml: rue { ... exp_type = instance_def Predef.type_unit; ... }
            // Keep original argument order to preserve Tlink direction.
            let result_unit_ty = env.type_unit(ctx);
            let inst_expected = instance_if_generic(ctx, expected_ty);
            unify_expression_types(tctx, loc, inst_expected, result_unit_ty, context)?;

            Ok(Expression::new(
                ExpressionDesc::Texp_while(Box::new(typed_cond), Box::new(typed_body)),
                loc,
                result_unit_ty,
                EnvRef(0),
                expr.pexp_attributes.clone(),
            ))
        }

        ED::Pexp_assert(e_idx) => {
            // Assert expression
            let bool_ty = ctx.predef_bool();

            let e = tctx.arena.get_expr(*e_idx);
            let typed_e = type_expect(tctx, env, e, bool_ty, None)?;

            // assert(false) has the expected type (polymorphic), others have type unit
            let exp_type = match &typed_e.exp_desc {
                ExpressionDesc::Texp_construct(_, cd, _) if cd.cstr_name == "false" => {
                    crate::types::instance(ctx, expected_ty)
                }
                _ => {
                    // OCaml: rue { ... exp_type = instance_def Predef.type_unit; ... }
                    // Keep original argument order to preserve Tlink direction.
                    let unit_ty = env.type_unit(ctx);
                    let inst_expected = instance_if_generic(ctx, expected_ty);
                    unify_expression_types(tctx, loc, inst_expected, unit_ty, context)?;
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

            // Instance generic expected_ty to avoid corruption
            let eff_expected = instance_if_generic(ctx, expected_ty);
            unify_expression_types(tctx, loc, array_ty, eff_expected, context)?;

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
            let typed_apply = type_application(
                tctx,
                env,
                loc,
                funct_expr,
                args,
                *partial,
                *transformed_jsx,
                expected_ty,
                context.clone(),
                &expr.pexp_attributes,
            )?;
            // Match OCaml Pexp_apply: mk_apply applies rue once, then the
            // caller applies rue again on the resulting expression.
            rue_unify(tctx, loc, typed_apply.exp_type, expected_ty, context)?;
            Ok(typed_apply)
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
            // Match OCaml typecore.ml optional-default rewrite:
            //   fun ?x:(p=default) -> body
            // becomes
            //   fun ?x:*opt* ->
            //     let[@#default] p =
            //       match *opt* with Some *sth* -> *sth* | None -> default
            //     in
            //     body
            if arg_label.is_optional() {
                let lhs_pat = tctx.arena.get_pat(*lhs);
                if let Some(default_idx) = default.as_ref()
                {
                    let default_expr = tctx.arena.get_expr(*default_idx);
                    let default_loc = default_expr.pexp_loc;
                    let opt_name = tctx.arena.optional_default_opt_str();
                    let sth_name = tctx.arena.optional_default_sth_str();
                    let opt_lid = tctx.arena.optional_default_opt_lid();
                    let sth_lid = tctx.arena.optional_default_sth_lid();

                    let sloc = {
                        let sloc_start = tctx.arena.loc_start_idx(lhs_pat.ppat_loc);
                        let sloc_end = tctx.arena.loc_end_idx(default_loc);
                        find_loc_idx_by_bounds(tctx.arena, sloc_start, sloc_end)
                            .unwrap_or(lhs_pat.ppat_loc)
                    };
                    let arena_ptr = tctx.arena as *const ParseArena as *mut ParseArena;

                    let matched_pat = unsafe { (*arena_ptr).push_pat(ParsedPattern {
                        ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_var(Located {
                            txt: sth_name,
                            loc: default_loc,
                        })),
                        ppat_loc: default_loc,
                        ppat_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let some_pat = unsafe { (*arena_ptr).push_pat(ParsedPattern {
                        ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_construct(
                            Located {
                                txt: tctx.arena.predef_some_lid(),
                                loc: default_loc,
                            },
                            Some(matched_pat),
                        )),
                        ppat_loc: default_loc,
                        ppat_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let none_pat = unsafe { (*arena_ptr).push_pat(ParsedPattern {
                        ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_construct(
                            Located {
                                txt: tctx.arena.predef_none_lid(),
                                loc: default_loc,
                            },
                            None,
                        )),
                        ppat_loc: default_loc,
                        ppat_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let some_rhs = unsafe { (*arena_ptr).push_expr(ParsedExpression {
                        pexp_desc: Box::new(crate::parser::ast::ExpressionDesc::Pexp_ident(Located {
                            txt: sth_lid,
                            loc: default_loc,
                        })),
                        pexp_loc: default_loc,
                        pexp_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let match_scrutinee = unsafe { (*arena_ptr).push_expr(ParsedExpression {
                        pexp_desc: Box::new(crate::parser::ast::ExpressionDesc::Pexp_ident(Located {
                            txt: opt_lid,
                            loc,
                        })),
                        pexp_loc: loc,
                        pexp_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let match_expr_idx = unsafe { (*arena_ptr).push_expr(ParsedExpression {
                        pexp_desc: Box::new(crate::parser::ast::ExpressionDesc::Pexp_match(
                            Box::new((
                                match_scrutinee,
                                vec![
                                crate::parser::ast::Case {
                                    pc_bar: None,
                                    pc_lhs: some_pat,
                                    pc_guard: None,
                                    pc_rhs: some_rhs,
                                },
                                crate::parser::ast::Case {
                                    pc_bar: None,
                                    pc_lhs: none_pat,
                                    pc_guard: None,
                                    pc_rhs: *default_idx,
                                },
                            ],
                            )),
                        )),
                        pexp_loc: sloc,
                        pexp_attributes: crate::parser::ast::Attributes::new(),
                    }) };

                    let default_attr = (
                        Located::mknoloc(tctx.arena.default_attr_str()),
                        crate::parser::ast::Payload::PStr(Box::new(vec![])),
                    );
                    let mut rewritten_attrs = Attributes::new();
                    rewritten_attrs.push(default_attr);

                    let rewritten_body = ParsedExpression {
                        pexp_desc: Box::new(crate::parser::ast::ExpressionDesc::Pexp_let(
                            Box::new((
                                RecFlag::Nonrecursive,
                                vec![crate::parser::ast::ValueBinding {
                                pvb_pat: *lhs,
                                pvb_expr: match_expr_idx,
                                pvb_attributes: crate::parser::ast::Attributes::new(),
                                pvb_loc: tctx.arena.none_loc(),
                                }],
                                *rhs,
                            )),
                        )),
                        pexp_loc: loc,
                        pexp_attributes: rewritten_attrs,
                    };

                    let opt_param = ParsedPattern {
                        ppat_desc: Box::new(crate::parser::ast::PatternDesc::Ppat_var(Located {
                            txt: opt_name,
                            loc: sloc,
                        })),
                        ppat_loc: sloc,
                        ppat_attributes: crate::parser::ast::Attributes::new(),
                    };

                    return type_function(
                        tctx,
                        env,
                        loc,
                        arg_label,
                        None,
                        &opt_param,
                        &rewritten_body,
                        arity.clone(),
                        *is_async,
                        expected_ty,
                        &expr.pexp_attributes,
                    );
                }
            }
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
            // OCaml quirk: in `Pexp_record (lid_sexp_list, Some sexp)`, the pattern
            // variable `sexp` shadows the outer function parameter, so
            // `sexp.pexp_attributes` at the result uses the spread expression's
            // attributes, not the record expression's attributes.
            let attrs = match base {
                Some(base_expr) => &tctx.arena.get_expr(*base_expr).pexp_attributes,
                None => &expr.pexp_attributes,
            };
            type_record(
                tctx,
                env,
                loc,
                fields,
                (*base).map(|idx| tctx.arena.get_expr(idx)),
                expected_ty,
                attrs,
            )
        }

        ED::Pexp_field(record_expr_idx, field_lid) => {
            // Field access
            let record_expr = tctx.arena.get_expr(*record_expr_idx);
            let typed_field = type_field(
                tctx,
                env,
                loc,
                record_expr,
                field_lid,
                &expr.pexp_attributes,
            )?;
            // OCaml: rue { ... exp_type = ty_arg; ... }
            rue_unify(tctx, loc, typed_field.exp_type, expected_ty, context)?;
            Ok(typed_field)
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
            let (ref override_flag, ref lid, ref body_idx) = **inner;
            // Open expression: M.{ E } or open M; E
            let body = tctx.arena.get_expr(*body_idx);
            type_open(
                tctx,
                env,
                loc,
                override_flag,
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
                context,
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
                context,
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
    loc: LocIdx,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
    context: Option<TypeClashContext>,
) -> TypeCoreResult<()> {
    use crate::types::unify;

    match unify(tctx.type_ctx, &mut tctx.unify_state, ty1, ty2) {
        Ok(()) => Ok(()),
        Err(err) => {
            if std::env::var_os("RUST_DEBUG_UNIFY_FAIL").is_some() {
                let summarize = |ty: TypeExprRef| {
                    let repr = tctx.type_ctx.repr(ty);
                    let desc = tctx.type_ctx.get_desc(repr);
                    match &*desc {
                        TypeDesc::Tconstr { path, args, .. } => {
                            let args = args
                                .iter()
                                .map(|a| {
                                    let arg = tctx.type_ctx.repr(*a);
                                    let arg_desc = tctx.type_ctx.get_desc(arg);
                                    let head = match &*arg_desc {
                                        TypeDesc::Tconstr { path, .. } => path.name(),
                                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                                        TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                                        TypeDesc::Tlink(t) => {
                                            format!("Tlink->{}", tctx.type_ctx.repr(*t).0)
                                        }
                                        _ => format!("ty#{}", arg.0),
                                    };
                                    format!("{}:{}", arg.0, head)
                                })
                                .collect::<Vec<_>>()
                                .join(",");
                            format!("Tconstr({},args=[{}])", path.name(), args)
                        }
                        TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                        TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                        TypeDesc::Tlink(t) => format!("Tlink({})", tctx.type_ctx.repr(*t).0),
                        TypeDesc::Tsubst(t) => format!("Tsubst({})", tctx.type_ctx.repr(*t).0),
                        TypeDesc::Ttuple(ts) => format!("Ttuple({})", ts.len()),
                        TypeDesc::Tobject { .. } => "Tobject".to_string(),
                        TypeDesc::Tfield { .. } => "Tfield".to_string(),
                        TypeDesc::Tnil => "Tnil".to_string(),
                        TypeDesc::Tvariant(row) => {
                            let labels = row
                                .row_fields
                                .iter()
                                .map(|(l, _)| l.as_str())
                                .take(12)
                                .collect::<Vec<_>>()
                                .join(",");
                            format!(
                                "Tvariant(closed={},fixed={},more={},labels=[{}])",
                                row.row_closed,
                                row.row_fixed,
                                tctx.type_ctx.repr(row.row_more).0,
                                labels
                            )
                        }
                        TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                        TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                    }
                };
                if let crate::types::TypeError::Unify(trace_pairs) = &err {
                    let trace_dump = trace_pairs
                        .iter()
                        .take(12)
                        .map(|(a, b)| {
                            format!(
                                "{}({})~{}({})",
                                tctx.type_ctx.repr(*a).0,
                                summarize(*a),
                                tctx.type_ctx.repr(*b).0,
                                summarize(*b)
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(" | ");
                    eprintln!("[unify-fail-trace] {}", trace_dump);
                }
                let full_loc = tctx.arena.to_location(loc);
                eprintln!(
                    "[unify-fail] loc={}:{} ty1={}({}) ty2={}({}) ctx={:?}",
                    full_loc.loc_start.line,
                    full_loc.loc_start.column(),
                    tctx.type_ctx.repr(ty1).0,
                    summarize(ty1),
                    tctx.type_ctx.repr(ty2).0,
                    summarize(ty2),
                    context
                );
            }
            Err(TypeCoreError::ExprTypeClash {
                trace: vec![(ty1, ty2)],
                context,
            })
        }
    }
}

/// Instance a type if it's at GENERIC_LEVEL, otherwise return it unchanged.
/// Used to protect generic expected types from corruption by non-rue handlers.
fn instance_if_generic(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    if ctx.get_level(ctx.repr(ty)) == crate::types::type_expr::GENERIC_LEVEL {
        crate::types::instance(ctx, ty)
    } else {
        ty
    }
}

/// OCaml's `rue` mechanism: instance the expected type if generic before unifying.
/// When expected_ty is generic (from type_constraint/type_argument), `instance` goes
/// through `copy` which checks `simple_abbrevs` for nullary Tconstr sharing, creating
/// Tlink nodes that produce physical sharing in the typed tree.
fn rue_unify(
    tctx: &mut TypeCheckContext<'_>,
    loc: LocIdx,
    exp_ty: TypeExprRef,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
) -> TypeCoreResult<()> {
    let inst = instance_if_generic(tctx.type_ctx, expected_ty);
    if std::env::var_os("RUST_DEBUG_TYPE_PACK").is_some() {
        let expected_repr = tctx.type_ctx.repr(expected_ty);
        let inst_repr = tctx.type_ctx.repr(inst);
        eprintln!(
            "[rue-unify] loc={:?} expected={}@{} inst={}@{} instanced={}",
            loc.0,
            expected_repr.0,
            tctx.type_ctx.get_level(expected_repr),
            inst_repr.0,
            tctx.type_ctx.get_level(inst_repr),
            expected_repr != inst_repr
        );
    }
    unify_expression_types(tctx, loc, exp_ty, inst, context)
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
        "Pervasives.+" | "Pervasives.-" | "Pervasives.*" | "Pervasives./" | "Pervasives.%"
        | "Pervasives.mod" | "Pervasives.**" | "Pervasives.<<" | "Pervasives.>>"
        | "Pervasives.>>>" | "Pervasives.|||" | "Pervasives.^^^" | "Pervasives.&&&" => {
            Some(UnifiedOpForm::Binary)
        }
        // Unary unified ops
        "Pervasives.~+" | "Pervasives.~-" | "Pervasives.~~~" => Some(UnifiedOpForm::Unary),
        _ => None,
    }
}

/// Check if a resolved type is a Tconstr matching a specific type name.
fn is_type_named(ctx: &TypeContext<'_>, ty: TypeExprRef, name: &str) -> bool {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } if args.is_empty() => match path {
            Path::Pident(id) => id.name() == name,
            _ => false,
        },
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
    args: &[(ArgLabel, crate::parse_arena::ExprIdx)],
    transformed_jsx: bool,
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
            let lhs_result = type_expect(tctx, env, tctx.arena.get_expr(args[0].1), lhs_ty, None);
            let lhs = match lhs_result {
                Ok(e) => e,
                Err(e) => return Some(Err(e)),
            };
            let lhs_type = ctx.repr(lhs.exp_type);

            let rhs_ty = ctx.new_var(None);
            let rhs_result = type_expect(tctx, env, tctx.arena.get_expr(args[1].1), rhs_ty, None);
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
            let make_concrete = || {
                ctx.new_constr(
                    Path::pident(Ident::create_persistent(concrete_type_name)),
                    vec![],
                )
            };

            // Unify LHS with a fresh concrete type
            let lhs_concrete = make_concrete();
            if let Err(e) = unify_expression_types(tctx, loc, lhs.exp_type, lhs_concrete, None) {
                return Some(Err(e));
            }
            // Unify RHS with a fresh concrete type (instead of re-typing which creates
            // duplicate type nodes that don't share with the first typing's nodes)
            let rhs_concrete = make_concrete();
            if let Err(e) = unify_expression_types(tctx, loc, rhs.exp_type, rhs_concrete, None) {
                return Some(Err(e));
            }

            // Result type is a fresh concrete type
            let result_ty = make_concrete();

            // OCaml: rue { ... exp_type = ty_res; ... } (unified ops are Pexp_apply)
            if let Err(e) = rue_unify(tctx, loc, result_ty, expected_ty, context) {
                return Some(Err(e));
            }

            let typed_args = vec![
                ApplyArg {
                    label: convert_arg_label_for_ctx(&args[0].0, tctx.arena),
                    expression: Some(lhs),
                },
                ApplyArg {
                    label: convert_arg_label_for_ctx(&args[1].0, tctx.arena),
                    expression: Some(rhs),
                },
            ];

            Some(Ok(Expression::new(
                ExpressionDesc::Texp_apply {
                    funct: Box::new(typed_funct.clone()),
                    args: typed_args,
                    partial: false,
                    transformed_jsx,
                },
                loc.clone(),
                result_ty,
                EnvRef(0),
                attributes.to_vec().into(),
            )))
        }
        UnifiedOpForm::Unary if args.len() == 1 => {
            // Type check the argument independently
            let arg_ty = ctx.new_var(None);
            let arg_result = type_expect(tctx, env, tctx.arena.get_expr(args[0].1), arg_ty, None);
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

            // OCaml: rue { ... exp_type = ty_res; ... } (unified ops are Pexp_apply)
            if let Err(e) = rue_unify(tctx, loc, result_ty, expected_ty, context) {
                return Some(Err(e));
            }

            let typed_args = vec![ApplyArg {
                label: convert_arg_label_for_ctx(&args[0].0, tctx.arena),
                expression: Some(arg),
            }];

            Some(Ok(Expression::new(
                ExpressionDesc::Texp_apply {
                    funct: Box::new(typed_funct.clone()),
                    args: typed_args,
                    partial: false,
                    transformed_jsx,
                },
                loc.clone(),
                result_ty,
                EnvRef(0),
                attributes.to_vec().into(),
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
    args: &[(ArgLabel, crate::parse_arena::ExprIdx)],
    partial: bool,
    transformed_jsx: bool,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::ApplyArg;

    enum PendingApplyArg<'a> {
        Provided {
            label: crate::types::ArgLabel,
            expr: &'a ParsedExpression,
            expected_ty: TypeExprRef,
            unify_ty: TypeExprRef,
            enforce_optional: bool,
            /// OCaml's type_unknown_args only calls type_expect, with no
            /// subsequent unify_exp. Skip the post-typing unify for this path.
            skip_post_unify: bool,
        },
        SynthOptionalNone {
            label: crate::types::ArgLabel,
            option_ty: TypeExprRef,
        },
        Omitted {
            label: crate::types::ArgLabel,
        },
    }

    fn parser_arg_label_name<'a>(label: &ArgLabel, arena: &'a ParseArena) -> &'a str {
        match label {
            ArgLabel::Nolabel => "",
            ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => arena.get_string(loc.txt),
        }
    }

    fn extract_label_index(
        remaining_args: &[(ArgLabel, crate::parse_arena::ExprIdx)],
        label_name: &str,
        arena: &ParseArena,
    ) -> Option<usize> {
        remaining_args
            .iter()
            .position(|(label, _)| parser_arg_label_name(label, arena) == label_name)
    }

    fn has_nolabel_arg(remaining_args: &[(ArgLabel, crate::parse_arena::ExprIdx)]) -> bool {
        remaining_args
            .iter()
            .any(|(label, _)| matches!(label, ArgLabel::Nolabel))
    }

    fn apply_arg_label_for_param(
        param_label: &crate::types::ArgLabel,
        call_label: &ArgLabel,
        arena: &ParseArena,
    ) -> crate::types::ArgLabel {
        match param_label {
            crate::types::ArgLabel::Nolabel => crate::types::ArgLabel::Nolabel,
            crate::types::ArgLabel::Labelled(_) => match call_label {
                ArgLabel::Nolabel => crate::types::ArgLabel::Nolabel,
                ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => {
                    crate::types::ArgLabel::labelled(
                        arena.get_string(loc.txt).to_string(),
                        arena.to_location(loc.loc),
                    )
                }
            },
            crate::types::ArgLabel::Optional(_) => match call_label {
                ArgLabel::Nolabel => crate::types::ArgLabel::Nolabel,
                ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => {
                    crate::types::ArgLabel::optional(
                        arena.get_string(loc.txt).to_string(),
                        arena.to_location(loc.loc),
                    )
                }
            },
        }
    }

    let ctx = tctx.type_ctx;
    let total_app = !partial;

    // Match OCaml Pexp_apply staging:
    //   begin_def (); type_exp funct; let ty = instance funct.exp_type; end_def ();
    //   lower_args env [] ty;
    //   begin_def (); ... type_application/translate_unified_ops ...; end_def ();
    ctx.begin_def();
    let funct_ty = ctx.new_var(None);
    let typed_funct = type_expect(tctx, env, funct, funct_ty, None)?;
    let lowered_ty = crate::types::instance(ctx, typed_funct.exp_type);
    ctx.end_def();
    crate::types::ctype::lower_args(ctx, env, lowered_ty);

    ctx.begin_def();

    // Try unified ops dispatch first (matching OCaml's translate_unified_ops)
    if let Some(result) = translate_unified_ops(
        tctx,
        env,
        loc,
        &typed_funct,
        args,
        transformed_jsx,
        expected_ty,
        context.clone(),
        attributes,
    ) {
        ctx.end_def();
        return result;
    }

    // Match OCaml's use of expand_head when deciding application behavior.
    let mut current_ty = typed_funct.exp_type;
    // OCaml typecore.ml:
    //   type_args ... ~ty_fun:funct.exp_type (instance env funct.exp_type)
    let mut current_ty0 = crate::types::instance(ctx, typed_funct.exp_type);
    let expanded_funct_ty = crate::types::ctype::expand_head(ctx, env, current_ty);

    // force_tvar only applies to total applications in OCaml.
    let force_tvar = total_app
        && matches!(
            &*tctx.type_ctx.get_desc(expanded_funct_ty),
            TypeDesc::Tvar(_)
        );
    let function_arity: Option<i32> = if force_tvar {
        Some(args.len() as i32)
    } else {
        match &*tctx.type_ctx.get_desc(expanded_funct_ty) {
            TypeDesc::Tarrow { arity, .. } => *arity,
            _ => None,
        }
    };
    let max_arity = function_arity.unwrap_or(i32::MAX);
    let mut top_arity: Option<i32> = function_arity;

    // OCaml special case for ignore: skip post-unify (type_argument's unify_exp)
    // so that Pexp_tuple/etc. result types stay as fresh nodes.
    // OCaml typecore.ml:3756 handles ignore via type_expect only (no type_argument).
    let is_ignore_fn = matches!(
        &typed_funct.exp_desc,
        ExpressionDesc::Texp_ident(_, _, desc)
            if matches!(&desc.val_kind, crate::types::ValueKind::ValPrim(prim) if prim.prim_name == "%ignore")
    );

    // Match labels by name (OCaml's extract_label) instead of consuming call args strictly
    // left-to-right.
    let mut remaining_args: Vec<(ArgLabel, crate::parse_arena::ExprIdx)> = args
        .iter()
        .map(|(label, expr_idx)| (label.clone(), *expr_idx))
        .collect();
    let mut pending_args: Vec<PendingApplyArg<'_>> = Vec::new();
    let mut omitted: Vec<(crate::types::ArgLabel, TypeExprRef)> = Vec::new();
    let mut consumed_optional_count = 0usize;
    let mut synthesized_optional_count = 0usize;

    while !remaining_args.is_empty() {
        let expanded_current_ty = crate::types::ctype::expand_head(ctx, env, current_ty);
        let expanded_current_ty0 = if ctx.repr(current_ty0) == ctx.repr(current_ty) {
            expanded_current_ty
        } else {
            crate::types::ctype::expand_head(ctx, env, current_ty0)
        };

        // Match OCaml type_unknown_args `foo()` handling for all-optional prefixes.
        // Treat `()` as an empty application only when all already-collected args
        // were synthesized optional defaults, and the next parameter is not an
        // explicit `unit` argument.
        if total_app
            && omitted.is_empty()
            && !pending_args.is_empty()
            && pending_args.len() == synthesized_optional_count
            && remaining_args.len() == 1
        {
            let (label, arg_expr_idx) = &remaining_args[0];
            if label.is_nolabel() {
                let arg_expr = tctx.arena.get_expr(*arg_expr_idx);
                if let crate::parser::ast::ExpressionDesc::Pexp_construct(lid, None) =
                    &*arg_expr.pexp_desc
                {
                    if tctx.arena.is_lident(lid.txt, "()") {
                        let should_treat_as_empty_app = match &*ctx.get_desc(expanded_current_ty) {
                            TypeDesc::Tarrow { arg, .. } => {
                                if arg.lbl.is_optional() {
                                    false
                                } else if matches!(arg.lbl, crate::types::ArgLabel::Nolabel) {
                                    let arg_ty = ctx.repr(arg.typ);
                                    !matches!(
                                        &*ctx.get_desc(arg_ty),
                                        TypeDesc::Tconstr { path, args, .. }
                                            if args.is_empty() && path.last() == "unit"
                                    )
                                } else {
                                    true
                                }
                            }
                            _ => true,
                        };

                        if should_treat_as_empty_app {
                            remaining_args.clear();
                            break;
                        }
                    }
                }
            }
        }

        let arrow_current = {
            let desc = ctx.get_desc(expanded_current_ty);
            match &*desc {
                TypeDesc::Tarrow {
                    arg,
                    ret,
                    commutable,
                    ..
                } => Some((
                    arg.lbl.clone(),
                    arg.typ,
                    *ret,
                    matches!(
                        ctx.commutable_repr(commutable),
                        crate::types::type_expr::Commutable::Cok
                    ),
                )),
                _ => None,
            }
        };
        let arrow_inst =
            crate::types::ctype::split_arrow_with_label(ctx, expanded_current_ty0);
        if let (
            Some((fn_label, arg_ty, ret_ty, commutable_ok)),
            Some((_fn_label0, arg_ty0, ret_ty0)),
        ) = (arrow_current, arrow_inst)
        {
            // Match OCaml type_args guard: only use the typed-args path when
            // the function arrow commutability is known to be Cok.
            if !commutable_ok {
                // Fall through to type_unknown_args behavior below.
            } else {
            let fn_label_name = fn_label.label_name().unwrap_or("");
            if let Some(match_idx) = extract_label_index(&remaining_args, fn_label_name, tctx.arena)
            {
                let (call_label, arg_expr_idx) = remaining_args.remove(match_idx);
                let arg_expr = tctx.arena.get_expr(arg_expr_idx);
                let call_is_optional = call_label.is_optional();
                let effective_arg_ty = if fn_label.is_optional() && !call_is_optional {
                    crate::types::ctype::extract_option_type(ctx, arg_ty).unwrap_or(arg_ty)
                } else {
                    arg_ty
                };
                let effective_arg_ty0 = if fn_label.is_optional() && !call_is_optional {
                    crate::types::ctype::extract_option_type(ctx, arg_ty0).unwrap_or(arg_ty0)
                } else {
                    arg_ty0
                };

                pending_args.push(PendingApplyArg::Provided {
                    label: apply_arg_label_for_param(&fn_label, &call_label, tctx.arena),
                    expr: arg_expr,
                    expected_ty: effective_arg_ty,
                    unify_ty: effective_arg_ty0,
                    enforce_optional: fn_label.is_optional() && !call_is_optional,
                    skip_post_unify: is_ignore_fn,
                });
                if std::env::var_os("RUST_DEBUG_REACTDOM_APPLY").is_some()
                    && matches!(
                        &typed_funct.exp_desc,
                        ExpressionDesc::Texp_ident(path, _, _) if path.name() == "ReactDOM.someElement"
                    )
                {
                    let expected_repr = ctx.repr(effective_arg_ty);
                    let unify_repr = ctx.repr(effective_arg_ty0);
                    eprintln!(
                        "[reactdom-apply] stage=provided label={} expected={}@{} unify={}@{}",
                        fn_label.label_name().unwrap_or(""),
                        expected_repr.0,
                        ctx.get_level(expected_repr),
                        unify_repr.0,
                        ctx.get_level(unify_repr),
                    );
                }
                current_ty = ret_ty;
                current_ty0 = ret_ty0;
                continue;
            }

            if fn_label.is_optional() && (total_app || has_nolabel_arg(&remaining_args)) {
                consumed_optional_count += 1;
                let option_ty = crate::types::instance(ctx, arg_ty);
                if std::env::var_os("RUST_DEBUG_JSX_OPTIONAL").is_some() {
                    let arg_repr = ctx.repr(arg_ty);
                    let opt_repr = ctx.repr(option_ty);
                    let describe = |ty: TypeExprRef| {
                        let d = ctx.get_desc(ty);
                        match &*d {
                            TypeDesc::Tconstr { path, args, .. } => {
                                format!("Tconstr({},{})", path.name(), args.len())
                            }
                            TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                            TypeDesc::Tvar(_) => "Tvar".to_string(),
                            TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                            _ => "other".to_string(),
                        }
                    };
                    eprintln!(
                        "[jsx-optional] stage=consume label={} arg={}@{} {} opt={}@{} {}",
                        fn_label.label_name().unwrap_or(""),
                        arg_repr.0,
                        ctx.get_level(arg_repr),
                        describe(arg_repr),
                        opt_repr.0,
                        ctx.get_level(opt_repr),
                        describe(opt_repr)
                    );
                }
                // OCaml type_application: consumed omitted optional labels still appear
                // in Texp_apply as explicit None arguments at Location.none.
                pending_args.push(PendingApplyArg::SynthOptionalNone {
                    label: fn_label.clone(),
                    option_ty,
                });
                synthesized_optional_count += 1;
                current_ty = ret_ty;
                current_ty0 = ret_ty0;
                continue;
            }

            pending_args.push(PendingApplyArg::Omitted {
                label: fn_label.clone(),
            });
            omitted.push((fn_label, arg_ty));
            current_ty = ret_ty;
            current_ty0 = ret_ty0;
            continue;
            }
        }

        let (label, arg_expr_idx) = remaining_args.remove(0);
        let arg_expr = tctx.arena.get_expr(arg_expr_idx);

        // OCaml special case: if all supplied args were optional defaults and
        // the final argument is `()`, treat it as an empty application.
        if consumed_optional_count > 0
            && omitted.is_empty()
            && remaining_args.is_empty()
            && label.is_nolabel()
            && pending_args.len() == synthesized_optional_count
        {
            if let crate::parser::ast::ExpressionDesc::Pexp_construct(lid, None) =
                &*arg_expr.pexp_desc
            {
                if tctx.arena.is_lident(lid.txt, "()") {
                    break;
                }
            }
        }

        // type_unknown_args fallback: build an arrow from call-site label if needed.
        let arg_ty = ctx.new_var(None);
        let ret_ty = ctx.new_var(None);
        let ctx_label = convert_arg_label_for_ctx(&label, tctx.arena);
        let use_unknown_commutable = force_tvar
            && matches!(&*ctx.get_desc(expanded_current_ty0), TypeDesc::Tvar(_));
        let arrow_ty = if use_unknown_commutable {
            ctx.new_arrow_unknown(ctx_label, arg_ty, ret_ty, top_arity)
        } else {
            ctx.new_arrow(ctx_label, arg_ty, ret_ty, top_arity)
        };
        // Match OCaml type_unknown_args: operate on ty_fun0 (instanced function type),
        // not on ty_fun (original function type).
        unify_expression_types(tctx, loc, expanded_current_ty0, arrow_ty, None)?;
        top_arity = None;

        pending_args.push(PendingApplyArg::Provided {
            label: convert_arg_label_for_ctx(&label, tctx.arena),
            expr: arg_expr,
            expected_ty: arg_ty,
            unify_ty: arg_ty,
            enforce_optional: label.is_optional(),
            skip_post_unify: true,
        });
        current_ty = ret_ty;
        current_ty0 = ret_ty;
    }

    if total_app {
        // Match OCaml `type_unknown_args []`: for total applications, trailing
        // optional arrows are materialized as explicit `None` arguments.
        let mut applied_count = pending_args.len();
        while (applied_count as i32) < max_arity {
            let expanded_current_ty = crate::types::ctype::expand_head(ctx, env, current_ty);
            let expanded_current_ty0 = if ctx.repr(current_ty0) == ctx.repr(current_ty) {
                expanded_current_ty
            } else {
                crate::types::ctype::expand_head(ctx, env, current_ty0)
            };
            if let (Some((fn_label, arg_ty, ret_ty)), Some((_fn_label0, _arg_ty0, ret_ty0))) = (
                crate::types::ctype::split_arrow_with_label(ctx, expanded_current_ty),
                crate::types::ctype::split_arrow_with_label(ctx, expanded_current_ty0),
            )
            {
                if fn_label.is_optional() {
                    let option_ty = crate::types::instance(ctx, arg_ty);
                    if std::env::var_os("RUST_DEBUG_JSX_OPTIONAL").is_some() {
                        let arg_repr = ctx.repr(arg_ty);
                        let opt_repr = ctx.repr(option_ty);
                        let describe = |ty: TypeExprRef| {
                            let d = ctx.get_desc(ty);
                            match &*d {
                                TypeDesc::Tconstr { path, args, .. } => {
                                    format!("Tconstr({},{})", path.name(), args.len())
                                }
                                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                                TypeDesc::Tvar(_) => "Tvar".to_string(),
                                TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                                _ => "other".to_string(),
                            }
                        };
                        eprintln!(
                            "[jsx-optional] stage=trailing label={} arg={}@{} {} opt={}@{} {}",
                            fn_label.label_name().unwrap_or(""),
                            arg_repr.0,
                            ctx.get_level(arg_repr),
                            describe(arg_repr),
                            opt_repr.0,
                            ctx.get_level(opt_repr),
                            describe(opt_repr)
                        );
                    }
                    pending_args.push(PendingApplyArg::SynthOptionalNone {
                        label: fn_label.clone(),
                        option_ty,
                    });
                    current_ty = ret_ty;
                    current_ty0 = ret_ty0;
                    applied_count += 1;
                    continue;
                }
            }
            break;
        }
    }

    let debug_apply_name = match &typed_funct.exp_desc {
        ExpressionDesc::Texp_ident(path, _, _) => Some(path.name()),
        _ => None,
    };
    let debug_apply_eq = if std::env::var_os("RUST_DEBUG_APPLY_TRACE_ALL").is_some() {
        true
    } else {
        std::env::var_os("RUST_DEBUG_APPLY_TRACE").is_some()
            && {
                let full_loc = tctx.arena.to_location(loc);
                full_loc.loc_start.line == 35
                    || matches!(
                        debug_apply_name.as_deref(),
                        Some("N.eq") | Some("basicComponent")
                    )
            }
    };
    let summarize_apply_ty = |ty: TypeExprRef| -> String {
        let ty = ctx.repr(ty);
        let level = ctx.get_level(ty);
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tarrow { arg, ret, .. } => format!(
                "arrow#{}@{}({}->{})",
                ty.0,
                level,
                ctx.repr(arg.typ).0,
                ctx.repr(*ret).0
            ),
            TypeDesc::Tconstr { path, args, .. } => {
                let args = args
                    .iter()
                    .map(|a| ctx.repr(*a).0.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{}#{}@{}({})", path.name(), ty.0, level, args)
            }
            TypeDesc::Tvar(_) => format!("tvar#{}@{}", ty.0, level),
            TypeDesc::Tlink(t) => format!("tlink#{}@{}->{}", ty.0, level, ctx.repr(*t).0),
            TypeDesc::Tsubst(t) => format!("tsubst#{}@{}->{}", ty.0, level, ctx.repr(*t).0),
            _ => format!("other#{}@{}", ty.0, level),
        }
    };

    let mut typed_args = Vec::with_capacity(pending_args.len());
    for (arg_index, pending_arg) in pending_args.into_iter().enumerate() {
        match pending_arg {
            PendingApplyArg::Provided {
                label,
                expr,
                expected_ty,
                unify_ty,
                enforce_optional,
                skip_post_unify,
            } => {
                if debug_apply_eq {
                    let full_loc = tctx.arena.to_location(loc);
                    let simple_memo = ctx.get_abbrev_memo(ctx.simple_abbrevs_memo());
                    eprintln!(
                        "[apply-trace] fn={} loc={}:{} arg_index={} kind=provided label={:?} expected_ty={} expected_repr={} unify_ty={} unify_repr={} expected_desc={} unify_desc={} skip_post_unify={} has_local_constraints={} unify_env_has_local_constraints={} simple={:?}",
                        debug_apply_name.as_deref().unwrap_or("<non-ident>"),
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        arg_index,
                        label,
                        expected_ty.0,
                        ctx.repr(expected_ty).0,
                        unify_ty.0,
                        ctx.repr(unify_ty).0,
                        summarize_apply_ty(expected_ty),
                        summarize_apply_ty(unify_ty),
                        skip_post_unify,
                        env.has_local_constraints(),
                        tctx.unify_state
                            .env()
                            .is_some_and(|ue| ue.has_local_constraints()),
                        simple_memo
                    );
                }
                let arg_expected_ty = expected_ty;
                let force_fresh_local_float = false;
                let previous_force_fresh_local_float = tctx.force_fresh_local_float;
                tctx.force_fresh_local_float = force_fresh_local_float;
                let saved_unify_env = tctx.unify_state.env().cloned();
                let typed_arg_result = type_expect(
                    tctx,
                    env,
                    expr,
                    arg_expected_ty,
                    Some(TypeClashContext::FunctionCall),
                );
                tctx.force_fresh_local_float = previous_force_fresh_local_float;

                let typed_arg = typed_arg_result?;
                if let Some(saved_env) = saved_unify_env {
                    tctx.unify_state.set_env(&saved_env);
                } else {
                    tctx.set_unify_env(env);
                }
                // OCaml's type_unknown_args only calls type_expect (no
                // subsequent unify_exp). Skip the post-unify for that path
                // to preserve separate physical nodes in the typed tree.
                if !skip_post_unify {
                    unify_expression_types(
                        tctx,
                        typed_arg.exp_loc,
                        typed_arg.exp_type,
                        unify_ty,
                        Some(TypeClashContext::FunctionCall),
                    )?;
                }
                if debug_apply_eq {
                    let full_loc = tctx.arena.to_location(loc);
                    eprintln!(
                        "[apply-post] fn={} loc={}:{} arg_index={} expected_repr={} unify_repr={} arg_repr={}",
                        match &typed_funct.exp_desc {
                            ExpressionDesc::Texp_ident(path, _, _) => path.name(),
                            _ => "<non-ident>".to_string(),
                        },
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        arg_index,
                        ctx.repr(arg_expected_ty).0,
                        ctx.repr(unify_ty).0,
                        ctx.repr(typed_arg.exp_type).0
                    );
                }
                let typed_arg = if enforce_optional {
                    let wrapped_loc = typed_arg.exp_loc;
                    let wrapped_env = typed_arg.exp_env;
                    let option_ty = env.type_option(ctx, typed_arg.exp_type);
                    Expression::new(
                        ExpressionDesc::Texp_construct(
                            Located {
                                txt: tctx.arena.plain_some_lid(),
                                loc: wrapped_loc,
                            },
                            make_some_constructor(ctx, option_ty),
                            vec![typed_arg],
                        ),
                        wrapped_loc,
                        option_ty,
                        wrapped_env,
                        Attributes::new(),
                    )
                } else {
                    typed_arg
                };
                typed_args.push(ApplyArg {
                    label,
                    expression: Some(typed_arg),
                });
            }
            PendingApplyArg::SynthOptionalNone { label, option_ty } => {
                if debug_apply_eq {
                    let full_loc = tctx.arena.to_location(loc);
                    let simple_memo = ctx.get_abbrev_memo(ctx.simple_abbrevs_memo());
                    eprintln!(
                        "[apply-trace] fn={} loc={}:{} arg_index={} kind=none label={:?} option_ty={} simple={:?}",
                        debug_apply_name.as_deref().unwrap_or("<non-ident>"),
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        arg_index,
                        label,
                        ctx.repr(option_ty).0,
                        simple_memo
                    );
                }
                let none_loc = tctx.arena.none_loc();
                let none_expr = Expression::new(
                    ExpressionDesc::Texp_construct(
                        Located {
                            txt: tctx.arena.none_lid(),
                            loc: none_loc,
                        },
                        make_none_constructor(ctx, option_ty),
                        vec![],
                    ),
                    none_loc,
                    option_ty,
                    EnvRef(0),
                    Attributes::new(),
                );
                typed_args.push(ApplyArg {
                    label,
                    expression: Some(none_expr),
                });
            }
            PendingApplyArg::Omitted { label } => {
                if debug_apply_eq {
                    let full_loc = tctx.arena.to_location(loc);
                    let simple_memo = ctx.get_abbrev_memo(ctx.simple_abbrevs_memo());
                    eprintln!(
                        "[apply-trace] fn={} loc={}:{} arg_index={} kind=omitted label={:?} simple={:?}",
                        debug_apply_name.as_deref().unwrap_or("<non-ident>"),
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        arg_index,
                        label,
                        simple_memo
                    );
                }
                typed_args.push(ApplyArg {
                    label,
                    expression: None,
                });
            }
        }
    }

    // Re-wrap omitted parameters for partial/labeled applications.
    let mut result_ty = current_ty0;
    for (label, arg_ty) in omitted.iter().rev() {
        result_ty = ctx.new_arrow(label.clone(), *arg_ty, result_ty, None);
    }

    // OCaml update_uncurried_arity: preserve remaining uncurried arity on
    // partially applied results.
    // OCaml uses `{new_t with desc = Tarrow(arg, ret, c, Some newarity)}` which
    // creates a new record sharing the same `id` as the original. In Rust we
    // create a separate new arrow and record an arity alias so the sexp
    // serializer deduplicates them (matching OCaml's id-based dedup).
    if let Some(arity) = function_arity {
        let applied_args = args.len() as i32 + consumed_optional_count as i32;
        let remaining_arity = arity - applied_args;
        if remaining_arity > 0 {
            let result_repr = ctx.repr(result_ty);
            if let TypeDesc::Tarrow { arg, ret, .. } = &*ctx.get_desc(result_repr) {
                let new_arrow = ctx.new_arrow(arg.lbl.clone(), arg.typ, *ret, Some(remaining_arity));
                // Record alias: new_arrow is the arity-updated version of result_repr.
                // Sexp serializer will use result_repr's dedup key for both.
                ctx.set_arity_alias(new_arrow, result_repr);
                result_ty = new_arrow;
            }
        }
    }

    // Match OCaml typecore.ml Pexp_apply post-application side effect:
    //   unify_var env (newvar ()) funct.exp_type
    // Keep this before unifying the application result with expected_ty.
    if debug_apply_eq {
        let summarize = |ty: TypeExprRef| -> String {
            let ty = ctx.repr(ty);
            let desc = ctx.get_desc(ty);
            match &*desc {
                TypeDesc::Tarrow { arg, ret, .. } => {
                    format!("arrow#{}({}->{})", ty.0, ctx.repr(arg.typ).0, ctx.repr(*ret).0)
                }
                TypeDesc::Tconstr { path, args, .. } => {
                    let args = args
                        .iter()
                        .map(|a| ctx.repr(*a).0.to_string())
                        .collect::<Vec<_>>()
                        .join(",");
                    format!("{}#{}({})", path.name(), ty.0, args)
                }
                TypeDesc::Tvar(_) => format!("tvar#{}", ty.0),
                TypeDesc::Tlink(t) => format!("tlink#{}->{}", ty.0, ctx.repr(*t).0),
                _ => format!("other#{}", ty.0),
            }
        };
        eprintln!(
            "[apply-final] fn={} funct={} result={} expected={}",
            debug_apply_name.as_deref().unwrap_or("<non-ident>"),
            summarize(typed_funct.exp_type),
            summarize(result_ty),
            summarize(expected_ty)
        );
        if debug_apply_name.as_deref() == Some("basicComponent") {
            let dump_constr = |label: &str, ty: TypeExprRef| {
                let ty = ctx.repr(ty);
                let desc = ctx.get_desc(ty);
                if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                    let parts: Vec<String> = args
                        .iter()
                        .enumerate()
                        .map(|(idx, arg)| {
                            let arg = ctx.repr(*arg);
                            let arg_desc = ctx.get_desc(arg);
                            match &*arg_desc {
                                TypeDesc::Tconstr { path, .. } => {
                                    format!("{idx}:{}#{}", path.name(), arg.0)
                                }
                                TypeDesc::Tvar(_) => format!("{idx}:tvar#{}", arg.0),
                                TypeDesc::Tlink(target) => {
                                    format!("{idx}:tlink#{}->{}", arg.0, ctx.repr(*target).0)
                                }
                                _ => format!("{idx}:other#{}", arg.0),
                            }
                        })
                        .collect();
                    eprintln!(
                        "[apply-final-detail] fn=basicComponent {}={}#{}({})",
                        label,
                        path.name(),
                        ty.0,
                        parts.join(",")
                    );
                } else {
                    eprintln!(
                        "[apply-final-detail] fn=basicComponent {}=non-constr#{}",
                        label, ty.0
                    );
                }
            };
            dump_constr("result", result_ty);
            dump_constr("expected", expected_ty);
        }
    }
    ctx.end_def();
    unify_expression_types(tctx, loc, ctx.new_var(None), typed_funct.exp_type, None)?;

    // OCaml: rue { ... exp_type = ty_res; ... }
    rue_unify(tctx, loc, result_ty, expected_ty, context)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_apply {
            funct: Box::new(typed_funct),
            args: typed_args,
            partial,
            transformed_jsx,
        },
        loc.clone(),
        result_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Simple exhaustiveness check for pattern matching.
/// Returns `Total` if the patterns are obviously exhaustive, `Partial` otherwise.
/// This is a simplified version of OCaml's `Parmatch.check_partial` that handles
/// the most common cases.
fn check_partial_simple<'a>(ctx: &'a TypeContext<'a>, env: &Env, cases: &[crate::types::typedtree::Case]) -> crate::types::typedtree::Partial {
    use crate::types::typedtree::Partial;

    /// Check if a pattern is irrefutable (matches everything of its type)
    fn is_catch_all(pat: &Pattern) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => true,
            PatternDesc::Tpat_var(_, _) => true,
            PatternDesc::Tpat_alias(inner, _, _) => is_catch_all(inner),
            PatternDesc::Tpat_or(p1, p2, _) => is_catch_all(p1) || is_catch_all(p2),
            PatternDesc::Tpat_record(_, _) => true,
            PatternDesc::Tpat_tuple(_) => true,
            _ => false,
        }
    }

    // If any case has a catch-all pattern, it's total
    for case in cases {
        if is_catch_all(&case.c_lhs) {
            return Partial::Total;
        }
    }

    // Check if all constructors of a variant type are covered
    // Collect constructor names from Tpat_construct patterns
    let mut construct_names: HashSet<String> = HashSet::new();
    let mut total_constructors: Option<i32> = None;
    let mut has_non_construct = false;

    for case in cases {
        collect_top_constructs(&case.c_lhs, &mut construct_names, &mut total_constructors, &mut has_non_construct);
    }

    // If we found constructor patterns and know the total, check coverage
    if !has_non_construct {
        if let Some(total) = total_constructors {
            if construct_names.len() as i32 >= total && total > 0 {
                return Partial::Total;
            }
        }
    }

    // Check if all boolean values are covered
    let mut has_true = false;
    let mut has_false = false;
    for case in cases {
        check_bool_coverage(&case.c_lhs, &mut has_true, &mut has_false);
    }
    if has_true && has_false {
        return Partial::Total;
    }

    // Check poly variant exhaustiveness: if all cases are Tpat_variant and the
    // scrutinee type is a closed variant, check if all tags are covered.
    if let Some(first_case) = cases.first() {
        let pat_ty = crate::types::ctype::expand_head(ctx, env, first_case.c_lhs.pat_type);
        let pat_ty = ctx.repr(pat_ty);
        let desc = ctx.get_desc(pat_ty);
        if let TypeDesc::Tvariant(row) = &*desc {
            let row = crate::types::btype::row_repr(ctx, row);
            if row.row_closed {
                // Collect all tags from the variant type
                let type_tags: HashSet<&str> = row.row_fields.iter()
                    .filter(|(_, f)| !matches!(f, crate::types::type_expr::RowField::Rabsent))
                    .map(|(l, _)| l.as_str())
                    .collect();

                // Collect all tags from the case patterns
                let mut case_tags: HashSet<String> = HashSet::new();
                let mut all_variant_pats = true;
                for case in cases {
                    collect_variant_tags(&case.c_lhs, &mut case_tags, &mut all_variant_pats);
                }

                if all_variant_pats && !type_tags.is_empty() {
                    if type_tags.iter().all(|tag| case_tags.contains(*tag)) {
                        return Partial::Total;
                    }
                }
            }
        }
    }

    Partial::Partial
}

/// Collect poly variant tag names from top-level patterns, handling or-patterns
fn collect_variant_tags(
    pat: &Pattern,
    tags: &mut HashSet<String>,
    all_variant: &mut bool,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(label, _, _) => {
            tags.insert(label.clone());
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            collect_variant_tags(p1, tags, all_variant);
            collect_variant_tags(p2, tags, all_variant);
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            collect_variant_tags(inner, tags, all_variant);
        }
        _ => {
            *all_variant = false;
        }
    }
}

/// Collect construct names from top-level patterns, handling or-patterns
fn collect_top_constructs(
    pat: &Pattern,
    names: &mut HashSet<String>,
    total: &mut Option<i32>,
    has_non_construct: &mut bool,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_construct(_, cstr_desc, _) => {
            names.insert(cstr_desc.cstr_name.clone());
            let cstr_total = cstr_desc.cstr_consts + cstr_desc.cstr_nonconsts;
            *total = Some(cstr_total);
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            collect_top_constructs(p1, names, total, has_non_construct);
            collect_top_constructs(p2, names, total, has_non_construct);
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            collect_top_constructs(inner, names, total, has_non_construct);
        }
        _ => {
            *has_non_construct = true;
        }
    }
}

/// Check if boolean true/false are covered
fn check_bool_coverage(pat: &Pattern, has_true: &mut bool, has_false: &mut bool) {
    match &pat.pat_desc {
        PatternDesc::Tpat_construct(_, cstr_desc, _) => {
            match cstr_desc.cstr_name.as_str() {
                "true" => *has_true = true,
                "false" => *has_false = true,
                _ => {}
            }
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            check_bool_coverage(p1, has_true, has_false);
            check_bool_coverage(p2, has_true, has_false);
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            check_bool_coverage(inner, has_true, has_false);
        }
        _ => {}
    }
}

fn type_match_cases_sequential(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[&crate::parser::ast::Case],
    scrutinee_ty: TypeExprRef,
    generic_scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
    erase_either: bool,
) -> TypeCoreResult<Vec<crate::types::typedtree::Case>> {
    let mut typed_cases = Vec::with_capacity(cases.len());
    for case in cases {
        typed_cases.push(type_case(
            tctx,
            env,
            case,
            scrutinee_ty,
            generic_scrutinee_ty,
            body_ty,
            erase_either,
        )?);
    }
    Ok(typed_cases)
}

struct PendingMatchCase<'a> {
    parsed_case: &'a crate::parser::ast::Case,
    typed_pat: Pattern,
    case_env: Env,
    unpacks: Vec<PatternVariable>,
}

fn type_match_cases_batch_non_gadt<'a>(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[&'a crate::parser::ast::Case],
    ty_arg: TypeExprRef,
    generic_scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
    erase_either: bool,
) -> TypeCoreResult<Vec<crate::types::typedtree::Case>> {
    if cases.is_empty() {
        return Ok(Vec::new());
    }

    let ctx = tctx.type_ctx;
    let debug_case_496 = std::env::var_os("RUST_DEBUG_CASE_496").is_some();
    let single_var_case = matches!(
        cases,
        [case] if is_simple_variable_pattern(tctx.arena, tctx.arena.get_pat(case.pc_lhs))
    );
    // Match OCaml: ty_arg is always generic for Pexp_match (generalized by caller),
    // so propagate is always true. Use generic_scrutinee_ty for the level check.
    let propagate = ctx.get_level(ctx.repr(generic_scrutinee_ty)) == crate::types::GENERIC_LEVEL
        || !single_var_case;

    let mut scope_open = false;
    let batch_result = (|| -> TypeCoreResult<Vec<crate::types::typedtree::Case>> {
        if propagate {
            ctx.begin_def();
            scope_open = true;
        }

        let mut pending_cases: Vec<PendingMatchCase<'a>> = Vec::with_capacity(cases.len());
        for case in cases {
            // Match OCaml type_cases: instance the GENERIC scrutinee type inside
            // begin_def. This creates fresh copies at the elevated level (L+1).
            // After end_def + generalize, pattern types become GENERIC, preventing
            // body unification from contaminating pattern types.
            let case_scrutinee_ty = if erase_either {
                instance_for_erase_either_patterns(ctx, ty_arg)
            } else if propagate {
                crate::types::instance(ctx, generic_scrutinee_ty)
            } else {
                crate::types::instance(ctx, ty_arg)
            };
            let mut state = PatternState::new();
            let typed_pat = type_pattern(
                tctx,
                env,
                tctx.arena.get_pat(case.pc_lhs),
                case_scrutinee_ty,
                PatternMode::Normal,
                &mut state,
            )?;
            if debug_case_496 {
                if let PatternDesc::Tpat_variant(tag, arg, _) = &typed_pat.pat_desc {
                    let pat_line = tctx.arena.to_location(typed_pat.pat_loc).loc_start.line;
                    if pat_line == 496 && tag == "V" {
                        let arg_ty = arg
                            .as_ref()
                            .map(|arg_pat| ctx.repr(arg_pat.pat_type).0)
                            .unwrap_or(usize::MAX);
                        eprintln!(
                            "[case496 initial] pat=#{} arg=#{} scrutinee=#{}",
                            ctx.repr(typed_pat.pat_type).0,
                            arg_ty,
                            ctx.repr(case_scrutinee_ty).0
                        );
                    }
                }
            }

            let mut case_env = env.clone();
            let mut unpacks: Vec<PatternVariable> = Vec::new();
            for pv in &state.pattern_variables {
                let binding_ty = pv.ty;
                let desc = ValueDescription {
                    val_type: binding_ty,
                    val_kind: crate::types::ValueKind::ValReg,
                    val_loc: pv.loc.clone(),
                    val_attributes: vec![],
                    val_path: None,
                };
                case_env.add_value(pv.id.clone(), desc);
                if pv.is_module {
                    let module_type = module_type_from_package_binding(tctx, &case_env, binding_ty);
                    case_env.add_module(
                        pv.id.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: module_type,
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                    );
                    // Match OCaml order in wrap_unpacks (`x :: module_variables`).
                    unpacks.insert(0, pv.clone());
                }
            }

            pending_cases.push(PendingMatchCase {
                parsed_case: case,
                typed_pat,
                case_env,
                unpacks,
            });
        }

        // Match OCaml type_cases delayed unification (`unify_pats ty_arg'`).
        let ty_arg_prime = ctx.new_var(None);
        let unify_pats_result = (|| -> TypeCoreResult<()> {
            for pending in &pending_cases {
                // OCaml uses `unify_pat ext_env ...` where each pattern is
                // unified under its own extended environment.
                tctx.unify_state.set_env(&pending.case_env);
                unify_pattern_types(
                    tctx,
                    pending.typed_pat.pat_loc,
                    pending.typed_pat.pat_type,
                    ty_arg_prime,
                )?;
            }
            Ok(())
        })();
        tctx.unify_state.set_env(env);
        unify_pats_result?;
        if debug_case_496 {
            for pending in &pending_cases {
                if let PatternDesc::Tpat_variant(tag, arg, _) = &pending.typed_pat.pat_desc {
                    let pat_line = tctx.arena.to_location(pending.typed_pat.pat_loc).loc_start.line;
                    if pat_line == 496 && tag == "V" {
                        let arg_ty = arg
                            .as_ref()
                            .map(|arg_pat| ctx.repr(arg_pat.pat_type).0)
                            .unwrap_or(usize::MAX);
                        eprintln!(
                            "[case496 after-ty_arg-prime] pat=#{} arg=#{} ty_arg_prime=#{}",
                            ctx.repr(pending.typed_pat.pat_type).0,
                            arg_ty,
                            ctx.repr(ty_arg_prime).0
                        );
                    }
                }
            }
        }

        // Match OCaml type_cases ordering:
        //   unify_pats ty_arg';
        //   if List.exists has_variants patl then (
        //     Parmatch.pressure_variants env patl;
        //     List.iter (iter_pattern finalize_variant) patl
        //   );
        //
        // Rust previously delayed this to type_match() after body typing,
        // which can leak open-row state into case bodies.
        let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
        let mut rows_with_wildcards: HashSet<usize> = HashSet::new();
        for pending in pending_cases.iter() {
            collect_variant_row_labels_in_pattern(
                tctx,
                env,
                &pending.typed_pat,
                &mut labels_by_row,
            );
            collect_rows_with_wildcard_coverage(
                tctx,
                env,
                &pending.typed_pat,
                &mut rows_with_wildcards,
            );
        }
        if !labels_by_row.is_empty() {
            normalize_wildcard_coverage_by_labels(tctx, &labels_by_row, &mut rows_with_wildcards);
            let rows_to_close: HashSet<usize> = labels_by_row
                .iter()
                .filter_map(|(row_key, labels)| {
                    (!labels.is_empty() && !rows_with_wildcards.contains(row_key))
                        .then_some(*row_key)
                })
                .collect();
            if !rows_to_close.is_empty() {
                for pending in pending_cases.iter_mut() {
                    close_multi_label_variant_rows_in_pattern(
                        tctx,
                        env,
                        &mut pending.typed_pat,
                        &rows_to_close,
                    );
                }
            }
            for pending in pending_cases.iter_mut() {
                finalize_variant_rpresent_only(tctx, env, &mut pending.typed_pat);
            }
        }

        if propagate || erase_either {
            let propagated_ty = if erase_either {
                crate::types::instance(ctx, ty_arg)
            } else {
                crate::types::instance(ctx, generic_scrutinee_ty)
            };
            for pending in &pending_cases {
                tctx.unify_state.set_env(&pending.case_env);
                unify_pattern_types(
                    tctx,
                    pending.typed_pat.pat_loc,
                    pending.typed_pat.pat_type,
                    propagated_ty,
                )?;
            }
            if debug_case_496 {
                for pending in &pending_cases {
                    if let PatternDesc::Tpat_variant(tag, arg, _) = &pending.typed_pat.pat_desc {
                        let pat_line = tctx.arena.to_location(pending.typed_pat.pat_loc).loc_start.line;
                        if pat_line == 496 && tag == "V" {
                            let arg_ty = arg
                                .as_ref()
                                .map(|arg_pat| ctx.repr(arg_pat.pat_type).0)
                                .unwrap_or(usize::MAX);
                            eprintln!(
                                "[case496 after-propagate] pat=#{} arg=#{} propagated=#{}",
                                ctx.repr(pending.typed_pat.pat_type).0,
                                arg_ty,
                                ctx.repr(propagated_ty).0
                            );
                        }
                    }
                }
            }
            tctx.unify_state.set_env(env);
            ctx.end_def();
            scope_open = false;
            for pending in &pending_cases {
                iter_typed_pattern(&pending.typed_pat, &mut |pat| {
                    crate::types::generalize(tctx.type_ctx, pat.pat_type);
                });
            }
        }

        let mut typed_cases = Vec::with_capacity(pending_cases.len());
        for pending in pending_cases {
            let typed_guard = if let Some(guard) = &pending.parsed_case.pc_guard {
                let bool_ty = ctx.predef_bool();
                let guard_expr = tctx.arena.get_expr(*guard);
                let typed_guard =
                    type_expect(tctx, &pending.case_env, guard_expr, bool_ty, None)?;
                Some(wrap_module_unpacks_in_expression(
                    tctx,
                    &pending.case_env,
                    typed_guard,
                    &pending.unpacks,
                    guard_expr.pexp_loc,
                ))
            } else {
                None
            };

            let case_has_gadt = pattern_contains_generalized_constructor(
                tctx,
                env,
                tctx.arena.get_pat(pending.parsed_case.pc_lhs),
            );
            if std::env::var_os("RUST_DEBUG_CASE_GADT").is_some() {
                let lhs_pat = tctx.arena.get_pat(pending.parsed_case.pc_lhs);
                let lhs_loc = tctx.arena.to_location(lhs_pat.ppat_loc);
                eprintln!(
                    "[case-gadt-batch] line={} has_gadt={}",
                    lhs_loc.loc_start.line,
                    case_has_gadt
                );
            }
            let case_body_ty = if case_has_gadt {
                crate::types::ctype::subst_identity_copy(ctx, body_ty)
            } else {
                body_ty
            };
            if std::env::var_os("RUST_DEBUG_CASE_GADT").is_some() {
                eprintln!(
                    "[case-gadt-batch-ty] body_ty={} case_body_ty={} body_level={} case_level={}",
                    ctx.repr(body_ty).0,
                    ctx.repr(case_body_ty).0,
                    ctx.get_level(ctx.repr(body_ty)),
                    ctx.get_level(ctx.repr(case_body_ty))
                );
            }

            let body_expr = tctx.arena.get_expr(pending.parsed_case.pc_rhs);
            let typed_body = type_expect(tctx, &pending.case_env, body_expr, case_body_ty, None)?;
            let typed_body = wrap_module_unpacks_in_expression(
                tctx,
                &pending.case_env,
                typed_body,
                &pending.unpacks,
                body_expr.pexp_loc,
            );
            // Match OCaml type_cases: `exp_type = instance env ty_res'` where
            // `ty_res'` is corrected per-case when the pattern contains GADTs.
            let case_exp_ty = crate::types::instance(ctx, case_body_ty);
            let typed_body = Expression {
                exp_type: case_exp_ty,
                ..typed_body
            };

            typed_cases.push(crate::types::typedtree::Case {
                c_lhs: pending.typed_pat,
                c_guard: typed_guard,
                c_rhs: typed_body,
            });
        }
        Ok(typed_cases)
    })();

    if scope_open {
        ctx.end_def();
    }

    batch_result
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
    let ctx = tctx.type_ctx;

    // Match OCaml typecore.ml Pexp_match:
    // begin_def (); type_exp scrutinee; end_def ();
    // generalize_expansive (if needed); generalize;
    ctx.begin_def();
    let scrutinee_ty = ctx.new_var(None);
    let typed_scrutinee = match type_expect(tctx, env, scrutinee, scrutinee_ty, None) {
        Ok(expr) => expr,
        Err(err) => {
            ctx.end_def();
            return Err(err);
        }
    };
    ctx.end_def();
    let is_expansive = !is_nonexpansive_expression(tctx, &typed_scrutinee);
    if is_expansive {
        crate::types::ctype::generalize_expansive(ctx, env, typed_scrutinee.exp_type);
    }
    crate::types::ctype::generalize(ctx, typed_scrutinee.exp_type);
    // OCaml split_cases: separate exception cases from value cases.
    // Exception cases have their Ppat_exception wrapper unwrapped, and
    // are typed against Predef.type_exn instead of the scrutinee type.
    let mut val_caselist: Vec<&crate::parser::ast::Case> = Vec::new();
    let mut exn_caselist: Vec<crate::parser::ast::Case> = Vec::new();
    for case in cases {
        let lhs_pat = tctx.arena.get_pat(case.pc_lhs);
        if let crate::parser::ast::PatternDesc::Ppat_exception(inner_pat) = &*lhs_pat.ppat_desc {
            // Unwrap the Ppat_exception: replace pc_lhs with the inner pattern
            let unwrapped_case = crate::parser::ast::Case {
                pc_bar: case.pc_bar,
                pc_lhs: *inner_pat,
                pc_guard: case.pc_guard,
                pc_rhs: case.pc_rhs,
            };
            exn_caselist.push(unwrapped_case);
        } else {
            val_caselist.push(case);
        }
    }

    let has_generalized_value_patterns = val_caselist.iter().any(|case| {
        pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(case.pc_lhs))
    });
    // Match OCaml type_cases: pass the generalized scrutinee type directly.
    // OCaml applies correct_levels/instance inside type_cases.
    let ty_arg = typed_scrutinee.exp_type;
    // Pass the GENERIC scrutinee type so instance() inside begin_def creates
    // fresh copies at the elevated level, matching OCaml's type_cases flow.
    let generic_scrutinee_ty = typed_scrutinee.exp_type;
    let contains_polyvars = val_caselist.iter().any(|case| {
        parsed_pattern_contains_polymorphic_variant(tctx.arena, tctx.arena.get_pat(case.pc_lhs))
    });
    let erase_either = contains_polyvars && type_contains_variant_either(ctx, ty_arg);
    let ty_arg = if has_generalized_value_patterns || erase_either {
        crate::types::ctype::subst_identity_copy(ctx, ty_arg)
    } else {
        ty_arg
    };
    let ty_res = if has_generalized_value_patterns {
        crate::types::ctype::subst_identity_copy(ctx, expected_ty)
    } else {
        expected_ty
    };
    let mut duplicated_case_env = None;
    let val_case_env = if has_generalized_value_patterns {
        duplicated_case_env = Some(duplicate_ident_types_for_gadt_cases(tctx, env, &val_caselist));
        duplicated_case_env.as_ref().unwrap_or(env)
    } else {
        env
    };
    let mut used_batch_non_gadt = false;
    let mut typed_val_cases = if has_generalized_value_patterns {
        type_match_cases_sequential(
            tctx,
            val_case_env,
            &val_caselist,
            ty_arg,
            generic_scrutinee_ty,
            ty_res,
            erase_either,
        )?
    } else {
        match type_match_cases_batch_non_gadt(
            tctx,
            env,
            &val_caselist,
            ty_arg,
            generic_scrutinee_ty,
            ty_res,
            erase_either,
        ) {
            Ok(cases) => {
                used_batch_non_gadt = true;
                cases
            }
            // Preserve existing recovery behavior for non-GADT patterns.
            Err(TypeCoreError::PatternTypeClash(_)) => {
                type_match_cases_sequential(
                    tctx,
                    env,
                    &val_caselist,
                    ty_arg,
                    generic_scrutinee_ty,
                    ty_res,
                    erase_either,
                )?
            }
            Err(err) => return Err(err),
        }
    };

    // Match OCaml's `unify_pats ty_arg'` step from type_cases.
    // OCaml unifies all pattern types through a shared node inside a single
    // begin_def scope. The sequential path misses this, causing each case's
    // pattern type to be an independent node. Post-hoc unification establishes
    // the same physical node-sharing (e.g., both GADT case patterns resolve
    // to the same Tconstr(kind, [Tconstr(t)]) node).
    if has_generalized_value_patterns && typed_val_cases.len() > 1 {
        let ctx = tctx.type_ctx;
        let ty_arg_prime = ctx.new_var(None);
        for typed_case in &typed_val_cases {
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, typed_case.c_lhs.pat_type, ty_arg_prime);
        }
    }

    // Type check exception cases against exn type.
    // OCaml routes exception cases through type_cases with Predef.type_exn,
    // which includes the propagation cycle (begin_def/end_def/generalize on
    // all pattern types). This ensures as-bound variables get generalized types
    // so instance() creates fresh copies at use sites.
    let typed_exn_cases = if !exn_caselist.is_empty() {
        let ctx = tctx.type_ctx;
        let exn_ty = crate::types::ctype::instance(ctx, ctx.predef_exn());
        let generic_exn_ty = ctx.predef_exn();
        let exn_case_refs: Vec<&crate::parser::ast::Case> = exn_caselist.iter().collect();
        type_match_cases_batch_non_gadt(
            tctx, env, &exn_case_refs, exn_ty, generic_exn_ty, expected_ty, false,
        )?
    } else {
        Vec::new()
    };

    // Match OCaml type_cases:
    //   if has_gadts then
    //     let ty_res' = instance env ty_res in
    //     List.iter (fun c -> unify_exp ~context:None env c.c_rhs ty_res') cases
    // This links per-case body result copies back through one shared node.
    if has_generalized_value_patterns {
        let shared_case_body_ty = crate::types::instance(ctx, expected_ty);
        for case in &typed_val_cases {
            unify_expression_types(
                tctx,
                case.c_rhs.exp_loc,
                case.c_rhs.exp_type,
                shared_case_body_ty,
                None,
            )?;
        }
    }

    if used_batch_non_gadt {
        // The batch non-GADT path now runs pressure/finalize on patterns in
        // OCaml order inside type_match_cases_batch_non_gadt (before body typing).
        // Keep only scrutinee-side propagation here.
        close_variant_rows_in_scrutinee_by_cases(tctx, val_case_env, &typed_val_cases, ty_arg);
        reopen_wildcard_covered_rows_in_scrutinee(tctx, val_case_env, &typed_val_cases, ty_arg);
        finalize_variant_in_scrutinee_type(tctx.type_ctx, ty_arg);
    } else {
        // OCaml shares row-field links between `instance` copies; Rust does not.
        // Merge case-discovered tags back into the scrutinee row before finalization.
        if std::env::var_os("RUST_DISABLE_CASE_ROW_MERGE").is_none() {
            merge_variant_row_fields_into_scrutinee(ctx, &typed_val_cases, ty_arg);
        }

        // Match OCaml typecore/parmatch: pressure_variants closes rows without
        // wildcard coverage, then finalize_variant converts Reither→Rpresent
        // in still-open rows. Both operate on ORIGINAL types first (shared with
        // expression types) to match OCaml's in-place mutation semantics, then
        // close_multi_label_variant_rows_in_cases copies and closes for pattern types.
        pressure_and_finalize_variant_rows(tctx, val_case_env, &mut typed_val_cases);

        close_variant_rows_across_case_pattern_types(tctx, val_case_env, &typed_val_cases);

        close_multi_label_variant_rows_in_cases(tctx, val_case_env, &mut typed_val_cases);

        // Also finalize on the copies (for fields in rows that stayed open after copy+close).
        for case in typed_val_cases.iter_mut() {
            finalize_variant_in_pattern(tctx, env, &mut case.c_lhs, erase_either);
        }

        close_variant_rows_in_scrutinee_by_cases(tctx, val_case_env, &typed_val_cases, ty_arg);

        // Reopen variant rows AFTER all closing steps. The closing logic operates
        // on per-case pattern types, but case 0 may share variant nodes with ty_arg
        // (identity instance). Closing case 0's pattern closes ty_arg too. Reopen
        // any ty_arg variant rows that have wildcard coverage in any case.
        reopen_wildcard_covered_rows_in_scrutinee(tctx, val_case_env, &typed_val_cases, ty_arg);

        // Propagate Reither→Rpresent conversions to ty_arg only after close/reopen.
        // This matches OCaml's pressure_variants -> finalize_variant sequencing:
        // rows closed by pressure must stay Reither-based, while rows that remain
        // open (wildcard coverage) are finalized to Rpresent.
        finalize_variant_in_scrutinee_type(tctx.type_ctx, ty_arg);
    }

    // OCaml type_cases: `unify_pats (instance env ty_arg)` propagation happens
    // INSIDE begin_def scope (line 3993), already handled by lines 5711-5720 in
    // type_match_cases_batch_non_gadt. Do NOT directly unify pattern types with
    // typed_scrutinee.exp_type — that creates false node sharing between scrutinee
    // and pattern types (OCaml keeps them separate via fresh instances).

    let partial = check_partial_simple(ctx, val_case_env, &typed_val_cases);

    // Keep sharing: match OCaml's `exp_type = instance env ty_expected`
    let result_ty = crate::types::instance(ctx, expected_ty);
    Ok(Expression::new(
        ExpressionDesc::Texp_match(
            Box::new(typed_scrutinee),
            typed_val_cases,
            typed_exn_cases,
            partial,
        ),
        loc.clone(),
        result_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Reopen variant rows in the scrutinee type that were closed by
/// pressure_and_finalize but have wildcard coverage in some case pattern.
fn reopen_wildcard_covered_rows_in_scrutinee(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[crate::types::typedtree::Case],
    scrutinee_ty: TypeExprRef,
) {
    let ctx = tctx.type_ctx;

    // For direct variant scrutinee
    let scrutinee_repr = ctx.repr(scrutinee_ty);
    let scrutinee_desc = ctx.get_desc(scrutinee_repr);
    match &*scrutinee_desc {
        TypeDesc::Tvariant(_) => {
            drop(scrutinee_desc);
            // Check if any case has a wildcard at this position
            let mut has_wildcard = false;
            for case in cases {
                if matches!(case.c_lhs.pat_desc, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) {
                    has_wildcard = true;
                    break;
                }
                // Also check inside or-patterns
                if has_wildcard_in_or_pattern(&case.c_lhs) {
                    has_wildcard = true;
                    break;
                }
            }
            if has_wildcard {
                reopen_variant_row(ctx, scrutinee_repr);
            }
        }
        TypeDesc::Ttuple(tys) => {
            let elem_tys: Vec<TypeExprRef> = tys.clone();
            drop(scrutinee_desc);
            // For each tuple position, check if any case has a wildcard there
            for (i, elem_ty) in elem_tys.iter().enumerate() {
                let elem_repr = ctx.repr(*elem_ty);
                let elem_desc = ctx.get_desc(elem_repr);
                let is_closed_variant = if let TypeDesc::Tvariant(row) = &*elem_desc {
                    let rd = crate::types::btype::row_repr(ctx, row);
                    rd.row_closed
                } else {
                    false
                };
                drop(elem_desc);
                if !is_closed_variant {
                    continue;
                }
                // Check if any case has a wildcard at tuple position i
                let mut has_wildcard = false;
                for case in cases {
                    if tuple_element_has_wildcard(&case.c_lhs, i) {
                        has_wildcard = true;
                        break;
                    }
                }
                if has_wildcard {
                    reopen_variant_row(ctx, elem_repr);
                }
            }
        }
        _ => {}
    }
}

fn close_variant_rows_in_scrutinee_by_cases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[crate::types::typedtree::Case],
    scrutinee_ty: TypeExprRef,
) {
    let mut matched_tags: HashSet<String> = HashSet::new();
    let mut variant_wildcard_rows: HashSet<usize> = HashSet::new();
    let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();

    for case in cases {
        collect_all_variant_tags_in_pattern(&case.c_lhs, &mut matched_tags);
        collect_rows_with_wildcard_coverage(tctx, env, &case.c_lhs, &mut variant_wildcard_rows);
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut labels_by_row);
    }

    normalize_wildcard_coverage_by_labels(tctx, &labels_by_row, &mut variant_wildcard_rows);

    let mut visited: HashSet<usize> = HashSet::new();
    close_open_variants_in_type(
        tctx.type_ctx,
        env,
        scrutinee_ty,
        &matched_tags,
        &variant_wildcard_rows,
        &mut visited,
    );
}

fn reopen_variant_row(ctx: &TypeContext<'_>, repr: TypeExprRef) {
    let desc = ctx.get_desc(repr);
    if let TypeDesc::Tvariant(row) = &*desc {
        let row_data = crate::types::btype::row_repr(ctx, row);
        let row_more_repr = ctx.repr(row_data.row_more);
        let row_more_desc = ctx.get_desc(row_more_repr);
        let has_non_nil_tail = !matches!(&*row_more_desc, TypeDesc::Tnil);
        drop(row_more_desc);
        if row_data.row_closed && has_non_nil_tail {
            drop(desc);
            let mut reopened = row_data;
            reopened.row_closed = false;
            ctx.set_desc(repr, TypeDesc::Tvariant(reopened));
        }
    }
}

/// Check if a pattern at a specific tuple element position is a wildcard
fn tuple_element_has_wildcard(pat: &Pattern, pos: usize) -> bool {
    match &pat.pat_desc {
        PatternDesc::Tpat_tuple(items) => {
            if pos < items.len() {
                pattern_is_wildcard(&items[pos])
            } else {
                false
            }
        }
        PatternDesc::Tpat_or(left, right, _) => {
            tuple_element_has_wildcard(left, pos) || tuple_element_has_wildcard(right, pos)
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            tuple_element_has_wildcard(inner, pos)
        }
        // If the entire pattern is a wildcard, all positions are wildcards
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
        _ => false,
    }
}

fn pattern_is_wildcard(pat: &Pattern) -> bool {
    match &pat.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
        PatternDesc::Tpat_alias(inner, _, _) => pattern_is_wildcard(inner),
        _ => false,
    }
}

fn has_wildcard_in_or_pattern(pat: &Pattern) -> bool {
    match &pat.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
        PatternDesc::Tpat_or(left, right, _) => {
            has_wildcard_in_or_pattern(left) || has_wildcard_in_or_pattern(right)
        }
        PatternDesc::Tpat_alias(inner, _, _) => has_wildcard_in_or_pattern(inner),
        _ => false,
    }
}

fn variant_row_key_for_pat_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat_type: TypeExprRef,
) -> Option<usize> {
    let ctx = tctx.type_ctx;
    let expanded = crate::types::ctype::expand_head(ctx, env, pat_type);
    let repr = ctx.repr(expanded);
    let desc = ctx.get_desc(repr);
    let is_variant = matches!(&*desc, TypeDesc::Tvariant(_));
    drop(desc);
    if is_variant { Some(repr.0) } else { None }
}

fn collect_variant_row_labels_in_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &Pattern,
    labels_by_row: &mut HashMap<usize, Vec<String>>,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(label, arg, _) => {
            if let Some(row_key) = variant_row_key_for_pat_type(tctx, env, pat.pat_type) {
                let labels = labels_by_row.entry(row_key).or_default();
                if !labels.iter().any(|existing| existing == label) {
                    labels.push(label.clone());
                }
            }
            if let Some(arg_pat) = arg {
                collect_variant_row_labels_in_pattern(tctx, env, arg_pat, labels_by_row);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            collect_variant_row_labels_in_pattern(tctx, env, inner, labels_by_row);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            collect_variant_row_labels_in_pattern(tctx, env, left, labels_by_row);
            collect_variant_row_labels_in_pattern(tctx, env, right, labels_by_row);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                collect_variant_row_labels_in_pattern(tctx, env, item, labels_by_row);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                collect_variant_row_labels_in_pattern(tctx, env, arg, labels_by_row);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                collect_variant_row_labels_in_pattern(tctx, env, field_pat, labels_by_row);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

fn reorder_variant_row_for_pat_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat_type: TypeExprRef,
    ordered_labels: &[String],
) {
    let ctx = tctx.type_ctx;
    let expanded = crate::types::ctype::expand_head(ctx, env, pat_type);
    let repr = ctx.repr(expanded);
    let desc = ctx.get_desc(repr);
    let row = match &*desc {
        TypeDesc::Tvariant(row) => row.clone(),
        _ => return,
    };
    drop(desc);

    let mut row = crate::types::btype::row_repr(ctx, &row);
    if row.row_fields.len() <= 1 {
        return;
    }

    let mut order_index: HashMap<String, usize> = HashMap::new();
    for (index, label) in ordered_labels.iter().enumerate() {
        order_index.entry(label.clone()).or_insert(index);
    }

    let mut indexed_fields = row
        .row_fields
        .into_iter()
        .enumerate()
        .map(|(original_index, (label, field))| {
            let label_order = order_index.get(&label).copied().unwrap_or(usize::MAX);
            (label_order, original_index, (label, field))
        })
        .collect::<Vec<_>>();
    indexed_fields.sort_by(|(order1, index1, _), (order2, index2, _)| {
        order1.cmp(order2).then(index1.cmp(index2))
    });
    row.row_fields = indexed_fields
        .into_iter()
        .map(|(_, _, entry)| entry)
        .collect();
    ctx.set_desc(repr, TypeDesc::Tvariant(row));
}

fn reorder_multi_label_variant_rows_in_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
    row_label_orders: &HashMap<usize, Vec<String>>,
) {
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(row_key) = variant_row_key_for_pat_type(tctx, env, pat.pat_type) {
                if let Some(ordered_labels) = row_label_orders.get(&row_key) {
                    reorder_variant_row_for_pat_type(tctx, env, pat.pat_type, ordered_labels);
                }
            }
            if let Some(arg_pat) = arg {
                reorder_multi_label_variant_rows_in_pattern(
                    tctx,
                    env,
                    arg_pat,
                    row_label_orders,
                );
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            reorder_multi_label_variant_rows_in_pattern(tctx, env, inner, row_label_orders);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            reorder_multi_label_variant_rows_in_pattern(tctx, env, left, row_label_orders);
            reorder_multi_label_variant_rows_in_pattern(tctx, env, right, row_label_orders);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                reorder_multi_label_variant_rows_in_pattern(tctx, env, item, row_label_orders);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                reorder_multi_label_variant_rows_in_pattern(tctx, env, arg, row_label_orders);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                reorder_multi_label_variant_rows_in_pattern(
                    tctx,
                    env,
                    field_pat,
                    row_label_orders,
                );
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Finalize variant patterns: convert Reither fields to Rpresent in open rows.
/// Matches OCaml's finalize_variant (typecore.ml:358-385).
fn finalize_variant_in_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
    convert_closed_reither: bool,
) {
    let debug_finalize = std::env::var_os("RUST_DEBUG_FINALIZE_VARIANT").is_some();
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(tag, arg, _) => {
            let ctx = tctx.type_ctx;
            let expanded = crate::types::ctype::expand_head(ctx, env, pat.pat_type);
            let repr = ctx.repr(expanded);
            let desc = ctx.get_desc(repr);
            if let TypeDesc::Tvariant(row) = &*desc {
                let row = crate::types::btype::row_repr(ctx, row);
                let field_repr = crate::types::btype::row_field(ctx, tag, &row);
                match field_repr {
                    crate::types::type_expr::RowField::Rabsent => {}
                    crate::types::type_expr::RowField::Reither {
                        constant: true,
                        types,
                        link,
                        ..
                    } if (!row.row_closed || convert_closed_reither) && types.is_empty() => {
                        drop(desc);
                        ctx.set_row_field(link, crate::types::type_expr::RowField::Rpresent(None));
                    }
                    crate::types::type_expr::RowField::Reither {
                        constant: false,
                        types,
                        link,
                        ..
                    } if (!row.row_closed || convert_closed_reither) && !types.is_empty() => {
                        if debug_finalize && tag == "V" {
                            let line = tctx.arena.to_location(pat.pat_loc).loc_start.line;
                            let arg_repr: isize = arg
                                .as_ref()
                                .map(|arg_pat| ctx.repr(arg_pat.pat_type).0 as isize)
                                .unwrap_or(-1);
                            let type_ids: Vec<usize> =
                                types.iter().map(|ty| ctx.repr(*ty).0).collect();
                            eprintln!(
                                "[finalize-variant] line={} row_closed={} convert_closed={} pat_type=#{} arg_type=#{} types={:?}",
                                line,
                                row.row_closed,
                                convert_closed_reither,
                                ctx.repr(pat.pat_type).0,
                                arg_repr,
                                type_ids
                            );
                        }
                        let head = types[0];
                        drop(desc);
                        ctx.set_row_field(
                            link,
                            crate::types::type_expr::RowField::Rpresent(Some(head)),
                        );
                        // OCaml finalize_variant only unifies payload pattern types
                        // for open rows. For closed-row conversion under erase_either,
                        // keep payload node identity as produced during pattern typing.
                        if !row.row_closed {
                            if let Some(arg_pat) = arg.as_ref() {
                                for ty in types {
                                    if debug_finalize && tag == "V" {
                                        eprintln!(
                                            "[finalize-variant-unify] before arg=#{} ty=#{}",
                                            ctx.repr(arg_pat.pat_type).0,
                                            ctx.repr(ty).0
                                        );
                                    }
                                    let _ = unify_pattern_types(
                                        tctx,
                                        arg_pat.pat_loc,
                                        arg_pat.pat_type,
                                        ty,
                                    );
                                    if debug_finalize && tag == "V" {
                                        eprintln!(
                                            "[finalize-variant-unify] after arg=#{} ty=#{}",
                                            ctx.repr(arg_pat.pat_type).0,
                                            ctx.repr(ty).0
                                        );
                                    }
                                }
                            }
                        }
                    }
                    // OCaml case:
                    // | Reither (c, _l, true, e) when not (row_fixed row) ->
                    //     set_row_field e (Reither (c, [], false, ref None))
                    crate::types::type_expr::RowField::Reither {
                        constant,
                        matched: true,
                        link,
                        ..
                    } if !crate::types::btype::row_fixed(ctx, &row) => {
                        drop(desc);
                        ctx.set_row_field(
                            link,
                            crate::types::type_expr::RowField::Reither {
                                constant,
                                types: vec![],
                                matched: false,
                                link: ctx.alloc_row_field(None),
                            },
                        );
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }

    // Recurse into sub-patterns
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                finalize_variant_in_pattern(tctx, env, arg_pat, convert_closed_reither);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            finalize_variant_in_pattern(tctx, env, inner, convert_closed_reither);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            finalize_variant_in_pattern(tctx, env, left, convert_closed_reither);
            finalize_variant_in_pattern(tctx, env, right, convert_closed_reither);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                finalize_variant_in_pattern(tctx, env, item, convert_closed_reither);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                finalize_variant_in_pattern(tctx, env, arg, convert_closed_reither);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                finalize_variant_in_pattern(tctx, env, field_pat, convert_closed_reither);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

fn close_variant_row_for_pat_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat_type: TypeExprRef,
) {
    let ctx = tctx.type_ctx;
    let expanded = crate::types::ctype::expand_head(ctx, env, pat_type);
    let repr = ctx.repr(expanded);
    let desc = ctx.get_desc(repr);
    let row = match &*desc {
        TypeDesc::Tvariant(row) => row.clone(),
        _ => return,
    };
    drop(desc);

    let row = crate::types::btype::row_repr(ctx, &row);
    if row.row_closed || crate::types::btype::row_fixed(ctx, &row) {
        return;
    }

    let mut row_name = row.row_name.clone();
    for (_tag, field) in &row.row_fields {
        if let crate::types::type_expr::RowField::Reither {
            matched: false,
            link,
            ..
        } = crate::types::btype::row_field_repr(ctx, field)
        {
            ctx.set_row_field(link, crate::types::type_expr::RowField::Rabsent);
            row_name = None;
        }
    }

    if !row.row_closed || row_name != row.row_name {
        let closed_tail = ctx.new_generic_type(TypeDesc::Tvariant(crate::types::type_expr::RowDesc {
            row_fields: vec![],
            row_more: ctx.new_generic_var(None),
            row_closed: true,
            row_fixed: row.row_fixed,
            row_name,
        }));
        let _ = crate::types::unify(ctx, &mut tctx.unify_state, row.row_more, closed_tail);
    }
}

/// Close variant rows in let binding patterns, matching OCaml's
/// `Parmatch.pressure_variants env [pat]` call in type_let (typecore.ml:4120).
/// For let bindings, variant patterns have no wildcard alternative at the same
/// position, so all non-fixed variant rows on Tpat_variant nodes are closed.
/// This matches OCaml's close_variant: sets unmatched Reither fields to Rabsent
/// and marks the row as closed.
fn pressure_variant_rows_in_let_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(_, _, _) => {
            let ctx = tctx.type_ctx;
            let expanded = crate::types::ctype::expand_head(ctx, env, pat.pat_type);
            let repr = ctx.repr(expanded);
            let desc = ctx.get_desc(repr);
            if let TypeDesc::Tvariant(row) = &*desc {
                let row = crate::types::btype::row_repr(ctx, row);
                if !row.row_closed && !row.row_fixed {
                    drop(desc);
                    close_variant_row_for_pat_type(tctx, env, pat.pat_type);
                } else {
                    drop(desc);
                }
            }
        }
        _ => {}
    }

    // Recurse into sub-patterns
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                pressure_variant_rows_in_let_pattern(tctx, env, arg_pat);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            pressure_variant_rows_in_let_pattern(tctx, env, inner);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            pressure_variant_rows_in_let_pattern(tctx, env, left);
            pressure_variant_rows_in_let_pattern(tctx, env, right);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                pressure_variant_rows_in_let_pattern(tctx, env, item);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                pressure_variant_rows_in_let_pattern(tctx, env, arg);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                pressure_variant_rows_in_let_pattern(tctx, env, field_pat);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Merge variant row fields from all case patterns into the scrutinee type.
/// In OCaml's type_cases, all patterns share the same ty_arg. When case `| #A`
/// adds tag "A" to the variant row and case `| #B` adds tag "B", both tags end
/// up in the shared ty_arg visible to the scrutinee expression.
/// In Rust's per-case instancing, each case has its own variant row copy.
/// This function collects row fields from all case patterns and merges
/// them into the SCRUTINEE type only (not into individual case pattern types,
/// which should keep their per-case field sets).
fn merge_variant_row_fields_into_scrutinee(
    ctx: &TypeContext<'_>,
    cases: &[crate::types::typedtree::Case],
    scrutinee_ty: TypeExprRef,
) {
    let scrutinee_repr = ctx.repr(scrutinee_ty);
    let scrutinee_desc = ctx.get_desc(scrutinee_repr);
    match &*scrutinee_desc {
        TypeDesc::Tvariant(_) => {
            drop(scrutinee_desc);
            merge_variant_row_fields_single(ctx, cases, scrutinee_repr, |case| case.c_lhs.pat_type);
        }
        TypeDesc::Ttuple(tys) => {
            let elem_tys: Vec<TypeExprRef> = tys.clone();
            drop(scrutinee_desc);
            for (i, elem_ty) in elem_tys.iter().enumerate() {
                let elem_repr = ctx.repr(*elem_ty);
                let elem_desc = ctx.get_desc(elem_repr);
                let is_variant = matches!(&*elem_desc, TypeDesc::Tvariant(_));
                drop(elem_desc);
                if is_variant {
                    merge_variant_row_fields_single(ctx, cases, elem_repr, |case| {
                        let pat_repr = ctx.repr(case.c_lhs.pat_type);
                        let pat_desc = ctx.get_desc(pat_repr);
                        if let TypeDesc::Ttuple(pat_tys) = &*pat_desc {
                            if i < pat_tys.len() {
                                return pat_tys[i];
                            }
                        }
                        case.c_lhs.pat_type
                    });
                }
            }
        }
        _ => return,
    }
}

/// Merge variant row fields from all case patterns into a single variant type node.
/// `get_pat_variant_ty` extracts the relevant variant type from each case's pattern.
fn merge_variant_row_fields_single(
    ctx: &TypeContext<'_>,
    cases: &[crate::types::typedtree::Case],
    variant_repr: TypeExprRef,
    get_pat_variant_ty: impl Fn(&crate::types::typedtree::Case) -> TypeExprRef,
) {
    use std::collections::HashMap;
    use crate::types::btype::row_repr;

    let desc = ctx.get_desc(variant_repr);
    let variant_row = match &*desc {
        TypeDesc::Tvariant(row) => row.clone(),
        _ => return,
    };
    drop(desc);

    let variant_row_data = row_repr(ctx, &variant_row);

    // Collect ALL variant row fields: start with scrutinee's, add from patterns.
    let mut all_fields: HashMap<String, crate::types::type_expr::RowField> = HashMap::new();
    for (tag, field) in &variant_row_data.row_fields {
        all_fields.insert(tag.clone(), field.clone());
    }

    // Collect new fields from all case pattern variant types
    for case in cases {
        let pat_ty = get_pat_variant_ty(case);
        let repr = ctx.repr(pat_ty);
        let desc = ctx.get_desc(repr);
        if let TypeDesc::Tvariant(row) = &*desc {
            let row_data = row_repr(ctx, row);
            for (tag, field) in &row_data.row_fields {
                all_fields.entry(tag.clone()).or_insert_with(|| field.clone());
            }
        }
    }

    if all_fields.len() <= variant_row_data.row_fields.len() {
        return; // No new fields to add
    }

    // Build sorted field list
    let mut merged_fields: Vec<_> = all_fields.into_iter().collect();
    merged_fields.sort_by(|(a, _), (b, _)| a.cmp(b));

    // Set on scrutinee element
    let mut merged_row = variant_row_data;
    merged_row.row_fields = merged_fields.clone();
    ctx.set_desc(variant_repr, TypeDesc::Tvariant(merged_row));

    // Also propagate all merged fields into each case's pattern type.
    for case in cases {
        let pat_ty = get_pat_variant_ty(case);
        let pat_repr = ctx.repr(pat_ty);
        if pat_repr == variant_repr {
            continue;
        }
        let pat_desc = ctx.get_desc(pat_repr);
        if let TypeDesc::Tvariant(row) = &*pat_desc {
            let pat_row_data = row_repr(ctx, row);
            if pat_row_data.row_fields.len() < merged_fields.len() {
                let mut pat_fields: HashMap<String, crate::types::type_expr::RowField> = HashMap::new();
                for (tag, field) in &pat_row_data.row_fields {
                    pat_fields.insert(tag.clone(), field.clone());
                }
                for (tag, field) in &merged_fields {
                    pat_fields.entry(tag.clone()).or_insert_with(|| field.clone());
                }
                let mut updated_row = pat_row_data;
                updated_row.row_fields = pat_fields.into_iter().collect();
                updated_row.row_fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                drop(pat_desc);
                ctx.set_desc(pat_repr, TypeDesc::Tvariant(updated_row));
            }
        }
    }
}

/// Propagate variant row closures across all case pattern types.
/// In OCaml, all cases share ty_arg directly, so closing a variant row in any
/// case (via pressure_variants) propagates to all cases. In Rust, each case
/// gets a fresh instance, so we must explicitly walk each case pattern type
/// and close open variant rows that are fully covered by tags matched across
/// all cases.
fn close_variant_rows_across_case_pattern_types(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[crate::types::typedtree::Case],
) {
    // Collect all variant tags matched across all patterns, and detect wildcards
    // at variant-typed positions.
    let mut matched_tags: HashSet<String> = HashSet::new();
    let mut variant_wildcard_rows: HashSet<usize> = HashSet::new();
    let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
    for case in cases {
        collect_all_variant_tags_in_pattern(&case.c_lhs, &mut matched_tags);
        collect_rows_with_wildcard_coverage(tctx, env, &case.c_lhs, &mut variant_wildcard_rows);
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut labels_by_row);
    }

    // Normalize wildcard coverage across per-case instances
    normalize_wildcard_coverage_by_labels(tctx, &labels_by_row, &mut variant_wildcard_rows);

    if matched_tags.is_empty() {
        return;
    }

    // Walk each case's pattern type tree and close open variant rows
    for case in cases {
        let mut visited = HashSet::new();
        close_open_variants_in_pattern_types(
            tctx.type_ctx,
            env,
            &case.c_lhs,
            &matched_tags,
            &variant_wildcard_rows,
            &mut visited,
        );
    }
}

/// Walk a pattern's type expression tree (recursively through the pattern and
/// its type), closing open variant rows whose fields are all covered.
fn close_open_variants_in_pattern_types(
    ctx: &TypeContext<'_>,
    env: &Env,
    pat: &Pattern,
    matched_tags: &HashSet<String>,
    wildcard_rows: &HashSet<usize>,
    visited: &mut HashSet<usize>,
) {
    // Close open variant rows in this pattern's type
    close_open_variants_in_type(ctx, env, pat.pat_type, matched_tags, wildcard_rows, visited);

    // Recurse into sub-patterns
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                close_open_variants_in_pattern_types(
                    ctx, env, arg_pat, matched_tags, wildcard_rows, visited,
                );
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            close_open_variants_in_pattern_types(
                ctx, env, inner, matched_tags, wildcard_rows, visited,
            );
        }
        PatternDesc::Tpat_or(left, right, _) => {
            close_open_variants_in_pattern_types(
                ctx, env, left, matched_tags, wildcard_rows, visited,
            );
            close_open_variants_in_pattern_types(
                ctx, env, right, matched_tags, wildcard_rows, visited,
            );
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                close_open_variants_in_pattern_types(
                    ctx, env, item, matched_tags, wildcard_rows, visited,
                );
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                close_open_variants_in_pattern_types(
                    ctx, env, arg, matched_tags, wildcard_rows, visited,
                );
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                close_open_variants_in_pattern_types(
                    ctx, env, field_pat, matched_tags, wildcard_rows, visited,
                );
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Collect ALL variant tag names from a pattern tree (recursively).
fn collect_all_variant_tags_in_pattern(
    pat: &Pattern,
    tags: &mut HashSet<String>,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(label, arg, _) => {
            tags.insert(label.clone());
            if let Some(arg_pat) = arg {
                collect_all_variant_tags_in_pattern(arg_pat, tags);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            collect_all_variant_tags_in_pattern(inner, tags);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            collect_all_variant_tags_in_pattern(left, tags);
            collect_all_variant_tags_in_pattern(right, tags);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                collect_all_variant_tags_in_pattern(item, tags);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                collect_all_variant_tags_in_pattern(arg, tags);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                collect_all_variant_tags_in_pattern(field_pat, tags);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Walk a type expression recursively and close open variant rows whose fields
/// are ALL covered by the given matched tags.
fn close_open_variants_in_type(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    matched_tags: &HashSet<String>,
    wildcard_rows: &HashSet<usize>,
    visited: &mut HashSet<usize>,
) {
    close_open_variants_in_type_inner(ctx, env, ty, matched_tags, wildcard_rows, visited, 0);
}

fn close_open_variants_in_type_inner(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    matched_tags: &HashSet<String>,
    wildcard_rows: &HashSet<usize>,
    visited: &mut HashSet<usize>,
    depth: usize,
) {
    // Guard against infinite expansion of recursive type aliases like
    // `type rec vlist<'a> = [#Nil | #Cons('a, vlist<'a>)]`.
    // expand_head creates fresh nodes each time, so the node-based `visited` set
    // can't catch cycles in these expansions. Use a depth limit as safety net.
    if depth > 50 {
        return;
    }
    let expanded = crate::types::ctype::expand_head(ctx, env, ty);
    let repr = ctx.repr(expanded);
    if !visited.insert(repr.0) {
        return;
    }
    let desc = ctx.get_desc(repr);
    match &*desc {
        TypeDesc::Tvariant(row) => {
            let row_data = crate::types::btype::row_repr(ctx, row);
            if !row_data.row_closed && !row_data.row_fields.is_empty() && !wildcard_rows.contains(&repr.0) {
                // Check if ALL row fields are covered by matched tags
                let all_covered = row_data
                    .row_fields
                    .iter()
                    .all(|(tag, _)| matched_tags.contains(tag));
                if all_covered {
                    let mut closed_row = row_data;
                    closed_row.row_closed = true;
                    drop(desc);
                    ctx.set_desc(repr, TypeDesc::Tvariant(closed_row));
                    return;
                }
            }
            // Recurse into row field types and row_more
            let more = row_data.row_more;
            let field_types: Vec<TypeExprRef> = row_data
                .row_fields
                .iter()
                .flat_map(|(_, field)| match field {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => vec![*t],
                    crate::types::type_expr::RowField::Reither { types, .. } => types.clone(),
                    _ => vec![],
                })
                .collect();
            drop(desc);
            close_open_variants_in_type_inner(ctx, env, more, matched_tags, wildcard_rows, visited, depth + 1);
            for t in field_types {
                close_open_variants_in_type_inner(ctx, env, t, matched_tags, wildcard_rows, visited, depth + 1);
            }
        }
        TypeDesc::Tconstr { args, .. } => {
            let args = args.clone();
            drop(desc);
            for arg in args {
                close_open_variants_in_type_inner(ctx, env, arg, matched_tags, wildcard_rows, visited, depth + 1);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            let arg_ty = arg.typ;
            let ret_ty = *ret;
            drop(desc);
            close_open_variants_in_type_inner(ctx, env, arg_ty, matched_tags, wildcard_rows, visited, depth + 1);
            close_open_variants_in_type_inner(ctx, env, ret_ty, matched_tags, wildcard_rows, visited, depth + 1);
        }
        TypeDesc::Ttuple(items) => {
            let items = items.clone();
            drop(desc);
            for item in items {
                close_open_variants_in_type_inner(ctx, env, item, matched_tags, wildcard_rows, visited, depth + 1);
            }
        }
        _ => {}
    }
}

fn copy_pattern_types(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) {
    pat.pat_type = copy_case_type(tctx.type_ctx, env, pat.pat_type, cache);
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                copy_pattern_types(tctx, env, arg_pat, cache);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            copy_pattern_types(tctx, env, inner, cache);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            copy_pattern_types(tctx, env, left, cache);
            copy_pattern_types(tctx, env, right, cache);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                copy_pattern_types(tctx, env, item, cache);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                copy_pattern_types(tctx, env, arg, cache);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                copy_pattern_types(tctx, env, field_pat, cache);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

fn close_multi_label_variant_rows_in_pattern(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
    rows_to_close: &HashSet<usize>,
) {
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(row_key) = variant_row_key_for_pat_type(tctx, env, pat.pat_type) {
                if rows_to_close.contains(&row_key) {
                    close_variant_row_for_pat_type(tctx, env, pat.pat_type);
                }
            }
            if let Some(arg_pat) = arg {
                close_multi_label_variant_rows_in_pattern(tctx, env, arg_pat, rows_to_close);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            close_multi_label_variant_rows_in_pattern(tctx, env, inner, rows_to_close);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            close_multi_label_variant_rows_in_pattern(tctx, env, left, rows_to_close);
            close_multi_label_variant_rows_in_pattern(tctx, env, right, rows_to_close);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                close_multi_label_variant_rows_in_pattern(tctx, env, item, rows_to_close);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                close_multi_label_variant_rows_in_pattern(tctx, env, arg, rows_to_close);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                close_multi_label_variant_rows_in_pattern(tctx, env, field_pat, rows_to_close);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Like finalize_variant_in_pattern but ONLY performs Reither→Rpresent conversion
/// (cases 1+2). Does NOT clear types in case 3. Used for modifying original types
/// shared with expression types, where OCaml's mutable ref links would preserve
/// the original field structure.
fn finalize_variant_rpresent_only(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &mut Pattern,
) {
    let debug_finalize_original = std::env::var_os("RUST_DEBUG_FINALIZE_ORIGINAL").is_some();
    let debug_pressure_rows = std::env::var_os("RUST_DEBUG_PRESSURE_ROWS").is_some();
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(tag, arg, _) => {
            let ctx = tctx.type_ctx;
            let expanded = crate::types::ctype::expand_head(ctx, env, pat.pat_type);
            let repr = ctx.repr(expanded);
            let desc = ctx.get_desc(repr);
            if let TypeDesc::Tvariant(row) = &*desc {
                let row = crate::types::btype::row_repr(ctx, row);
                let field_repr = crate::types::btype::row_field(ctx, tag, &row);
                if debug_pressure_rows
                    && (tag == "TopLeft"
                        || tag == "BottomLeft"
                        || tag == "S"
                        || tag == "M"
                        || tag == "L")
                {
                    let row_key = variant_row_key_for_pat_type(tctx, env, pat.pat_type)
                        .map(|k| k as isize)
                        .unwrap_or(-1);
                    let line = tctx.arena.to_location(pat.pat_loc).loc_start.line;
                    eprintln!(
                        "[finalize-original-seen] line={} row_key={} repr={} row_closed={} row_name={} tag={} field={:?}",
                        line,
                        row_key,
                        repr.0,
                        row.row_closed,
                        row.row_name.is_some(),
                        tag,
                        field_repr
                    );
                }
                let replacement = match field_repr {
                    crate::types::type_expr::RowField::Rabsent => None,
                    crate::types::type_expr::RowField::Reither {
                        constant: true,
                        types,
                        link,
                        ..
                    } if !row.row_closed && types.is_empty() => {
                        Some((link, crate::types::type_expr::RowField::Rpresent(None)))
                    }
                    crate::types::type_expr::RowField::Reither {
                        constant: false,
                        types,
                        link,
                        ..
                    } if !row.row_closed && !types.is_empty() => {
                        if debug_finalize_original && tag == "V" {
                            let line = tctx.arena.to_location(pat.pat_loc).loc_start.line;
                            let arg_repr: isize = arg
                                .as_ref()
                                .map(|arg_pat| ctx.repr(arg_pat.pat_type).0 as isize)
                                .unwrap_or(-1);
                            let type_ids: Vec<usize> =
                                types.iter().map(|ty| ctx.repr(*ty).0).collect();
                            eprintln!(
                                "[finalize-original] line={} row_closed={} pat_type=#{} arg_type=#{} types={:?}",
                                line,
                                row.row_closed,
                                ctx.repr(pat.pat_type).0,
                                arg_repr,
                                type_ids
                            );
                        }
                        if let Some(arg_pat) = arg.as_ref() {
                            for ty in &types {
                                if debug_finalize_original && tag == "V" {
                                    eprintln!(
                                        "[finalize-original-unify] before arg=#{} ty=#{}",
                                        ctx.repr(arg_pat.pat_type).0,
                                        ctx.repr(*ty).0
                                    );
                                }
                                let _ = unify_pattern_types(
                                    tctx,
                                    arg_pat.pat_loc,
                                    arg_pat.pat_type,
                                    *ty,
                                );
                                if debug_finalize_original && tag == "V" {
                                    eprintln!(
                                        "[finalize-original-unify] after arg=#{} ty=#{}",
                                        ctx.repr(arg_pat.pat_type).0,
                                        ctx.repr(*ty).0
                                    );
                                }
                            }
                        }
                        Some((
                            link,
                            crate::types::type_expr::RowField::Rpresent(Some(types[0])),
                        ))
                    }
                    // Match OCaml finalize_variant case 3:
                    // Reither(c, _l, true, e) when not (row_fixed row) ->
                    //   Reither(c, [], false, ref None)
                    crate::types::type_expr::RowField::Reither {
                        constant,
                        matched: true,
                        link,
                        ..
                    } if !crate::types::btype::row_fixed(ctx, &row) => Some((
                        link,
                        crate::types::type_expr::RowField::Reither {
                            constant,
                            types: vec![],
                            matched: false,
                            link: ctx.alloc_row_field(None),
                        },
                    )),
                    _ => None,
                };
                if let Some((link, new_field)) = replacement {
                    if debug_pressure_rows
                        && (tag == "TopLeft"
                            || tag == "BottomLeft"
                            || tag == "S"
                            || tag == "M"
                            || tag == "L")
                    {
                        let row_key = variant_row_key_for_pat_type(tctx, env, pat.pat_type)
                            .map(|k| k as isize)
                            .unwrap_or(-1);
                        let line = tctx.arena.to_location(pat.pat_loc).loc_start.line;
                        eprintln!(
                            "[finalize-original-row] line={} row_key={} repr={} row_closed={} tag={} set={:?}",
                            line,
                            row_key,
                            repr.0,
                            row.row_closed,
                            tag,
                            new_field
                        );
                    }
                    drop(desc);
                    ctx.set_row_field(link, new_field);
                }
            }
        }
        _ => {}
    }

    // Recurse into sub-patterns
    match &mut pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                finalize_variant_rpresent_only(tctx, env, arg_pat);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            finalize_variant_rpresent_only(tctx, env, inner);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            finalize_variant_rpresent_only(tctx, env, left);
            finalize_variant_rpresent_only(tctx, env, right);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                finalize_variant_rpresent_only(tctx, env, item);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                finalize_variant_rpresent_only(tctx, env, arg);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                finalize_variant_rpresent_only(tctx, env, field_pat);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Convert Reither→Rpresent in a single variant row (if open).
/// Returns true if any conversion was made.
fn finalize_variant_row_rpresent(
    ctx: &TypeContext<'_>,
    variant_repr: TypeExprRef,
) -> bool {
    let desc = ctx.get_desc(variant_repr);
    if let TypeDesc::Tvariant(row) = &*desc {
        let row = crate::types::btype::row_repr(ctx, row);
        if !row.row_closed {
            let labels: Vec<String> = row.row_fields.iter().map(|(tag, _)| tag.clone()).collect();
            drop(desc);
            let mut changed = false;
            for tag in labels {
                match crate::types::btype::row_field(ctx, &tag, &row) {
                    crate::types::type_expr::RowField::Reither {
                        constant: true,
                        types,
                        link,
                        ..
                    } if types.is_empty() => {
                        ctx.set_row_field(link, crate::types::type_expr::RowField::Rpresent(None));
                        changed = true;
                    }
                    crate::types::type_expr::RowField::Reither {
                        constant: false,
                        types,
                        link,
                        ..
                    } if !types.is_empty() => {
                        ctx.set_row_field(
                            link,
                            crate::types::type_expr::RowField::Rpresent(Some(types[0])),
                        );
                        changed = true;
                    }
                    _ => {}
                }
            }
            return changed;
        }
    }
    false
}

/// Finalize variant rows in ty_arg after case pattern finalization.
/// In OCaml, finalize_variant on case patterns also updates ty_arg because
/// they share mutable row field refs. In Rust, we need an explicit pass.
/// Only handles direct variants and tuple-of-variants (the common patterns).
fn finalize_variant_in_scrutinee_type(
    ctx: &TypeContext<'_>,
    ty_arg: TypeExprRef,
) {
    let repr = ctx.repr(ty_arg);
    let desc = ctx.get_desc(repr);
    match &*desc {
        TypeDesc::Tvariant(_) => {
            drop(desc);
            finalize_variant_row_rpresent(ctx, repr);
        }
        TypeDesc::Ttuple(tys) => {
            let tys: Vec<_> = tys.clone();
            drop(desc);
            for t in &tys {
                let elem_repr = ctx.repr(*t);
                let elem_desc = ctx.get_desc(elem_repr);
                let is_variant = matches!(&*elem_desc, TypeDesc::Tvariant(_));
                drop(elem_desc);
                if is_variant {
                    finalize_variant_row_rpresent(ctx, elem_repr);
                }
            }
        }
        _ => {}
    }
}

/// Collect variant row keys where any case has a non-variant pattern (wildcard/any/var)
/// at a position whose type is a variant. These rows have "wildcard coverage" and
/// should NOT be closed (matching OCaml's pressure_variants behavior).
fn collect_rows_with_wildcard_coverage(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &Pattern,
    result: &mut HashSet<usize>,
) {
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            // This IS a variant pattern — not a wildcard for this row
            if let Some(arg_pat) = arg {
                collect_rows_with_wildcard_coverage(tctx, env, arg_pat, result);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => {
            // Wildcard: if this position's type is a variant, mark that row
            if let Some(row_key) = variant_row_key_for_pat_type(tctx, env, pat.pat_type) {
                result.insert(row_key);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            collect_rows_with_wildcard_coverage(tctx, env, inner, result);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            collect_rows_with_wildcard_coverage(tctx, env, left, result);
            collect_rows_with_wildcard_coverage(tctx, env, right, result);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                collect_rows_with_wildcard_coverage(tctx, env, item, result);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                collect_rows_with_wildcard_coverage(tctx, env, arg, result);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                collect_rows_with_wildcard_coverage(tctx, env, field_pat, result);
            }
        }
        PatternDesc::Tpat_constant(_) => {}
    }
}

/// Normalize wildcard coverage across per-case instances.
/// Since instance() creates separate Tvariant nodes for each case, a wildcard
/// in case N has a different node ID from the variant patterns in other cases.
/// This function extracts the row_fields labels from each wildcard row's type,
/// then marks any labeled row with the same label set as also having wildcard coverage.
fn normalize_wildcard_coverage_by_labels(
    tctx: &mut TypeCheckContext<'_>,
    labels_by_row: &HashMap<usize, Vec<String>>,
    rows_with_wildcards: &mut HashSet<usize>,
) {
    // For each wildcard row, get its variant labels from the type's row_fields
    let mut wildcard_label_sets: Vec<Vec<String>> = Vec::new();
    for &wildcard_key in rows_with_wildcards.iter() {
        let ctx = tctx.type_ctx;
        let ty = TypeExprRef(wildcard_key);
        let desc = ctx.get_desc(ty);
        if let TypeDesc::Tvariant(row) = &*desc {
            let mut labels: Vec<String> = row.row_fields.iter().map(|(l, _)| l.clone()).collect();
            labels.sort();
            wildcard_label_sets.push(labels);
        }
    }

    // For each labeled row, check if its row_fields labels match any wildcard row's labels
    let mut new_wildcards: Vec<usize> = Vec::new();
    for (&row_key, _) in labels_by_row.iter() {
        if rows_with_wildcards.contains(&row_key) {
            continue;
        }
        let ctx = tctx.type_ctx;
        let ty = TypeExprRef(row_key);
        let desc = ctx.get_desc(ty);
        if let TypeDesc::Tvariant(row) = &*desc {
            let mut labels: Vec<String> = row.row_fields.iter().map(|(l, _)| l.clone()).collect();
            labels.sort();
            for wildcard_labels in &wildcard_label_sets {
                // Use subset matching: a wildcard row from an earlier case
                // may have fewer labels than a labeled row from a later case
                // (since per-case instances are created before merge adds all
                // tags). If all wildcard labels appear in the labeled row,
                // they represent the same variant type position.
                if !wildcard_labels.is_empty()
                    && wildcard_labels.iter().all(|l| labels.contains(l))
                {
                    new_wildcards.push(row_key);
                    break;
                }
            }
        }
    }

    for key in new_wildcards {
        rows_with_wildcards.insert(key);
    }
}

/// Match OCaml's pressure_variants + finalize_variant on ORIGINAL types.
/// 1. Close variant rows without wildcard coverage (like OCaml's pressure_variants)
/// 2. Convert Reither→Rpresent in still-open rows (like OCaml's finalize_variant)
/// Both operate on the original types shared with expression types.
/// NOTE: Only performs Rpresent conversion (cases 1+2), NOT the types-clearing
/// case 3, because OCaml's case 3 uses mutable ref links that preserve the
/// original field structure visible to other references.
fn pressure_and_finalize_variant_rows(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &mut [crate::types::typedtree::Case],
) {
    let debug_pressure_rows = std::env::var_os("RUST_DEBUG_PRESSURE_ROWS").is_some();
    // Step 1: Collect variant row labels and wildcard coverage info
    let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
    let mut rows_with_wildcards: HashSet<usize> = HashSet::new();

    for case in cases.iter() {
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut labels_by_row);
        collect_rows_with_wildcard_coverage(tctx, env, &case.c_lhs, &mut rows_with_wildcards);
    }

    // Normalize wildcard coverage across per-case instances:
    // instance() creates separate Tvariant nodes for each case, so a wildcard in
    // case N has a different node ID from the variant pattern in case M, even though
    // they represent the same type. Propagate wildcard coverage by matching variant
    // label sets: if a wildcard row has the same labels as a labeled row, they came
    // from the same scrutinee type and the labeled row should be protected too.
    normalize_wildcard_coverage_by_labels(tctx, &labels_by_row, &mut rows_with_wildcards);

    // Step 2: Determine which rows to close (has labels, no wildcard coverage)
    // OCaml's pressure_variants closes any variant row without wildcard coverage,
    // even single-tag rows.
    let rows_to_close: HashSet<usize> = labels_by_row
        .iter()
        .filter_map(|(row_key, labels)| {
            (!labels.is_empty() && !rows_with_wildcards.contains(row_key))
                .then_some(*row_key)
        })
        .collect();
    if debug_pressure_rows {
        for (row_key, labels) in &labels_by_row {
            if labels.iter().any(|l| {
                l == "TopLeft"
                    || l == "BottomLeft"
                    || l == "S"
                    || l == "M"
                    || l == "L"
            }) {
                eprintln!(
                    "[pressure-rows] row_key={} labels=[{}] wildcard={} close={}",
                    row_key,
                    labels.join(","),
                    rows_with_wildcards.contains(row_key),
                    rows_to_close.contains(row_key)
                );
            }
        }
    }

    // Step 3: Close those rows in the original types
    if !rows_to_close.is_empty() {
        for case in cases.iter_mut() {
            close_multi_label_variant_rows_in_pattern(tctx, env, &mut case.c_lhs, &rows_to_close);
        }
    }

    // Step 4: Convert Reither→Rpresent in still-open rows (cases 1+2 only).
    // Keep case 3 handling in the later finalize pass after per-case closing.
    for case in cases.iter_mut() {
        finalize_variant_rpresent_only(tctx, env, &mut case.c_lhs);
    }
}

fn close_multi_label_variant_rows_in_cases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &mut [crate::types::typedtree::Case],
) {
    let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
    let mut row_has_non_variant_case: HashSet<usize> = HashSet::new();
    let mut rows_with_wildcards: HashSet<usize> = HashSet::new();
    for case in cases.iter() {
        if let Some(row_key) = variant_row_key_for_pat_type(tctx, env, case.c_lhs.pat_type) {
            let mut tags = HashSet::new();
            let mut all_variant = true;
            collect_variant_tags(&case.c_lhs, &mut tags, &mut all_variant);
            if !all_variant {
                row_has_non_variant_case.insert(row_key);
            }
        }
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut labels_by_row);
        // Also detect nested wildcard patterns at variant-typed positions
        collect_rows_with_wildcard_coverage(tctx, env, &case.c_lhs, &mut rows_with_wildcards);
    }

    // Normalize wildcard coverage across per-case instances
    normalize_wildcard_coverage_by_labels(tctx, &labels_by_row, &mut rows_with_wildcards);

    let row_label_orders: HashMap<usize, Vec<String>> = labels_by_row
        .into_iter()
        .filter_map(|(row_key, labels)| {
            (!labels.is_empty()
                && !row_has_non_variant_case.contains(&row_key)
                && !rows_with_wildcards.contains(&row_key))
                .then_some((row_key, labels))
        })
        .collect();
    if row_label_orders.is_empty() {
        return;
    }

    // Match OCaml: close variant rows in-place on the ORIGINAL types (no copy).
    // OCaml's pressure_variants and finalize_variant modify shared mutable refs,
    // so closing affects both pattern and expression types. Copying pattern types
    // here would create extra type nodes that break sexp parity.
    let rows_to_close: HashSet<usize> = row_label_orders.keys().copied().collect();

    for case in cases.iter_mut() {
        close_multi_label_variant_rows_in_pattern(tctx, env, &mut case.c_lhs, &rows_to_close);
    }
}

fn pattern_contains_generalized_constructor(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
) -> bool {
    match &*pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_construct(lid, arg) => {
            let lid_txt = tctx.resolve_lid(lid.txt).clone();
            let lid_name = tctx.longident_last_name(&lid_txt);
            let is_qualified = matches!(lid_txt, Longident::Ldot(..));
            let is_generalized = if is_qualified {
                lookup_predef_option_constructor(&lid_txt, tctx.arena, env, tctx.type_ctx)
                    .map(|(_, desc)| desc.cstr_generalized)
                    .or_else(|| {
                        let module_candidates = lookup_constructors_in_module(
                            &lid_txt,
                            tctx.arena,
                            env,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        );
                        (!module_candidates.is_empty()).then_some(
                            module_candidates
                                .iter()
                                .any(|(_, desc)| desc.cstr_generalized),
                        )
                    })
                    .unwrap_or(false)
            } else {
                // Match OCaml contains_gadt: lookup_all_constructors and
                // treat the pattern as generalized if ANY candidate is generalized.
                env.find_all_constructors(&lid_name)
                    .iter()
                    .any(|desc| desc.cstr_generalized)
            };
            is_generalized
                || arg
                    .as_ref()
                    .is_some_and(|inner| {
                        pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*inner))
                    })
        }
        crate::parser::ast::PatternDesc::Ppat_alias(inner, _) => {
            pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*inner))
        }
        crate::parser::ast::PatternDesc::Ppat_tuple(items)
        | crate::parser::ast::PatternDesc::Ppat_array(items) => items
            .iter()
            .any(|item| {
                pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*item))
            }),
        crate::parser::ast::PatternDesc::Ppat_record(inner) => inner
            .0
            .iter()
            .any(|field| {
                pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(field.pat))
            }),
        crate::parser::ast::PatternDesc::Ppat_or(left, right) => {
            pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*left))
                || pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*right))
        }
        crate::parser::ast::PatternDesc::Ppat_constraint(inner) => {
            pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(inner.0))
        }
        crate::parser::ast::PatternDesc::Ppat_exception(inner)
        | crate::parser::ast::PatternDesc::Ppat_open(_, inner) => {
            pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(*inner))
        }
        _ => false,
    }
}

fn collect_lident_idents_in_module_expr(
    arena: &ParseArena,
    mod_expr: &crate::parser::ast::ModuleExpr,
    out: &mut Vec<String>,
) {
    use crate::parser::ast::ModuleExprDesc as MED;
    use crate::parser::ast::StructureItemDesc as SID;

    match &*mod_expr.pmod_desc {
        MED::Pmod_ident(_) | MED::Pmod_extension(_) => {}
        MED::Pmod_structure(items) => {
            for item in items.iter() {
                match &*item.pstr_desc {
                    SID::Pstr_eval(inner) => {
                        collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
                    }
                    SID::Pstr_value(inner) => {
                        for binding in inner.1.iter() {
                            collect_lident_idents_in_expression(
                                arena,
                                arena.get_expr(binding.pvb_expr),
                                out,
                            );
                        }
                    }
                    SID::Pstr_module(binding) => {
                        collect_lident_idents_in_module_expr(
                            arena,
                            arena.get_mod_expr(binding.pmb_expr),
                            out,
                        );
                    }
                    SID::Pstr_recmodule(bindings) => {
                        for binding in bindings.iter() {
                            collect_lident_idents_in_module_expr(
                                arena,
                                arena.get_mod_expr(binding.pmb_expr),
                                out,
                            );
                        }
                    }
                    SID::Pstr_include(include_decl) => {
                        collect_lident_idents_in_module_expr(
                            arena,
                            arena.get_mod_expr(include_decl.pincl_mod),
                            out,
                        );
                    }
                    SID::Pstr_primitive(_)
                    | SID::Pstr_type(_)
                    | SID::Pstr_typext(_)
                    | SID::Pstr_exception(_)
                    | SID::Pstr_modtype(_)
                    | SID::Pstr_open(_)
                    | SID::Pstr_attribute(_)
                    | SID::Pstr_extension(_) => {}
                }
            }
        }
        MED::Pmod_functor(inner) => {
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(inner.2), out);
        }
        MED::Pmod_apply(lhs, rhs) => {
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(*lhs), out);
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(*rhs), out);
        }
        MED::Pmod_constraint(inner, _) => {
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(*inner), out);
        }
        MED::Pmod_unpack(expr) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(*expr), out);
        }
    }
}

fn collect_lident_idents_in_expression(
    arena: &ParseArena,
    expr: &ParsedExpression,
    out: &mut Vec<String>,
) {
    use crate::parser::ast::ExpressionDesc as ED;
    use crate::parser::ast::JsxElement;
    use crate::parser::ast::JsxProp;

    match &*expr.pexp_desc {
        ED::Pexp_ident(lid) => {
            if let Longident::Lident(id) = arena.get_longident(lid.txt) {
                out.push(arena.get_string(*id).to_string());
            }
        }
        ED::Pexp_constant(_) | ED::Pexp_construct(_, None) | ED::Pexp_extension(_) => {}
        ED::Pexp_let(inner) => {
            for binding in inner.1.iter() {
                collect_lident_idents_in_expression(arena, arena.get_expr(binding.pvb_expr), out);
            }
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.2), out);
        }
        ED::Pexp_fun(inner) => {
            if let Some(default) = inner.default {
                collect_lident_idents_in_expression(arena, arena.get_expr(default), out);
            }
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.rhs), out);
        }
        ED::Pexp_apply(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.funct), out);
            for (_label, arg) in &inner.args {
                collect_lident_idents_in_expression(arena, arena.get_expr(*arg), out);
            }
        }
        ED::Pexp_match(inner) | ED::Pexp_try(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
            for case in inner.1.iter() {
                if let Some(guard) = case.pc_guard {
                    collect_lident_idents_in_expression(arena, arena.get_expr(guard), out);
                }
                collect_lident_idents_in_expression(arena, arena.get_expr(case.pc_rhs), out);
            }
        }
        ED::Pexp_tuple(items) | ED::Pexp_array(items) => {
            for item in items.iter() {
                collect_lident_idents_in_expression(arena, arena.get_expr(*item), out);
            }
        }
        ED::Pexp_construct(_, Some(arg)) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(*arg), out);
        }
        ED::Pexp_variant(inner) => {
            if let Some(arg) = inner.1 {
                collect_lident_idents_in_expression(arena, arena.get_expr(arg), out);
            }
        }
        ED::Pexp_record(inner) => {
            for field in inner.0.iter() {
                collect_lident_idents_in_expression(arena, arena.get_expr(field.expr), out);
            }
            if let Some(base) = inner.1 {
                collect_lident_idents_in_expression(arena, arena.get_expr(base), out);
            }
        }
        ED::Pexp_field(expr, _) | ED::Pexp_assert(expr) | ED::Pexp_await(expr) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(*expr), out);
        }
        ED::Pexp_setfield(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.2), out);
        }
        ED::Pexp_ifthenelse(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.1), out);
            if let Some(else_expr) = inner.2 {
                collect_lident_idents_in_expression(arena, arena.get_expr(else_expr), out);
            }
        }
        ED::Pexp_sequence(lhs, rhs) | ED::Pexp_while(lhs, rhs) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(*lhs), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(*rhs), out);
        }
        ED::Pexp_for(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.1), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.2), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.4), out);
        }
        ED::Pexp_constraint(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
        }
        ED::Pexp_coerce(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
        }
        ED::Pexp_send(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.0), out);
        }
        ED::Pexp_letmodule(inner) => {
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(inner.1), out);
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.2), out);
        }
        ED::Pexp_letexception(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.1), out);
        }
        ED::Pexp_newtype(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.1), out);
        }
        ED::Pexp_pack(mod_expr) => {
            collect_lident_idents_in_module_expr(arena, arena.get_mod_expr(*mod_expr), out);
        }
        ED::Pexp_open(inner) => {
            collect_lident_idents_in_expression(arena, arena.get_expr(inner.2), out);
        }
        ED::Pexp_jsx_element(inner) => match &**inner {
            JsxElement::Fragment(fragment) => {
                for child in fragment.children.iter() {
                    collect_lident_idents_in_expression(arena, arena.get_expr(*child), out);
                }
            }
            JsxElement::Unary(unary) => {
                for prop in unary.props.iter() {
                    match prop {
                        JsxProp::Punning { .. } => {}
                        JsxProp::Value { value, .. } => {
                            collect_lident_idents_in_expression(arena, arena.get_expr(*value), out);
                        }
                        JsxProp::Spreading { expr, .. } => {
                            collect_lident_idents_in_expression(arena, arena.get_expr(*expr), out);
                        }
                    }
                }
            }
            JsxElement::Container(container) => {
                for prop in container.props.iter() {
                    match prop {
                        JsxProp::Punning { .. } => {}
                        JsxProp::Value { value, .. } => {
                            collect_lident_idents_in_expression(arena, arena.get_expr(*value), out);
                        }
                        JsxProp::Spreading { expr, .. } => {
                            collect_lident_idents_in_expression(arena, arena.get_expr(*expr), out);
                        }
                    }
                }
                for child in container.children.iter() {
                    collect_lident_idents_in_expression(arena, arena.get_expr(*child), out);
                }
            }
        },
    }
}

fn all_idents_cases_with_generalized_constructor_order(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[&crate::parser::ast::Case],
) -> Vec<String> {
    let mut encountered = Vec::new();
    for case in cases {
        let lhs = tctx.arena.get_pat(case.pc_lhs);
        if !pattern_contains_generalized_constructor(tctx, env, lhs) {
            continue;
        }
        if let Some(guard) = case.pc_guard {
            collect_lident_idents_in_expression(tctx.arena, tctx.arena.get_expr(guard), &mut encountered);
        }
        collect_lident_idents_in_expression(
            tctx.arena,
            tctx.arena.get_expr(case.pc_rhs),
            &mut encountered,
        );
    }
    ocaml_hashtbl_replace_fold_order(&encountered)
}

fn duplicate_ident_types_for_gadt_cases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &[&crate::parser::ast::Case],
) -> Env {
    let mut copied_env = env.clone();
    let idents = all_idents_cases_with_generalized_constructor_order(tctx, env, cases);
    if std::env::var_os("RUST_DEBUG_DUP_IDENTS").is_some() {
        eprintln!("[dup-idents] {}", idents.join(","));
    }
    for ident in idents {
        let current_ty = copied_env
            .find_value_with_id(&ident)
            .ok()
            .map(|(_, desc)| desc.val_type);
        if let Some(ty) = current_ty {
            let copied_ty = crate::types::ctype::subst_identity_copy(tctx.type_ctx, ty);
            let _ = copied_env.update_value_type_by_name(&ident, copied_ty);
        }
    }
    copied_env
}

/// Type check a single case.
fn type_case(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    case: &crate::parser::ast::Case,
    scrutinee_ty: TypeExprRef,
    generic_scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
    erase_either: bool,
) -> TypeCoreResult<crate::types::typedtree::Case> {
    match type_case_impl(
        tctx,
        env,
        case,
        scrutinee_ty,
        generic_scrutinee_ty,
        body_ty,
        erase_either,
        false,
    ) {
        Ok(case) => Ok(case),
        Err(TypeCoreError::PatternTypeClash(_)) => {
            type_case_impl(
                tctx,
                env,
                case,
                scrutinee_ty,
                generic_scrutinee_ty,
                body_ty,
                erase_either,
                true,
            )
        }
        Err(err) => Err(err),
    }
}

fn shallow_copy_pattern_binding_type(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    copy_nullary: bool,
) -> TypeExprRef {
    let repr = ctx.repr(ty);
    let desc = ctx.get_desc(repr);
    let (path, args) = match &*desc {
        TypeDesc::Tconstr { path, args, .. } if copy_nullary || !args.is_empty() => {
            (path.clone(), args.clone())
        }
        _ => return ty,
    };
    let level = ctx.get_level(repr);
    drop(desc);

    let copied = ctx.new_constr(path, args);
    ctx.set_level(copied, level);
    copied
}

fn is_simple_variable_pattern(arena: &ParseArena, pat: &ParsedPattern) -> bool {
    match &*pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_any | crate::parser::ast::PatternDesc::Ppat_var(_) => {
            true
        }
        crate::parser::ast::PatternDesc::Ppat_alias(inner, _) => {
            is_simple_variable_pattern(arena, arena.get_pat(*inner))
        }
        _ => false,
    }
}

fn parsed_pattern_contains_polymorphic_variant(arena: &ParseArena, pat: &ParsedPattern) -> bool {
    match &*pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_variant(_)
        | crate::parser::ast::PatternDesc::Ppat_type(_) => true,
        crate::parser::ast::PatternDesc::Ppat_array(pats)
        | crate::parser::ast::PatternDesc::Ppat_tuple(pats) => pats
            .iter()
            .any(|pat_idx| parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(*pat_idx))),
        crate::parser::ast::PatternDesc::Ppat_or(p1, p2) => {
            parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(*p1))
                || parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(*p2))
        }
        crate::parser::ast::PatternDesc::Ppat_construct(_, arg) => arg
            .as_ref()
            .is_some_and(|pat_idx| {
                parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(*pat_idx))
            }),
        crate::parser::ast::PatternDesc::Ppat_record(inner) => inner.0.iter().any(|field| {
            parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(field.pat))
        }),
        crate::parser::ast::PatternDesc::Ppat_exception(inner)
        | crate::parser::ast::PatternDesc::Ppat_alias(inner, _)
        | crate::parser::ast::PatternDesc::Ppat_open(_, inner) => {
            parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(*inner))
        }
        crate::parser::ast::PatternDesc::Ppat_constraint(inner) => {
            parsed_pattern_contains_polymorphic_variant(arena, arena.get_pat(inner.0))
        }
        crate::parser::ast::PatternDesc::Ppat_any
        | crate::parser::ast::PatternDesc::Ppat_var(_)
        | crate::parser::ast::PatternDesc::Ppat_constant(_)
        | crate::parser::ast::PatternDesc::Ppat_interval(_)
        | crate::parser::ast::PatternDesc::Ppat_unpack(_)
        | crate::parser::ast::PatternDesc::Ppat_extension(_) => false,
    }
}

fn type_contains_variant_either(ctx: &TypeContext<'_>, ty: TypeExprRef) -> bool {
    let mut worklist = vec![ctx.repr(ty)];
    let mut visited = HashSet::new();
    while let Some(current) = worklist.pop() {
        let current = ctx.repr(current);
        if !visited.insert(current) {
            continue;
        }
        if ctx.get_level(current) < crate::types::LOWEST_LEVEL {
            continue;
        }
        let mut children = Vec::new();
        let desc = ctx.get_desc(current);
        if let TypeDesc::Tvariant(row) = &*desc {
            let row = crate::types::btype::row_repr(ctx, row);
            if !row.row_fixed {
                for (_, field) in &row.row_fields {
                    if matches!(
                        crate::types::btype::row_field_repr(ctx, field),
                        crate::types::type_expr::RowField::Reither { .. }
                    ) {
                        return true;
                    }
                }
            }
        }
        drop(desc);
        crate::types::iter_type_expr(ctx, current, |child| {
            children.push(child);
        });
        worklist.extend(children);
    }
    false
}

/// Match OCaml `instance ~partial:false` behavior in `type_cases` for
/// polymorphic variant pattern instantiation (`erase_either`): when a copied
/// variant row is closed, non-fixed, and still has `Reither` fields, reopen
/// the row and drop those `Reither` fields.
fn instance_for_erase_either_patterns(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let inst = crate::types::instance(ctx, ty);
    let mut stack = vec![ctx.repr(inst)];
    let mut visited: HashSet<usize> = HashSet::new();

    while let Some(current) = stack.pop() {
        let current = ctx.repr(current);
        if !visited.insert(current.0) {
            continue;
        }

        let mut replacement: Option<crate::types::type_expr::RowDesc> = None;
        let desc = ctx.get_desc(current);
        if let TypeDesc::Tvariant(row) = &*desc {
            let mut row = crate::types::btype::row_repr(ctx, row);
            let has_reither = row.row_fields.iter().any(|(_, field)| {
                matches!(
                    crate::types::btype::row_field_repr(ctx, field),
                    crate::types::type_expr::RowField::Reither { .. }
                )
            });
            if row.row_closed && !row.row_fixed && has_reither {
                row.row_fields.retain(|(_, field)| {
                    !matches!(
                        crate::types::btype::row_field_repr(ctx, field),
                        crate::types::type_expr::RowField::Reither { .. }
                    )
                });
                row.row_closed = false;
                row.row_fixed = false;
                row.row_name = None;
                replacement = Some(row);
            }
        }
        drop(desc);

        if let Some(row) = replacement {
            ctx.set_desc(current, TypeDesc::Tvariant(row));
        }

        crate::types::iter_type_expr(ctx, current, |child| {
            stack.push(child);
        });
    }

    inst
}

fn type_case_impl(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    case: &crate::parser::ast::Case,
    scrutinee_ty: TypeExprRef,
    generic_scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
    erase_either: bool,
    force_case_local_constraints: bool,
) -> TypeCoreResult<crate::types::typedtree::Case> {
    let mut case_env = env.clone();
    let case_has_gadt =
        pattern_contains_generalized_constructor(tctx, env, tctx.arena.get_pat(case.pc_lhs));
    if std::env::var_os("RUST_DEBUG_CASE_GADT").is_some() {
        let lhs_pat = tctx.arena.get_pat(case.pc_lhs);
        let lhs_loc = tctx.arena.to_location(lhs_pat.ppat_loc);
        eprintln!(
            "[case-gadt-seq] line={} has_gadt={} forced={}",
            lhs_loc.loc_start.line,
            case_has_gadt,
            force_case_local_constraints
        );
    }
    let needs_case_local_constraints = force_case_local_constraints || case_has_gadt;

    let mut state = PatternState::new();

    // For GADT cases, set the unify state env to a fresh clone of case_env.
    // OCaml passes a per-case `env ref` to unify_gadt; in Rust, we must
    // reset the shared unify_state env so equations from prior cases don't leak.
    // Save old env to restore after propagation.
    let saved_unify_env = if needs_case_local_constraints {
        let saved = tctx.unify_state.env().cloned();
        tctx.unify_state.set_env(&case_env);
        saved
    } else {
        None
    };
    tctx.type_ctx.begin_def();
    // Match OCaml type_cases: instance the GENERIC scrutinee type inside begin_def.
    // This creates fresh copies at the elevated level (L+1). After end_def +
    // generalize, pattern types become GENERIC, preventing body unification
    // from contaminating pattern types (e.g., string → Js.String.t).
    let case_scrutinee_ty = if erase_either {
        instance_for_erase_either_patterns(tctx.type_ctx, scrutinee_ty)
    } else {
        crate::types::instance(tctx.type_ctx, generic_scrutinee_ty)
    };
    let typed_pat_result = type_pattern(
        tctx,
        &case_env,
        tctx.arena.get_pat(case.pc_lhs),
        case_scrutinee_ty,
        PatternMode::Normal,
        &mut state,
    );
    tctx.type_ctx.end_def();
    let typed_pat = typed_pat_result?;
    iter_typed_pattern(&typed_pat, &mut |pat| {
        crate::types::generalize(tctx.type_ctx, pat.pat_type);
    });

    // Propagate GADT equations from unify state env back to case env,
    // then restore the original unify state env.
    if needs_case_local_constraints {
        if let Some(unify_env) = tctx.unify_state.env() {
            let constraints: Vec<_> = unify_env
                .iter_local_constraints()
                .map(|(p, d)| (p.clone(), d.clone()))
                .collect();
            for (path, decl) in constraints {
                if case_env.find_local_constraint(&path).is_none() {
                    case_env.add_local_constraint(path, decl);
                }
            }
        }
        // Restore the original unify state env
        if let Some(old_env) = saved_unify_env {
            tctx.unify_state.set_env(&old_env);
        }
    }

    // Extend environment with pattern bindings
    let mut unpacks: Vec<PatternVariable> = Vec::new();
    for pv in &state.pattern_variables {
        // Match the task-9 OCaml parity fix: give case-body bindings their
        // own shallow Tconstr node so body unification can't mutate the
        // exact node shared with the typed pattern.
        let binding_ty = shallow_copy_pattern_binding_type(tctx.type_ctx, pv.ty, false);
        let desc = ValueDescription {
            val_type: binding_ty,
            val_kind: crate::types::ValueKind::ValReg,
            val_loc: pv.loc.clone(),
            val_attributes: vec![],
            val_path: None,
        };
        case_env.add_value(pv.id.clone(), desc);
        if pv.is_module {
            let module_type = module_type_from_package_binding(tctx, &case_env, binding_ty);
            case_env.add_module(
                pv.id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: module_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
            // OCaml records unpack vars in reverse insertion order
            // (`module_variables := x :: module_variables`).
            unpacks.insert(0, pv.clone());
        }
    }

    // Type check the guard if present
    let typed_guard = if let Some(guard) = &case.pc_guard {
        let bool_ty = env.type_bool(tctx.type_ctx);
        let guard_expr = tctx.arena.get_expr(*guard);
        let typed_guard = type_expect(tctx, &case_env, guard_expr, bool_ty, None)?;
        Some(wrap_module_unpacks_in_expression(
            tctx,
            &case_env,
            typed_guard,
            &unpacks,
            guard_expr.pexp_loc,
        ))
    } else {
        None
    };

    // Type check the body
    let case_body_ty = if case_has_gadt {
        crate::types::ctype::subst_identity_copy(tctx.type_ctx, body_ty)
    } else {
        body_ty
    };
    if std::env::var_os("RUST_DEBUG_CASE_GADT").is_some() {
        let ctx = tctx.type_ctx;
        eprintln!(
            "[case-gadt-seq-ty] body_ty={} case_body_ty={} body_level={} case_level={}",
            ctx.repr(body_ty).0,
            ctx.repr(case_body_ty).0,
            ctx.get_level(ctx.repr(body_ty)),
            ctx.get_level(ctx.repr(case_body_ty))
        );
    }
    let body_expr = tctx.arena.get_expr(case.pc_rhs);
    let typed_body = type_expect(tctx, &case_env, body_expr, case_body_ty, None)?;
    let typed_body = wrap_module_unpacks_in_expression(
        tctx,
        &case_env,
        typed_body,
        &unpacks,
        body_expr.pexp_loc,
    );
    let case_exp_ty = crate::types::instance(tctx.type_ctx, case_body_ty);
    let typed_body = Expression {
        exp_type: case_exp_ty,
        ..typed_body
    };

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

    // Type check each handler against exn type.
    // OCaml routes try-catch handlers through type_cases with Predef.type_exn,
    // which includes the propagation cycle (begin_def/end_def/generalize on
    // all pattern types). This ensures as-bound variables (e.g. `| exn as e`)
    // get generalized types so instance() creates fresh copies at use sites.
    let exn_ty = crate::types::ctype::instance(ctx, ctx.predef_exn());
    let generic_exn_ty = ctx.predef_exn();
    let handler_refs: Vec<&crate::parser::ast::Case> = handlers.iter().collect();
    let typed_handlers = type_match_cases_batch_non_gadt(
        tctx, env, &handler_refs, exn_ty, generic_exn_ty, expected_ty, false,
    )?;

    // Keep sharing: use typed_body.exp_type instead of expected_ty
    // (matches OCaml: exp_type = body.exp_type)
    let result_ty = typed_body.exp_type;
    Ok(Expression::new(
        ExpressionDesc::Texp_try(Box::new(typed_body), typed_handlers),
        loc.clone(),
        result_ty,
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
    is_async: bool,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::{Case, FunctionParam, FunctionParamPattern, Partial};

    let ctx = tctx.type_ctx;

    // Clone (not take) type_variables so inner functions can SEE outer scope
    // variables (enabling cross-scope sharing like 'self in @this callbacks)
    // but additions inside the function don't leak back to the outer scope.
    let saved_type_variables = tctx.type_variables.clone();
    let result = (|| -> TypeCoreResult<Expression> {

    // Convert arity to Option<i32> for the arrow type
    // Arity is now ArityIdx, look up from arena
    let arity_opt = tctx.arena.get_arity(arity);

    let ctx_label = convert_arg_label_for_ctx(arg_label, tctx.arena);

    // Match OCaml's type_function arity handling (typecore.ml:3270-3288).
    // When arity is Some, OCaml creates a MINIMAL fresh arrow with Tvars
    // and unifies with ty_expected_, consuming the generic type through
    // unification (linking Tvars to components without copying). This avoids
    // creating a full instance of the generic type, matching OCaml's node
    // allocation pattern. When arity is None, OCaml instances ty_expected.
    let expected_ty = match arity_opt {
        Some(_) => {
            // OCaml: let fun_t = newty (Tarrow({lbl=l; typ=newvar()}, newvar(), Cok, Some arity))
            //        unify_exp_types loc env fun_t ty_expected_
            //        fun_t
            let fun_t = ctx.new_arrow(
                ctx_label.clone(),
                ctx.new_var(None),
                ctx.new_var(None),
                arity_opt,
            );
            unify_expression_types(tctx, loc, fun_t, expected_ty, None)?;
            fun_t
        }
        None => {
            // OCaml keeps ty_expected_ unchanged and instances where needed.
            expected_ty
        }
    };

    // Match OCaml's filter_arrow path: if expected type already expands to an
    // arrow with matching label, reuse its argument/result types directly.
    // Otherwise introduce a fresh arrow and unify against expected type.
    let expected_inst = crate::types::instance(ctx, expected_ty);
    let expanded_expected = crate::types::ctype::expand_head(ctx, env, expected_inst);
    let expanded_desc = ctx.get_desc(expanded_expected);
    let mut expected_arrow = match &*expanded_desc {
        TypeDesc::Tarrow { arg, ret, .. } if arg.lbl == ctx_label => Some((arg.typ, *ret)),
        _ => None,
    };
    drop(expanded_desc);
    let (mut param_ty, return_ty) = match expected_arrow {
        Some((param_ty, return_ty)) => (param_ty, return_ty),
        _ => {
            let param_ty = ctx.new_var(None);
            let return_ty = ctx.new_var(None);
            let func_ty = ctx.new_arrow(ctx_label.clone(), param_ty, return_ty, arity_opt);
            unify_expression_types(tctx, loc, func_ty, expected_ty, None)?;
            (param_ty, return_ty)
        }
    };
    if std::env::var_os("RUST_DEBUG_TYPE_FUNCTION").is_some() {
        let full_loc = tctx.arena.to_location(loc);
        if full_loc.loc_start.line <= 220
            || full_loc.loc_start.line == 254
            || full_loc.loc_start.line == 255
            || (full_loc.loc_start.line >= 260 && full_loc.loc_start.line <= 280)
        {
            eprintln!(
                "[rust-type-function] loc={}:{} rec_depth={} label={:?} ty_expected={} ty_arg={} ty_res={}",
                full_loc.loc_start.line,
                full_loc.loc_start.column(),
                tctx.recursive_let_depth,
                ctx_label,
                ctx.repr(expected_ty).0,
                ctx.repr(param_ty).0,
                ctx.repr(return_ty).0
            );
        }
    }

    // OCaml typecore.ml:3297-3302: ALWAYS wrap optional params in option.
    // For optional params with defaults, the pattern and default are typed
    // against the INNER type (before option wrapping), while the Tarrow arg
    // gets the option-wrapped type.
    // NOTE: OCaml calls type_option(tv) TWICE — once for unification (linked
    // to the existing ty_arg Tvar) and once for the returned ty_arg. This
    // creates two physically distinct option nodes: the first gets generalized
    // through the pattern type chain, the second stays non-generic for the
    // function body. Matching this behavior avoids over-sharing in sexp output.
    let inner_ty = if arg_label.is_optional() {
        let tv = ctx.new_var(None);
        let option_ty_for_unify = env.type_option(ctx, tv);
        unify_expression_types(tctx, loc, param_ty, option_ty_for_unify, None)?;
        // Create a SECOND option node (matching OCaml's second type_option call)
        let option_ty = env.type_option(ctx, tv);
        param_ty = option_ty;
        tv
    } else {
        param_ty
    };

    // Type check default expression if present (against inner type, before option)
    let typed_default = if let Some(default_expr) = default {
        Some(Box::new(type_expect(
            tctx,
            env,
            default_expr,
            inner_ty,
            None,
        )?))
    } else {
        None
    };

    // Match OCaml type_cases propagation logic (typecore.ml:3947-3999):
    // propagate = has_gadts || ty_arg at GENERIC_LEVEL || !is_var
    // For type_function (single case), propagate only if pattern is complex
    // or ty_arg is generic. Simple variable patterns skip begin_def/generalize,
    // preserving non-generic identity for body lookups via Pexp_ident.
    let is_simple_param = is_simple_variable_pattern(tctx.arena, param);
    // For optional params with defaults, the pattern sees the inner type
    let pattern_ty = if default.is_some() && arg_label.is_optional() {
        inner_ty
    } else {
        param_ty
    };
    let param_ty_repr = ctx.repr(pattern_ty);
    let param_ty_is_generic = ctx.get_level(param_ty_repr) == crate::types::GENERIC_LEVEL;
    let propagate = param_ty_is_generic || !is_simple_param;

    let mut state = PatternState::new();
    state.reset(true);
    let param_pat_ty = crate::types::instance(ctx, pattern_ty);
    if propagate {
        ctx.begin_def();
    }
    let typed_param_result =
        type_pattern(tctx, env, param, param_pat_ty, PatternMode::Normal, &mut state);
    if propagate {
        ctx.end_def();
    }
    let typed_param = typed_param_result?;
    if propagate {
        iter_typed_pattern(&typed_param, &mut |pat| {
            crate::types::generalize(ctx, pat.pat_type);
        });
    }

    // Match OCaml add_pattern_variables/type_cases: extend with pattern-bound
    // values using the types from type_pattern directly.
    let mut body_env = env.clone();
    let mut unpacks: Vec<PatternVariable> = Vec::new();
    let should_copy_pattern_bindings = !is_simple_variable_pattern(tctx.arena, param);
    for pv in &state.pattern_variables {
        let binding_ty = if should_copy_pattern_bindings {
            shallow_copy_pattern_binding_type(ctx, pv.ty, false)
        } else {
            pv.ty
        };
        let desc = ValueDescription {
            val_type: binding_ty,
            val_kind: crate::types::ValueKind::ValReg,
            val_loc: pv.loc.clone(),
            val_attributes: vec![],
            val_path: None,
        };
        body_env.add_value(pv.id.clone(), desc);

        if pv.is_module {
            let module_type = module_type_from_package_binding(tctx, &body_env, binding_ty);
            body_env.add_module(
                pv.id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: module_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
            // OCaml records unpack vars in reverse insertion order
            // (`module_variables := x :: module_variables`).
            unpacks.insert(0, pv.clone());
        }
    }

    // Type check body.
    // Clear generic_constraint_body_ty: when the outer constraint was an arrow
    // type, type_function has decomposed it into param_ty and return_ty.
    // Match case bodies inside this function should use return_ty (passed as
    // body_ty), not the full arrow. Leaving the arrow as generic_constraint
    // causes case bodies to get instance(arrow_type) instead of instance(return_ty).
    let saved_generic_constraint = tctx.generic_constraint_body_ty;
    tctx.generic_constraint_body_ty = None;
    if std::env::var_os("RUST_DEBUG_TYPE_FUNCTION").is_some() {
        let full_loc = tctx.arena.to_location(loc);
        if full_loc.loc_start.line <= 220
            || full_loc.loc_start.line == 254
            || full_loc.loc_start.line == 255
            || full_loc.loc_start.line == 269
        {
            let return_repr = ctx.repr(return_ty);
            let return_kind = {
                let desc = ctx.get_desc(return_repr);
                match &*desc {
                    TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
                    TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                    TypeDesc::Tvar(_) => "Tvar".to_string(),
                    TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                    _ => "other".to_string(),
                }
            };
            eprintln!(
                "[rust-type-function-body] loc={}:{} rec_depth={} body_env_id={} return_ty={} kind={}",
                full_loc.loc_start.line,
                full_loc.loc_start.column(),
                tctx.recursive_let_depth,
                body_env.id(),
                return_repr.0,
                return_kind
            );
        }
    }
    let typed_body = type_expect(tctx, &body_env, body, return_ty, None)?;
    tctx.generic_constraint_body_ty = saved_generic_constraint;
    let typed_body = wrap_module_unpacks_in_expression(
        tctx,
        &body_env,
        typed_body,
        &unpacks,
        body.pexp_loc,
    );
    let typed_body = Expression {
        exp_type: crate::types::instance(ctx, return_ty),
        ..typed_body
    };

    // Build function parameter
    let fp = FunctionParam {
        label: arg_label.clone(),
        default: typed_default,
        pat: FunctionParamPattern::Simple(typed_param.clone()),
    };
    let exp_param_ty = typed_param.pat_type;

    // Build single case for the body
    let cases = vec![Case {
        c_lhs: typed_param,
        c_guard: None,
        c_rhs: typed_body,
    }];

    // Match OCaml typecore.ml:
    //   exp_type = instance env (newgenty (Tarrow (...)))
    // Instantiating the freshly built generic arrow preserves OCaml's
    // node-sharing behavior in typedtree output.
    let debug_type_function = std::env::var_os("RUST_DEBUG_TYPE_FUNCTION").is_some();
    let debug_loc = tctx.arena.to_location(loc);
    if debug_type_function
        && (debug_loc.loc_start.line <= 220
            || debug_loc.loc_start.line == 254
            || debug_loc.loc_start.line == 255
            || (debug_loc.loc_start.line >= 260 && debug_loc.loc_start.line <= 280))
    {
        eprintln!(
            "[rust-type-function-exp-pre] loc={}:{} exp_param_ty={} exp_param_level={} return_ty={} return_level={}",
            debug_loc.loc_start.line,
            debug_loc.loc_start.column(),
            ctx.repr(exp_param_ty).0,
            ctx.get_level(ctx.repr(exp_param_ty)),
            ctx.repr(return_ty).0,
            ctx.get_level(ctx.repr(return_ty)),
        );
    }
    let exp_type = crate::types::instance(
        ctx,
        ctx.new_generic_arrow(ctx_label, exp_param_ty, return_ty, arity_opt),
    );
    if debug_type_function
        && (debug_loc.loc_start.line <= 220
            || debug_loc.loc_start.line == 254
            || debug_loc.loc_start.line == 255
            || (debug_loc.loc_start.line >= 260 && debug_loc.loc_start.line <= 280))
    {
        let exp_type_repr = ctx.repr(exp_type);
        let exp_desc = ctx.get_desc(exp_type_repr);
        if let TypeDesc::Tarrow { arg, ret, .. } = &*exp_desc {
            let arg_repr = ctx.repr(arg.typ);
            let ret_repr = ctx.repr(*ret);
            eprintln!(
                "[rust-type-function-exp-post] loc={}:{} exp_type={} arg={} arg_level={} ret={} ret_level={}",
                debug_loc.loc_start.line,
                debug_loc.loc_start.column(),
                exp_type_repr.0,
                arg_repr.0,
                ctx.get_level(arg_repr),
                ret_repr.0,
                ctx.get_level(ret_repr),
            );
            let ret_desc = ctx.get_desc(ret_repr);
            if let TypeDesc::Tconstr { path, args, .. } = &*ret_desc {
                let args_summary = args
                    .iter()
                    .map(|arg| {
                        let arg = ctx.repr(*arg);
                        format!("{}@{}", arg.0, ctx.get_level(arg))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!(
                    "[rust-type-function-exp-post-ret-constr] loc={}:{} path={} args={}",
                    debug_loc.loc_start.line,
                    debug_loc.loc_start.column(),
                    path.name(),
                    args_summary
                );
            }
        }
    }

    let partial = check_partial_simple(ctx, env, &cases);

    Ok(Expression::new(
        ExpressionDesc::Texp_function {
            params: vec![fp],
            body: cases,
            partial,
            arity,
            async_: is_async,
        },
        loc.clone(),
        exp_type,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
    })();
    tctx.type_variables = saved_type_variables;
    result
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
    // OCaml passes Predef.type_int (generic singleton) to type_expect for each bound.
    // Inside type_expect, `rue` calls instance(ty_expected) — creating a FRESH copy
    // for each expression. Match this by creating separate int types per bound.
    let start_int_ty = env.type_int(ctx);
    let end_int_ty = env.type_int(ctx);

    // Type check bounds with separate expected types
    let typed_start = type_expect(tctx, env, start_expr, start_int_ty, None)?;
    let typed_end = type_expect(tctx, env, end_expr, end_int_ty, None)?;

    // OCaml only accepts `_` or a variable for `for` loop indices.
    if !matches!(&*pat.ppat_desc, crate::parser::ast::PatternDesc::Ppat_any
        | crate::parser::ast::PatternDesc::Ppat_var(_))
    {
        return Err(TypeCoreError::InvalidForLoopIndex);
    }

    // Type check pattern with a fresh int type (separate from loop bounds),
    // matching OCaml where loop bounds and loop variable don't share the same node.
    let loop_index_ty = env.type_int(ctx);
    let mut state = PatternState::new();
    let typed_pat = type_pattern(
        tctx,
        env,
        pat,
        loop_index_ty,
        PatternMode::Normal,
        &mut state,
    )?;

    // The loop variable
    let loop_var_id = match &*pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_any => {
            if !state.pattern_variables.is_empty() {
                return Err(TypeCoreError::InvalidForLoopIndex);
            }
            Ident::create_local("_for")
        }
        crate::parser::ast::PatternDesc::Ppat_var(_) => {
            if state.pattern_variables.len() == 1 {
                state.pattern_variables[0].id.clone()
            } else {
                return Err(TypeCoreError::InvalidForLoopIndex);
            }
        }
        _ => return Err(TypeCoreError::InvalidForLoopIndex),
    };

    // Extend environment with loop variable
    let mut body_env = env.clone();
    for pv in &state.pattern_variables {
        let desc = ValueDescription {
            val_type: pv.ty,
            val_kind: crate::types::ValueKind::ValReg,
            // Match OCaml `type_for`: for-index value descriptions use the
            // enclosing `for` expression location.
            val_loc: tctx.arena.to_location(loc),
            val_attributes: vec![],
            val_path: None,
        };
        body_env.add_value(pv.id.clone(), desc);
    }

    // OCaml uses type_statement for for-loop bodies and instance_def(type_unit)
    // for the loop expression result.
    let typed_body = type_statement(tctx, &body_env, body)?;

    // OCaml: rue { ... exp_type = instance_def Predef.type_unit; ... }
    // Keep original argument order to preserve Tlink direction.
    let result_unit_ty = env.type_unit(ctx);
    let inst_expected = instance_if_generic(ctx, expected_ty);
    unify_expression_types(tctx, loc, inst_expected, result_unit_ty, context)?;

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
        result_unit_ty,
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
    let longident = tctx.resolve_lid(lid.txt).clone();
    let debug_expected_ty = || {
        let expected_repr = ctx.repr(expected_ty);
        let expected_desc = ctx.get_desc(expected_repr);
        match &*expected_desc {
            TypeDesc::Tconstr { path, .. } => {
                format!("Tconstr({})@{}", path.name(), expected_repr.0)
            }
            TypeDesc::Tvar(name) => format!("Tvar({name:?})@{}", expected_repr.0),
            TypeDesc::Tlink(inner) => format!("Tlink({})@{}", inner.0, expected_repr.0),
            TypeDesc::Tarrow { .. } => format!("Tarrow@{}", expected_repr.0),
            TypeDesc::Ttuple(_) => format!("Ttuple@{}", expected_repr.0),
            TypeDesc::Tobject { .. } => format!("Tobject@{}", expected_repr.0),
            TypeDesc::Tfield { .. } => format!("Tfield@{}", expected_repr.0),
            TypeDesc::Tnil => format!("Tnil@{}", expected_repr.0),
            TypeDesc::Tvariant(_) => format!("Tvariant@{}", expected_repr.0),
            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})@{}", expected_repr.0),
            TypeDesc::Tpoly { .. } => format!("Tpoly@{}", expected_repr.0),
            TypeDesc::Tpackage { .. } => format!("Tpackage@{}", expected_repr.0),
            TypeDesc::Tsubst(_) => format!("Tsubst@{}", expected_repr.0),
        }
    };
    // Look up constructor with disambiguation following OCaml's approach:
    // 1. For module-qualified constructors (Ldot), use direct module lookup
    // 2. For unqualified constructors (Lident), use disambiguation considering expected type
    let lid_name = tctx.longident_last_name(&longident);
    let is_qualified = matches!(longident, Longident::Ldot(..));
    let (_cstr_path, cstr_desc) = if is_qualified {
        if let Some((path, desc)) =
            lookup_predef_option_constructor(&longident, tctx.arena, env, tctx.type_ctx)
        {
            (path, desc)
        } else {
            let module_candidates = lookup_constructors_in_module(
                &longident,
                tctx.arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            );
            if let Some((path, desc)) = disambiguate_constructor_candidates(
                &module_candidates,
                expected_ty,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                (path, desc)
            } else {
                match env.find_constructor(&lid_name) {
                    Ok(desc) => (
                        Path::pident(Ident::create_persistent(lid_name)),
                        desc.clone(),
                    ),
                    Err(_) => {
                        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
                            let full_loc = tctx.arena.to_location(loc);
                            eprintln!(
                                "[type-expr-cstr] unresolved name={} qualified=true stage=env.find_constructor loc={}:{} expected={}",
                                lid_name,
                                full_loc.loc_start.line,
                                full_loc.loc_start.column(),
                                debug_expected_ty()
                            );
                        }
                        return Err(TypeCoreError::NotAVariantType(longident));
                    }
                }
            }
        }
    } else {
        // Unqualified: use disambiguation with expected type
        match disambiguate_constructor(
            &lid_name,
            expected_ty,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        ) {
            Some((path, desc)) => (path, desc),
            None => {
                match lookup_constructor_in_module(
                    &longident,
                    tctx.arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                ) {
                    Some((path, desc)) => (path, desc),
                    None => {
                        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
                            let full_loc = tctx.arena.to_location(loc);
                            eprintln!(
                                "[type-expr-cstr] unresolved name={} qualified=false stage=module-fallback loc={}:{} expected={}",
                                lid_name,
                                full_loc.loc_start.line,
                                full_loc.loc_start.column(),
                                debug_expected_ty()
                            );
                        }
                        return Err(TypeCoreError::NotAVariantType(longident));
                    }
                }
            }
        }
    };

    // Match OCaml type_construct:
    // - optional separate begin_def/generalization around constructor instance
    // - second instance_list pass producing (ty_res, ty_args0)
    // - type arguments against ty_args, then unify against ty_args0
    let separate = env.has_local_constraints();
    if separate {
        ctx.begin_def();
        ctx.begin_def();
    }

    let (inst_arg_types, result_ty_raw) = crate::types::instance_constructor(ctx, &cstr_desc);
    let mut result_ty = result_ty_raw;
    let mut arg_types_for_expect = inst_arg_types;

    if separate {
        ctx.end_def();
        let var_level = ctx.current_level();
        crate::types::generalize_structure(ctx, var_level, result_ty);
        let result_ty_inst = crate::types::ctype::instance(ctx, result_ty);
        let expected_inst = crate::types::ctype::instance(ctx, expected_ty);
        unify_expression_types(tctx, loc, result_ty_inst, expected_inst, None)?;
        ctx.end_def();

        let var_level = ctx.current_level();
        for arg_ty in &arg_types_for_expect {
            crate::types::generalize_structure(ctx, var_level, *arg_ty);
        }
        crate::types::generalize_structure(ctx, var_level, result_ty);
    }

    let mut inst_list = Vec::with_capacity(1 + arg_types_for_expect.len());
    inst_list.push(result_ty);
    inst_list.extend(arg_types_for_expect.iter().copied());
    let mut instanced = crate::types::ctype::instance_list(ctx, &inst_list);
    result_ty = instanced.remove(0);
    let arg_types_for_unify = instanced;

    if !separate {
        let expected_inst = crate::types::ctype::instance(ctx, expected_ty);
        unify_expression_types(tctx, loc, result_ty, expected_inst, None)?;
    }

    // Type check arguments
    let typed_args = match (arg_types_for_expect.as_slice(), arg_types_for_unify.as_slice(), arg) {
        (arg_types, unify_types, Some(arg_expr)) if arg_types.len() == 1 && unify_types.len() == 1 => {
            // Single argument
            let typed_arg = type_expect(tctx, env, arg_expr, arg_types[0], None)?;
            unify_expression_types(tctx, loc, typed_arg.exp_type, unify_types[0], None)?;
            vec![typed_arg]
        }
        (arg_types, unify_types, Some(arg_expr)) if arg_types.len() > 1 && arg_types.len() == unify_types.len() => {
            // Multiple arguments - the parser wraps them in a tuple
            let tuple_ty = ctx.new_tuple(arg_types.to_vec());
            let typed_tuple = type_expect(tctx, env, arg_expr, tuple_ty, None)?;
            // Extract tuple elements
            let elements = match &typed_tuple.exp_desc {
                ExpressionDesc::Texp_tuple(elements) => elements.clone(),
                _ => vec![typed_tuple], // Fallback if not a tuple
            };
            for (elem, arg_ty) in elements.iter().zip(unify_types.iter()) {
                let _ = unify_expression_types(tctx, loc, elem.exp_type, *arg_ty, None);
            }
            elements
        }
        (arg_types, _unify_types, None) if arg_types.is_empty() => {
            // Constant constructor with no arguments
            vec![]
        }
        (arg_types, _unify_types, None) => {
            // Constructor needs arguments but none provided
            let longident = tctx.resolve_lid(lid.txt);
            return Err(TypeCoreError::ConstructorArityMismatch {
                name: longident.clone(),
                expected: arg_types.len(),
                provided: 0,
            });
        }
        (_arg_types, _unify_types, Some(arg_expr)) => {
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

fn is_active_recursive_value_ident(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    lid: &Located<LidentIdx>,
) -> bool {
    if tctx.active_recursive_value_ids.is_empty() {
        return false;
    }

    let longident = tctx.arena.get_longident(lid.txt);
    let Ok((path, _)) = env.lookup_value_by_lid(
        longident,
        tctx.arena,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    ) else {
        return false;
    };

    match path {
        Path::Pident(id) => tctx.active_recursive_value_ids.iter().any(|active| active == &id),
        _ => false,
    }
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

    if let Some(arg_expr) = arg {
        // OCaml fast path: when expected type is already a variant row with
        // this label carrying payload, type the payload against that row slot
        // and keep `exp_type = instance expected_ty`.
        let expected_inst = crate::types::ctype::instance(ctx, expected_ty);
        let expanded_expected = crate::types::ctype::expand_head(ctx, env, expected_ty);
        let expanded_expected_inst = crate::types::ctype::expand_head(ctx, env, expected_inst);

        let expected_payload = {
            let expected_desc = ctx.get_desc(ctx.repr(expanded_expected));
            let expected_inst_desc = ctx.get_desc(ctx.repr(expanded_expected_inst));
            match (&*expected_desc, &*expected_inst_desc) {
                (TypeDesc::Tvariant(row), TypeDesc::Tvariant(row0)) => {
                    let row = crate::types::btype::row_repr(ctx, row);
                    let row0 = crate::types::btype::row_repr(ctx, row0);
                    let field = row
                        .row_fields
                        .iter()
                        .find(|(l, _)| l == label)
                        .map(|(_, rf)| crate::types::btype::row_field_repr(ctx, rf));
                    let field0 = row0
                        .row_fields
                        .iter()
                        .find(|(l, _)| l == label)
                        .map(|(_, rf)| crate::types::btype::row_field_repr(ctx, rf));
                    match (field, field0) {
                        (
                            Some(crate::types::type_expr::RowField::Rpresent(Some(ty))),
                            Some(crate::types::type_expr::RowField::Rpresent(Some(ty0))),
                        ) => Some((ty, ty0)),
                        _ => None,
                    }
                }
                _ => None,
            }
        };

        if let Some((arg_ty, arg_ty0)) = expected_payload {
            let typed_arg = type_expect(tctx, env, arg_expr, arg_ty, None)?;
            unify_expression_types(tctx, loc, typed_arg.exp_type, arg_ty0, None)?;
            return Ok(Expression::new(
                ExpressionDesc::Texp_variant(label.to_string(), Some(Box::new(typed_arg))),
                loc.clone(),
                expected_inst,
                EnvRef(0),
                attributes.to_vec().into(),
            ));
        }

        let arg_ty = ctx.new_var(None);
        let typed_arg = type_expect(tctx, env, arg_expr, arg_ty, None)?;
        // OCaml (typecore.ml:2596-2605) always creates a proper Tvariant with
        // Rpresent for variant expression types, including recursive payloads.
        let variant_ty = ctx.new_variant(crate::types::type_expr::RowDesc {
            row_fields: vec![(
                label.to_string(),
                crate::types::type_expr::RowField::Rpresent(Some(typed_arg.exp_type)),
            )],
            row_more: ctx.new_var(None),
            row_closed: false,
            row_fixed: false,
            row_name: None,
        });
        // OCaml: rue { ... exp_type = variant_row; ... }
        rue_unify(tctx, loc, variant_ty, expected_ty, None)?;
        return Ok(Expression::new(
            ExpressionDesc::Texp_variant(label.to_string(), Some(Box::new(typed_arg))),
            loc.clone(),
            variant_ty,
            EnvRef(0),
            attributes.to_vec().into(),
        ));
    }

    // Constant polymorphic variants (`#Tag`) use an explicit one-field open row.
    let variant_ty = ctx.new_variant(crate::types::type_expr::RowDesc {
        row_fields: vec![(
            label.to_string(),
            crate::types::type_expr::RowField::Rpresent(None),
        )],
        row_more: ctx.new_var(None),
        row_closed: false,
        row_fixed: false,
        row_name: None,
    });
    // OCaml: rue { ... exp_type = variant_row; ... }
    rue_unify(tctx, loc, variant_ty, expected_ty, None)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_variant(label.to_string(), None),
        loc.clone(),
        variant_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

fn record_labels_match_ids(
    labels: &[crate::types::decl::LabelDeclaration],
    field_names: &[String],
    closed_record: bool,
) -> bool {
    let label_names: HashSet<String> = labels
        .iter()
        .map(|ld| ld.ld_id.name().to_string())
        .collect();
    if !field_names.iter().all(|name| label_names.contains(name)) {
        return false;
    }

    if !closed_record {
        return true;
    }

    let mandatory_count = labels.iter().filter(|ld| !ld.ld_optional).count();
    let has_optional = labels.iter().any(|ld| ld.ld_optional);
    if has_optional {
        field_names.len() >= mandatory_count
    } else {
        field_names.len() == labels.len()
    }
}

fn select_record_type_for_fields<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    field_names: &[String],
    expected_ty: TypeExprRef,
    base_ty: Option<TypeExprRef>,
    closed_record: bool,
) -> Option<TypeExprRef> {
    for candidate_ty in [Some(expected_ty), base_ty].into_iter().flatten() {
        if let Some(labels) = get_record_labels(ctx, env, pers_env, candidate_ty) {
            if record_labels_match_ids(&labels, field_names, closed_record) {
                return Some(candidate_ty);
            }
        }
    }

    let first_name = field_names.first()?;
    let candidates = env.find_all_labels(first_name);
    let mut matching: Vec<(Option<Path>, TypeExprRef)> = Vec::new();
    for label in candidates.into_iter().rev() {
        if let Some(labels) = get_record_labels(ctx, env, pers_env, label.lbl_res) {
            if record_labels_match_ids(&labels, field_names, closed_record) {
                let key = extract_type_path_from_expected(label.lbl_res, env, ctx);
                if matching.iter().any(|(existing, _)| *existing == key) {
                    continue;
                }
                matching.push((key, label.lbl_res));
            }
        }
    }

    if matching.len() == 1 {
        Some(matching[0].1)
    } else {
        None
    }
}

fn disambiguate_label_for_record_fields<'a>(
    label_name: &str,
    disambiguation_ty: TypeExprRef,
    field_names: &[String],
    closed_record: bool,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    if extract_type_path_from_expected_with_persistent_env(disambiguation_ty, env, pers_env, ctx)
        .is_some()
    {
        return disambiguate_label(label_name, disambiguation_ty, env, pers_env, ctx);
    }

    let all_labels = env.find_all_labels(label_name);
    if all_labels.is_empty() {
        return None;
    }

    let matching: Vec<crate::types::LabelDescription> = all_labels
        .iter()
        .filter_map(|label| {
            get_record_labels(ctx, env, pers_env, label.lbl_res).and_then(|labels| {
                if record_labels_match_ids(&labels, field_names, closed_record) {
                    Some((*label).clone())
                } else {
                    None
                }
            })
        })
        .collect();

    if let Some(label) = matching.last() {
        return Some(label.clone());
    }

    None
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
    let debug_record_c = std::env::var_os("RUST_DEBUG_RECORD_C").is_some();
    let summarize_ty = |ty: TypeExprRef| -> String {
        let r = ctx.repr(ty);
        let desc = ctx.get_desc(r);
        let head = match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let args = args
                    .iter()
                    .map(|a| ctx.repr(*a).0.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{}({})", path.name(), args)
            }
            TypeDesc::Tvar(_) => "Tvar".to_string(),
            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
            _ => "other".to_string(),
        };
        format!("{}@{}:{}", r.0, ctx.get_level(r), head)
    };
    // Most callers should protect generic expected types from record typing
    // side effects, but constraint bodies must type against the shared generic
    // node so unification side effects match OCaml.
    let expected_ty = if tctx
        .generic_constraint_body_ty
        .is_some_and(|constraint_ty| ctx.repr(constraint_ty) == ctx.repr(expected_ty))
    {
        expected_ty
    } else {
        instance_if_generic(ctx, expected_ty)
    };
    let placeholder_lid = tctx.arena.placeholder_located(loc);

    // Type check base expression if present.
    // Match OCaml: type the base with type_exp (no expected type constraint),
    // then defer unification with expected_ty until after label processing.
    // This preserves separate type identity between the base expression's
    // type chain and the expected type chain, matching OCaml's cycle structure.
    let typed_base = if let Some(base_expr) = base {
        let base_ty = ctx.new_var(None);
        let typed = type_expect(tctx, env, base_expr, base_ty, None)?;
        Some(typed)
    } else {
        None
    };

    let field_names: Vec<String> = fields
        .iter()
        .map(|field| tctx.longident_last_name(tctx.resolve_lid(field.lid.txt)))
        .collect();
    let closed_record = typed_base.is_none();
    let disambiguation_ty = select_record_type_for_fields(
        ctx,
        env,
        &mut tctx.persistent_env,
        &field_names,
        expected_ty,
        typed_base.as_ref().map(|expr| expr.exp_type),
        closed_record,
    )
    .unwrap_or_else(|| {
        typed_base
            .as_ref()
            .map(|expr| expr.exp_type)
            .unwrap_or(expected_ty)
    });
    if std::env::var_os("RUST_DEBUG_RECORD_PATH").is_some()
        && field_names
            .iter()
            .any(|name| matches!(name.as_str(), "currency" | "useGrouping"))
    {
        let expected_path = extract_type_path_from_expected_with_persistent_env(
            expected_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        )
        .map(|p| p.name())
        .unwrap_or_else(|| "<none>".to_string());
        let disamb_path = extract_type_path_from_expected_with_persistent_env(
            disambiguation_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        )
        .map(|p| p.name())
        .unwrap_or_else(|| "<none>".to_string());
        eprintln!(
            "[record-path] loc={}:{} fields={:?} expected={} disambiguation={}",
            tctx.arena.to_location(loc).loc_start.line,
            tctx.arena.to_location(loc).loc_start.column(),
            field_names,
            expected_path,
            disamb_path
        );
    }

    // OCaml typecore.ml find_record_qual:
    // if any field is module-qualified, bare sibling labels are emitted with
    // the same qualifier in typedtree.
    let shared_record_field_prefix: Option<Longident> = fields.iter().find_map(|field| {
        match tctx.resolve_lid(field.lid.txt) {
            Longident::Ldot(field_prefix, _) => Some((**field_prefix).clone()),
            _ => None,
        }
    });

    // OCaml builds record definitions by label position over the full label set.
    // Keep explicit overrides keyed by lbl_pos so we can reconstruct full fields.
    let mut explicit_overrides: HashMap<
        i32,
        (
            Located<LidentIdx>,
            crate::types::LabelDescription,
            RecordLabelDefinition,
            bool,
        ),
    > = HashMap::new();
    let mut explicit_overrides_by_name: HashMap<
        String,
        (
            Located<LidentIdx>,
            crate::types::LabelDescription,
            RecordLabelDefinition,
            bool,
        ),
    > = HashMap::new();
    let mut explicit_overrides_in_order = Vec::new();
    let mut first_disambiguated_label: Option<crate::types::LabelDescription> = None;
    // OCaml typecore.ml find_record_qual:
    // when one record field is module-qualified, qualify sibling bare labels
    // with the same module path for disambiguation.
    let record_field_qualifier: Option<Longident> = fields.iter().find_map(|field| {
        match tctx.resolve_lid(field.lid.txt) {
            Longident::Ldot(prefix, _) => Some((**prefix).clone()),
            _ => None,
        }
    });

    struct EndDefGuard<'a> {
        ctx: &'a TypeContext<'a>,
    }

    impl Drop for EndDefGuard<'_> {
        fn drop(&mut self) {
            self.ctx.end_def();
        }
    }

    struct ExplicitFieldPlan<'a> {
        source_idx: usize,
        field: &'a crate::parser::ast::ExpressionRecordField,
        resolved_lid: Longident,
        field_name: String,
        disambiguated: Option<crate::types::LabelDescription>,
        sort_key: i32,
    }

    // OCaml typecore.ml type_record_elem_list:
    // - disambiguate fields first
    // - then sort by lbl_pos before typing each field expression
    let mut explicit_field_plans = Vec::with_capacity(fields.len());
    for (idx, field) in fields.iter().enumerate() {
        let raw_lid = tctx.resolve_lid(field.lid.txt).clone();
        let resolved_lid = match (&record_field_qualifier, &raw_lid) {
            (Some(prefix), Longident::Lident(name_idx)) => {
                Longident::Ldot(Box::new(prefix.clone()), *name_idx)
            }
            _ => raw_lid,
        };
        let field_name = tctx.longident_last_name(&resolved_lid);
        let disambiguated = lookup_label_by_lid_matching_fields(
            &resolved_lid,
            tctx.arena,
            env,
            &mut tctx.persistent_env,
            ctx,
            &field_names,
            closed_record,
        )
        .or_else(|| {
            disambiguate_label_for_record_fields(
                &field_name,
                disambiguation_ty,
                &field_names,
                closed_record,
                env,
                &mut tctx.persistent_env,
                ctx,
            )
        })
        .or_else(|| {
            lookup_label_by_lid(
                &resolved_lid,
                tctx.arena,
                env,
                &mut tctx.persistent_env,
                ctx,
            )
        })
        .or_else(|| {
            if field_names.len() == 1 {
                disambiguate_label(
                    &field_name,
                    disambiguation_ty,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                )
            } else {
                None
            }
        });
        if first_disambiguated_label.is_none() {
            first_disambiguated_label = disambiguated.clone();
        }
        let sort_key = disambiguated
            .as_ref()
            .map(|label| label.lbl_pos)
            .unwrap_or(idx as i32);
        if std::env::var_os("RUST_DEBUG_RECORD_PLAN").is_some() {
            let resolved_name = tctx.longident_to_string(&resolved_lid);
            let picked = disambiguated
                .as_ref()
                .map(|label| {
                    let lbl_res = ctx.repr(label.lbl_res);
                    let res = match &*ctx.get_desc(lbl_res) {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        _ => format!("ty#{}", lbl_res.0),
                    };
                    format!("{}@{} res={}", label.lbl_name, label.lbl_pos, res)
                })
                .unwrap_or_else(|| "<none>".to_string());
            let field_loc = tctx.arena.to_location(field.lid.loc);
            eprintln!(
                "[record-plan] loc={}:{} source_idx={} field={} resolved={} picked={} sort_key={}",
                field_loc.loc_start.line,
                field_loc.loc_start.column(),
                idx,
                field_name,
                resolved_name,
                picked,
                sort_key
            );
        }
        if std::env::var_os("RUST_DEBUG_RECORD_PLAN_RECORDER").is_some()
            && matches!(field_name.as_str(), "camera" | "screen" | "audio")
        {
            let resolved_name = tctx.longident_to_string(&resolved_lid);
            let picked = disambiguated
                .as_ref()
                .map(|label| {
                    let lbl_res = ctx.repr(label.lbl_res);
                    let res = match &*ctx.get_desc(lbl_res) {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        _ => format!("ty#{}", lbl_res.0),
                    };
                    format!("{}@{} res={}", label.lbl_name, label.lbl_pos, res)
                })
                .unwrap_or_else(|| "<none>".to_string());
            let field_loc = tctx.arena.to_location(field.lid.loc);
            eprintln!(
                "[record-plan] loc={}:{} source_idx={} field={} resolved={} picked={} sort_key={}",
                field_loc.loc_start.line,
                field_loc.loc_start.column(),
                idx,
                field_name,
                resolved_name,
                picked,
                sort_key
            );
        }
        explicit_field_plans.push(ExplicitFieldPlan {
            source_idx: idx,
            field,
            resolved_lid,
            field_name,
            disambiguated,
            sort_key,
        });
    }
    explicit_field_plans.sort_by_key(|plan| plan.sort_key);

    // Type check explicitly written fields.
    for plan in explicit_field_plans {
        ctx.begin_def();
        let _field_def_guard = EndDefGuard { ctx };

        let idx = plan.source_idx;
        let field = plan.field;
        let resolved_lid = plan.resolved_lid;
        let field_name = plan.field_name;
        let disambiguated = plan.disambiguated;

        // Build label description (prefer env-disambiguated metadata).
        let (mut label_desc, field_input_ty, poly_vars) = if let Some(env_label) = disambiguated {
            if std::env::var_os("RUST_DEBUG_GPR_4274").is_some()
                && env_label.lbl_name == "i"
            {
                let src_arg = ctx.repr(env_label.lbl_arg);
                let src_res = ctx.repr(env_label.lbl_res);
                let src_arg_desc = ctx.get_desc(src_arg);
                let src_kind = match &*src_arg_desc {
                    TypeDesc::Tpoly { body, vars } => {
                        format!("Tpoly(body={},vars={})", ctx.repr(*body).0, vars.len())
                    }
                    TypeDesc::Tconstr { path, args, .. } => {
                        format!("Tconstr({},args={})", path.name(), args.len())
                    }
                    TypeDesc::Tvar(_) => "Tvar".to_string(),
                    _ => "other".to_string(),
                };
                drop(src_arg_desc);
                eprintln!(
                    "[gpr4274][record-field-source] src_arg={}({}) src_res={}",
                    src_arg.0,
                    src_kind,
                    src_res.0
                );
            }
            let (poly_vars, ty_arg, ty_res) =
                crate::types::ctype::instance_label(ctx, true, &env_label);
            if std::env::var_os("RUST_DEBUG_RECORD_REF").is_some() && env_label.lbl_name == "ref"
            {
                eprintln!(
                    "[record-ref] stage=after-instance ty_arg={} ty_res={} simple={:?}",
                    ctx.repr(ty_arg).0,
                    ctx.repr(ty_res).0,
                    ctx.get_abbrev_memo(ctx.simple_abbrevs_memo())
                );
            }
            if debug_record_c && env_label.lbl_name == "c" {
                let full_loc = tctx.arena.to_location(tctx.arena.get_expr(field.expr).pexp_loc);
                eprintln!(
                    "[record-c] stage=instance_label loc={}:{} expected={} src_arg={} src_res={} ty_arg={} ty_res={}",
                    full_loc.loc_start.line,
                    full_loc.loc_start.column(),
                    summarize_ty(expected_ty),
                    summarize_ty(env_label.lbl_arg),
                    summarize_ty(env_label.lbl_res),
                    summarize_ty(ty_arg),
                    summarize_ty(ty_res)
                );
            }
            if std::env::var_os("RUST_DEBUG_GPR_4274").is_some()
                && env_label.lbl_name == "i"
            {
                let full_loc = tctx.arena.to_location(tctx.arena.get_expr(field.expr).pexp_loc);
                let expected_repr = ctx.repr(expected_ty);
                let ty_arg_repr = ctx.repr(ty_arg);
                let ty_res_repr = ctx.repr(ty_res);
                eprintln!(
                    "[gpr4274][record-field-before] loc={}:{} field=i expected={}@{} ty_arg={}@{} ty_res={}@{}",
                    full_loc.loc_start.line,
                    full_loc.loc_start.column(),
                    expected_repr.0,
                    ctx.get_level(expected_repr),
                    ty_arg_repr.0,
                    ctx.get_level(ty_arg_repr),
                    ty_res_repr.0,
                    ctx.get_level(ty_res_repr),
                );
            }
            if std::env::var_os("RUST_DEBUG_LABEL_INST").is_some() {
                let name = env_label.lbl_name.as_str();
                if name == "frame_size"
                    || name == "src_offset"
                    || name == "bbox_offset"
                    || name == "bbox_size"
                {
                    let full_loc = tctx.arena.to_location(tctx.arena.get_expr(field.expr).pexp_loc);
                    let src_arg_repr = ctx.repr(env_label.lbl_arg);
                    let ty_arg_repr = ctx.repr(ty_arg);
                    let ty_res_repr = ctx.repr(ty_res);
                    eprintln!(
                        "[rust-label-inst] loc={}:{} field={} src_arg={}@{} ty_arg={}@{} ty_res={}@{}",
                        full_loc.loc_start.line,
                        full_loc.loc_start.column(),
                        name,
                        src_arg_repr.0,
                        ctx.get_level(src_arg_repr),
                        ty_arg_repr.0,
                        ctx.get_level(ty_arg_repr),
                        ty_res_repr.0,
                        ctx.get_level(ty_res_repr),
                    );
                }
            }
            let unify_res = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, expected_ty);
            if std::env::var_os("RUST_DEBUG_RECORD_REF").is_some() && env_label.lbl_name == "ref"
            {
                eprintln!(
                    "[record-ref] stage=after-unify ok={} ty_arg={} ty_res={} expected={} simple={:?}",
                    unify_res.is_ok(),
                    ctx.repr(ty_arg).0,
                    ctx.repr(ty_res).0,
                    ctx.repr(expected_ty).0,
                    ctx.get_abbrev_memo(ctx.simple_abbrevs_memo())
                );
            }
            if debug_record_c && env_label.lbl_name == "c" {
                eprintln!(
                    "[record-c] stage=after-label-unify ok={} expected={} ty_arg={} ty_res={}",
                    unify_res.is_ok(),
                    summarize_ty(expected_ty),
                    summarize_ty(ty_arg),
                    summarize_ty(ty_res)
                );
            }
            if std::env::var_os("RUST_DEBUG_GPR_4274").is_some()
                && env_label.lbl_name == "i"
            {
                let expected_repr = ctx.repr(expected_ty);
                let ty_arg_repr = ctx.repr(ty_arg);
                let ty_res_repr = ctx.repr(ty_res);
                eprintln!(
                    "[gpr4274][record-field-after] field=i ok={} expected={}@{} ty_arg={}@{} ty_res={}@{}",
                    unify_res.is_ok(),
                    expected_repr.0,
                    ctx.get_level(expected_repr),
                    ty_arg_repr.0,
                    ctx.get_level(ty_arg_repr),
                    ty_res_repr.0,
                    ctx.get_level(ty_res_repr),
                );
            }

            let input_ty = if env_label.lbl_optional && !field.opt {
                crate::types::ctype::extract_option_type(ctx, ty_arg).unwrap_or(ty_arg)
            } else {
                ty_arg
            };
            if debug_record_c && env_label.lbl_name == "c" {
                eprintln!(
                    "[record-c] stage=field-input expected={} input_ty={} lbl_arg={}",
                    summarize_ty(expected_ty),
                    summarize_ty(input_ty),
                    summarize_ty(ty_arg)
                );
            }

            (
                crate::types::LabelDescription {
                    lbl_name: env_label.lbl_name.clone(),
                    lbl_res: expected_ty,
                    lbl_arg: ty_arg,
                    lbl_mut: env_label.lbl_mut.clone(),
                    lbl_optional: env_label.lbl_optional,
                    lbl_pos: env_label.lbl_pos,
                    lbl_all: env_label.lbl_all,
                    lbl_repres: env_label.lbl_repres.clone(),
                    lbl_private: env_label.lbl_private.clone(),
                    lbl_loc: env_label.lbl_loc.clone(),
                    lbl_attributes: env_label.lbl_attributes.clone(),
                },
                input_ty,
                poly_vars,
            )
        } else {
            let inner_ty = ctx.new_var(None);
            let lbl_arg = if field.opt {
                env.type_option(ctx, inner_ty)
            } else {
                inner_ty
            };

            (
                crate::types::LabelDescription {
                    lbl_name: field_name,
                    lbl_res: expected_ty,
                    lbl_arg,
                    lbl_mut: crate::types::MutableFlag::Immutable,
                    lbl_optional: field.opt,
                    lbl_pos: idx as i32,
                    lbl_all: crate::types::LabelArrayRef(0),
                    lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                    lbl_private: crate::types::PrivateFlag::Public,
                    lbl_loc: tctx.arena.to_location(field.lid.loc),
                    lbl_attributes: vec![],
                },
                lbl_arg,
                vec![],
            )
        };

        let typed_expr = type_expect(
            tctx,
            env,
            tctx.arena.get_expr(field.expr),
            field_input_ty,
            None,
        )?;
        if debug_record_c && label_desc.lbl_name == "c" {
            eprintln!(
                "[record-c] stage=after-type-expect field_input={} typed_expr={}",
                summarize_ty(field_input_ty),
                summarize_ty(typed_expr.exp_type)
            );
        }
        if std::env::var_os("RUST_DEBUG_GPR_4274").is_some()
            && label_desc.lbl_name == "i"
        {
            let typed_repr = ctx.repr(typed_expr.exp_type);
            let input_repr = ctx.repr(field_input_ty);
            eprintln!(
                "[gpr4274][record-field-typed] field=i typed={}@{} input={}@{}",
                typed_repr.0,
                ctx.get_level(typed_repr),
                input_repr.0,
                ctx.get_level(input_repr),
            );
        }
        // OCaml `type_argument`: after typing against `ty_expected'`, unify with
        // a fresh `instance` of that type to preserve sharing behavior.
        let field_input_ty_inst = crate::types::ctype::instance(ctx, field_input_ty);
        if debug_record_c && label_desc.lbl_name == "c" {
            eprintln!(
                "[record-c] stage=before-post-unify field_input={} field_input_inst={} typed_expr={}",
                summarize_ty(field_input_ty),
                summarize_ty(field_input_ty_inst),
                summarize_ty(typed_expr.exp_type)
            );
        }
        unify_expression_types(tctx, loc, typed_expr.exp_type, field_input_ty_inst, None)?;
        if debug_record_c && label_desc.lbl_name == "c" {
            eprintln!(
                "[record-c] stage=after-post-unify field_input={} field_input_inst={} typed_expr={}",
                summarize_ty(field_input_ty),
                summarize_ty(field_input_ty_inst),
                summarize_ty(typed_expr.exp_type)
            );
        }
        if std::env::var_os("RUST_DEBUG_GPR_4274").is_some()
            && label_desc.lbl_name == "i"
        {
            let typed_repr = ctx.repr(typed_expr.exp_type);
            let input_inst_repr = ctx.repr(field_input_ty_inst);
            eprintln!(
                "[gpr4274][record-field-post-unify] field=i typed={}@{} input_inst={}@{}",
                typed_repr.0,
                ctx.get_level(typed_repr),
                input_inst_repr.0,
                ctx.get_level(input_inst_repr),
            );
        }

        // OCaml check_univars: convert fresh Tvars back to Tunivar for poly fields
        if !poly_vars.is_empty() {
            crate::types::ctype::check_univars(ctx, &poly_vars);
        }

        // process_optional_label: wrap optional fields in Some(...) only when the
        // user did not write the `?` form.
        let final_expr = if label_desc.lbl_optional && !field.opt {
            let some_cstr = make_some_constructor(ctx, label_desc.lbl_arg);
            let some_lid = Located::mknoloc(tctx.arena.some_lid());
            let wrapped_loc = typed_expr.exp_loc;
            let wrapped_env = typed_expr.exp_env;
            label_desc.lbl_optional = false;
            Expression::new(
                ExpressionDesc::Texp_construct(some_lid.clone(), some_cstr, vec![typed_expr]),
                wrapped_loc,
                label_desc.lbl_arg,
                wrapped_env,
                Attributes::new(),
            )
        } else {
            typed_expr
        };
        // OCaml `type_label_exp` returns `{arg with exp_type = instance env arg.exp_type}`.
        let final_expr = Expression::new(
            final_expr.exp_desc.clone(),
            final_expr.exp_loc,
            crate::types::ctype::instance(ctx, final_expr.exp_type),
            final_expr.exp_env,
            final_expr.exp_attributes.clone(),
        );

        let output_longident = match (&shared_record_field_prefix, &resolved_lid) {
            (Some(prefix), Longident::Lident(name_idx)) => {
                Longident::Ldot(Box::new(prefix.clone()), *name_idx)
            }
            _ => resolved_lid.clone(),
        };
        let output_idx = find_existing_longident_idx(tctx.arena, &output_longident)
            .unwrap_or_else(|| {
                // Type checking mostly reads from ParseArena, but typedtree
                // longident normalization occasionally needs a synthetic longident.
                let arena_ptr = tctx.arena as *const ParseArena as *mut ParseArena;
                unsafe { (*arena_ptr).push_longident(output_longident) }
            });
        let output_lid = Located {
            txt: output_idx,
            loc: field.lid.loc,
        };

        let entry = (
            output_lid.clone(),
            label_desc.clone(),
            RecordLabelDefinition::Overridden(output_lid, final_expr),
            false, // OCaml Texp_record always uses false for this flag
        );

        explicit_overrides.insert(label_desc.lbl_pos, entry.clone());
        explicit_overrides_by_name.insert(label_desc.lbl_name.clone(), entry.clone());
        explicit_overrides_in_order.push(entry);
    }

    let has_dotdotdot_field = fields
        .iter()
        .any(|field| tctx.longident_last_name(tctx.resolve_lid(field.lid.txt)) == "...");

    // Resolve the full label set for this record type (OCaml builds definitions over lbl_all).
    // Skip this path for object-like spread placeholders (`...`) and keep the
    // explicit field representation in that case.
    let mut all_labels = if has_dotdotdot_field {
        None
    } else {
        get_record_labels(ctx, env, &mut tctx.persistent_env, disambiguation_ty)
    };
    if all_labels.is_none() {
        if let Some(base_expr) = typed_base.as_ref() {
            all_labels = get_record_labels(ctx, env, &mut tctx.persistent_env, base_expr.exp_type);
        }
    }
    if all_labels.is_none() {
        if let Some(lbl) = first_disambiguated_label {
            all_labels = get_record_labels(ctx, env, &mut tctx.persistent_env, lbl.lbl_res);
        }
    }
    if all_labels
        .as_ref()
        .is_some_and(|labels| labels.iter().any(|ld| ld.ld_id.name() == "..."))
    {
        all_labels = None;
    }
    if std::env::var_os("RUST_DEBUG_RECORD_LOOKUP").is_some() {
        let full_loc = tctx.arena.to_location(loc);
        let expected_path = extract_type_path_from_expected_with_persistent_env(
            expected_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        )
        .map(|p| p.name())
        .unwrap_or_else(|| "<none>".to_string());
        let disamb_path = extract_type_path_from_expected_with_persistent_env(
            disambiguation_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        )
        .map(|p| p.name())
        .unwrap_or_else(|| "<none>".to_string());
        let base_path = typed_base
            .as_ref()
            .and_then(|expr| {
                extract_type_path_from_expected_with_persistent_env(
                    expr.exp_type,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                )
            })
            .map(|p| p.name())
            .unwrap_or_else(|| "<none>".to_string());
        eprintln!(
            "[record-lookup] loc={}:{} fields={:?} expected={} disamb={} base={} labels={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            field_names,
            expected_path,
            disamb_path,
            base_path,
            all_labels.as_ref().map(|v| v.len()).unwrap_or(0)
        );
    }

    let mut typed_fields = Vec::new();
    // OCaml special-case (typecore.ml, Pexp_record with no base):
    // for `{}` in a known record context, keep `Texp_record` fields empty when
    // all fields are optional; only error when required fields are missing.
    // Do not synthesize explicit `None` overrides for the all-optional case.
    if typed_base.is_none() && fields.is_empty() {
        match all_labels.as_ref() {
            Some(labels) => {
                let labels_missing: Vec<String> = labels
                    .iter()
                    .filter(|ld| !ld.ld_optional)
                    .map(|ld| ld.ld_id.name().to_string())
                    .collect();
                if !labels_missing.is_empty() {
                    return Err(TypeCoreError::LabelsMissing {
                        labels: labels_missing,
                        jsx_component_info: None,
                    });
                }
                all_labels = Some(Vec::new());
            }
            None => {
                // Keep the existing fallback for record shapes where Rust cannot
                // reconstruct `lbl_all` yet (notably some inline-record paths).
            }
        }
    }

    if let Some(all_labels) = all_labels {
        let mut labels_missing = Vec::new();

        for (lbl_idx, label_decl) in all_labels.iter().enumerate() {
            let label_name = label_decl.ld_id.name().to_string();

            // OCaml matches overrides by lbl_pos, not by declaration array index.
            let disambiguated = disambiguate_label(
                &label_name,
                disambiguation_ty,
                env,
                &mut tctx.persistent_env,
                ctx,
            );
            let key_pos = disambiguated
                .as_ref()
                .map(|label| label.lbl_pos)
                .unwrap_or(lbl_idx as i32);
            // Check if this label has an explicit override BEFORE doing instance_label.
            // OCaml only calls instance_label for explicit fields (in type_label_exp),
            // not for missing optional fields (which use lbl.lbl_arg directly).
            if let Some(explicit) = explicit_overrides.remove(&key_pos) {
                explicit_overrides_by_name.remove(&label_name);
                typed_fields.push(explicit);
                continue;
            }
            if let Some(explicit) = explicit_overrides_by_name.remove(&label_name) {
                typed_fields.push(explicit);
                continue;
            }

            // For kept fields (base expression), we still need instance_label
            // for type resolution. For optional None fields, use lbl_arg directly.
            if typed_base.is_some() {
                let label_desc = if let Some(env_label) = disambiguated {
                    let (_poly_vars, ty_arg, ty_res) =
                        crate::types::ctype::instance_label(ctx, false, &env_label);
                    let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, expected_ty);
                    crate::types::LabelDescription {
                        lbl_name: env_label.lbl_name.clone(),
                        lbl_res: expected_ty,
                        lbl_arg: ty_arg,
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
                        lbl_name: label_name.clone(),
                        lbl_res: expected_ty,
                        lbl_arg: crate::types::instance(ctx, label_decl.ld_type),
                        lbl_mut: label_decl.ld_mutable.clone(),
                        lbl_optional: label_decl.ld_optional,
                        lbl_pos: lbl_idx as i32,
                        lbl_all: crate::types::LabelArrayRef(0),
                        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                        lbl_private: crate::types::PrivateFlag::Public,
                        lbl_loc: label_decl.ld_loc.clone(),
                        lbl_attributes: label_decl.ld_attributes.clone(),
                    }
                };
                typed_fields.push((
                    placeholder_lid.clone(),
                    label_desc.clone(),
                    RecordLabelDefinition::Kept(label_desc.lbl_arg),
                    false,
                ));
                continue;
            }

            // For missing optional fields: use lbl_arg directly (no instance_label),
            // matching OCaml's option_none(lbl.lbl_arg, loc) pattern
            let is_optional = disambiguated.as_ref().map_or(label_decl.ld_optional, |l| l.lbl_optional);
            if is_optional {
                // Get the option type from the raw label, not from instance_label
                let option_ty = disambiguated.as_ref()
                    .map_or_else(|| label_decl.ld_type, |l| l.lbl_arg);
                let none_cstr = make_none_constructor(ctx, option_ty);
                let none_lid = Located {
                    txt: tctx.arena.none_lid(),
                    loc,
                };
                let none_expr = Expression::new(
                    ExpressionDesc::Texp_construct(none_lid.clone(), none_cstr, vec![]),
                    loc,
                    option_ty,
                    EnvRef(0),
                    Attributes::new(),
                );
                // Build label desc using the raw label's lbl_arg (not instanced)
                let label_desc = if let Some(env_label) = disambiguated {
                    let mut desc = env_label.clone();
                    desc.lbl_optional = false;
                    desc
                } else {
                    crate::types::LabelDescription {
                        lbl_name: label_name.clone(),
                        lbl_res: expected_ty,
                        lbl_arg: option_ty,
                        lbl_mut: label_decl.ld_mutable.clone(),
                        lbl_optional: false,
                        lbl_pos: lbl_idx as i32,
                        lbl_all: crate::types::LabelArrayRef(0),
                        lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                        lbl_private: crate::types::PrivateFlag::Public,
                        lbl_loc: label_decl.ld_loc.clone(),
                        lbl_attributes: label_decl.ld_attributes.clone(),
                    }
                };
                // OCaml uses {loc; txt = Lident lbl.lbl_name} for synthesized optional fields
                let label_lid_idx = find_existing_lident_idx(tctx.arena, &label_name)
                    .unwrap_or_else(|| {
                        let arena_ptr = tctx.arena as *const ParseArena as *mut ParseArena;
                        unsafe { (*arena_ptr).push_lident(&label_name) }
                    });
                let label_lid = Located { txt: label_lid_idx, loc };
                typed_fields.push((
                    label_lid.clone(),
                    label_desc,
                    RecordLabelDefinition::Overridden(label_lid, none_expr),
                    false,
                ));
            } else {
                labels_missing.push(label_name);
            }
        }

        if !labels_missing.is_empty() {
            return Err(TypeCoreError::LabelsMissing {
                labels: labels_missing,
                jsx_component_info: None,
            });
        }

        // Preserve explicitly-typed fields even if we couldn't align their position.
        typed_fields.extend(explicit_overrides_by_name.into_values());
    } else {
        typed_fields = explicit_overrides_in_order;
    }

    // Match OCaml's unify_kept (typecore.ml:2755-2770):
    // For each label in the record type, create two instance_label calls.
    // Instance 1 connects to the base expression type.
    // For non-overridden labels, instance 2 connects to the expected type,
    // with ty_arg1 = ty_arg2 bridging them. This propagates type constraints
    // from the expected type (e.g., component<stateless, noRetainedProps, _>)
    // through to the base expression's type params.
    if let Some(ref typed_base_expr) = typed_base {
        // OCaml: let ty_exp = instance env exp.exp_type
        let ty_exp = crate::types::instance(ctx, typed_base_expr.exp_type);
        let debug_record_unify = std::env::var_os("RUST_DEBUG_RECORD_UNIFY").is_some()
            && tctx.arena.to_location(loc).loc_start.line == 302;

        // Collect the set of overridden label positions
        let overridden_positions: std::collections::HashSet<i32> = typed_fields
            .iter()
            .filter_map(|(_, lbl, defn, _)| {
                if matches!(defn, RecordLabelDefinition::Overridden(..)) {
                    Some(lbl.lbl_pos)
                } else {
                    None
                }
            })
            .collect();

        // Get all labels for this record type to iterate over
        let all_labels_for_unify = get_record_labels(ctx, env, &mut tctx.persistent_env, expected_ty)
            .or_else(|| get_record_labels(ctx, env, &mut tctx.persistent_env, ty_exp));

        if let Some(labels) = all_labels_for_unify {
            for (idx, label_decl) in labels.iter().enumerate() {
                let label_name = label_decl.ld_id.name().to_string();
                let env_label = disambiguate_label(
                    &label_name,
                    expected_ty,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                );
                if let Some(env_label) = env_label {
                    // Instance 1: connect to base expression
                    let (_poly1, ty_arg1, ty_res1) =
                        crate::types::ctype::instance_label(ctx, false, &env_label);
                    let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_exp, ty_res1);

                    let is_overridden = overridden_positions.contains(&(idx as i32))
                        || overridden_positions.contains(&env_label.lbl_pos);

                    if debug_record_unify {
                        let summarize = |ty: TypeExprRef| {
                            let ty = ctx.repr(ty);
                            let desc = ctx.get_desc(ty);
                            match &*desc {
                                TypeDesc::Tconstr { path, args, .. } => {
                                    let args = args
                                        .iter()
                                        .map(|t| ctx.repr(*t).0.to_string())
                                        .collect::<Vec<_>>()
                                        .join(",");
                                    format!("{}#{}({})", path.name(), ty.0, args)
                                }
                                TypeDesc::Tvar(_) => format!("Tvar#{}", ty.0),
                                TypeDesc::Tlink(t) => format!("Tlink#{}->{}", ty.0, ctx.repr(*t).0),
                                _ => format!("other#{}", ty.0),
                            }
                        };
                        eprintln!(
                            "[record-unify] label={} idx={} lbl_pos={} overridden={} ty_exp={} ty_res1={}",
                            label_name,
                            idx,
                            env_label.lbl_pos,
                            is_overridden,
                            summarize(ty_exp),
                            summarize(ty_res1)
                        );
                    }

                    if !is_overridden {
                        // Match OCaml unify_kept: Kept fields carry ty_arg1 from
                        // the first instance_label in unify_kept, not the earlier
                        // pre-pass placeholder type.
                        if let Some((_lid, lbl, defn, _)) = typed_fields.iter_mut().find(
                            |(_, lbl, defn, _)| {
                                matches!(defn, RecordLabelDefinition::Kept(_))
                                    && (lbl.lbl_pos == env_label.lbl_pos
                                        || lbl.lbl_name == label_name)
                            },
                        ) {
                            *defn = RecordLabelDefinition::Kept(ty_arg1);
                            lbl.lbl_arg = ty_arg1;
                        }
                        // Instance 2: connect to expected type
                        let (_poly2, ty_arg2, ty_res2) =
                            crate::types::ctype::instance_label(ctx, false, &env_label);
                        // Bridge the two instances through their arg types
                        let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_arg1, ty_arg2);
                        // Connect instance 2 to expected type
                        let expected_inst = crate::types::instance(ctx, expected_ty);
                        if debug_record_unify {
                            let summarize = |ty: TypeExprRef| {
                                let ty = ctx.repr(ty);
                                let desc = ctx.get_desc(ty);
                                match &*desc {
                                    TypeDesc::Tconstr { path, args, .. } => {
                                        let args = args
                                            .iter()
                                            .map(|t| ctx.repr(*t).0.to_string())
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        format!("{}#{}({})", path.name(), ty.0, args)
                                    }
                                    TypeDesc::Tvar(_) => format!("Tvar#{}", ty.0),
                                    TypeDesc::Tlink(t) => format!("Tlink#{}->{}", ty.0, ctx.repr(*t).0),
                                    _ => format!("other#{}", ty.0),
                                }
                            };
                            eprintln!(
                                "[record-unify] label={} bridge ty_arg1={} ty_arg2={} expected_inst={} ty_res2={}",
                                label_name,
                                summarize(ty_arg1),
                                summarize(ty_arg2),
                                summarize(expected_inst),
                                summarize(ty_res2)
                            );
                        }
                        let _ = crate::types::unify(ctx, &mut tctx.unify_state, expected_inst, ty_res2);
                    }
                }
            }
        } else {
            // Fallback: find any label for single-instance unification
            let label_for_unify = typed_fields.iter().find_map(|(_, lbl, _, _)| {
                disambiguate_label(
                    &lbl.lbl_name,
                    expected_ty,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                )
            });
            if let Some(env_label) = label_for_unify {
                let (_poly_vars, _ty_arg, ty_res) =
                    crate::types::ctype::instance_label(ctx, false, &env_label);
                let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_exp, ty_res);
            } else {
                // Final fallback: direct unification
                unify_expression_types(
                    tctx,
                    loc,
                    ty_exp,
                    expected_ty,
                    Some(TypeClashContext::RecordSpread),
                )?;
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
        attributes.to_vec().into(),
    ))
}

/// Create a ConstructorDescription for the `Some` constructor.
fn make_some_constructor(
    ctx: &TypeContext<'_>,
    option_ty: TypeExprRef,
) -> crate::types::ConstructorDescription {
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
fn make_none_constructor(
    _ctx: &TypeContext<'_>,
    option_ty: TypeExprRef,
) -> crate::types::ConstructorDescription {
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
fn get_record_labels<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ty: TypeExprRef,
) -> Option<Vec<crate::types::decl::LabelDeclaration>> {
    let repr = ctx.repr(ty);
    let desc = ctx.get_desc(repr);
    if let crate::types::TypeDesc::Tconstr { ref path, .. } = *desc {
        if let Some(type_decl) = lookup_type_decl_for_path(path, env, pers_env, ctx) {
            if let crate::types::TypeKind::TypeRecord(ref labels, _) = type_decl.type_kind {
                if std::env::var_os("RUST_DEBUG_RECORD_LABELS").is_some()
                    && path.last() == "options"
                {
                    for lbl in labels {
                        if matches!(
                            lbl.ld_id.name(),
                            "compactDisplay" | "currency" | "useGrouping"
                        ) {
                            let ty = ctx.repr(lbl.ld_type);
                            let d = ctx.get_desc(ty);
                            let head = match &*d {
                                TypeDesc::Tconstr { path, args, .. } => {
                                    if path.name() == "option" && args.len() == 1 {
                                        let a = ctx.repr(args[0]);
                                        let ad = ctx.get_desc(a);
                                        match &*ad {
                                            TypeDesc::Tconstr { path, .. } => {
                                                format!("option<{}>", path.name())
                                            }
                                            _ => format!("option<ty#{}>", a.0),
                                        }
                                    } else {
                                        path.name()
                                    }
                                }
                                _ => format!("ty#{}", ty.0),
                            };
                            eprintln!(
                                "[record-labels] path={} field={} type={}",
                                path.name(),
                                lbl.ld_id.name(),
                                head
                            );
                        }
                    }
                }
                return Some(labels.clone());
            }
        }
        // For inline records in extension/exception constructors, the type path
        // is the constructor name. Look up the constructor and check cstr_inlined.
        let cstr_name = match path {
            Path::Pident(id) => Some(id.name().to_string()),
            Path::Pdot(_, name, _) => Some(name.clone()),
            _ => None,
        };
        if let Some(name) = cstr_name {
            if let Ok(cstr) = env.find_constructor(&name) {
                if let Some(ref inlined) = cstr.cstr_inlined {
                    if let crate::types::TypeKind::TypeRecord(ref labels, _) = inlined.type_kind {
                        return Some(labels.clone());
                    }
                }
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
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let resolved_lid = tctx.resolve_lid(field_lid.txt).clone();
    let field_name = tctx.longident_last_name(&resolved_lid);

    // Match OCaml type_label_access: type record first, then disambiguate.
    let typed_record = type_expect(tctx, env, record_expr, tctx.type_ctx.new_var(None), None)?;
    let ty_exp = typed_record.exp_type;

    // For qualified labels (M.field), respect the explicit path first.
    // OCaml keeps module-qualified field accesses path-directed instead of
    // preferring the "most recent" unqualified label candidate.
    let env_label = match resolved_lid {
        Longident::Ldot(_, _) => {
            let has_expected_path = extract_type_path_from_expected_with_persistent_env(
                ty_exp,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
            .is_some();

            if has_expected_path {
                disambiguate_label(
                    &field_name,
                    ty_exp,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .or_else(|| {
                    lookup_label_by_lid(
                        &resolved_lid,
                        tctx.arena,
                        env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                })
            } else {
                lookup_label_by_lid(
                    &resolved_lid,
                    tctx.arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                )
                .or_else(|| {
                    disambiguate_label(
                        &field_name,
                        ty_exp,
                        env,
                        &mut tctx.persistent_env,
                        tctx.type_ctx,
                    )
                })
            }
        }
        _ => disambiguate_label(
            &field_name,
            ty_exp,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        )
        .or_else(|| {
            lookup_label_by_lid(
                &resolved_lid,
                tctx.arena,
                env,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )
        }),
    };

    let (label_desc, field_ty, ty_res) = if let Some(env_label) = env_label {
        let (_poly_vars, ty_arg, ty_res) =
            crate::types::ctype::instance_label(tctx.type_ctx, false, &env_label);
        if std::env::var_os("RUST_DEBUG_FIELD_INST").is_some() {
            let name = env_label.lbl_name.as_str();
            if name == "bbox_offset" || name == "bbox_size" || name == "layout_transition_type" {
                let full_loc = tctx.arena.to_location(loc);
                let src_arg_repr = tctx.type_ctx.repr(env_label.lbl_arg);
                let src_res_repr = tctx.type_ctx.repr(env_label.lbl_res);
                let src_head = {
                    let d = tctx.type_ctx.get_desc(src_arg_repr);
                    match &*d {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                        _ => format!("ty#{}", src_arg_repr.0),
                    }
                };
                let ty_arg_repr = tctx.type_ctx.repr(ty_arg);
                let ty_res_repr = tctx.type_ctx.repr(ty_res);
                let ty_exp_repr = tctx.type_ctx.repr(ty_exp);
                eprintln!(
                    "[rust-field-inst] stage=before_unify loc={}:{} field={} src_arg={}({}) src_res={} ty_exp={}@{} ty_arg={}@{} ty_res={}@{}",
                    full_loc.loc_start.line,
                    full_loc.loc_start.column(),
                    name,
                    src_arg_repr.0,
                    src_head,
                    src_res_repr.0,
                    ty_exp_repr.0,
                    tctx.type_ctx.get_level(ty_exp_repr),
                    ty_arg_repr.0,
                    tctx.type_ctx.get_level(ty_arg_repr),
                    ty_res_repr.0,
                    tctx.type_ctx.get_level(ty_res_repr)
                );
            }
        }
        (env_label, ty_arg, ty_res)
    } else {
        let record_ty = tctx.type_ctx.new_var(None);
        let field_ty = tctx.type_ctx.new_var(None);
        (
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
            },
            field_ty,
            record_ty,
        )
    };

    // Match OCaml Pexp_field: unify record expression type against label result.
    unify_expression_types(tctx, loc, ty_exp, ty_res, None)?;

    if std::env::var_os("RUST_DEBUG_FIELD_INST").is_some() {
        let name = label_desc.lbl_name.as_str();
        if name == "bbox_offset" || name == "bbox_size" || name == "layout_transition_type" {
            let full_loc = tctx.arena.to_location(loc);
            let ty_exp_repr = tctx.type_ctx.repr(ty_exp);
            let ty_res_repr = tctx.type_ctx.repr(ty_res);
            let field_ty_repr = tctx.type_ctx.repr(field_ty);
            let summarize = |ty: TypeExprRef| {
                let r = tctx.type_ctx.repr(ty);
                let d = tctx.type_ctx.get_desc(r);
                match &*d {
                    TypeDesc::Tconstr { path, .. } => path.name(),
                    TypeDesc::Tvar(_) => "Tvar".to_string(),
                    TypeDesc::Tlink(target) => format!("Tlink->{}", tctx.type_ctx.repr(*target).0),
                    _ => format!("ty#{}", r.0),
                }
            };
            eprintln!(
                "[rust-field-inst] stage=after_unify loc={}:{} field={} ty_exp={}@{}({}) ty_res={}@{}({}) field_ty={}@{}({})",
                full_loc.loc_start.line,
                full_loc.loc_start.column(),
                name,
                ty_exp_repr.0,
                tctx.type_ctx.get_level(ty_exp_repr),
                summarize(ty_exp),
                ty_res_repr.0,
                tctx.type_ctx.get_level(ty_res_repr),
                summarize(ty_res),
                field_ty_repr.0,
                tctx.type_ctx.get_level(field_ty_repr),
                summarize(field_ty),
            );
        }
    }

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
    let resolved_lid = tctx.resolve_lid(field_lid.txt).clone();
    let field_name = tctx.longident_last_name(&resolved_lid);
    // Match field-access disambiguation: type the record expression first,
    // then pick the label based on the resolved record type.
    let record_ty = ctx.new_var(None);
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;
    let ty_exp = typed_record.exp_type;

    let env_label = disambiguate_label(
        &field_name,
        ty_exp,
        env,
        &mut tctx.persistent_env,
        ctx,
    )
    .or_else(|| {
        lookup_label_by_lid(
            &resolved_lid,
            tctx.arena,
            env,
            &mut tctx.persistent_env,
            ctx,
        )
    });
    let (label_desc, field_ty) = if let Some(env_label) = env_label {
        let (_poly_vars, ty_arg, ty_res) =
            crate::types::ctype::instance_label(ctx, false, &env_label);
        unify_expression_types(tctx, loc, ty_res, record_ty, None)?;
        (env_label, ty_arg)
    } else {
        let field_ty = ctx.new_var(None);
        (
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
            },
            field_ty,
        )
    };

    // Type check the new value with the proper field type
    let typed_value = type_expect(tctx, env, new_value, field_ty, None)?;

    // OCaml: rue { ... exp_type = instance_def Predef.type_unit; ... }
    // Keep original argument order to preserve Tlink direction.
    let inst_expected = instance_if_generic(tctx.type_ctx, expected_ty);
    unify_expression_types(tctx, loc, inst_expected, unit_ty, context)?;

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
    let ctx = tctx.type_ctx;
    let debug_constraint_trace = std::env::var_os("RUST_DEBUG_CONSTRAINT_TRACE").is_some();
    let debug_constraint_trace_all =
        std::env::var_os("RUST_DEBUG_CONSTRAINT_TRACE_ALL").is_some();
    let debug_loc = if debug_constraint_trace {
        Some(tctx.arena.to_location(loc))
    } else {
        None
    };
    let should_debug_loc = debug_constraint_trace_all
        || debug_loc.as_ref().is_some_and(|full_loc| {
            matches!(full_loc.loc_start.line, 207 | 215 | 223 | 231 | 271 | 301)
        });
    let summarize = |ty: TypeExprRef| -> String {
        let ty = ctx.repr(ty);
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let args = args
                    .iter()
                    .map(|a| ctx.repr(*a).0.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{}#{}({})", path.name(), ty.0, args)
            }
            TypeDesc::Tarrow { .. } => format!("Tarrow#{}", ty.0),
            TypeDesc::Tvar(_) => format!("Tvar#{}", ty.0),
            TypeDesc::Tlink(t) => format!("Tlink#{}->{}", ty.0, ctx.repr(*t).0),
            _ => format!("other#{}", ty.0),
        }
    };

    // Match OCaml typecore.ml Pexp_constraint:
    // begin_def; transl_simple_type; end_def; generalize_structure;
    // type_argument env sarg ty (instance env ty); exp_type = instance env ty.
    ctx.begin_def();
    let (typed_ctype, ctype_ty) = transl_type(tctx, env, core_type)?;
    ctx.end_def();
    let var_level = ctx.current_level();
    crate::types::generalize_structure(ctx, var_level, ctype_ty);

    // Match OCaml's right-to-left tuple evaluation order in Pexp_constraint:
    //   (type_argument env sarg ty (instance env ty), instance env ty)
    // evaluates as:
    //   1. result_ty = instance env ty     (second element first)
    //   2. arg_unify_ty = instance env ty  (arg to type_argument)
    //   3. type_expect env sarg ty         (inside type_argument)
    //   4. unify_exp env texp arg_unify_ty (type_argument's post-unify)
    //   5. rue { exp_type = result_ty }    (outer rue)
    //
    // Both instances are created BEFORE type_expect runs, so they see the
    // GENERIC ctype_ty before any handler can consume it via unification.
    let result_ty = crate::types::instance(ctx, ctype_ty);
    let arg_unify_ty = crate::types::instance(ctx, ctype_ty);

    if should_debug_loc {
        let full_loc = debug_loc.as_ref().unwrap();
        eprintln!(
            "[rust-constraint] stage=init loc={}:{} cty={} result_ty={} arg_ty={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            summarize(ctype_ty),
            summarize(result_ty),
            summarize(arg_unify_ty)
        );
    }

    // Pass the GENERIC constraint type to type_expect (matches OCaml).
    // Rue handlers create per-expression instances via rue_unify.
    // Non-rue handlers (tuple, array, construct) use instance_if_generic
    // to avoid corrupting the generic type. Set generic_constraint_body_ty
    // so match cases can create fresh instances per case body.
    let prev_generic_constraint = tctx.generic_constraint_body_ty;
    tctx.generic_constraint_body_ty = Some(ctype_ty);
    let typed_inner = type_expect(tctx, env, inner_expr, ctype_ty, None)?;
    if should_debug_loc {
        let full_loc = debug_loc.as_ref().unwrap();
        eprintln!(
            "[rust-constraint] stage=typed_inner loc={}:{} inner_ty={} cty_now={} arg_ty_now={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            summarize(typed_inner.exp_type),
            summarize(ctype_ty),
            summarize(arg_unify_ty)
        );
    }
    tctx.generic_constraint_body_ty = prev_generic_constraint;
    unify_expression_types(tctx, loc, typed_inner.exp_type, arg_unify_ty, None)?;

    if should_debug_loc {
        let full_loc = debug_loc.as_ref().unwrap();
        eprintln!(
            "[rust-constraint] stage=post_unify loc={}:{} inner_ty={} cty_now={} arg_ty_now={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            summarize(typed_inner.exp_type),
            summarize(ctype_ty),
            summarize(arg_unify_ty)
        );
    }

    rue_unify(tctx, loc, result_ty, expected_ty, None)?;

    if should_debug_loc {
        let full_loc = debug_loc.as_ref().unwrap();
        eprintln!(
            "[rust-constraint] stage=post_rue loc={}:{} result_ty={} expected_ty={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            summarize(result_ty),
            summarize(expected_ty)
        );
    }

    let mut result = typed_inner;
    result.exp_type = result_ty;
    let mut extras = Vec::with_capacity(result.exp_extra.len() + 1);
    extras.push((
        crate::types::typedtree::ExpExtra::Texp_constraint(typed_ctype),
        loc.clone(),
        attributes.to_vec().into(),
    ));
    extras.extend(result.exp_extra.into_iter());
    result.exp_extra = extras;
    Ok(result)
}

/// OCaml stores expression extras with list-cons, so outer wrappers appear
/// before inner wrappers in `exp_extra`.
fn prepend_exp_extra(
    mut expr: Expression,
    extra: crate::types::typedtree::ExpExtra,
    loc: LocIdx,
    attrs: Attributes,
) -> Expression {
    let mut extras = Vec::with_capacity(expr.exp_extra.len() + 1);
    extras.push((extra, loc, attrs));
    extras.extend(expr.exp_extra.into_iter());
    expr.exp_extra = extras;
    expr
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

    // OCaml: rue { ... exp_type = ty'; ... } — unify coercion target with expected
    // Keep original argument order to preserve Tlink direction.
    let inst_expected = instance_if_generic(tctx.type_ctx, expected_ty);
    if crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, inst_expected, to_ty).is_err() {
        return Err(TypeCoreError::ExprTypeClash {
            trace: vec![(inst_expected, to_ty)],
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

    // When no explicit from_type and from_ty is still an unresolved Tvar,
    // unify it with the target type. This matches OCaml's subtype approximation
    // which resolves unconstrained expression types to the coercion target.
    // Guard: only when still Tvar to avoid incorrectly replacing private types.
    if opt_from_type.is_none() {
        let from_repr = tctx.type_ctx.repr(from_ty);
        if matches!(&*tctx.type_ctx.get_desc(from_repr), TypeDesc::Tvar(_)) {
            let _ = crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, from_ty, to_ty);
        }
    }

    // Return the inner expression with the coercion as exp_extra
    // The expression type becomes the target type after coercion
    let mut result = prepend_exp_extra(
        typed_inner,
        crate::types::typedtree::ExpExtra::Texp_coerce(to_typed_ctype),
        loc.clone(),
        attributes.to_vec().into(),
    );
    result.exp_type = to_ty;
    Ok(result)
}

/// Type check open expression.
fn type_open(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    override_flag: &crate::parser::ast::OverrideFlag,
    lid: &Located<LidentIdx>,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Open the module's bindings into scope for the body
    let open_lid = tctx.arena.get_longident(lid.txt);
    let mut open_env = env.clone();

    // Resolve through Env alias scraping and rewritten signatures so opened
    // bindings preserve OCaml-style module prefixes in types.
    let path = if let Some((resolved_path, sig_items)) =
        env.resolve_module_lid(open_lid, tctx.arena, &mut tctx.persistent_env, tctx.type_ctx)
    {
        crate::cmi::persistent_env::add_signature_to_env(
            &sig_items,
            &resolved_path,
            &mut open_env,
            tctx.type_ctx,
            true,
        );
        resolved_path
    } else {
        crate::types::typemod::path_from_longident(open_lid, |idx| tctx.arena.get_string(idx))
    };

    // Type check the body expression in the extended environment
    let typed_body = type_expect(tctx, &open_env, body, expected_ty, None)?;

    // Return expression with Texp_open in exp_extra (matching OCaml)
    Ok(prepend_exp_extra(
        typed_body,
        crate::types::typedtree::ExpExtra::Texp_open(
            override_flag.clone(),
            path,
            lid.clone(),
            EnvRef(0),
        ),
        loc.clone(),
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
    let ctx = tctx.type_ctx;
    let name_str = tctx.arena.get_string(name.txt).to_string();
    let replacement_ty = ctx.new_var(None);

    // Match OCaml typecore.ml:
    // 1. Enter a fresh abstract type declaration for the newtype name.
    // 2. Type the body with that declaration in scope.
    // 3. Copy the resulting type and replace occurrences of the newtype constructor
    //    with a fresh type variable.
    // 4. Restore definition level even on error.
    ctx.begin_def();
    let result = (|| -> TypeCoreResult<Expression> {
        let level = ctx.current_level();
        let mut new_env = env.clone();
        let newtype_id = Ident::create_local(name_str.clone());
        new_env.add_type(
            newtype_id.clone(),
            crate::types::decl::TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: crate::types::decl::TypeKind::TypeAbstract,
                type_private: crate::types::asttypes::PrivateFlag::Public,
                type_manifest: None,
                type_variance: vec![],
                type_newtype_level: Some((level, level)),
                type_loc: convert_loc(loc, tctx.arena),
                type_attributes: vec![],
                type_immediate: false,
                type_unboxed: crate::types::decl::UnboxedStatus::FALSE_FALSE,
                type_inlined_types: vec![],
                type_path: None,
            },
        );

        // OCaml types the newtype body with type_exp (no expected type).
        // Use a fresh variable here to avoid constraining the body early.
        let body_ty = ctx.new_var(None);
        let typed_body = type_expect(tctx, &new_env, body, body_ty, None)?;

        // Subst.type_expr Subst.identity in OCaml: full structural copy
        // (copies ALL nodes regardless of level, unlike copy_type which
        // returns identity for non-generic nodes). This ensures
        // replace_newtype_path only modifies the copy, not shared originals.
        let rewritten_ty = crate::types::ctype::subst_identity_copy(ctx, typed_body.exp_type);

        fn replace_newtype_path(
            ctx: &TypeContext<'_>,
            ty: TypeExprRef,
            target_id: &Ident,
            replacement_ty: TypeExprRef,
            seen: &mut HashSet<TypeExprRef>,
        ) {
            let ty = ctx.repr(ty);
            if !seen.insert(ty) {
                return;
            }

            let should_replace = matches!(
                &*ctx.get_desc(ty),
                TypeDesc::Tconstr {
                    path: Path::Pident(id),
                    ..
                } if id.same(target_id)
            );

            if should_replace {
                crate::types::link_type(ctx, ty, replacement_ty);
                return;
            }

            crate::types::iter_type_expr(ctx, ty, |child| {
                replace_newtype_path(ctx, child, target_id, replacement_ty, seen);
            });
        }

        let mut seen = HashSet::new();
        replace_newtype_path(ctx, rewritten_ty, &newtype_id, replacement_ty, &mut seen);

        // OCaml: rue { ... exp_type = ety; ... }
        rue_unify(tctx, loc, rewritten_ty, expected_ty, None)?;

        let mut result = prepend_exp_extra(
            typed_body,
            crate::types::typedtree::ExpExtra::Texp_newtype(name_str),
            loc,
            attributes.to_vec().into(),
        );
        result.exp_loc = loc;
        result.exp_type = rewritten_ty;
        Ok(result)
    })();
    ctx.end_def();
    result
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
fn collect_public_methods_from_object_type<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<Vec<String>> {
    let expanded = crate::types::ctype::expand_head(ctx, env, ty);
    let fields = {
        let desc = ctx.get_desc(expanded);
        match &*desc {
            TypeDesc::Tobject { fields, .. } => *fields,
            _ => return None,
        }
    };

    let mut methods = Vec::new();
    let mut seen = HashSet::new();
    let mut current = fields;

    loop {
        let current_repr = ctx.repr(current);
        if !seen.insert(current_repr) {
            break;
        }

        let (next, should_collect, method_name, stop) = {
            let desc = ctx.get_desc(current_repr);
            match &*desc {
                TypeDesc::Tfield {
                    name, kind, rest, ..
                } => (
                    *rest,
                    matches!(kind, crate::types::type_expr::FieldKind::Fpresent),
                    name.clone(),
                    false,
                ),
                TypeDesc::Tnil => (current_repr, false, String::new(), true),
                _ => (current_repr, false, String::new(), true),
            }
        };

        if stop {
            break;
        }
        if should_collect {
            methods.push(method_name);
        }
        current = next;
    }

    Some(methods)
}

fn method_name_is_plain_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !first.is_ascii_alphabetic() {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn instantiate_poly_body_for_send(
    ctx: &TypeContext<'_>,
    body: TypeExprRef,
    vars: &[TypeExprRef],
) -> TypeExprRef {
    let mut cache = HashMap::new();
    for var in vars {
        cache.insert(ctx.repr(*var), ctx.new_var(None));
    }
    copy_lookup_type_expr(ctx, body, &mut cache)
}

fn type_send(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    obj_expr: &ParsedExpression,
    method: &Located<std::borrow::Cow<'static, str>>,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // Type the object expression first (OCaml `type_exp` path).
    let obj_ty = ctx.new_var(None);
    let mut typed_obj = type_expect(tctx, env, obj_expr, obj_ty, None)?;
    if let ExpressionDesc::Texp_ident(_, _, desc) = &typed_obj.exp_desc {
        if let crate::types::ValueKind::ValPrim(prim) = &desc.val_kind {
            let val_ty = ctx.repr(desc.val_type);
            let val_desc = ctx.get_desc(val_ty);
            if method_name_is_plain_ident(&prim.prim_name)
                && method_name_is_plain_ident(method.txt.as_ref())
                && matches!(&*val_desc, TypeDesc::Tconstr { args, .. } if args.is_empty())
            {
                typed_obj.exp_type = desc.val_type;
            }
        }
    }

    // Port OCaml `Pexp_send` + `Ctype.filter_method` behavior:
    // - constrain object type to contain the requested method
    // - derive method result type from polymorphic method slot
    let method_result_ty = (|| -> Result<TypeExprRef, TypeError> {
        let method_slot_ty =
            crate::types::ctype::filter_method(ctx, env, &method.txt, typed_obj.exp_type)?;
        let method_slot_ty = ctx.repr(method_slot_ty);

        enum MethodSlotAction {
            PolyNoVars(TypeExprRef),
            PolyWithVars(TypeExprRef, Vec<TypeExprRef>),
            Var,
            Other,
        }

        let action = {
            let slot_desc = ctx.get_desc(method_slot_ty);
            match &*slot_desc {
                TypeDesc::Tpoly { body, vars } if vars.is_empty() => {
                    MethodSlotAction::PolyNoVars(*body)
                }
                TypeDesc::Tpoly { body, vars } => {
                    MethodSlotAction::PolyWithVars(*body, vars.clone())
                }
                TypeDesc::Tvar(_) => MethodSlotAction::Var,
                _ => MethodSlotAction::Other,
            }
        };

        let result_ty = match action {
            MethodSlotAction::PolyNoVars(body) => crate::types::ctype::instance(ctx, body),
            MethodSlotAction::PolyWithVars(body, vars) => {
                instantiate_poly_body_for_send(ctx, body, &vars)
            }
            MethodSlotAction::Var => {
                let method_result_ty = ctx.new_var(None);
                let poly_ty = ctx.new_poly(method_result_ty, vec![]);
                let method_slot_ty = crate::types::ctype::copy_type(ctx, method_slot_ty);
                crate::types::unify(ctx, &mut tctx.unify_state, method_slot_ty, poly_ty)?;
                method_result_ty
            }
            MethodSlotAction::Other => method_slot_ty,
        };
        Ok(result_ty)
    })();

    let method_result_ty = match method_result_ty {
        Ok(ty) => ty,
        Err(_) => {
            if method.txt.ends_with("#=") {
                return Ok(Expression::new(
                    ExpressionDesc::Texp_send(
                        Box::new(typed_obj),
                        crate::types::typedtree::MethKind::Tmeth_name(method.txt.to_string()),
                        None,
                    ),
                    loc.clone(),
                    expected_ty,
                    EnvRef(0),
                    attributes.to_vec().into(),
                ));
            }
            let alternatives = collect_public_methods_from_object_type(ctx, env, typed_obj.exp_type);
                return Err(TypeCoreError::UndefinedMethod {
                    ty: typed_obj.exp_type,
                    method: method.txt.to_string(),
                    alternatives,
                });
            }
    };

    // OCaml: rue { ... exp_type = method_result_ty; ... }
    if rue_unify(tctx, loc, method_result_ty, expected_ty, None).is_err() {
        return Ok(Expression::new(
            ExpressionDesc::Texp_send(
                Box::new(typed_obj),
                crate::types::typedtree::MethKind::Tmeth_name(method.txt.to_string()),
                None,
            ),
            loc.clone(),
            expected_ty,
            EnvRef(0),
            attributes.to_vec().into(),
        ));
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_send(
            Box::new(typed_obj),
            crate::types::typedtree::MethKind::Tmeth_name(method.txt.to_string()),
            None,
        ),
        loc.clone(),
        method_result_ty,
        EnvRef(0),
        attributes.to_vec().into(),
    ))
}

/// Type check let exception.
fn type_letexception(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    ext_constr: &crate::parser::ast::ExtensionConstructor,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;
    let arena = tctx.arena;

    let name_str = arena.get_string(ext_constr.pext_name.txt).to_string();
    let id = Ident::create_local(&name_str);

    // Match OCaml's transl_exception: begin_def before creating arg types,
    // end_def + generalize after, so instance_constructor creates fresh copies.
    ctx.begin_def();
    let (typed_args, typed_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) =
        match &ext_constr.pext_kind {
            crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                let mut arg_ty_refs = Vec::new();
                let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                    crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                        let mut typed = Vec::new();
                        for ty in types {
                            let (typed_ct, ty_ref) =
                                transl_type(tctx, env, arena.get_core_type(*ty))?;
                            arg_ty_refs.push(ty_ref);
                            typed.push(typed_ct);
                        }
                        (
                            crate::types::typedtree::ConstructorArgument::Cstr_tuple(typed),
                            crate::types::ConstructorArguments::CstrTuple(arg_ty_refs.clone()),
                            arg_ty_refs.clone(),
                            None,
                        )
                    }
                    crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                        let mut typed_labels = Vec::new();
                        let mut decl_labels = Vec::new();
                        for label in labels {
                            let label_name = arena.get_string(label.pld_name.txt).to_string();
                            let (typed_ct, ty_ref) =
                                transl_type(tctx, env, arena.get_core_type(label.pld_type))?;
                            let poly_ty_ref = ctx.new_poly(ty_ref, vec![]);
                            let poly_typed_ct = crate::types::typedtree::TypedCoreType {
                                ctyp_desc: crate::types::typedtree::TypedCoreTypeDesc::Ttyp_poly(
                                    vec![],
                                    Box::new(typed_ct.clone()),
                                ),
                                ctyp_type: poly_ty_ref,
                                ctyp_env: typed_ct.ctyp_env,
                                ctyp_loc: typed_ct.ctyp_loc,
                                ctyp_attributes: Attributes::new(),
                            };
                            typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                ld_id: Ident::create_local(&label_name),
                                ld_name: crate::parse_arena::Located {
                                    txt: label_name.clone(),
                                    loc: label.pld_name.loc,
                                },
                                ld_mutable: label.pld_mutable,
                                ld_optional: label.pld_optional,
                                ld_type: poly_typed_ct,
                                ld_loc: label.pld_loc,
                                ld_attributes: label.pld_attributes.clone(),
                            });
                            decl_labels.push(crate::types::decl::LabelDeclaration {
                                ld_id: Ident::create_local(&label_name),
                                ld_mutable: match label.pld_mutable {
                                    crate::parser::ast::MutableFlag::Immutable => {
                                        crate::types::MutableFlag::Immutable
                                    }
                                    crate::parser::ast::MutableFlag::Mutable => {
                                        crate::types::MutableFlag::Mutable
                                    }
                                },
                                ld_optional: label.pld_optional,
                                ld_type: poly_ty_ref,
                                ld_loc: arena.to_location(label.pld_loc),
                                ld_attributes: vec![],
                            });
                        }
                        let inline_path = Path::pident(id.clone());
                        // Match OCaml's newgenconstr: create at generic_level
                        let inline_ty = ctx.new_generic_constr(inline_path.clone(), vec![]);
                        let inline_decl = crate::types::TypeDeclaration {
                            type_params: vec![],
                            type_arity: 0,
                            type_kind: crate::types::TypeKind::TypeRecord(
                                decl_labels.clone(),
                                crate::types::RecordRepresentation::RecordExtension,
                            ),
                            type_private: crate::types::PrivateFlag::Public,
                            type_manifest: None,
                            type_variance: vec![],
                            type_newtype_level: None,
                            type_loc: crate::location::Location::none(),
                            type_attributes: vec![],
                            type_immediate: false,
                            type_unboxed: crate::types::UnboxedStatus::default(),
                            type_inlined_types: vec![],
                            type_path: None,
                        };
                        (
                            crate::types::typedtree::ConstructorArgument::Cstr_record(typed_labels),
                            crate::types::ConstructorArguments::CstrRecord(decl_labels),
                            vec![inline_ty],
                            Some(Box::new(inline_decl)),
                        )
                    }
                };
                let (typed_ret, ext_ret_ty) = match ret {
                    Some(ct) => {
                        let (typed_ct, ty_ref) = transl_type(tctx, env, arena.get_core_type(*ct))?;
                        (Some(typed_ct), Some(ty_ref))
                    }
                    None => (None, None),
                };
                (
                    typed_args,
                    typed_ret,
                    ext_args,
                    cstr_args,
                    cstr_inlined,
                    ext_ret_ty,
                )
            }
            crate::parser::ast::ExtensionConstructorKind::Pext_rebind(_lid) => (
                crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![]),
                None,
                crate::types::ConstructorArguments::CstrTuple(vec![]),
                vec![],
                None,
                None,
            ),
        };
    ctx.end_def();

    // Generalize constructor arg types (matching OCaml's iter_type_expr_cstr_args generalize)
    match &ext_args {
        crate::types::ConstructorArguments::CstrTuple(types) => {
            for ty in types {
                crate::types::generalize(ctx, *ty);
            }
        }
        crate::types::ConstructorArguments::CstrRecord(labels) => {
            for label in labels {
                crate::types::generalize(ctx, label.ld_type);
            }
        }
    }
    if let Some(ret_ty) = ext_ret_ty {
        crate::types::generalize(ctx, ret_ty);
    }

    let exn_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("exn")), vec![]);
    let exn_path = Path::pident(id.clone());
    let cstr_desc = crate::types::decl::ConstructorDescription {
        cstr_name: name_str.clone(),
        cstr_res: exn_ty,
        cstr_existentials: vec![],
        cstr_args: cstr_args.clone(),
        cstr_arity: cstr_args.len() as i32,
        cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(exn_path),
        cstr_consts: 0,
        cstr_nonconsts: 0,
        cstr_generalized: false,
        cstr_private: crate::types::PrivateFlag::Public,
        cstr_loc: crate::location::Location::none(),
        cstr_attributes: vec![],
        cstr_inlined: cstr_inlined.clone(),
    };

    let mut new_env = env.clone();
    if let Some(ref inlined_decl) = cstr_inlined {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) = inlined_decl.type_kind {
            let ty_res = ctx.new_generic_constr(
                Path::pident(id.clone()),
                inlined_decl.type_params.clone(),
            );
            for (pos, ld) in labels.iter().enumerate() {
                let lbl_desc = crate::types::LabelDescription {
                    lbl_name: ld.ld_id.name().to_string(),
                    lbl_res: ty_res,
                    lbl_arg: crate::types::ctype::remap_label_type_to_params(
                        ctx,
                        ld.ld_type,
                        &inlined_decl.type_params,
                    ),
                    lbl_mut: ld.ld_mutable,
                    lbl_optional: ld.ld_optional,
                    lbl_pos: pos as i32,
                    lbl_all: crate::types::LabelArrayRef(0),
                    lbl_repres: repres.clone(),
                    lbl_private: inlined_decl.type_private,
                    lbl_loc: ld.ld_loc.clone(),
                    lbl_attributes: ld.ld_attributes.clone(),
                };
                new_env.add_label(ld.ld_id.clone(), lbl_desc);
            }
        }
    }
    new_env.add_constructor(id.clone(), cstr_desc);

    let typed_body = type_expect(tctx, &new_env, body, expected_ty, None)?;

    let typed_ext_constr = crate::types::typedtree::ExtensionConstructor {
        ext_id: id,
        ext_name: crate::parse_arena::Located {
            txt: name_str,
            loc: ext_constr.pext_name.loc,
        },
        ext_type: crate::types::ExtensionConstructor {
            ext_type_path: Path::pident(Ident::create_persistent("exn")),
            ext_type_params: vec![],
            ext_args,
            ext_ret_type: ext_ret_ty,
            ext_private: crate::types::PrivateFlag::Public,
            ext_loc: arena.to_location(loc),
            ext_attributes: vec![],
            ext_is_exception: true,
        },
        ext_kind: crate::types::typedtree::ExtensionConstructorKind::Text_decl(
            typed_args, typed_ret,
        ),
        ext_loc: ext_constr.pext_loc,
        ext_attributes: ext_constr.pext_attributes.clone(),
    };
    let body_ty = typed_body.exp_type;

    Ok(Expression::new(
        ExpressionDesc::Texp_letexception(typed_ext_constr, Box::new(typed_body)),
        loc.clone(),
        body_ty,
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
    name: &Located<StrIdx>,
    module_expr: &crate::parser::ast::ModuleExpr,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    fn path_root_is_module(path: &Path, module_id: &Ident) -> bool {
        match path {
            Path::Pident(id) => id.same(module_id),
            Path::Pdot(prefix, _, _) => path_root_is_module(prefix, module_id),
            Path::Papply(_, _) => false,
        }
    }

    fn replace_module_root_path(path: &Path, module_id: &Ident, alias_root: &Path) -> Path {
        match path {
            Path::Pident(id) => {
                if id.same(module_id) {
                    alias_root.clone()
                } else {
                    path.clone()
                }
            }
            Path::Pdot(prefix, name, _) => {
                let rewritten_prefix = replace_module_root_path(prefix, module_id, alias_root);
                if rewritten_prefix == **prefix {
                    path.clone()
                } else {
                    Path::pdot(rewritten_prefix, name.clone())
                }
            }
            Path::Papply(_, _) => path.clone(),
        }
    }

    fn resolve_alias_root_from_module_type(
        env: &Env,
        mty: &crate::types::decl::ModuleType,
        visited: &mut HashSet<String>,
    ) -> Option<Path> {
        use crate::types::decl::ModuleType as DeclMty;

        match mty {
            DeclMty::MtyAlias(_, alias_path) => Some(alias_path.clone()),
            DeclMty::MtyIdent(path) => match path {
                Path::Pident(id) => {
                    let name = id.name().to_string();
                    if !visited.insert(name.clone()) {
                        return None;
                    }

                    if let Ok(mtd) = env.find_modtype(&name) {
                        if let Some(inner_mty) = &mtd.mtd_type {
                            if let Some(alias_root) =
                                resolve_alias_root_from_module_type(env, inner_mty, visited)
                            {
                                return Some(alias_root);
                            }
                        }
                    }

                    if let Ok(md) = env.find_module(&name) {
                        if let Some(alias_root) =
                            resolve_alias_root_from_module_type(env, &md.md_type, visited)
                        {
                            return Some(alias_root);
                        }
                    }

                    None
                }
                _ => Some(path.clone()),
            },
            _ => None,
        }
    }

    fn resolve_letmodule_alias_root(env: &Env, module_id: &Ident) -> Option<Path> {
        let md = env.find_module(module_id.name()).ok()?;
        let mut visited = HashSet::new();
        resolve_alias_root_from_module_type(env, &md.md_type, &mut visited)
    }

    fn register_module_type_type_decls_by_stamp(
        ctx: &TypeContext<'_>,
        mty: &crate::types::decl::ModuleType,
    ) {
        use crate::types::decl::ModuleType as DeclMty;
        use crate::types::decl::SignatureItem;

        match mty {
            DeclMty::MtySignature(sig_items) => {
                for item in sig_items {
                    match item {
                        SignatureItem::SigType(id, decl, _) => {
                            if id.stamp() != 0 {
                                ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
                            }
                        }
                        SignatureItem::SigModule(_, md, _) => {
                            register_module_type_type_decls_by_stamp(ctx, &md.md_type);
                        }
                        SignatureItem::SigModtype(_, mtd) => {
                            if let Some(inner) = &mtd.mtd_type {
                                register_module_type_type_decls_by_stamp(ctx, inner);
                            }
                        }
                        _ => {}
                    }
                }
            }
            DeclMty::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_mty) = param_type.as_deref() {
                    register_module_type_type_decls_by_stamp(ctx, param_mty);
                }
                register_module_type_type_decls_by_stamp(ctx, result);
            }
            DeclMty::MtyAlias(_, _) | DeclMty::MtyIdent(_) => {}
        }
    }

    fn replace_letmodule_local_paths<'a>(
        ctx: &'a TypeContext<'a>,
        env: &Env,
        ty: TypeExprRef,
        module_id: &Ident,
        replacements: &mut HashMap<String, TypeExprRef>,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return;
        }

        let local_constr = match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, args, .. } if path_root_is_module(path, module_id) => {
                Some((path.clone(), args.clone()))
            }
            _ => None,
        };

        if let Some((local_path, local_args)) = local_constr {
            // Match OCaml `Ctype.nondep_type`: for local module-rooted paths,
            // first try one-step abbreviation expansion.
            if let Some(expanded) = crate::types::ctype::expand_head_once(ctx, env, ty) {
                let expanded = ctx.repr(expanded);
                if expanded != ty {
                    crate::types::link_type(ctx, ty, expanded);
                    replace_letmodule_local_paths(
                        ctx,
                        env,
                        expanded,
                        module_id,
                        replacements,
                        seen,
                    );
                    return;
                }
            }

            // If expansion is unavailable, try replacing the local root module
            // with its underlying alias root path (`MS.t` -> `Belt_MapString.t`).
            if let Some(alias_root) = resolve_letmodule_alias_root(env, module_id) {
                let rewritten_path = replace_module_root_path(&local_path, module_id, &alias_root);
                if rewritten_path != local_path {
                    let rewritten_ty = ctx.new_constr(rewritten_path, local_args);
                    crate::types::link_type(ctx, ty, rewritten_ty);
                    replace_letmodule_local_paths(
                        ctx,
                        env,
                        rewritten_ty,
                        module_id,
                        replacements,
                        seen,
                    );
                    return;
                }
            }

            // If no manifest expansion is available, keep the existing fallback:
            // abstract this module-rooted constructor with a shared fresh variable.
            let key = local_path.name();
            let replacement_ty = *replacements.entry(key).or_insert_with(|| ctx.new_var(None));
            crate::types::link_type(ctx, ty, replacement_ty);
            return;
        }

        crate::types::iter_type_expr(ctx, ty, |child| {
            replace_letmodule_local_paths(ctx, env, child, module_id, replacements, seen);
        });
    }

    let arena = tctx.arena;
    let ctx = tctx.type_ctx;
    let mod_name_str = arena.get_string(name.txt).to_string();
    let mod_id = Ident::create_local(&mod_name_str);
    let letmodule_ty = ctx.new_var(None);

    // Match OCaml `Pexp_letmodule` level scoping (`begin_def`/`end_def`).
    // Mirror Typetexp.narrow()/widen() so module typing does not clobber
    // outer expression type variables (e.g. `'self` in @this callbacks).
    let narrow_global_level = ctx.increase_global_level();
    let saved_type_variables = tctx.type_variables.clone();
    ctx.begin_def();
    let letmodule_def_level = ctx.current_level();
    let scoped_result = (|| -> TypeCoreResult<(
        crate::types::typedtree::ModuleExpr,
        Env,
        Expression,
        TypeExprRef,
    )> {
        // Type check the module expression and build its signature for the env
        let (typed_mod, mut mod_sig) = match &*module_expr.pmod_desc {
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
                    mod_attributes: Attributes::new(),
                };
                (md, crate::types::decl::ModuleType::MtySignature(sig_items))
            }
            crate::parser::ast::ModuleExprDesc::Pmod_ident(lid) => {
                let md = crate::types::typemod::type_module_expr_with_alias_mode(
                    tctx,
                    env,
                    arena,
                    module_expr,
                    true,
                )
                .map_err(|e| TypeCoreError::Other(format!("letmodule: {e:?}")))?;
                // Match OCaml Pexp_letmodule: store MtyAlias for module aliases.
                // OCaml's Env.enter_module stores Mty_alias(Mta_absent, path) for
                // Pmod_ident, which enables normalize_path_full to follow the alias
                // and memorize_simple_abbrev to create type sharing.
                let longident = arena.get_longident(lid.txt);
                let alias_path = crate::types::typemod::lookup_module_path_by_lid(
                    longident,
                    arena,
                    env,
                    &mut tctx.persistent_env,
                    tctx.type_ctx,
                );
                let mod_sig = if let Some(path) = alias_path {
                    crate::types::decl::ModuleType::MtyAlias(
                        crate::types::decl::AliasPresence::MtaAbsent,
                        path,
                    )
                } else if let Some(sig) = crate::types::typemod::lookup_module_type_from_parsed_module_expr(
                    tctx,
                    env,
                    arena,
                    module_expr,
                ) {
                    sig
                } else if let Some(sig) =
                    crate::types::typemod::extract_module_type_from_mod_expr_pub(&md)
                {
                    sig
                } else {
                    crate::types::decl::ModuleType::MtySignature(vec![])
                };
                (md, mod_sig)
            }
            _ => {
                let md = crate::types::typemod::type_module_expr_with_alias_mode(
                    tctx,
                    env,
                    arena,
                    module_expr,
                    true,
                )
                .map_err(|e| TypeCoreError::Other(format!("letmodule: {e:?}")))?;
                // Match OCaml Pexp_letmodule: prefer semantic module type from the
                // parsed module expression (same source as Env.enter_module), then
                // fall back to typed-expression extraction.
                let mod_sig = if let Some(sig) = crate::types::typemod::lookup_module_type_from_parsed_module_expr(
                    tctx,
                    env,
                    arena,
                    module_expr,
                ) {
                    sig
                } else if let Some(sig) =
                    crate::types::typemod::extract_module_type_from_mod_expr_pub(&md)
                {
                    sig
                } else {
                    crate::types::decl::ModuleType::MtySignature(vec![])
                };
                (md, mod_sig)
            }
        };

        // Keep let-module member lookups stable for direct module aliases
        // (`module M = List` / constrained direct idents) by materializing
        // aliases/identifiers to signatures when the environment can resolve them.
        let materialize_alias_sig = match &*module_expr.pmod_desc {
            crate::parser::ast::ModuleExprDesc::Pmod_ident(_) => true,
            crate::parser::ast::ModuleExprDesc::Pmod_constraint(inner, _) => {
                matches!(
                    &*arena.get_mod_expr(*inner).pmod_desc,
                    crate::parser::ast::ModuleExprDesc::Pmod_ident(_)
                )
            }
            _ => false,
        };
        if materialize_alias_sig
            && matches!(
                &mod_sig,
                crate::types::decl::ModuleType::MtyIdent(_)
            )
        {
            if let Some(sig) = crate::types::typemod::resolve_mod_type_to_sig(
                &mod_sig,
                Some(env),
                &mut tctx.persistent_env,
                ctx,
            ) {
                mod_sig = crate::types::decl::ModuleType::MtySignature(sig);
            }
        }

        if std::env::var_os("RUST_DEBUG_LETMODULE_SIG").is_some()
            && (mod_name_str == "Mm" || mod_name_str == "N")
        {
            fn dump_mty(
                prefix: &str,
                mty: &crate::types::decl::ModuleType,
                ctx: &TypeContext<'_>,
            ) {
                use crate::types::decl::{ModuleType as DeclMty, SignatureItem};
                match mty {
                    DeclMty::MtySignature(items) => {
                        eprintln!("[letmodule-sig] {prefix} kind=signature items={}", items.len());
                        for item in items {
                            match item {
                                SignatureItem::SigType(id, decl, _) => {
                                    let manifest = decl.type_manifest.map(|ty| {
                                        let ty = ctx.repr(ty);
                                        let desc = ctx.get_desc(ty);
                                        match &*desc {
                                            TypeDesc::Tconstr { path, args, .. } => {
                                                let args = args
                                                    .iter()
                                                    .map(|arg| {
                                                        let arg = ctx.repr(*arg);
                                                        let arg_desc = ctx.get_desc(arg);
                                                        match &*arg_desc {
                                                            TypeDesc::Tconstr { path, .. } => {
                                                                format!("{}:{}", arg.0, path.name())
                                                            }
                                                            _ => format!("{}:other", arg.0),
                                                        }
                                                    })
                                                    .collect::<Vec<_>>()
                                                    .join(",");
                                                format!("{}#{}({})", path.name(), ty.0, args)
                                            }
                                            _ => format!("ty#{}", ty.0),
                                        }
                                    });
                                    eprintln!(
                                        "[letmodule-sig] {prefix} type={} stamp={} manifest={} arity={} manifest_ty={}",
                                        id.name(),
                                        id.stamp(),
                                        decl.type_manifest.is_some(),
                                        decl.type_arity,
                                        manifest.unwrap_or_else(|| "<none>".to_string())
                                    );
                                }
                                SignatureItem::SigModule(id, md, _) => {
                                    eprintln!("[letmodule-sig] {prefix} module={}", id.name());
                                    dump_mty(&format!("{prefix}.{}", id.name()), &md.md_type, ctx);
                                }
                                SignatureItem::SigValue(id, vd) => {
                                    eprintln!(
                                        "[letmodule-sig] {prefix} value={} ty={}",
                                        id.name(),
                                        ctx.repr(vd.val_type).0
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                    DeclMty::MtyIdent(path) => {
                        eprintln!("[letmodule-sig] {prefix} kind=ident path={}", path.name());
                    }
                    DeclMty::MtyAlias(_, path) => {
                        eprintln!("[letmodule-sig] {prefix} kind=alias path={}", path.name());
                    }
                    DeclMty::MtyFunctor { .. } => {
                        eprintln!("[letmodule-sig] {prefix} kind=functor");
                    }
                }
            }
            dump_mty(&mod_name_str, &mod_sig, tctx.type_ctx);
        }

        // Add the module to the environment so the body can access M.value
        let mut body_env = env.clone();
        register_module_type_type_decls_by_stamp(ctx, &mod_sig);
        let md_decl = crate::types::decl::ModuleDeclaration {
            md_type: mod_sig,
            md_attributes: vec![],
            md_loc: crate::location::Location::none(),
            md_path: None,
        };
        body_env.add_module(mod_id.clone(), md_decl);

        // Match OCaml `Ctype.init_def(Ident.current_time())` + Typetexp.widen()
        // after module typing
        // and before body typing. type_structure calls init_def per-item which
        // trashes the current_level from our begin_def. Restore it here.
        if std::env::var_os("RUST_DEBUG_LETMODULE_LEVELS").is_some() {
            eprintln!(
                "[letmodule-level] name={} before_init current={} nongen={} stamp={}",
                mod_name_str,
                ctx.current_level(),
                ctx.nongen_level(),
                ctx.current_stamp()
            );
        }
        // OCaml uses init_def(Ident.current_time()) here, and current_time is
        // monotonic/increasing. Rust stamp tracking can lag behind nested
        // begin_def scopes, so never restore below the surrounding letmodule
        // definition level.
        let restored_level = std::cmp::max(ctx.current_stamp(), letmodule_def_level);
        ctx.init_def(restored_level);
        ctx.restore_global_level(narrow_global_level);
        tctx.type_variables = saved_type_variables.clone();
        if std::env::var_os("RUST_DEBUG_LETMODULE_LEVELS").is_some() {
            eprintln!(
                "[letmodule-level] name={} after_init current={} nongen={}",
                mod_name_str,
                ctx.current_level(),
                ctx.nongen_level()
            );
        }

        // Type check the body in the extended environment. Match OCaml let-module
        // scoping by abstracting local module-rooted type paths out of the exposed
        // expression type before unifying with the surrounding expectation.
        let typed_body = type_expect(tctx, &body_env, body, expected_ty, None)?;
        let rewritten_ty = typed_body.exp_type;
        let mut replacements: HashMap<String, TypeExprRef> = HashMap::new();
        let mut seen: HashSet<TypeExprRef> = HashSet::new();
        replace_letmodule_local_paths(
            ctx,
            &body_env,
            rewritten_ty,
            &mod_id,
            &mut replacements,
            &mut seen,
        );
        replace_letmodule_local_paths(
            ctx,
            &body_env,
            expected_ty,
            &mod_id,
            &mut replacements,
            &mut seen,
        );
        for (_id, value_desc) in env.iter_values() {
            replace_letmodule_local_paths(
                ctx,
                &body_env,
                value_desc.val_type,
                &mod_id,
                &mut replacements,
                &mut seen,
            );
        }
        // NOTE: OCaml does NOT unify body.exp_type with ty_expected here.
        // type_expect already connected them internally. Unifying here would
        // merge the Pexp_tuple's result_ty with the filter_arrow's return_ty,
        // collapsing two distinct Ttuple nodes that OCaml keeps separate.
        // OCaml only does unify_var(ty, body.exp_type) after end_def (below).
        Ok((typed_mod, body_env, typed_body, rewritten_ty))
    })();
    if scoped_result.is_err() {
        ctx.restore_global_level(narrow_global_level);
        tctx.type_variables = saved_type_variables;
    }
    ctx.end_def();

    let (typed_mod, body_env, typed_body, rewritten_ty) = scoped_result?;
    tctx.set_unify_env(&body_env);
    unify_expression_types(tctx, loc, letmodule_ty, rewritten_ty, None)?;

    Ok(Expression::new(
        crate::types::typedtree::ExpressionDesc::Texp_letmodule(
            mod_id,
            Located {
                txt: mod_name_str.clone(),
                loc: name.loc,
            },
            Box::new(typed_mod),
            Box::new(typed_body),
        ),
        loc,
        letmodule_ty,
        EnvRef(0),
        attributes.to_vec().into(),
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
fn build_signature_from_structure(
    structure: &crate::types::typedtree::Structure,
) -> Vec<crate::types::decl::SignatureItem> {
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
                        },
                    ),
                    val_loc: crate::location::Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                };
                sig.push(crate::types::decl::SignatureItem::SigValue(
                    tvd.val_id.clone(),
                    vd,
                ));
            }
            StructureItemDesc::Tstr_value(_rec, bindings) => {
                for binding in bindings {
                    extract_sig_values_from_binding_pattern(
                        &binding.vb_pat,
                        // Signature values come from bound identifiers (pattern types),
                        // not the raw expression type.
                        binding.vb_pat.pat_type,
                        &mut sig,
                    );
                }
            }
            StructureItemDesc::Tstr_module(mb) => {
                let inner_mty =
                    crate::types::typemod::extract_module_type_from_mod_expr_pub(&mb.mb_expr)
                        .unwrap_or(crate::types::decl::ModuleType::MtySignature(vec![]));
                sig.push(crate::types::decl::SignatureItem::SigModule(
                    mb.mb_id.clone(),
                    crate::types::decl::ModuleDeclaration {
                        md_type: inner_mty,
                        md_attributes: vec![],
                        md_loc: crate::location::Location::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                ));
            }
            StructureItemDesc::Tstr_type(rec_flag, decls) => {
                let rec_status = match rec_flag {
                    crate::parser::ast::RecFlag::Recursive => {
                        crate::types::decl::RecStatus::TrecFirst
                    }
                    crate::parser::ast::RecFlag::Nonrecursive => {
                        crate::types::decl::RecStatus::TrecNot
                    }
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
    env: &Env,
    loc: LocIdx,
    module_expr: &crate::parser::ast::ModuleExpr,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Match OCaml typecore/typemod type_package flow:
    // - the expected type must be a package
    // - type the packed module expression
    // - wrap it in an implicit module-type constraint
    let ctx = tctx.type_ctx;
    let expected_inst = crate::types::ctype::instance(ctx, expected_ty);
    let expanded = crate::types::ctype::expand_head(ctx, env, expected_inst);
    let package_info = {
        let desc = ctx.get_desc(ctx.repr(expanded));
        match &*desc {
            TypeDesc::Tpackage { path, lids, args } => {
                Some((path.clone(), lids.clone(), args.clone()))
            }
            _ => None,
        }
    };
    let debug_pack = std::env::var_os("RUST_DEBUG_TYPE_PACK").is_some();
    if debug_pack {
        let full_loc = tctx.arena.to_location(loc);
        let expected_repr = ctx.repr(expected_ty);
        if let TypeDesc::Tconstr { path, .. } = &*ctx.get_desc(expected_repr) {
            if let Some(decl) = ctx.find_type_decl_by_path(&path.name()) {
                let params: Vec<String> = decl
                    .type_params
                    .iter()
                    .map(|p| {
                        let r = ctx.repr(*p);
                        match &*ctx.get_desc(r) {
                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                            TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
                            _ => format!("ty#{}", r.0),
                        }
                    })
                    .collect();
                eprintln!(
                    "[type-pack] expected_decl path={} params={}",
                    path.name(),
                    params.join(",")
                );
            }
        }
        let expected_head = {
            let d = ctx.get_desc(expected_repr);
            match &*d {
                TypeDesc::Tpackage { path, lids, .. } => {
                    format!("Tpackage({},{} lids)", path.name(), lids.len())
                }
                TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                TypeDesc::Tvar(_) => "Tvar".to_string(),
                TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                TypeDesc::Tobject { .. } => "Tobject".to_string(),
                TypeDesc::Tfield { .. } => "Tfield".to_string(),
                TypeDesc::Tnil => "Tnil".to_string(),
                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
            }
        };
        eprintln!(
            "[type-pack] loc={}:{} expected_ty={} expected_head={} package_info={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            expected_repr.0,
            expected_head,
            package_info.is_some()
        );
    }

    let (pack_path, pack_lids, expected_pack_args) = match package_info {
        Some(info) => info,
        None => {
            // Keep placeholder behavior when the package expectation is not
            // available yet. This preserves existing compilation coverage while
            // still emitting OCaml-like module packing for inferred packages.
            let placeholder_lid = tctx.arena.placeholder_located(loc);
            return Ok(Expression::new(
                ExpressionDesc::Texp_pack(Box::new(crate::types::typedtree::ModuleExpr {
                    mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_ident(
                        crate::types::Path::pident(Ident::create_local("placeholder")),
                        placeholder_lid,
                    ),
                    mod_loc: loc,
                    mod_type: crate::types::typedtree::ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: Attributes::new(),
                })),
                loc,
                expected_ty,
                EnvRef(0),
                attributes.to_vec().into(),
            ));
        }
    };

    let typed_module = crate::types::typemod::type_module_expr(tctx, env, tctx.arena, module_expr)
        .map_err(|e| TypeCoreError::Other(format!("pack: {e:?}")))?;
    if debug_pack {
        let full_loc = tctx.arena.to_location(loc);
        let mod_kind = match &typed_module.mod_desc {
            crate::types::typedtree::ModuleExprDesc::Tmod_ident(path, _) => {
                format!("Tmod_ident({})", path.name())
            }
            crate::types::typedtree::ModuleExprDesc::Tmod_structure(_) => "Tmod_structure".to_string(),
            crate::types::typedtree::ModuleExprDesc::Tmod_functor(..) => "Tmod_functor".to_string(),
            crate::types::typedtree::ModuleExprDesc::Tmod_apply(_, _, _) => "Tmod_apply".to_string(),
            crate::types::typedtree::ModuleExprDesc::Tmod_constraint(_, _, cst, _) => {
                format!("Tmod_constraint({:?})", cst)
            }
            crate::types::typedtree::ModuleExprDesc::Tmod_unpack(_, _) => "Tmod_unpack".to_string(),
        };
        eprintln!(
            "[type-pack] loc={}:{} mod_kind={} expected_pack_path={} lids={}",
            full_loc.loc_start.line,
            full_loc.loc_start.column(),
            mod_kind,
            pack_path.name(),
            pack_lids
                .iter()
                .map(|lid| format!("{lid:?}"))
                .collect::<Vec<_>>()
                .join(",")
        );
    }

    fn mkpath_from_pack_lid(
        base: &Path,
        lid: &Longident,
        arena: &ParseArena,
        ctx: &TypeContext<'_>,
    ) -> Option<Path> {
        match lid {
            Longident::Lident(name) => Some(Path::pdot(
                base.clone(),
                ctx.resolve_longident_component(arena, *name),
            )),
            Longident::Ldot(prefix, name) => {
                let prefix_path = mkpath_from_pack_lid(base, prefix, arena, ctx)?;
                Some(Path::pdot(
                    prefix_path,
                    ctx.resolve_longident_component(arena, *name),
                ))
            }
            Longident::Lapply(_, _) => None,
        }
    }

    fn packed_module_path_from_expr(expr: &crate::types::typedtree::ModuleExpr) -> Option<Path> {
        match &expr.mod_desc {
            crate::types::typedtree::ModuleExprDesc::Tmod_ident(path, _) => Some(path.clone()),
            crate::types::typedtree::ModuleExprDesc::Tmod_constraint(
                inner,
                _,
                crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                _,
            ) => packed_module_path_from_expr(inner),
            _ => None,
        }
    }

    // Match OCaml typemod.ml type_package: build package args from the packed
    // module path (`mkpath mp name`) when the packed module expression provides
    // an identifiable module path (Tmod_ident or implicit Tmod_constraint over it).
    // Fallback to expected args for non-identifiable module expressions.
    let pack_args = if let Some(pack_module_path) = packed_module_path_from_expr(&typed_module) {
        if debug_pack {
            eprintln!("[type-pack] module_path={}", pack_module_path.name());
        }
        let mut rebuilt_args = Vec::with_capacity(pack_lids.len());
        let mut can_rebuild = true;
        for lid in &pack_lids {
            match mkpath_from_pack_lid(&pack_module_path, lid, tctx.arena, ctx) {
                Some(path) => rebuilt_args.push(ctx.new_generic_constr(path, vec![])),
                None => {
                    can_rebuild = false;
                    break;
                }
            }
        }
        if can_rebuild && rebuilt_args.len() == pack_lids.len() {
            if debug_pack {
                let parts: Vec<String> = rebuilt_args
                    .iter()
                    .map(|ty| {
                        let r = ctx.repr(*ty);
                        let d = ctx.get_desc(r);
                        match &*d {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            _ => format!("ty#{}", r.0),
                        }
                    })
                    .collect();
                eprintln!("[type-pack] args_source=rebuild args={}", parts.join(","));
            }
            rebuilt_args
        } else {
            if debug_pack {
                eprintln!("[type-pack] args_source=expected(rebuild_failed)");
            }
            expected_pack_args.clone()
        }
    } else {
        if debug_pack {
            eprintln!("[type-pack] args_source=expected(no_module_path)");
        }
        expected_pack_args.clone()
    };
    let typed_module_loc = typed_module.mod_loc;
    let package_mty = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_ident(
            pack_path.clone(),
            tctx.arena.placeholder_located(loc),
        ),
        mty_loc: loc,
        mty_attributes: Attributes::new(),
    };
    let wrapped_module = crate::types::typedtree::ModuleExpr {
        mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_constraint(
            Box::new(typed_module),
            package_mty.clone(),
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
            crate::types::typedtree::ModuleCoercion::Tcoerce_none,
        ),
        mod_loc: typed_module_loc,
        mod_type: package_mty,
        mod_env: EnvRef(0),
        mod_attributes: Attributes::new(),
    };
    let packed_type = ctx.new_type(TypeDesc::Tpackage {
        path: pack_path,
        lids: pack_lids,
        args: pack_args,
    });
    if debug_pack {
        let packed_repr = ctx.repr(packed_type);
        if let TypeDesc::Tpackage { args, .. } = &*ctx.get_desc(packed_repr) {
            let parts: Vec<String> = args
                .iter()
                .map(|ty| {
                    let r = ctx.repr(*ty);
                    let d = ctx.get_desc(r);
                    match &*d {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                        TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                        _ => format!("ty#{}", r.0),
                    }
                })
                .collect();
            eprintln!("[type-pack] before_unify packed_args={}", parts.join(","));
        }
        let expected_repr = ctx.repr(expected_ty);
        match &*ctx.get_desc(expected_repr) {
            TypeDesc::Tpackage { args, .. } | TypeDesc::Tconstr { args, .. } => {
                let parts: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| {
                        let r = ctx.repr(*ty);
                        let d = ctx.get_desc(r);
                        let kind = match &*d {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                            _ => format!("ty#{}", r.0),
                        };
                        format!("{i}:raw{}->repr{}={kind}", ty.0, r.0)
                    })
                    .collect();
                eprintln!("[type-pack] before_unify expected_args={}", parts.join(","));
            }
            _ => {}
        }
    }
    // OCaml: rue { ... exp_type = Tpackage(...); ... }
    let pack_unified = rue_unify(tctx, loc, packed_type, expected_ty, context).is_ok();
    if debug_pack {
        eprintln!("[type-pack] unify_ok={pack_unified}");
    }
    if debug_pack {
        let packed_repr = ctx.repr(packed_type);
        if let TypeDesc::Tpackage { args, .. } = &*ctx.get_desc(packed_repr) {
            let parts: Vec<String> = args
                .iter()
                .map(|ty| {
                    let r = ctx.repr(*ty);
                    let d = ctx.get_desc(r);
                    match &*d {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                        TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                        _ => format!("ty#{}", r.0),
                    }
                })
                .collect();
            eprintln!("[type-pack] after_unify packed_args={}", parts.join(","));
        }
        let expected_repr = ctx.repr(expected_ty);
        match &*ctx.get_desc(expected_repr) {
            TypeDesc::Tpackage { args, .. } | TypeDesc::Tconstr { args, .. } => {
                let parts: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| {
                        let r = ctx.repr(*ty);
                        let d = ctx.get_desc(r);
                        let kind = match &*d {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                            _ => format!("ty#{}", r.0),
                        };
                        format!("{i}:raw{}->repr{}={kind}", ty.0, r.0)
                    })
                    .collect();
                eprintln!("[type-pack] after_unify expected_args={}", parts.join(","));
            }
            _ => {}
        }
    }
    let exp_type = if pack_unified {
        ctx.repr(expected_ty)
    } else {
        packed_type
    };
    if debug_pack {
        let exp_repr = ctx.repr(exp_type);
        let desc = ctx.get_desc(exp_repr);
        let summary = match &*desc {
            TypeDesc::Tpackage { path, args, .. } => {
                let parts: Vec<String> = args
                    .iter()
                    .map(|ty| {
                        let r = ctx.repr(*ty);
                        let d = ctx.get_desc(r);
                        match &*d {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                            _ => format!("ty#{}", r.0),
                        }
                    })
                    .collect();
                format!("Tpackage({},args={})", path.name(), parts.join(","))
            }
            TypeDesc::Tconstr { path, args, .. } => format!("Tconstr({},{} args)", path.name(), args.len()),
            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
            TypeDesc::Tlink(target) => format!("Tlink({})", ctx.repr(*target).0),
            _ => format!("ty#{}", exp_repr.0),
        };
        eprintln!("[type-pack] exp_type={summary}");
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_pack(Box::new(wrapped_module)),
        loc,
        exp_type,
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

fn module_type_from_package_binding(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    ty: TypeExprRef,
) -> crate::types::decl::ModuleType {
    let ctx = tctx.type_ctx;
    let expanded = crate::types::ctype::expand_head(ctx, env, ty);
    let package_info = {
        let desc = ctx.get_desc(ctx.repr(expanded));
        match &*desc {
            TypeDesc::Tpackage { path, lids, args } => Some((path.clone(), lids.clone(), args.clone())),
            _ => None,
        }
    };
    match package_info {
        Some((path, lids, args)) => crate::types::typemod::modtype_of_package(
            env,
            &path,
            &lids,
            &args,
            tctx.arena,
            &mut tctx.persistent_env,
            ctx,
        )
        .unwrap_or(crate::types::decl::ModuleType::MtyIdent(path)),
        _ => crate::types::decl::ModuleType::MtySignature(vec![]),
    }
}

fn typed_module_type_for_unpack(
    arena: &ParseArena,
    loc: LocIdx,
    module_type: &crate::types::decl::ModuleType,
) -> crate::types::typedtree::ModuleType {
    use crate::types::decl::ModuleType as DeclMty;
    use crate::types::typedtree::ModuleTypeDesc;

    match module_type {
        DeclMty::MtyIdent(path) => crate::types::typedtree::ModuleType {
            mty_desc: ModuleTypeDesc::Tmty_ident(path.clone(), arena.placeholder_located(loc)),
            mty_loc: loc,
            mty_attributes: Attributes::new(),
        },
        DeclMty::MtyAlias(_, path) => crate::types::typedtree::ModuleType {
            mty_desc: ModuleTypeDesc::Tmty_alias(path.clone(), arena.placeholder_located(loc)),
            mty_loc: loc,
            mty_attributes: Attributes::new(),
        },
        _ => crate::types::typedtree::ModuleType::placeholder(),
    }
}

fn wrap_module_unpacks_in_expression(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    mut body: Expression,
    unpacks: &[PatternVariable],
    wrapper_loc: LocIdx,
) -> Expression {
    fn ensure_string_idx(arena: &ParseArena, s: &str) -> StrIdx {
        if let Some(idx) = arena.find_string_idx(s) {
            return idx;
        }
        // TypeCore runs after parsing and needs to synthesize a few internal
        // attributes (`#modulepat`) exactly like OCaml typecore.
        let arena_ptr = arena as *const ParseArena as *mut ParseArena;
        unsafe { (*arena_ptr).intern_string(s) }
    }

    for unpack in unpacks {
        let lid = find_existing_lident_idx(tctx.arena, unpack.id.name())
            .unwrap_or_else(|| tctx.arena.placeholder_lid());
        let located_lid = Located {
            txt: lid,
            loc: unpack.loc_idx,
        };

        let value_desc = env
            .find_value(unpack.id.name())
            .cloned()
            .unwrap_or(ValueDescription {
                val_type: unpack.ty,
                val_kind: crate::types::ValueKind::ValReg,
                val_loc: unpack.loc.clone(),
                val_attributes: vec![],
                val_path: None,
            });

        // OCaml's wrap_unpacks types the unpack as Pexp_ident through type_expect,
        // which calls instance() on the looked-up type. Match that by instancing here.
        let unpack_inst_ty = crate::types::instance(tctx.type_ctx, unpack.ty);
        let unpack_expr = Expression::new(
            ExpressionDesc::Texp_ident(Path::pident(unpack.id.clone()), located_lid, value_desc),
            unpack.loc_idx,
            unpack_inst_ty,
            EnvRef(0),
            Attributes::new(),
        );

        let decl_mty = module_type_from_package_binding(tctx, env, unpack.ty);
        let typed_mty = typed_module_type_for_unpack(tctx.arena, unpack.loc_idx, &decl_mty);
        let unpack_module = crate::types::typedtree::ModuleExpr {
            mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_unpack(
                unpack_expr,
                typed_mty.clone(),
            ),
            mod_loc: unpack.loc_idx,
            mod_type: typed_mty,
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        };

        // OCaml `wrap_unpacks` uses the source expression location (`sexp.pexp_loc`)
        // for each generated `let module` wrapper.
        let wrapped_loc = wrapper_loc;
        let wrapped_ty = body.exp_type;
        let modulepat_attrs = vec![(
            Located {
                txt: ensure_string_idx(tctx.arena, "#modulepat"),
                loc: tctx.arena.none_loc(),
            },
            crate::parser::ast::Payload::PStr(Box::new(vec![])),
        )];
        body = Expression::new(
            crate::types::typedtree::ExpressionDesc::Texp_letmodule(
                Ident::create_local(unpack.id.name()),
                unpack.name.clone(),
                Box::new(unpack_module),
                Box::new(body),
            ),
            wrapped_loc,
            wrapped_ty,
            EnvRef(0),
            modulepat_attrs.into(),
        );
    }

    body
}

fn extract_recursive_binding_name(
    pat: &crate::parser::ast::Pattern,
    arena: &ParseArena,
) -> Option<crate::parser::ast::StringLoc> {
    match &*pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_var(name) => Some(*name),
        crate::parser::ast::PatternDesc::Ppat_constraint(inner) => {
            let (inner_pat, _) = &**inner;
            extract_recursive_binding_name(arena.get_pat(*inner_pat), arena)
        }
        crate::parser::ast::PatternDesc::Ppat_alias(inner, alias_name) => {
            let inner_pat = arena.get_pat(*inner);
            if matches!(&*inner_pat.ppat_desc, crate::parser::ast::PatternDesc::Ppat_any) {
                Some(*alias_name)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn has_internal_expansive_attribute(
    arena: &ParseArena,
    attrs: &[crate::parser::ast::Attribute],
) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "internal.expansive")
}

fn is_nonexpansive_expression(tctx: &TypeCheckContext<'_>, exp: &Expression) -> bool {
    if has_internal_expansive_attribute(tctx.arena, &exp.exp_attributes) {
        return true;
    }

    match &exp.exp_desc {
        ExpressionDesc::Texp_ident(_, _, _) => true,
        ExpressionDesc::Texp_constant(_) => true,
        ExpressionDesc::Texp_let(_, bindings, body) => {
            bindings
                .iter()
                .all(|binding| is_nonexpansive_expression(tctx, &binding.vb_expr))
                && is_nonexpansive_expression(tctx, body)
        }
        ExpressionDesc::Texp_function { .. } => true,
        ExpressionDesc::Texp_match(scrutinee, cases, exn_cases, _) => {
            exn_cases.is_empty()
                && is_nonexpansive_expression(tctx, scrutinee)
                && cases.iter().all(|case| {
                    case.c_guard
                        .as_ref()
                        .map_or(true, |guard| is_nonexpansive_expression(tctx, guard))
                        && is_nonexpansive_expression(tctx, &case.c_rhs)
                })
        }
        ExpressionDesc::Texp_tuple(items) => items
            .iter()
            .all(|item| is_nonexpansive_expression(tctx, item)),
        ExpressionDesc::Texp_construct(_, _, items) => items
            .iter()
            .all(|item| is_nonexpansive_expression(tctx, item)),
        ExpressionDesc::Texp_variant(_, maybe_arg) => maybe_arg
            .as_deref()
            .map_or(true, |arg| is_nonexpansive_expression(tctx, arg)),
        ExpressionDesc::Texp_record {
            fields,
            extended_expression,
        } => {
            fields
                .iter()
                .all(|(_, label, definition, _)| match definition {
                    crate::types::typedtree::RecordLabelDefinition::Overridden(_, expr) => {
                        label.lbl_mut == crate::types::MutableFlag::Immutable
                            && is_nonexpansive_expression(tctx, expr)
                    }
                    crate::types::typedtree::RecordLabelDefinition::Kept(_) => true,
                })
                && extended_expression
                    .as_deref()
                    .map_or(true, |expr| is_nonexpansive_expression(tctx, expr))
        }
        ExpressionDesc::Texp_field(expr, _, _) => is_nonexpansive_expression(tctx, expr),
        ExpressionDesc::Texp_array(_) => false,
        ExpressionDesc::Texp_ifthenelse(_, ifso, ifnot) => {
            is_nonexpansive_expression(tctx, ifso)
                && ifnot
                    .as_deref()
                    .map_or(true, |expr| is_nonexpansive_expression(tctx, expr))
        }
        ExpressionDesc::Texp_sequence(_, expr) => is_nonexpansive_expression(tctx, expr),
        ExpressionDesc::Texp_letmodule(_, _, module_expr, expr) => {
            is_nonexpansive_module_expr(tctx, module_expr) && is_nonexpansive_expression(tctx, expr)
        }
        ExpressionDesc::Texp_pack(module_expr) => is_nonexpansive_module_expr(tctx, module_expr),
        ExpressionDesc::Texp_assert(expr) => is_nonexpansive_expression(tctx, expr),
        ExpressionDesc::Texp_apply { funct, args, .. } => {
            if let Some((first_arg, rest_args)) = args.split_first() {
                if first_arg.expression.is_none() {
                    return is_nonexpansive_expression(tctx, funct)
                        && rest_args.iter().all(|arg| {
                            arg.expression
                                .as_ref()
                                .map_or(true, |expr| is_nonexpansive_expression(tctx, expr))
                        });
                }
            }

            if let ExpressionDesc::Texp_ident(_, _, desc) = &funct.exp_desc {
                if let crate::types::ValueKind::ValPrim(prim) = &desc.val_kind {
                    if prim.prim_name == "%raise"
                        && args.len() == 1
                        && matches!(args[0].label, crate::types::ArgLabel::Nolabel)
                    {
                        if let Some(arg_expr) = &args[0].expression {
                            return is_nonexpansive_expression(tctx, arg_expr);
                        }
                    }
                }
            }
            false
        }
        _ => false,
    }
}

fn is_nonexpansive_module_expr(
    tctx: &TypeCheckContext<'_>,
    module_expr: &crate::types::typedtree::ModuleExpr,
) -> bool {
    match &module_expr.mod_desc {
        crate::types::typedtree::ModuleExprDesc::Tmod_ident(_, _) => true,
        crate::types::typedtree::ModuleExprDesc::Tmod_functor(_, _, _, _) => true,
        crate::types::typedtree::ModuleExprDesc::Tmod_unpack(expr, _) => {
            is_nonexpansive_expression(tctx, expr)
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            is_nonexpansive_module_expr(tctx, inner)
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_structure(structure) => {
            structure.str_items.iter().all(|item| match &item.str_desc {
                crate::types::typedtree::StructureItemDesc::Tstr_eval(_, _) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_primitive(_) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_type(_, _) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_modtype(_) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_open(_) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_attribute(_) => true,
                crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => bindings
                    .iter()
                    .all(|binding| is_nonexpansive_expression(tctx, &binding.vb_expr)),
                crate::types::typedtree::StructureItemDesc::Tstr_module(binding) => {
                    is_nonexpansive_module_expr(tctx, &binding.mb_expr)
                }
                crate::types::typedtree::StructureItemDesc::Tstr_include(include_decl) => {
                    is_nonexpansive_module_expr(tctx, &include_decl.incl_mod)
                }
                crate::types::typedtree::StructureItemDesc::Tstr_recmodule(bindings) => bindings
                    .iter()
                    .all(|binding| is_nonexpansive_module_expr(tctx, &binding.mb_expr)),
                crate::types::typedtree::StructureItemDesc::Tstr_exception(ext) => matches!(
                    ext.ext_kind,
                    crate::types::typedtree::ExtensionConstructorKind::Text_rebind(_, _)
                ),
                crate::types::typedtree::StructureItemDesc::Tstr_typext(type_extension) => {
                    type_extension.tyext_constructors.iter().all(|ext| {
                        matches!(
                            ext.ext_kind,
                            crate::types::typedtree::ExtensionConstructorKind::Text_rebind(_, _)
                        )
                    })
                }
            })
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_apply(_, _, _) => false,
    }
}

/// OCaml typecore.ml `approx_type`: approximate a parsed core type for recursive let pre-unification.
fn approx_type_for_rec_let(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    sty: &crate::parser::ast::CoreType,
) -> TypeExprRef {
    use crate::parser::ast::CoreTypeDesc as CTD;

    let ctx = tctx.type_ctx;

    match &*sty.ptyp_desc {
        CTD::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = &**inner;
            let arg_ty = if arg.lbl.is_optional() {
                env.type_option(ctx, ctx.new_var(None))
            } else {
                ctx.new_var(None)
            };
            let ret_ty = approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*ret));
            let label = convert_arg_label_for_ctx(&arg.lbl, tctx.arena);
            ctx.new_arrow(label, arg_ty, ret_ty, tctx.arena.get_arity(*arity))
        }
        CTD::Ptyp_tuple(args) => {
            let tys = args
                .iter()
                .map(|arg| approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*arg)))
                .collect();
            ctx.new_tuple(tys)
        }
        CTD::Ptyp_constr(inner) => {
            let (lid, args) = &**inner;
            let longident = tctx.resolve_lid(lid.txt).clone();
            let (path, decl) = resolve_type_constructor_path(tctx, env, &longident);
            if let Some(decl) = decl {
                if args.len() == decl.type_arity as usize {
                    let tys = args
                        .iter()
                        .map(|arg| {
                            approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*arg))
                        })
                        .collect();
                    return ctx.new_constr(path, tys);
                }
            }
            ctx.new_var(None)
        }
        CTD::Ptyp_poly(inner) => {
            let (_, inner) = &**inner;
            approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*inner))
        }
        _ => ctx.new_var(None),
    }
}

/// OCaml typecore.ml `type_approx`: approximate an expression type for recursive let pre-unification.
fn type_approx_for_rec_let(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    sexp: &ParsedExpression,
) -> TypeCoreResult<TypeExprRef> {
    use crate::parser::ast::ExpressionDesc as ED;

    let ctx = tctx.type_ctx;
    let loc = sexp.pexp_loc;

    match &*sexp.pexp_desc {
        ED::Pexp_let(inner) => {
            let (_, _, body) = &**inner;
            type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*body))
        }
        ED::Pexp_fun(inner) => {
            let PexpFun {
                arg_label,
                rhs,
                arity,
                ..
            } = &**inner;
            let arg_ty = if arg_label.is_optional() {
                env.type_option(ctx, ctx.new_var(None))
            } else {
                ctx.new_var(None)
            };
            let ret_ty = type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*rhs))?;
            let label = convert_arg_label_for_ctx(arg_label, tctx.arena);
            Ok(ctx.new_arrow(label, arg_ty, ret_ty, tctx.arena.get_arity(*arity)))
        }
        ED::Pexp_match(inner) => {
            let (_, cases) = &**inner;
            match cases.first() {
                Some(case) => type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(case.pc_rhs)),
                None => Ok(ctx.new_var(None)),
            }
        }
        ED::Pexp_try(inner) => {
            let (expr, _) = &**inner;
            type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*expr))
        }
        ED::Pexp_tuple(items) => {
            let tys: TypeCoreResult<Vec<_>> = items
                .iter()
                .map(|item| type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*item)))
                .collect();
            Ok(ctx.new_tuple(tys?))
        }
        ED::Pexp_ifthenelse(inner) => {
            let (_, then_expr, _) = &**inner;
            type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*then_expr))
        }
        ED::Pexp_sequence(_, expr) => type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*expr)),
        ED::Pexp_constraint(inner) => {
            let (expr, sty) = &**inner;
            let ty = type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*expr))?;
            let ty1 = approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*sty));
            unify_expression_types(tctx, loc, ty, ty1, None)?;
            Ok(ty1)
        }
        ED::Pexp_coerce(inner) => {
            let (expr, _sty1, sty2) = &**inner;
            let ty = type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(*expr))?;
            let ty1 = ctx.new_var(None);
            let ty2 = approx_type_for_rec_let(tctx, env, tctx.arena.get_core_type(*sty2));
            unify_expression_types(tctx, loc, ty, ty1, None)?;
            Ok(ty2)
        }
        _ => Ok(ctx.new_var(None)),
    }
}

fn iter_typed_pattern<F: FnMut(&Pattern)>(pat: &Pattern, f: &mut F) {
    f(pat);
    match &pat.pat_desc {
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(arg_pat) = arg {
                iter_typed_pattern(arg_pat, f);
            }
        }
        PatternDesc::Tpat_alias(inner, _, _) => {
            iter_typed_pattern(inner, f);
        }
        PatternDesc::Tpat_or(left, right, _) => {
            iter_typed_pattern(left, f);
            iter_typed_pattern(right, f);
        }
        PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
            for item in items {
                iter_typed_pattern(item, f);
            }
        }
        PatternDesc::Tpat_construct(_, _, args) => {
            for arg in args {
                iter_typed_pattern(arg, f);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, field_pat, _) in fields {
                iter_typed_pattern(field_pat, f);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_constant(_) => {}
    }
}

/// Type check let bindings.
fn type_let_bindings(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeCoreResult<(Vec<ValueBinding>, Env, Vec<PatternVariable>)> {
    let previous_recursive_let_depth = tctx.recursive_let_depth;
    let previous_recursive_value_count = tctx.active_recursive_value_ids.len();
    if rec_flag == RecFlag::Recursive {
        tctx.recursive_let_depth += 1;
    }
    let result = (|| -> TypeCoreResult<(Vec<ValueBinding>, Env, Vec<PatternVariable>)> {
        let ctx = tctx.type_ctx;

        // Begin a new definition level
        ctx.begin_def();

        // Create type variables for all bindings
        let binding_types: Vec<TypeExprRef> = bindings.iter().map(|_| ctx.new_var(None)).collect();

        // For recursive bindings, extend environment first
        let mut recursive_binding_ids = Vec::new();
        let mut typing_env = if rec_flag == RecFlag::Recursive {
            let mut new_env = env.clone();
            for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
                if let Some(name) =
                    extract_recursive_binding_name(tctx.arena.get_pat(binding.pvb_pat), tctx.arena)
                {
                    let id = Ident::create_local(tctx.arena.get_string(name.txt));
                    recursive_binding_ids.push(id.clone());
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
            tctx.active_recursive_value_ids.extend(recursive_binding_ids);
            new_env
        } else {
            env.clone()
        };

        // Type check each pattern first, collecting pattern variables per binding.
        // Matches OCaml `type_let`: recursive pre-unification runs on typed patterns
        // before typing right-hand-side expressions.
        let mut typed_patterns = Vec::new();
        let mut state = PatternState::new();
        let mut all_pattern_vars: Vec<Vec<PatternVariable>> = Vec::new();

        for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
            state.reset(true);

            // Type check pattern
            let typed_pat = type_pattern(
                tctx,
                &typing_env,
                tctx.arena.get_pat(binding.pvb_pat),
                *ty,
                PatternMode::Normal,
                &mut state,
            )?;

            typed_patterns.push(typed_pat);

            // Save pattern variables from this binding
            all_pattern_vars.push(state.pattern_variables.clone());
        }

        // Match OCaml: update recursive env with pattern variable types.
        // OCaml's type_pattern_list returns new_env with pattern variables
        // (from enter_variable/build_as_type), used as exp_env for body typing.
        // Without this, binding_type Tvars (linked to outer constraint_ty)
        // are used instead of inner pattern types from enter_variable.
        if rec_flag == RecFlag::Recursive {
            for pvars in &all_pattern_vars {
                for pv in pvars {
                    let desc = ValueDescription {
                        val_type: pv.ty,
                        val_kind: crate::types::ValueKind::ValReg,
                        val_loc: pv.loc.clone(),
                        val_attributes: vec![],
                        val_path: None,
                    };
                    typing_env.add_value(pv.id.clone(), desc);
                }
            }
        }

        if rec_flag == RecFlag::Recursive {
            for (typed_pat, binding) in typed_patterns.iter().zip(bindings.iter()) {
                let approx_ty =
                    type_approx_for_rec_let(tctx, env, tctx.arena.get_expr(binding.pvb_expr))?;
                let pat_ty_for_unify = {
                    let pat_ty = typed_pat.pat_type;
                    let pat_repr = ctx.repr(pat_ty);
                    let desc = ctx.get_desc(pat_repr);
                    match &*desc {
                        TypeDesc::Tpoly { body, vars } => {
                            let body = *body;
                            let vars = vars.clone();
                            drop(desc);
                            let (_, instantiated) = crate::types::ctype::instance_poly(
                                ctx, true, false, &vars, body,
                            );
                            instantiated
                        }
                        _ => pat_ty,
                    }
                };
                unify_pattern_types(tctx, typed_pat.pat_loc, pat_ty_for_unify, approx_ty)?;
            }
        }

        // Type check expressions after recursive approximation unification.
        // OCaml typecore.ml type_let lines 4189-4211
        let mut typed_bindings = Vec::new();
        for ((binding, typed_pat), ty) in bindings
            .iter()
            .zip(typed_patterns.into_iter())
            .zip(binding_types.iter())
        {
            // OCaml typecore.ml lines 4196-4209: Tpoly pattern types get special handling
            let pat_ty = typed_pat.pat_type;
            let pat_repr = ctx.repr(pat_ty);
            let pat_desc = ctx.get_desc(pat_repr);
            let typed_expr = match &*pat_desc {
                TypeDesc::Tpoly { body, vars } if !vars.is_empty() => {
                    let body = *body;
                    let vars = vars.clone();
                    drop(pat_desc);
                    // OCaml: begin_def(); let vars, ty' = instance_poly ~keep_names:true true tl ty
                    ctx.begin_def();
                    let (inst_vars, inst_ty) =
                        crate::types::ctype::instance_poly(ctx, true, true, &vars, body);
                    let exp = type_expect(
                        tctx,
                        &typing_env,
                        tctx.arena.get_expr(binding.pvb_expr),
                        inst_ty,
                        None,
                    )?;
                    ctx.end_def();
                    // OCaml: check_univars env true "definition" exp pat.pat_type vars
                    crate::types::ctype::check_univars(ctx, &inst_vars);
                    // OCaml: {exp with exp_type = instance env exp.exp_type}
                    let new_exp_type = crate::types::ctype::instance(ctx, exp.exp_type);
                    Expression { exp_type: new_exp_type, ..exp }
                }
                _ => {
                    drop(pat_desc);
                    // OCaml: type_expect ~context exp_env sexp pat.pat_type
                    type_expect(
                        tctx,
                        &typing_env,
                        tctx.arena.get_expr(binding.pvb_expr),
                        pat_ty,
                        None,
                    )?
                }
            };
            if std::env::var_os("RUST_DEBUG_VAR_LEVELS").is_some() {
                if let crate::types::typedtree::PatternDesc::Tpat_var(id, _) = &typed_pat.pat_desc {
                    if matches!(
                        id.name(),
                        "f" | "v" | "u" | "v0" | "v1" | "v3" | "res" | "initY" | "merge2"
                    ) {
                        let pat_ty = tctx.type_ctx.repr(typed_pat.pat_type);
                        let pat_level = tctx.type_ctx.get_level(pat_ty);
                        let exp_ty = tctx.type_ctx.repr(typed_expr.exp_type);
                        let exp_level = tctx.type_ctx.get_level(exp_ty);
                        eprintln!(
                            "[var-level-pre-gen] binding={} pat_ty={} pat_level={} exp_ty={} exp_level={}",
                            id.name(),
                            pat_ty.0,
                            pat_level,
                            exp_ty.0,
                            exp_level
                        );
                        let pat_desc = tctx.type_ctx.get_desc(pat_ty);
                        if let TypeDesc::Ttuple(items) = &*pat_desc {
                            let parts: Vec<String> = items
                                .iter()
                                .map(|item| {
                                    let r = tctx.type_ctx.repr(*item);
                                    format!("{}@{}", r.0, tctx.type_ctx.get_level(r))
                                })
                                .collect();
                            eprintln!(
                                "[var-level-pre-gen] binding={} tuple_items={}",
                                id.name(),
                                parts.join(",")
                            );
                        }
                        if id.name() == "merge2" {
                            if let TypeDesc::Tarrow { arg, ret, .. } = &*pat_desc {
                                let dump_constr = |label: &str, ty: TypeExprRef| {
                                    let ty = tctx.type_ctx.repr(ty);
                                    let ty_desc = tctx.type_ctx.get_desc(ty);
                                    if let TypeDesc::Tconstr { path, args, .. } = &*ty_desc {
                                        let parts: Vec<String> = args
                                            .iter()
                                            .map(|arg| {
                                                let arg = tctx.type_ctx.repr(*arg);
                                                format!("{}@{}", arg.0, tctx.type_ctx.get_level(arg))
                                            })
                                            .collect();
                                        eprintln!(
                                            "[var-level-pre-gen] binding=merge2 {}={}#{}@{}({})",
                                            label,
                                            path.name(),
                                            ty.0,
                                            tctx.type_ctx.get_level(ty),
                                            parts.join(",")
                                        );
                                    } else {
                                        eprintln!(
                                            "[var-level-pre-gen] binding=merge2 {}=non-constr#{}@{}",
                                            label,
                                            ty.0,
                                            tctx.type_ctx.get_level(ty)
                                        );
                                    }
                                };
                                let arg_r = tctx.type_ctx.repr(arg.typ);
                                let ret_r = tctx.type_ctx.repr(*ret);
                                dump_constr("arg", arg_r);
                                dump_constr("ret", ret_r);
                                let ret_desc = tctx.type_ctx.get_desc(ret_r);
                                if let TypeDesc::Tarrow { arg, ret, .. } = &*ret_desc {
                                    dump_constr("ret_arg", tctx.type_ctx.repr(arg.typ));
                                    dump_constr("ret_ret", tctx.type_ctx.repr(*ret));
                                }
                            }
                        }
                    }
                }
            }
            typed_bindings.push(ValueBinding::new(
                typed_pat,
                typed_expr,
                binding.pvb_loc.clone(),
                binding.pvb_attributes.clone(),
            ));
        }

        // End definition level
        ctx.end_def();

        // Match OCaml typecore.ml `type_let`: generalize over every typed
        // subpattern (not just root binding types) using iter_pattern.
        for binding in typed_bindings.iter() {
            let is_nonexp = is_nonexpansive_expression(tctx, &binding.vb_expr);
            if !is_nonexp {
                iter_typed_pattern(&binding.vb_pat, &mut |pat| {
                    crate::types::ctype::generalize_expansive(ctx, env, pat.pat_type);
                });
            }
        }

        for binding in &typed_bindings {
            iter_typed_pattern(&binding.vb_pat, &mut |pat| {
                crate::types::generalize(ctx, pat.pat_type);
            });
        }

        // Finalize variant patterns in let bindings (matches OCaml typecore.ml:4117-4121)
        // First, pressure_variants to close variant rows (OCaml: Parmatch.pressure_variants env [pat])
        for binding in typed_bindings.iter_mut() {
            pressure_variant_rows_in_let_pattern(tctx, env, &mut binding.vb_pat);
        }
        // Then, finalize Reither→Rpresent in still-open rows (OCaml: iter_pattern finalize_variant pat)
        for binding in typed_bindings.iter_mut() {
            finalize_variant_in_pattern(tctx, env, &mut binding.vb_pat, false);
        }

        // Build final environment from all collected pattern variables.
        // Module unpack bindings are first bound as values (package type), then
        // lowered into nested Texp_letmodule wrappers around the let body.
        let mut new_env = env.clone();
        let mut unpacks: Vec<PatternVariable> = Vec::new();
        for pvars in all_pattern_vars.iter() {
            for pv in pvars {
                if std::env::var_os("RUST_DEBUG_VAR_LEVELS").is_some()
                    && matches!(
                        pv.id.name(),
                        "f" | "v" | "u" | "v0" | "v1" | "v3" | "res" | "initY" | "merge2"
                    )
                {
                    let ty = tctx.type_ctx.repr(pv.ty);
                    let level = tctx.type_ctx.get_level(ty);
                    let desc = tctx.type_ctx.get_desc(ty);
                    eprintln!(
                        "[var-level] binding={} ty_id={} repr={} level={} desc={:?}",
                        pv.id.name(),
                        pv.ty.0,
                        ty.0,
                        level,
                        &*desc
                    );
                    if let TypeDesc::Ttuple(items) = &*desc {
                        let parts: Vec<String> = items
                            .iter()
                            .map(|item| {
                                let r = tctx.type_ctx.repr(*item);
                                format!("{}@{}", r.0, tctx.type_ctx.get_level(r))
                            })
                            .collect();
                        eprintln!(
                            "[var-level] binding={} tuple_items={}",
                            pv.id.name(),
                            parts.join(",")
                        );
                    }
                    if let TypeDesc::Tarrow { arg, ret, .. } = &*desc {
                        let arg_r = tctx.type_ctx.repr(arg.typ);
                        let ret_r = tctx.type_ctx.repr(*ret);
                        eprintln!(
                            "[var-level] binding={} arrow_arg={}@{} arrow_ret={}@{}",
                            pv.id.name(),
                            arg_r.0,
                            tctx.type_ctx.get_level(arg_r),
                            ret_r.0,
                            tctx.type_ctx.get_level(ret_r)
                        );
                        if pv.id.name() == "merge2" {
                            let dump_constr = |label: &str, ty: TypeExprRef| {
                                let ty = tctx.type_ctx.repr(ty);
                                let ty_desc = tctx.type_ctx.get_desc(ty);
                                if let TypeDesc::Tconstr { path, args, .. } = &*ty_desc {
                                    let parts: Vec<String> = args
                                        .iter()
                                        .map(|arg| {
                                            let arg = tctx.type_ctx.repr(*arg);
                                            format!("{}@{}", arg.0, tctx.type_ctx.get_level(arg))
                                        })
                                        .collect();
                                    eprintln!(
                                        "[var-level] binding=merge2 {}={}#{}@{}({})",
                                        label,
                                        path.name(),
                                        ty.0,
                                        tctx.type_ctx.get_level(ty),
                                        parts.join(",")
                                    );
                                } else {
                                    eprintln!(
                                        "[var-level] binding=merge2 {}=non-constr#{}@{}",
                                        label,
                                        ty.0,
                                        tctx.type_ctx.get_level(ty)
                                    );
                                }
                            };
                            dump_constr("arg", arg_r);
                            dump_constr("ret", ret_r);
                            let ret_desc = tctx.type_ctx.get_desc(ret_r);
                            if let TypeDesc::Tarrow { arg, ret, .. } = &*ret_desc {
                                dump_constr("ret_arg", tctx.type_ctx.repr(arg.typ));
                                dump_constr("ret_ret", tctx.type_ctx.repr(*ret));
                            }
                        }
                        let ret_desc = tctx.type_ctx.get_desc(ret_r);
                        if let TypeDesc::Ttuple(items) = &*ret_desc {
                            let parts: Vec<String> = items
                                .iter()
                                .map(|item| {
                                    let r = tctx.type_ctx.repr(*item);
                                    format!("{}@{}", r.0, tctx.type_ctx.get_level(r))
                                })
                                .collect();
                            eprintln!(
                                "[var-level] binding={} arrow_ret_tuple_items={}",
                                pv.id.name(),
                                parts.join(",")
                            );
                        }
                    }
                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                        let parts: Vec<String> = args
                            .iter()
                            .map(|arg| {
                                let arg = tctx.type_ctx.repr(*arg);
                                let arg_level = tctx.type_ctx.get_level(arg);
                                let arg_desc = tctx.type_ctx.get_desc(arg);
                                format!("{}@{}:{:?}", arg.0, arg_level, &*arg_desc)
                            })
                            .collect();
                        eprintln!(
                            "[var-level] binding={} constr_path={} args={}",
                            pv.id.name(),
                            path.name(),
                            parts.join(" | ")
                        );
                    }
                }
                let desc = ValueDescription {
                    val_type: pv.ty,
                    val_kind: crate::types::ValueKind::ValReg,
                    val_loc: pv.loc.clone(),
                    val_attributes: vec![],
                    val_path: None,
                };
                new_env.add_value(pv.id.clone(), desc);
                if pv.is_module {
                    let module_type = module_type_from_package_binding(tctx, &new_env, pv.ty);
                    new_env.add_module(
                        pv.id.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: module_type,
                            md_attributes: vec![],
                            md_loc: crate::location::Location::none(),
                            md_path: None,
                        },
                    );
                    // OCaml records unpack vars in reverse insertion order
                    // (`module_variables := x :: module_variables`).
                    unpacks.insert(0, pv.clone());
                }
            }
        }

        Ok((typed_bindings, new_env, unpacks))
    })();

    tctx.recursive_let_depth = previous_recursive_let_depth;
    tctx.active_recursive_value_ids
        .truncate(previous_recursive_value_count);
    result
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
    // Match OCaml Typecore.type_expression -> Typetexp.reset_type_variables.
    tctx.reset_type_variables();

    // Begin a definition scope
    type_ctx.begin_def();

    // Type with a fresh variable
    let expected_ty = type_ctx.new_var(None);
    let typed_expr = type_expect(tctx, env, expr, expected_ty, None)?;

    // Try to unify with unit (matching OCaml's Bs_toplevel_expression_unit warning behavior)
    // This resolves unresolved type variables to unit for statement-level expressions
    let unit_ty = env.type_unit(type_ctx);
    let _ = crate::types::unify(
        type_ctx,
        &mut tctx.unify_state,
        typed_expr.exp_type,
        unit_ty,
    );

    // End definition scope
    type_ctx.end_def();

    if !is_nonexpansive_expression(tctx, &typed_expr) {
        crate::types::ctype::generalize_expansive(type_ctx, env, typed_expr.exp_type);
    }

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
    // Match OCaml Typecore.type_binding -> Typetexp.reset_type_variables.
    tctx.reset_type_variables();
    let (typed_bindings, new_env, _unpacks) = type_let_bindings(tctx, env, rec_flag, bindings)?;
    Ok((typed_bindings, new_env))
}

fn copy_lookup_type_expr(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    use crate::types::type_expr::{RowDesc, RowField};

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

    ctx.set_desc(placeholder, TypeDesc::Tlink(copied));
    cache.insert(ty, copied);
    copied
}

fn copy_lookup_constructor_args(
    args: &crate::types::decl::ConstructorArguments,
    ctx: &TypeContext<'_>,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
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
    let mut cache = HashMap::new();
    copy_lookup_signature(sig_items, ctx, &mut cache)
}

// ============================================================================
// Environment Extensions for Built-in Types
// ============================================================================

impl Env {
    /// Get a fresh int type instance.
    /// Uses cached generic singleton + instance(), matching OCaml's
    /// `instance_def Predef.type_int` pattern.
    pub fn type_int(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_int())
    }

    /// Get a fresh char type instance.
    pub fn type_char(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_char())
    }

    /// Get a fresh string type instance.
    pub fn type_string(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_string())
    }

    /// Get a fresh float type instance.
    pub fn type_float(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_float())
    }

    /// Get a fresh bigint type instance.
    pub fn type_bigint(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_bigint())
    }

    /// Get a fresh unit type instance.
    pub fn type_unit(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_unit())
    }

    /// Get a fresh bool type instance.
    pub fn type_bool(&self, ctx: &TypeContext<'_>) -> TypeExprRef {
        crate::types::ctype::instance(ctx, ctx.predef_bool())
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
                let prefix_str = Self::longident_to_string(prefix, arena);
                let debug_lookup_filter = std::env::var("RUST_DEBUG_LOOKUP_VALUE").ok();
                let debug_lookup = debug_lookup_filter.as_ref().is_some_and(|target| {
                    target == "*" || lid_str == *target || prefix_str == *target
                });
                let prefix_cache_fragment = match &**prefix {
                    Longident::Lident(mod_idx) => {
                        let mod_name = arena.get_string(*mod_idx);
                        match self.find_module_with_id(mod_name) {
                            Ok((mod_id, _)) => format!("{}#{}", mod_id.name(), mod_id.stamp()),
                            Err(_) => mod_name.to_string(),
                        }
                    }
                    _ => prefix_str.clone(),
                };
                let module_cache_key = format!("module::{}", prefix_cache_fragment);

                let cached_module = ctx.find_resolved_module_sig(&module_cache_key);
                let cache_hit = cached_module.is_some();
                let resolved_module = cached_module.or_else(|| {
                    let resolved = self.resolve_module_lid(prefix, arena, pers_env, ctx);
                    if let Some((mod_path, sig)) = &resolved {
                        ctx.register_resolved_module_sig(
                            &module_cache_key,
                            mod_path.clone(),
                            sig.clone(),
                        );
                    }
                    resolved
                });
                if std::env::var_os("RUST_DEBUG_MODULE_CACHE").is_some() && prefix_str == "N" {
                    eprintln!(
                        "[module-cache] prefix={} key={} hit={} resolved={}",
                        prefix_str,
                        module_cache_key,
                        cache_hit,
                        resolved_module.is_some()
                    );
                }
                if debug_lookup {
                    eprintln!(
                        "[lookup-value] lid={} prefix={} value={} cache_key={} cache_hit={} resolved={}",
                        lid_str,
                        prefix_str,
                        value_name,
                        module_cache_key,
                        cache_hit,
                        resolved_module.is_some()
                    );
                }

                if let Some((mod_path, sig)) = resolved_module {
                    if debug_lookup {
                        let values = sig
                            .iter()
                            .filter_map(|item| {
                                if let crate::types::decl::SignatureItem::SigValue(id, _) = item {
                                    Some(id.name().to_string())
                                } else {
                                    None
                                }
                            })
                            .take(30)
                            .collect::<Vec<_>>()
                            .join(",");
                        eprintln!(
                            "[lookup-value] resolved-module path={} values(sample)=[{}]",
                            mod_path.name(),
                            values
                        );
                    }
                    // Search for the value in the signature
                    // Signature lookup must respect shadowing order:
                    // later items in a structure/signature shadow earlier ones.
                    for sig_item in sig.iter().rev() {
                        if let crate::types::decl::SignatureItem::SigValue(id, vd) = sig_item {
                            if id.name() == value_name {
                                if debug_lookup {
                                    let vd_ty = ctx.repr(vd.val_type);
                                    let vd_desc = ctx.get_desc(vd_ty);
                                    let vd_summary = match &*vd_desc {
                                        TypeDesc::Tarrow { ret, .. } => {
                                            let ret = ctx.repr(*ret);
                                            let ret_desc = ctx.get_desc(ret);
                                            let ret_head = match &*ret_desc {
                                                TypeDesc::Tconstr { path, args, .. } => {
                                                    if path.name() == "result" && !args.is_empty() {
                                                        let ok = ctx.repr(args[0]);
                                                        let ok_desc = ctx.get_desc(ok);
                                                        let ok_head = match &*ok_desc {
                                                            TypeDesc::Tconstr { path, .. } => path.name(),
                                                            _ => format!("ty#{}", ok.0),
                                                        };
                                                        format!("result(ok={})", ok_head)
                                                    } else {
                                                        path.name()
                                                    }
                                                }
                                                _ => format!("ty#{}", ret.0),
                                            };
                                            format!("Tarrow(ret_head={})", ret_head)
                                        }
                                        TypeDesc::Tconstr { path, .. } => {
                                            format!("Tconstr({})", path.name())
                                        }
                                        _ => format!("{:?}", *vd_desc),
                                    };
                                    eprintln!(
                                        "[lookup-value] found value={} in path={} ty={} {}",
                                        value_name,
                                        mod_path.name(),
                                        vd_ty.0,
                                        vd_summary
                                    );
                                }
                                if std::env::var_os("RUST_DEBUG_INTL_GROUPING").is_some()
                                    && value_name == "fromBool"
                                {
                                    let ty = ctx.repr(vd.val_type);
                                    let desc = ctx.get_desc(ty);
                                    let summary = match &*desc {
                                        TypeDesc::Tarrow { arg, ret, .. } => {
                                            let arg = ctx.repr(arg.typ);
                                            let ret = ctx.repr(*ret);
                                            let ret_desc = ctx.get_desc(ret);
                                            let ret_head = match &*ret_desc {
                                                TypeDesc::Tconstr { path, .. } => path.name(),
                                                _ => format!("ty#{}", ret.0),
                                            };
                                            format!(
                                                "Tarrow(arg={} ret={} ret_head={})",
                                                arg.0, ret.0, ret_head
                                            )
                                        }
                                        TypeDesc::Tconstr { path, .. } => {
                                            format!("Tconstr({})", path.name())
                                        }
                                        _ => format!("{:?}", *desc),
                                    };
                                    eprintln!(
                                        "[intl-grouping] prefix={} mod_path={} value={} ty={} {}",
                                        prefix_str,
                                        mod_path.name(),
                                        value_name,
                                        ty.0,
                                        summary
                                    );
                                }
                                if std::env::var_os("RUST_DEBUG_LOOKUP_MMCMP").is_some()
                                    && prefix_str == "Mm"
                                    && value_name == "cmp"
                                {
                                    let ty = ctx.repr(vd.val_type);
                                    let desc = ctx.get_desc(ty);
                                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                                        let args = args
                                            .iter()
                                            .map(|arg| {
                                                let arg = ctx.repr(*arg);
                                                let arg_desc = ctx.get_desc(arg);
                                                match &*arg_desc {
                                                    TypeDesc::Tconstr { path, .. } => {
                                                        format!("{}:{}#{}", arg.0, path.name(), path.head().stamp())
                                                    }
                                                    _ => format!("{}:other", arg.0),
                                                }
                                            })
                                            .collect::<Vec<_>>()
                                            .join(",");
                                        eprintln!(
                                            "[lookup-mm-cmp] path={} head_stamp={} args=[{}]",
                                            path.name(),
                                            path.head().stamp(),
                                            args
                                        );
                                    }
                                }
                                let path = Path::pdot(mod_path.clone(), value_name.to_string());
                                return Ok((path, vd.clone()));
                            }
                        }
                    }
                    if debug_lookup {
                        eprintln!(
                            "[lookup-value] missing value={} in resolved path={}",
                            value_name,
                            mod_path.name()
                        );
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
                        if debug_lookup {
                            eprintln!(
                                "[lookup-value] fallback hit value={} ident={}#{}",
                                value_name,
                                id.name(),
                                id.stamp()
                            );
                        }
                        let path = desc
                            .val_path
                            .clone()
                            .unwrap_or_else(|| Path::pident(id.clone()));
                        Ok((path, desc.clone()))
                    }
                    Err(_) => {
                        if debug_lookup {
                            eprintln!("[lookup-value] fallback miss value={}", value_name);
                        }
                        Err(TypeCoreError::UndefinedMethod {
                            ty: TypeExprRef(0),
                            method: lid_str,
                            alternatives: None,
                        })
                    }
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

    /// Lift alias paths that are local to a parent signature into qualified
    /// paths rooted at the parent module path.
    ///
    /// OCaml can encode nested module aliases like `module Separate = Main`
    /// with local identifiers in the alias path. Those local ids are not
    /// directly resolvable in the global env, so we qualify them through the
    /// parent access path before alias resolution.
    fn qualify_local_alias_path_in_signature(
        alias_path: &Path,
        parent_path: &Path,
        parent_sig: &crate::types::decl::Signature,
    ) -> Option<Path> {
        fn signature_contains_module(
            sig: &crate::types::decl::Signature,
            id: &Ident,
        ) -> bool {
            sig.iter().rev().any(|item| {
                if let crate::types::decl::SignatureItem::SigModule(mid, _, _) = item {
                    // Prefer physical id when available; also accept local ids
                    // with matching names because cmi-loaded local aliases can
                    // lose direct stamp connectivity in the active env.
                    mid.same(id) || (id.stamp() != 0 && mid.name() == id.name())
                } else {
                    false
                }
            })
        }

        match alias_path {
            Path::Pident(id) => {
                if signature_contains_module(parent_sig, id) {
                    Some(Path::pdot(parent_path.clone(), id.name()))
                } else {
                    None
                }
            }
            Path::Pdot(parent, name, pos) => {
                let qualified_parent =
                    Self::qualify_local_alias_path_in_signature(parent, parent_path, parent_sig)?;
                Some(Path::Pdot(
                    Box::new(qualified_parent),
                    name.clone(),
                    *pos,
                ))
            }
            Path::Papply(_, _) => None,
        }
    }

    /// Resolve a module longident to its signature and path.
    /// Applies path rewriting/substitution for downstream value/module lookups.
    pub(crate) fn resolve_module_lid<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        self.resolve_module_lid_impl(lid, arena, pers_env, ctx, true)
    }

    /// Resolve a module longident without mutating type paths inside the returned signature.
    /// This matches OCaml's non-destructive behavior needed for pure type-path lookup.
    fn resolve_module_lid_raw<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        self.resolve_module_lid_impl(lid, arena, pers_env, ctx, false)
    }

    /// Resolve a module longident to path+signature, optionally applying
    /// rewrite/substitution to contained type paths.
    fn resolve_module_lid_impl<'b>(
        &self,
        lid: &Longident,
        arena: &crate::parse_arena::ParseArena,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
        apply_subst: bool,
    ) -> Option<(Path, crate::types::decl::Signature)> {
        match lid {
            Longident::Lident(mod_idx) => {
                let mod_name = arena.get_string(*mod_idx);
                // First try local environment
                if let Ok((mod_id, md)) = self.find_module_with_id(mod_name) {
                    let result = self.resolve_module_type(&md.md_type, pers_env, ctx);
                    if let Some((sig, resolved_name)) = result {
                        // Use md_path if available (e.g., Pdot(Pident("Stdlib"), "Console")
                        // for Console from opened Stdlib), otherwise fall back to Pident.
                        let path = if let Some(ref qualified_path) = md.md_path {
                            qualified_path.clone()
                        } else {
                            Path::pident(mod_id.clone())
                        };
                        // If an alias was followed (resolved_name is Some),
                        // rewrite type paths from the resolved module name
                        // to the access path. This handles both:
                        // - opened modules: Console from Stdlib → Pdot(Pident("Stdlib"), "Console")
                        // - local aliases: module N = Belt.List → Pident("N")
                        //
                        // Skip deep copy when the signature has no type/module
                        // definitions that need path substitution. This preserves
                        // type node sharing for local module opens (e.g., %%private)
                        // so that value-restriction Tvars remain shared between
                        // pattern types and env types.
                        let has_type_or_module_defs = sig.iter().any(|item| {
                            matches!(
                                item,
                                crate::types::decl::SignatureItem::SigType(..)
                                    | crate::types::decl::SignatureItem::SigModule(..)
                                    | crate::types::decl::SignatureItem::SigModtype(..)
                            )
                        });
                        // Extract module alias target for path prefix rewriting.
                        // E.g., module J = Js.Json: target = Pdot(Pident("Js"), "Json")
                        // Extract module alias target for path prefix rewriting.
                        // Only for Pdot targets (nested modules like Js.Json).
                        // Pident targets (like Stdlib_Date) are handled by existing substitution.
                        let alias_target = if apply_subst {
                            match &md.md_type {
                                crate::types::decl::ModuleType::MtyAlias(_, target) => {
                                    if matches!(target, Path::Pdot(..)) && !target.same(&path) {
                                        Some(target.clone())
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            }
                        } else {
                            None
                        };
                        let needs_copy = apply_subst
                            && (has_type_or_module_defs || resolved_name.is_some() || alias_target.is_some());
                        let mut sig = if needs_copy {
                            copy_lookup_signature_for_subst(&sig, ctx)
                        } else {
                            sig
                        };
                        if apply_subst
                            && matches!(
                                &md.md_type,
                                crate::types::decl::ModuleType::MtyAlias(..)
                            )
                        {
                            sig = strengthen_signature_for_module_access_path(ctx, &path, &sig);
                        }
                        if apply_subst {
                            if let Some(ref old_name) = resolved_name {
                                crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                                    &sig, old_name, &path, ctx,
                                );
                            }
                            if has_type_or_module_defs {
                                crate::cmi::persistent_env::substitute_type_paths_in_sig(
                                    &sig, &path, ctx,
                                );
                            }
                            // Rewrite paths for module aliases: replace the canonical
                            // module path prefix with the alias path in all types.
                            // E.g., module J = Js.Json: rewrite Js.Json.Kind.t → J.Kind.t
                            if let Some(ref target) = alias_target {
                                crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                                    &sig, target, &path, ctx,
                                );
                            }
                        }
                        if std::env::var_os("RUST_DEBUG_SIG_N_T").is_some() && path.name() == "N" {
                            for item in &sig {
                                if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item
                                {
                                    if id.name() == "t" {
                                        eprintln!(
                                            "[sig-n-t] path={} manifest={} params={}",
                                            path.name(),
                                            decl.type_manifest.is_some(),
                                            decl.type_params.len()
                                        );
                                    }
                                }
                            }
                        }
                        if std::env::var_os("RUST_DEBUG_NUMBERFORMAT_SIG").is_some()
                            && path.name().ends_with("NumberFormat")
                        {
                            for item in &sig {
                                if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item
                                {
                                    if id.name() == "options" {
                                        if let crate::types::TypeKind::TypeRecord(labels, _) =
                                            &decl.type_kind
                                        {
                                            for lbl in labels {
                                                if matches!(
                                                    lbl.ld_id.name(),
                                                    "useGrouping" | "compactDisplay" | "currency"
                                                ) {
                                                    let ty = ctx.repr(lbl.ld_type);
                                                    let desc = ctx.get_desc(ty);
                                                    let head = match &*desc {
                                                        TypeDesc::Tconstr { path, args, .. } => {
                                                            if path.name() == "option"
                                                                && args.len() == 1
                                                            {
                                                                let arg = ctx.repr(args[0]);
                                                                let arg_desc = ctx.get_desc(arg);
                                                                match &*arg_desc {
                                                                    TypeDesc::Tconstr { path, .. } => {
                                                                        format!("option<{}>", path.name())
                                                                    }
                                                                    _ => format!("option<ty#{}>", arg.0),
                                                                }
                                                            } else {
                                                                path.name()
                                                            }
                                                        }
                                                        _ => format!("ty#{}", ty.0),
                                                    };
                                                    eprintln!(
                                                        "[numberformat-sig] path={} options.useGrouping ty={} head={}",
                                                        path.name(),
                                                        ty.0,
                                                        head
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        return Some((path, sig));
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
                if let Some((parent_path, parent_sig)) =
                    self.resolve_module_lid_impl(prefix, arena, pers_env, ctx, apply_subst)
                {
                    // Search for the sub-module in the parent's signature
                    for sig_item in parent_sig.iter().rev() {
                        if let crate::types::decl::SignatureItem::SigModule(id, sub_md, _) =
                            sig_item
                        {
                            if id.name() == submod_name {
                                let sub_path =
                                    Path::pdot(parent_path.clone(), submod_name.to_string());
                                let result = self
                                    .resolve_module_type(&sub_md.md_type, pers_env, ctx)
                                    .or_else(|| {
                                        if let crate::types::decl::ModuleType::MtyAlias(
                                            alias_presence,
                                            alias_path,
                                        ) = &sub_md.md_type
                                        {
                                            Self::qualify_local_alias_path_in_signature(
                                                alias_path,
                                                &parent_path,
                                                &parent_sig,
                                            )
                                            .and_then(|qualified_alias_path| {
                                                self.resolve_module_type(
                                                    &crate::types::decl::ModuleType::MtyAlias(
                                                        *alias_presence,
                                                        qualified_alias_path,
                                                    ),
                                                    pers_env,
                                                    ctx,
                                                )
                                            })
                                        } else {
                                            None
                                        }
                                    });
                                if let Some((sig, resolved_name)) = result {
                                    if std::env::var_os("RUST_DEBUG_JS_STRING2_SIG").is_some()
                                        && sub_path.name() == "Js.String2"
                                    {
                                        for item in &sig {
                                            if let crate::types::decl::SignatureItem::SigValue(id, vd) = item {
                                                if id.name() == "substrAtMost" {
                                                    let ty = ctx.repr(vd.val_type);
                                                    let mut summary = vec![format!("ty={}@{}", ty.0, ctx.get_level(ty))];
                                                    let mut cursor = ty;
                                                    for _ in 0..8 {
                                                        let desc = ctx.get_desc(cursor);
                                                        match &*desc {
                                                            TypeDesc::Tarrow { arg, ret, .. } => {
                                                                let a = ctx.repr(arg.typ);
                                                                summary.push(format!("arg:{}@{}", a.0, ctx.get_level(a)));
                                                                cursor = ctx.repr(*ret);
                                                            }
                                                            TypeDesc::Tconstr { path, args, .. } => {
                                                                let args_summary = args
                                                                    .iter()
                                                                    .map(|t| {
                                                                        let t = ctx.repr(*t);
                                                                        format!("{}@{}", t.0, ctx.get_level(t))
                                                                    })
                                                                    .collect::<Vec<_>>()
                                                                    .join(",");
                                                                summary.push(format!(
                                                                    "ret:{}#{}@{}({})",
                                                                    path.name(),
                                                                    cursor.0,
                                                                    ctx.get_level(cursor),
                                                                    args_summary
                                                                ));
                                                                break;
                                                            }
                                                            other => {
                                                                summary.push(format!("ret:{:?}", other));
                                                                break;
                                                            }
                                                        }
                                                    }
                                                    eprintln!(
                                                        "[js-string2-sig] stage=before-copy path={} {}",
                                                        sub_path.name(),
                                                        summary.join(" -> ")
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    // If an alias was followed, rewrite type paths from the
                                    // resolved module name to the access path.
                                    // E.g., Belt.Array aliases Belt_Array, so rewrite
                                    // Pdot(Pident("Belt_Array"), X) → Pdot(sub_path, X)
                                    let alias_target = if apply_subst {
                                        match &sub_md.md_type {
                                            crate::types::decl::ModuleType::MtyAlias(
                                                _,
                                                target,
                                            ) => {
                                                if matches!(target, Path::Pdot(..))
                                                    && !target.same(&sub_path)
                                                {
                                                    Some(target.clone())
                                                } else {
                                                    None
                                                }
                                            }
                                            _ => sub_md.md_path.as_ref().and_then(|md_path| {
                                                if matches!(md_path, Path::Pdot(..))
                                                    && !md_path.same(&sub_path)
                                                {
                                                    Some(md_path.clone())
                                                } else {
                                                    None
                                                }
                                            }),
                                        }
                                    } else {
                                        None
                                    };
                                    let mut sig = if apply_subst {
                                        copy_lookup_signature_for_subst(&sig, ctx)
                                    } else {
                                        sig
                                    };
                                    if std::env::var_os("RUST_DEBUG_JS_STRING2_SIG").is_some()
                                        && sub_path.name() == "Js.String2"
                                    {
                                        for item in &sig {
                                            if let crate::types::decl::SignatureItem::SigValue(id, vd) = item {
                                                if id.name() == "substrAtMost" {
                                                    let ty = ctx.repr(vd.val_type);
                                                    let mut summary = vec![format!("ty={}@{}", ty.0, ctx.get_level(ty))];
                                                    let mut cursor = ty;
                                                    for _ in 0..8 {
                                                        let desc = ctx.get_desc(cursor);
                                                        match &*desc {
                                                            TypeDesc::Tarrow { arg, ret, .. } => {
                                                                let a = ctx.repr(arg.typ);
                                                                summary.push(format!("arg:{}@{}", a.0, ctx.get_level(a)));
                                                                cursor = ctx.repr(*ret);
                                                            }
                                                            TypeDesc::Tconstr { path, args, .. } => {
                                                                let args_summary = args
                                                                    .iter()
                                                                    .map(|t| {
                                                                        let t = ctx.repr(*t);
                                                                        format!("{}@{}", t.0, ctx.get_level(t))
                                                                    })
                                                                    .collect::<Vec<_>>()
                                                                    .join(",");
                                                                summary.push(format!(
                                                                    "ret:{}#{}@{}({})",
                                                                    path.name(),
                                                                    cursor.0,
                                                                    ctx.get_level(cursor),
                                                                    args_summary
                                                                ));
                                                                break;
                                                            }
                                                            other => {
                                                                summary.push(format!("ret:{:?}", other));
                                                                break;
                                                            }
                                                        }
                                                    }
                                                    eprintln!(
                                                        "[js-string2-sig] stage=after-copy path={} {}",
                                                        sub_path.name(),
                                                        summary.join(" -> ")
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    if apply_subst
                                        && matches!(
                                            &sub_md.md_type,
                                            crate::types::decl::ModuleType::MtyAlias(..)
                                        )
                                    {
                                        sig = strengthen_signature_for_module_access_path(
                                            ctx, &sub_path, &sig,
                                        );
                                    }
                                    if apply_subst {
                                        if let Some(ref old_name) = resolved_name {
                                            crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                                                &sig, old_name, &sub_path, ctx,
                                            );
                                        }
                                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                                            &sig, &sub_path, ctx,
                                        );
                                        if let Some(ref target) = alias_target {
                                            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                                                &sig, target, &sub_path, ctx,
                                            );
                                        }
                                    }
                                    if std::env::var_os("RUST_DEBUG_SIG_N_T").is_some()
                                        && sub_path.name() == "N"
                                    {
                                        for item in &sig {
                                            if let crate::types::decl::SignatureItem::SigType(
                                                id,
                                                decl,
                                                _,
                                            ) = item
                                            {
                                                if id.name() == "t" {
                                                    eprintln!(
                                                        "[sig-n-t] path={} manifest={} params={}",
                                                        sub_path.name(),
                                                        decl.type_manifest.is_some(),
                                                        decl.type_params.len()
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    if std::env::var_os("RUST_DEBUG_NUMBERFORMAT_SIG").is_some()
                                        && sub_path.name().ends_with("NumberFormat")
                                    {
                                        for item in &sig {
                                            if let crate::types::decl::SignatureItem::SigType(
                                                id,
                                                decl,
                                                _,
                                            ) = item
                                            {
                                                if id.name() == "options" {
                                                    if let crate::types::TypeKind::TypeRecord(
                                                        labels,
                                                        _,
                                                    ) = &decl.type_kind
                                                    {
                                                        for lbl in labels {
                                                            if matches!(
                                                                lbl.ld_id.name(),
                                                                "useGrouping"
                                                                    | "compactDisplay"
                                                                    | "currency"
                                                            ) {
                                                                let ty = ctx.repr(lbl.ld_type);
                                                                let desc = ctx.get_desc(ty);
                                                                let head = match &*desc {
                                                                    TypeDesc::Tconstr { path, args, .. } => {
                                                                        if path.name() == "option"
                                                                            && args.len() == 1
                                                                        {
                                                                            let arg = ctx.repr(args[0]);
                                                                            let arg_desc = ctx.get_desc(arg);
                                                                            match &*arg_desc {
                                                                                TypeDesc::Tconstr { path, .. } => {
                                                                                    format!("option<{}>", path.name())
                                                                                }
                                                                                _ => format!("option<ty#{}>", arg.0),
                                                                            }
                                                                        } else {
                                                                            path.name()
                                                                        }
                                                                    }
                                                                    _ => format!("ty#{}", ty.0),
                                                                };
                                                                eprintln!(
                                                                    "[numberformat-sig] path={} options.useGrouping ty={} head={}",
                                                                    sub_path.name(),
                                                                    ty.0,
                                                                    head
                                                                );
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
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
    /// Returns (signature, Option<resolved_module_name>) where resolved_module_name is Some
    /// when an alias was followed (so the caller can rewrite paths).
    fn resolve_module_type<'b>(
        &self,
        mty: &crate::types::decl::ModuleType,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'b crate::types::context::TypeContext<'b>,
    ) -> Option<(crate::types::decl::Signature, Option<String>)> {
        use std::collections::HashSet;

        fn resolve_module_type_inner<'b>(
            env: &Env,
            mty: &crate::types::decl::ModuleType,
            pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
            ctx: &'b crate::types::context::TypeContext<'b>,
            visiting: &mut HashSet<Path>,
        ) -> Option<(crate::types::decl::Signature, Option<String>)> {
            match mty {
                crate::types::decl::ModuleType::MtySignature(sig) => Some((sig.clone(), None)),
                crate::types::decl::ModuleType::MtyAlias(_, path) => {
                    resolve_path(env, path, pers_env, ctx, visiting)
                }
                crate::types::decl::ModuleType::MtyIdent(path) => {
                    // Match OCaml Env.scrape_alias: resolve Mty_ident via module-type
                    // expansion first, then fall back to module-path resolution.
                    resolve_modtype_path(env, path, pers_env, ctx, visiting)
                        .or_else(|| resolve_path(env, path, pers_env, ctx, visiting))
                }
                _ => None,
            }
        }

        fn resolve_modtype_path<'b>(
            env: &Env,
            path: &Path,
            pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
            ctx: &'b crate::types::context::TypeContext<'b>,
            visiting: &mut HashSet<Path>,
        ) -> Option<(crate::types::decl::Signature, Option<String>)> {
            use crate::types::decl::SignatureItem;

            if !visiting.insert(path.clone()) {
                return None;
            }

            let result = match path {
                Path::Pident(id) => {
                    match env.lookup_modtype(path) {
                        Ok(mtd) => mtd.mtd_type.as_ref().and_then(|mty| {
                            resolve_module_type_inner(env, mty, pers_env, ctx, visiting)
                        }),
                        Err(_) => None,
                    }
                }
                Path::Pdot(parent, modtype_name, _) => {
                    let (parent_sig, _resolved_name) =
                        match resolve_path(env, parent, pers_env, ctx, visiting) {
                            Some(x) => x,
                            None => {
                                visiting.remove(path);
                                return None;
                            }
                        };
                    parent_sig.iter().rev().find_map(|sig_item| {
                        if let SignatureItem::SigModtype(id, mtd) = sig_item {
                            if id.name() == modtype_name.as_str() {
                                return mtd.mtd_type.as_ref().and_then(|mty| {
                                    resolve_module_type_inner(env, mty, pers_env, ctx, visiting)
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
            pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
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
                    if let Ok(md) = env.lookup_module(path) {
                        if let Some(result) =
                            resolve_module_type_inner(env, &md.md_type, pers_env, ctx, visiting)
                        {
                            visiting.remove(path);
                            return Some(result);
                        }
                    }
                    if id.stamp() == 0 {
                        if let Some(pers) = pers_env.as_mut() {
                            if let Some(ps) = pers.find_pers_struct(mod_name, ctx) {
                                let result =
                                    Some((ps.ps_sig.clone(), Some(mod_name.to_string())));
                                visiting.remove(path);
                                return result;
                            }
                        }
                    }
                    visiting.remove(path);
                    None
                }
                Path::Pdot(parent, submod_name, _) => {
                    let (parent_sig, _resolved_name) =
                        match resolve_path(env, parent, pers_env, ctx, visiting) {
                            Some(x) => x,
                            None => {
                                visiting.remove(path);
                                return None;
                            }
                        };
                    for sig_item in parent_sig.iter().rev() {
                        if let SignatureItem::SigModule(id, sub_md, _) = sig_item {
                            if id.name() == submod_name.as_str() {
                                let result = resolve_module_type_inner(
                                    env,
                                    &sub_md.md_type,
                                    pers_env,
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

        // Follow aliases through both local and persistent modules, while avoiding cycles.
        let mut visiting = HashSet::new();
        resolve_module_type_inner(self, mty, pers_env, ctx, &mut visiting)
    }
}

/// Look up all constructors in a module-qualified path (e.g., `M.C`).
/// For `Ldot` paths, resolves the module and searches all type declarations.
fn lookup_constructors_in_module<'b>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Vec<(Path, crate::types::decl::ConstructorDescription)> {
    use crate::parser::longident::Longident;
    use crate::types::decl::SignatureItem;
    let mut matches = Vec::new();

    match lid {
        Longident::Ldot(module_lid, cstr_idx) => {
            let cstr_name = arena.get_string(*cstr_idx);
            let Some((mod_path, sig)) = env.resolve_module_lid(module_lid, arena, pers_env, ctx) else {
                return matches;
            };
            for sig_item in &sig {
                if let SignatureItem::SigType(type_id, type_decl, _rec) = sig_item {
                    if let crate::types::TypeKind::TypeVariant(ref constrs) = type_decl.type_kind {
                        let num_consts = constrs
                            .iter()
                            .filter(|c| {
                                matches!(c.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty())
                                    && c.cd_res.is_none()
                            })
                            .count() as i32;
                        let num_nonconsts = constrs.len() as i32 - num_consts;
                        let mut const_idx = 0i32;
                        let mut block_idx = 0i32;
                        for cd in constrs {
                            let is_constant = matches!(
                                cd.cd_args,
                                crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()
                            ) && cd.cd_res.is_none();

                            if cd.cd_id.name() == cstr_name {
                                let tag = if is_constant {
                                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                                } else {
                                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                                };
                                let type_path =
                                    Path::pdot(mod_path.clone(), type_id.name().to_string());
                                let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
                                    crate::types::ConstructorArguments::CstrTuple(args) => {
                                        (args.clone(), args.len() as i32, None)
                                    }
                                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                                        let inline_params = inline_record_type_params(
                                            ctx,
                                            &type_decl.type_params,
                                            labels,
                                        );
                                        let inline_path =
                                            Path::pdot(type_path.clone(), cstr_name.to_string());
                                        let inline_constr =
                                            ctx.new_generic_constr(inline_path, inline_params.clone());
                                        let inline_decl = crate::types::TypeDeclaration {
                                            type_params: inline_params.clone(),
                                            type_arity: inline_params.len() as i32,
                                            type_kind: crate::types::TypeKind::TypeRecord(
                                                labels.clone(),
                                                crate::types::RecordRepresentation::RecordInlined {
                                                    tag: block_idx,
                                                    name: cstr_name.to_string(),
                                                    num_nonconsts,
                                                    attrs: cd.cd_attributes.clone(),
                                                },
                                            ),
                                            type_private: type_decl.type_private,
                                            type_manifest: None,
                                            type_variance: inline_params
                                                .iter()
                                                .map(|_| crate::types::variance::Variance::full())
                                                .collect(),
                                            type_newtype_level: None,
                                            type_loc: cd.cd_loc,
                                            type_attributes: vec![],
                                            type_immediate: false,
                                            type_unboxed: crate::types::UnboxedStatus::default(),
                                            type_inlined_types: vec![],
                                            type_path: None,
                                        };
                                        (
                                            vec![inline_constr],
                                            1,
                                            Some(Box::new(inline_decl)),
                                        )
                                    }
                                };
                                let cstr_res = if let Some(res_ty) = cd.cd_res {
                                    let desc = ctx.get_desc(res_ty);
                                    match &*desc {
                                        crate::types::TypeDesc::Tconstr { args, .. } => {
                                            let args = args.clone();
                                            drop(desc);
                                            ctx.new_generic_constr(type_path.clone(), args)
                                        }
                                        _ => {
                                            drop(desc);
                                            res_ty
                                        }
                                    }
                                } else {
                                    ctx.new_generic_constr(
                                        type_path.clone(),
                                        type_decl.type_params.clone(),
                                    )
                                };
                                let desc = crate::types::decl::ConstructorDescription {
                                    cstr_name: cstr_name.to_string(),
                                    cstr_res,
                                    cstr_existentials: vec![],
                                    cstr_args,
                                    cstr_arity,
                                    cstr_tag: tag,
                                    cstr_consts: num_consts,
                                    cstr_nonconsts: num_nonconsts,
                                    cstr_generalized: cd.cd_res.is_some(),
                                    cstr_private: type_decl.type_private,
                                    cstr_loc: cd.cd_loc,
                                    cstr_attributes: cd.cd_attributes.clone(),
                                    cstr_inlined,
                                };
                                let path = Path::pident(Ident::create_persistent(cstr_name));
                                matches.push((path, desc));
                            }
                            if is_constant {
                                const_idx += 1;
                            } else {
                                block_idx += 1;
                            }
                        }
                    }
                }
                if let SignatureItem::SigTypext(id, ext, _status) = sig_item {
                    if id.name() == cstr_name {
                        let ext_path = Path::pident(Ident::create_persistent(cstr_name));
                        let (cstr_args, cstr_arity, cstr_inlined) = match &ext.ext_args {
                            crate::types::ConstructorArguments::CstrTuple(args) => {
                                (args.clone(), args.len() as i32, None)
                            }
                            crate::types::ConstructorArguments::CstrRecord(labels) => {
                                let inline_params =
                                    inline_record_type_params(ctx, &ext.ext_type_params, labels);
                                let inline_constr =
                                    ctx.new_generic_constr(ext_path.clone(), inline_params.clone());
                                let inline_decl = crate::types::TypeDeclaration {
                                    type_params: inline_params.clone(),
                                    type_arity: inline_params.len() as i32,
                                    type_kind: crate::types::TypeKind::TypeRecord(
                                        labels.clone(),
                                        crate::types::RecordRepresentation::RecordExtension,
                                    ),
                                    type_private: ext.ext_private,
                                    type_manifest: None,
                                    type_variance: inline_params
                                        .iter()
                                        .map(|_| crate::types::variance::Variance::full())
                                        .collect(),
                                    type_newtype_level: None,
                                    type_loc: ext.ext_loc,
                                    type_attributes: vec![],
                                    type_immediate: false,
                                    type_unboxed: crate::types::UnboxedStatus::default(),
                                    type_inlined_types: vec![],
                                    type_path: None,
                                };
                                (
                                    vec![inline_constr],
                                    1,
                                    Some(Box::new(inline_decl)),
                                )
                            }
                        };
                        let ext_type_path = crate::cmi::persistent_env::substitute_sig_path(
                            &ext.ext_type_path,
                            &sig,
                            &mod_path,
                        );
                        let cstr_res =
                            ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone());
                        let desc = crate::types::decl::ConstructorDescription {
                            cstr_name: cstr_name.to_string(),
                            cstr_res,
                            cstr_existentials: vec![],
                            cstr_args,
                            cstr_arity,
                            cstr_tag: crate::types::decl::ConstructorTag::CstrExtension(
                                ext_path.clone(),
                            ),
                            cstr_consts: 0,
                            cstr_nonconsts: 0,
                            cstr_generalized: ext.ext_ret_type.is_some(),
                            cstr_private: ext.ext_private,
                            cstr_loc: ext.ext_loc,
                            cstr_attributes: ext.ext_attributes.clone(),
                            cstr_inlined,
                        };
                        matches.push((ext_path, desc));
                    }
                }
            }
            matches
        }
        _ => matches,
    }
}

fn lookup_constructor_in_module<'b>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    lookup_constructors_in_module(lid, arena, env, pers_env, ctx)
        .into_iter()
        .last()
}

fn lookup_predef_option_constructor<'b>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    let (prefix, cstr_idx) = match lid {
        Longident::Ldot(prefix, cstr_idx) => (prefix, cstr_idx),
        _ => return None,
    };
    let module_name = match &**prefix {
        Longident::Lident(mod_idx) => arena.get_string(*mod_idx),
        _ => return None,
    };
    if module_name != "*predef*" {
        return None;
    }

    let cstr_name = arena.get_string(*cstr_idx);
    let inner_ty = ctx.new_var(None);
    let option_ty = env.type_option(ctx, inner_ty);
    let (arity, args, tag) = match cstr_name {
        "Some" => (
            1,
            vec![inner_ty],
            crate::types::decl::ConstructorTag::CstrBlock(0),
        ),
        "None" => (
            0,
            vec![],
            crate::types::decl::ConstructorTag::CstrConstant(0),
        ),
        _ => return None,
    };

    let desc = crate::types::decl::ConstructorDescription {
        cstr_name: cstr_name.to_string(),
        cstr_res: option_ty,
        cstr_existentials: vec![],
        cstr_args: args,
        cstr_arity: arity,
        cstr_tag: tag,
        cstr_consts: 1,
        cstr_nonconsts: 1,
        cstr_generalized: false,
        cstr_private: crate::types::PrivateFlag::Public,
        cstr_loc: crate::location::Location::none(),
        cstr_attributes: vec![],
        cstr_inlined: None,
    };
    let path = Path::pident(Ident::create_persistent(cstr_name));
    Some((path, desc))
}

/// Extract the type path from a type expression if it's a concrete type constructor.
/// Follows repr/Tlink chains, and for abstract types tries to expand through aliases.
/// Returns the path from the Tconstr if found.
fn extract_type_path_from_expected<'a>(
    expected_ty: TypeExprRef,
    env: &Env,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<Path> {
    let mut no_persistent_env = None;
    extract_type_path_from_expected_with_persistent_env(
        expected_ty,
        env,
        &mut no_persistent_env,
        ctx,
    )
}

fn extract_type_path_from_expected_with_persistent_env<'a>(
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<Path> {
    let mut visited_types = std::collections::HashSet::new();
    let mut visited_paths = std::collections::HashSet::new();
    extract_type_path_from_expected_inner(
        expected_ty,
        env,
        pers_env,
        ctx,
        &mut visited_types,
        &mut visited_paths,
    )
}

fn extract_type_path_from_expected_inner<'a>(
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
    visited_types: &mut std::collections::HashSet<usize>,
    visited_paths: &mut std::collections::HashSet<Path>,
) -> Option<Path> {
    let ty = ctx.repr(expected_ty);
    if !visited_types.insert(ty.0) {
        return None; // Already visited this type expression — break the cycle
    }
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, .. } => {
            // Track visited paths to detect cycles through type declaration manifests.
            // Different TypeExprRefs can point to the same path via manifests, so
            // tracking type expression IDs alone is not sufficient.
            if !visited_paths.insert(path.clone()) {
                return None; // Already expanded through this path — break the cycle
            }
            // Check if this is a concrete (non-abstract) type
            if let Some(decl) = lookup_type_decl_for_path(path, env, pers_env, ctx) {
                match &decl.type_kind {
                    crate::types::TypeKind::TypeAbstract => {
                        // Abstract type - try to expand through manifest
                        if let Some(manifest) = decl.type_manifest {
                            drop(desc);
                            return extract_type_path_from_expected_inner(
                                manifest,
                                env,
                                pers_env,
                                ctx,
                                visited_types,
                                visited_paths,
                            );
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

/// Extract variant type path for constructor disambiguation.
///
/// OCaml `extract_concrete_variant` first resolves through type abbreviations,
/// then checks the resulting head is variant-like. Mirror that behavior here,
/// while keeping label/path extraction logic unchanged.
fn extract_variant_type_path_from_expected_with_persistent_env<'a>(
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<Path> {
    fn resolve_variant_type_path<'a>(
        path: &Path,
        env: &Env,
        pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
        ctx: &'a crate::types::context::TypeContext<'a>,
    ) -> Option<Path> {
        let mut current = path.clone();
        let mut visited = HashSet::new();
        loop {
            // Don't normalize module aliases at the top of the loop — this would
            // flatten qualified paths like Pdot(Pdot(Pident("Stdlib"), "JSON"), "t")
            // into Pdot(Pident("Stdlib_JSON"), "t"), losing the module-qualified
            // structure. lookup_type_decl_for_path handles module aliases internally
            // via resolve_module_signature_for_path. Module alias normalization is
            // only used as a fallback for self-manifest cycles (below).
            if !visited.insert(current.name()) {
                return None;
            }
            let Some(decl) = lookup_type_decl_for_path(&current, env, pers_env, ctx) else {
                // If the declaration is unavailable, keep the path for
                // env-based constructor path comparison.
                return Some(current);
            };
            match decl.type_kind {
                crate::types::TypeKind::TypeVariant(_) => {
                    return Some(current);
                }
                crate::types::TypeKind::TypeOpen => {
                    // `type t = | ...Other.t` can be represented as TypeOpen with
                    // a manifest pointing at the concrete variant source.
                    // Follow that manifest first; otherwise keep the open head.
                    let manifest = decl.type_manifest;
                    if manifest.is_none() {
                        return Some(current);
                    }
                    let manifest = manifest.unwrap();
                    let manifest_repr = ctx.repr(manifest);
                    let manifest_desc = ctx.get_desc(manifest_repr);
                    let next_path = match &*manifest_desc {
                        TypeDesc::Tconstr { path, .. } => path.clone(),
                        _ => return Some(current),
                    };
                    if next_path.same(&current) {
                        return Some(current);
                    }
                    current = next_path;
                    continue;
                }
                crate::types::TypeKind::TypeAbstract => {
                    let manifest = decl.type_manifest;
                    if manifest.is_none() {
                        return None;
                    }
                    let manifest = manifest.unwrap();
                    let manifest_repr = ctx.repr(manifest);
                    let manifest_desc = ctx.get_desc(manifest_repr);
                    let next_path = match &*manifest_desc {
                        TypeDesc::Tconstr { path, .. } => path.clone(),
                        _ => return None,
                    };
                    if next_path.same(&current) {
                        // Self-manifest cycle: try normalize_path as fallback
                        let normalized = env.normalize_path(&current);
                        if normalized.same(&current) {
                            return None;
                        }
                        current = normalized;
                        continue;
                    }
                    current = next_path;
                }
                _ => {
                    return None;
                }
            }
        }
    }

    let opath =
        extract_type_path_from_expected_with_persistent_env(expected_ty, env, pers_env, ctx);
    if let Some(path) = opath {
        if let Some(resolved) = resolve_variant_type_path(&path, env, pers_env, ctx) {
            return Some(resolved);
        }
    }
    None
}

/// OCaml `typecore.ml` compares constructor/label type paths with
/// `compare_type_path`, which expands type manifests and normalizes aliases.
/// Mirror that behavior for constructor disambiguation.
fn expand_type_path_for_compare<'a>(
    path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
    depth: usize,
    visiting: &mut HashSet<String>,
) -> Path {
    if depth > 50 {
        return path.clone();
    }

    let visit_key = path.name();
    if !visiting.insert(visit_key.clone()) {
        return path.clone();
    }

    if let Some(decl) = lookup_type_decl_for_path(path, env, pers_env, ctx) {
        if let Some(manifest) = decl.type_manifest {
            let manifest_path = {
                let manifest_desc = ctx.get_desc(ctx.repr(manifest));
                match &*manifest_desc {
                    TypeDesc::Tconstr {
                        path: manifest_path,
                        ..
                    } => Some(manifest_path.clone()),
                    _ => None,
                }
            };
            if let Some(manifest_path) = manifest_path {
                let expanded = expand_type_path_for_compare(
                    &manifest_path,
                    env,
                    pers_env,
                    ctx,
                    depth + 1,
                    visiting,
                );
                visiting.remove(&visit_key);
                return expanded;
            }
        }
    }

    let normalized = env.normalize_path(path);
    if !normalized.same(path) {
        let expanded =
            expand_type_path_for_compare(&normalized, env, pers_env, ctx, depth + 1, visiting);
        visiting.remove(&visit_key);
        return expanded;
    }

    visiting.remove(&visit_key);
    path.clone()
}

fn compare_type_paths_for_disambiguation<'a>(
    left: &Path,
    right: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> bool {
    let mut left_visiting = HashSet::new();
    let mut right_visiting = HashSet::new();
    let left_expanded = expand_type_path_for_compare(left, env, pers_env, ctx, 0, &mut left_visiting);
    let right_expanded =
        expand_type_path_for_compare(right, env, pers_env, ctx, 0, &mut right_visiting);
    left_expanded.same(&right_expanded)
}

fn disambiguate_constructor_candidates<'a>(
    candidates: &[(Path, crate::types::decl::ConstructorDescription)],
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    if candidates.is_empty() {
        return None;
    }

    let opath = extract_variant_type_path_from_expected_with_persistent_env(
        expected_ty,
        env,
        pers_env,
        ctx,
    );

    if let Some(ref target_path) = opath {
        for (path, cstr_desc) in candidates.iter().rev() {
            let cstr_ty = ctx.repr(cstr_desc.cstr_res);
            let cstr_ty_desc = ctx.get_desc(cstr_ty);
            if let TypeDesc::Tconstr {
                path: cstr_path, ..
            } = &*cstr_ty_desc
            {
                if cstr_path.same(target_path)
                    || compare_type_paths_for_disambiguation(
                        cstr_path,
                        target_path,
                        env,
                        pers_env,
                        ctx,
                    )
                {
                    return Some((path.clone(), cstr_desc.clone()));
                }
            }
        }
    }

    candidates.last().cloned()
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
    let debug_disamb_cstr = std::env::var_os("RUST_DEBUG_DISAMB_CSTR").is_some();
    // Step 1: Try to extract the variant type path from the expected type
    let opath = extract_variant_type_path_from_expected_with_persistent_env(
        expected_ty,
        env,
        pers_env,
        ctx,
    );

    // Step 2: Find all constructors with this name
    let all_constrs = env.find_all_constructors(cstr_name);

    if all_constrs.is_empty() {
        let resolved =
            lookup_constructor_by_expected_type(cstr_name, expected_ty, env, pers_env, ctx);
        if debug_disamb_cstr && resolved.is_none() {
            let target = opath
                .as_ref()
                .map(|p| p.name())
                .unwrap_or_else(|| "<none>".to_string());
            eprintln!(
                "[disamb-cstr] source=env-empty name={} target={} selected=<none>",
                cstr_name, target
            );
        }
        // No constructors found in env - try type-directed lookup
        return resolved;
    }

    // Step 3: If we have a target type path, try to disambiguate
    if let Some(ref target_path) = opath {
        // Match OCaml NameChoice.disambiguate_by_type: choose the first
        // path-compatible constructor in scope order (most recent first),
        // with compare_type_path semantics (alias-expanded path compare).
        for cstr in all_constrs.iter().rev() {
            let cstr_ty = ctx.repr(cstr.cstr_res);
            let cstr_desc = ctx.get_desc(cstr_ty);
            if let TypeDesc::Tconstr {
                path: cstr_path, ..
            } = &*cstr_desc
            {
                if cstr_path.same(target_path)
                    || compare_type_paths_for_disambiguation(
                        cstr_path,
                        target_path,
                        env,
                        pers_env,
                        ctx,
                    )
                {
                    if debug_disamb_cstr {
                        let args = cstr
                            .cstr_args
                            .iter()
                            .map(|t| {
                                let r = ctx.repr(*t);
                                format!("{}@{}", r.0, ctx.get_level(r))
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        let res = ctx.repr(cstr.cstr_res);
                        eprintln!(
                            "[disamb-cstr] source=env name={} target={} res={}@{} args=[{}]",
                            cstr_name,
                            target_path.name(),
                            res.0,
                            ctx.get_level(res),
                            args
                        );
                    }
                    let path = Path::pident(Ident::create_persistent(cstr_name));
                    return Some((path, (*cstr).clone()));
                }
            }
        }
        // No constructor in env matched the expected type - try type-directed lookup
        // (the type might be defined in another module loaded from CMI)
        if let Some(result) =
            lookup_constructor_by_expected_type(cstr_name, expected_ty, env, pers_env, ctx)
        {
            if debug_disamb_cstr {
                let res = ctx.repr(result.1.cstr_res);
                let args = result
                    .1
                    .cstr_args
                    .iter()
                    .map(|t| {
                        let r = ctx.repr(*t);
                        format!("{}@{}", r.0, ctx.get_level(r))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!(
                    "[disamb-cstr] source=expected name={} res={}@{} args=[{}]",
                    cstr_name,
                    res.0,
                    ctx.get_level(res),
                    args
                );
            }
            return Some(result);
        } else if debug_disamb_cstr {
            eprintln!(
                "[disamb-cstr] source=expected name={} target={} selected=<none>",
                cstr_name,
                target_path.name()
            );
        }
    }

    // Step 4: Fall back to the most recent constructor (last in the list = most recently added)
    let cstr = all_constrs.last().unwrap();
    if debug_disamb_cstr {
        let res = ctx.repr(cstr.cstr_res);
        let args = cstr
            .cstr_args
            .iter()
            .map(|t| {
                let r = ctx.repr(*t);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect::<Vec<_>>()
            .join(",");
        eprintln!(
            "[disamb-cstr] source=fallback name={} res={}@{} args=[{}]",
            cstr_name,
            res.0,
            ctx.get_level(res),
            args
        );
    }
    let path = Path::pident(Ident::create_persistent(cstr_name));
    Some((path, (*cstr).clone()))
}

/// Type-directed label disambiguation when the label is not in scope.
///
/// OCaml's `Label.disambiguate` can still resolve labels using `opath` even
/// when `find_all_labels` is empty. Mirror that by inspecting the expected
/// record type declaration directly.
fn lookup_label_by_lid<'a>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    use crate::types::decl::SignatureItem;

    let Longident::Ldot(module_lid, label_idx) = lid else {
        return None;
    };

    let label_name = arena.get_string(*label_idx);
    let (module_path, signature) = env.resolve_module_lid(module_lid, arena, pers_env, ctx)?;

    // For qualified labels, mirror OCaml's in-scope precedence and prefer the
    // most recently declared matching record type in the module.
    for sig_item in signature.iter().rev() {
        if let SignatureItem::SigType(type_id, type_decl, _) = sig_item {
            let (labels, repr) = match &type_decl.type_kind {
                crate::types::TypeKind::TypeRecord(labels, repr) => (labels, repr),
                _ => continue,
            };

            let type_path = Path::pdot(module_path.clone(), type_id.name().to_string());
            let mut decl_for_cache = type_decl.clone();
            if decl_for_cache.type_path.is_none() {
                decl_for_cache.type_path = Some(type_path.clone());
            }
            if type_id.stamp() != 0 {
                ctx.register_type_decl_by_stamp(type_id.stamp(), decl_for_cache.clone());
            }
            ctx.register_type_decl_by_path(&type_path.name(), decl_for_cache);
            let res_ty = ctx.new_generic_constr(type_path.clone(), type_decl.type_params.clone());

            for (pos, ld) in labels.iter().enumerate() {
                if ld.ld_id.name() == label_name {
                    return Some(crate::types::LabelDescription {
                        lbl_name: ld.ld_id.name().to_string(),
                        lbl_res: res_ty,
                        lbl_arg: crate::types::ctype::remap_label_type_to_params(
                            ctx,
                            ld.ld_type,
                            &type_decl.type_params,
                        ),
                        lbl_mut: ld.ld_mutable,
                        lbl_optional: ld.ld_optional,
                        lbl_pos: pos as i32,
                        lbl_all: crate::types::LabelArrayRef(0),
                        lbl_repres: repr.clone(),
                        lbl_private: type_decl.type_private,
                        lbl_loc: ld.ld_loc.clone(),
                        lbl_attributes: ld.ld_attributes.clone(),
                    });
                }
            }
        }
    }

    None
}

fn lookup_label_by_lid_matching_fields<'a>(
    lid: &Longident,
    arena: &ParseArena,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
    field_names: &[String],
    closed_record: bool,
) -> Option<crate::types::LabelDescription> {
    use crate::types::decl::SignatureItem;

    let Longident::Ldot(module_lid, label_idx) = lid else {
        return None;
    };

    let label_name = arena.get_string(*label_idx);
    let (module_path, signature) = env.resolve_module_lid(module_lid, arena, pers_env, ctx)?;

    // Match OCaml label lookup precedence: prefer the most recently declared
    // matching type in the module signature.
    for sig_item in signature.iter().rev() {
        if let SignatureItem::SigType(type_id, type_decl, _) = sig_item {
            let (labels, repr) = match &type_decl.type_kind {
                crate::types::TypeKind::TypeRecord(labels, repr) => (labels, repr),
                _ => continue,
            };
            if !record_labels_match_ids(labels, field_names, closed_record) {
                continue;
            }

            let type_path = Path::pdot(module_path.clone(), type_id.name().to_string());
            let mut decl_for_cache = type_decl.clone();
            if decl_for_cache.type_path.is_none() {
                decl_for_cache.type_path = Some(type_path.clone());
            }
            if type_id.stamp() != 0 {
                ctx.register_type_decl_by_stamp(type_id.stamp(), decl_for_cache.clone());
            }
            ctx.register_type_decl_by_path(&type_path.name(), decl_for_cache);
            let res_ty = ctx.new_generic_constr(type_path.clone(), type_decl.type_params.clone());

            for (pos, ld) in labels.iter().enumerate() {
                if ld.ld_id.name() == label_name {
                    return Some(crate::types::LabelDescription {
                        lbl_name: ld.ld_id.name().to_string(),
                        lbl_res: res_ty,
                        lbl_arg: crate::types::ctype::remap_label_type_to_params(
                            ctx,
                            ld.ld_type,
                            &type_decl.type_params,
                        ),
                        lbl_mut: ld.ld_mutable,
                        lbl_optional: ld.ld_optional,
                        lbl_pos: pos as i32,
                        lbl_all: crate::types::LabelArrayRef(0),
                        lbl_repres: repr.clone(),
                        lbl_private: type_decl.type_private,
                        lbl_loc: ld.ld_loc.clone(),
                        lbl_attributes: ld.ld_attributes.clone(),
                    });
                }
            }
        }
    }

    None
}

fn lookup_label_by_expected_type<'a>(
    label_name: &str,
    record_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    let debug_label = std::env::var("RUST_DEBUG_DISAMB_LABEL").ok();
    let should_debug = debug_label
        .as_deref()
        .is_some_and(|filter| filter == "*" || filter == label_name);

    let type_path =
        extract_type_path_from_expected_with_persistent_env(record_ty, env, pers_env, ctx)?;
    if should_debug {
        eprintln!(
            "[disamb-label-expected] label={} record_ty={} path={}",
            label_name,
            ctx.repr(record_ty).0,
            type_path.name()
        );
    }
    let normalized_type_path = env.normalize_path(&type_path);
    let type_decl = lookup_type_decl_for_path(&type_path, env, pers_env, ctx)
        .or_else(|| {
            if !normalized_type_path.same(&type_path) {
                lookup_type_decl_for_path(&normalized_type_path, env, pers_env, ctx)
            } else {
                None
            }
        })
        .or_else(|| {
            // Some imported nested-module paths are stored in the context cache by
            // qualified string name (for example `LayoutTransition.t`) but are not
            // directly resolvable through the current env path tables.
            let path_name = type_path.name();
            ctx.find_type_decl_by_path(&path_name).map(|decl| decl.clone())
        })
        .or_else(|| {
            if !normalized_type_path.same(&type_path) {
                ctx.find_type_decl_by_path(&normalized_type_path.name())
                    .map(|decl| decl.clone())
            } else {
                None
            }
        })?;
    let (labels, repr) = match &type_decl.type_kind {
        crate::types::TypeKind::TypeRecord(labels, repr) => (labels, repr),
        _ => {
            if should_debug {
                let kind = match &type_decl.type_kind {
                    crate::types::TypeKind::TypeAbstract => "abstract",
                    crate::types::TypeKind::TypeOpen => "open",
                    crate::types::TypeKind::TypeVariant(_) => "variant",
                    crate::types::TypeKind::TypeRecord(_, _) => "record",
                };
                eprintln!(
                    "[disamb-label-expected] label={} path={} kind={} type_path={}",
                    label_name,
                    type_path.name(),
                    kind,
                    type_decl
                        .type_path
                        .as_ref()
                        .map(|p| p.name())
                        .unwrap_or_else(|| "<none>".to_string())
                );
            }
            return None;
        }
    };
    let resolved_type_path = match (type_decl.type_path.as_ref(), &type_path) {
        // When disambiguating against a qualified expected type (M.t), keep that
        // qualified head if the declaration only carries a local self path (`t`).
        // This matches OCaml path shapes for module-accessed record labels.
        (Some(Path::Pident(local_id)), Path::Pdot(_, type_name, _))
            if local_id.name() == type_name.as_str() =>
        {
            type_path.clone()
        }
        // For qualified expected paths (`M.t`), preserve that access path.
        // Declaration paths can be canonicalized through aliases (for example
        // `Schema__InstantExport.t`), but record-field disambiguation should
        // keep the head from the expected type.
        (Some(_), Path::Pdot(..)) => {
            type_path.clone()
        }
        (Some(path), _) => path.clone(),
        (None, Path::Pdot(parent, type_name, _)) => {
            if let Path::Pident(parent_id) = parent.as_ref() {
                if parent_id.stamp() != 0 {
                    if let Some(mapped_parent) = ctx.find_module_path_by_stamp(parent_id.stamp()) {
                        Path::pdot(mapped_parent, type_name.as_str())
                    } else {
                        type_path.clone()
                    }
                } else {
                    type_path.clone()
                }
            } else {
                type_path.clone()
            }
        }
        (None, _) => type_path.clone(),
    };
    let res_ty = ctx.new_generic_constr(resolved_type_path.clone(), type_decl.type_params.clone());
    for (pos, ld) in labels.iter().enumerate() {
        if ld.ld_id.name() == label_name {
            if should_debug {
                eprintln!(
                    "[disamb-label-expected] label={} selected={} pos={} resolved_path={}",
                    label_name,
                    ld.ld_id.name(),
                    pos,
                    resolved_type_path.name()
                );
            }
            return Some(crate::types::LabelDescription {
                lbl_name: ld.ld_id.name().to_string(),
                lbl_res: res_ty,
                lbl_arg: crate::types::ctype::remap_label_type_to_params(
                    ctx,
                    ld.ld_type,
                    &type_decl.type_params,
                ),
                lbl_mut: ld.ld_mutable,
                lbl_optional: ld.ld_optional,
                lbl_pos: pos as i32,
                lbl_all: crate::types::LabelArrayRef(0),
                lbl_repres: repr.clone(),
                lbl_private: type_decl.type_private,
                lbl_loc: ld.ld_loc.clone(),
                lbl_attributes: ld.ld_attributes.clone(),
            });
        }
    }
    None
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
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    let debug_filter = std::env::var("RUST_DEBUG_DISAMB_LABEL").ok();
    let debug_disamb_label = debug_filter
        .as_deref()
        .is_some_and(|filter| filter == "*" || filter == label_name);
    // Extract type path from the record expression's type
    let opath =
        extract_type_path_from_expected_with_persistent_env(record_ty, env, pers_env, ctx);

    // OCaml special-case: when disambiguating labels on dict, route any field lookup
    // through dictValuesType, then preserve the source field name in the final label.
    let (lookup_name, override_name) = if let Some(ref path) = opath {
        if is_dict_type_path(path) {
            (DICT_MAGIC_FIELD_NAME, Some(label_name.to_string()))
        } else {
            (label_name, None)
        }
    } else {
        (label_name, None)
    };

    // Find all labels with this name
    let all_labels = env.find_all_labels(lookup_name);
    if debug_disamb_label {
        let target = opath
            .as_ref()
            .map(|p| p.name())
            .unwrap_or_else(|| "<none>".to_string());
        let candidate_paths: Vec<String> = all_labels
            .iter()
            .map(|label| {
                let lbl_ty = ctx.repr(label.lbl_res);
                let lbl_desc = ctx.get_desc(lbl_ty);
                match &*lbl_desc {
                    TypeDesc::Tconstr { path, .. } => path.name(),
                    _ => format!("ty#{}", lbl_ty.0),
                }
            })
            .collect();
        eprintln!(
            "[disamb-label] name={} lookup_name={} target={} env_candidates={} candidates={:?}",
            label_name,
            lookup_name,
            target,
            all_labels.len(),
            candidate_paths
        );
    }

    if all_labels.is_empty() {
        let mut selected =
            lookup_label_by_expected_type(lookup_name, record_ty, env, pers_env, ctx);
        if debug_disamb_label {
            let chosen = selected
                .as_ref()
                .map(|label| format!("{}@{}", label.lbl_name, label.lbl_pos))
                .unwrap_or_else(|| "<none>".to_string());
            eprintln!(
                "[disamb-label] name={} source=expected-only selected={}",
                label_name, chosen
            );
        }
        if let Some(override_name) = override_name {
            if let Some(label) = selected.as_mut() {
                label.lbl_name = override_name;
            }
        }
        return selected;
    }

    let mut selected = None;

    // If we have a target type path, try to disambiguate by exact path identity.
    // Prefer the most recently added matching label (reverse iteration).
    if let Some(ref target_path) = opath {
        for label in all_labels.iter().rev() {
            let lbl_ty = ctx.repr(label.lbl_res);
            let lbl_desc = ctx.get_desc(lbl_ty);
            if let TypeDesc::Tconstr { path: lbl_path, .. } = &*lbl_desc {
                if lbl_path.same(target_path) {
                    selected = Some((*label).clone());
                    break;
                }
            }
        }

        // Fallback for semantically identical paths carrying different local stamps.
        if selected.is_none() {
            let target_name = target_path.name();
            for label in all_labels.iter().rev() {
                let lbl_ty = ctx.repr(label.lbl_res);
                let lbl_desc = ctx.get_desc(lbl_ty);
                if let TypeDesc::Tconstr { path: lbl_path, .. } = &*lbl_desc {
                    if lbl_path.name() == target_name {
                        selected = Some((*label).clone());
                        break;
                    }
                }
            }
        }

        // Try lookup_label_by_expected_type BEFORE the leaf-name fallback.
        // This correctly resolves labels like `children` to `React.Context.props`
        // instead of a local `props` type that happens to share the leaf name.
        if selected.is_none() {
            selected = lookup_label_by_expected_type(lookup_name, record_ty, env, pers_env, ctx);
        }

        // Final fallback: compare leaf names (ignoring compiler-introduced `!` suffixes
        // on local aliases like `sprite!`) to recover the concrete record family.
        if selected.is_none() {
            let target_leaf = target_path.last().trim_end_matches('!');
            for label in all_labels.iter().rev() {
                let lbl_ty = ctx.repr(label.lbl_res);
                let lbl_desc = ctx.get_desc(lbl_ty);
                if let TypeDesc::Tconstr { path: lbl_path, .. } = &*lbl_desc {
                    if lbl_path.last().trim_end_matches('!') == target_leaf {
                        selected = Some((*label).clone());
                        break;
                    }
                }
            }
        }
    }

    // Fall back to the most recent label (last in the list)
    if selected.is_none() {
        selected = lookup_label_by_expected_type(lookup_name, record_ty, env, pers_env, ctx);
    }

    if selected.is_none() {
        selected = all_labels.last().map(|l| (*l).clone());
    }

    if let Some(override_name) = override_name {
        if let Some(label) = selected.as_mut() {
            label.lbl_name = override_name;
        }
    }

    if std::env::var_os("RUST_DEBUG_LABEL_INTL").is_some()
        && matches!(label_name, "compactDisplay" | "currency" | "useGrouping")
    {
        let target = opath.as_ref().map(|p| p.name()).unwrap_or_else(|| "<none>".to_string());
        if let Some(label) = selected.as_ref() {
            let lbl_res = ctx.repr(label.lbl_res);
            let lbl_arg = ctx.repr(label.lbl_arg);
            let lbl_res_path = {
                let d = ctx.get_desc(lbl_res);
                match &*d {
                    TypeDesc::Tconstr { path, .. } => path.name(),
                    _ => format!("ty#{}", lbl_res.0),
                }
            };
            let lbl_arg_path = {
                let d = ctx.get_desc(lbl_arg);
                match &*d {
                    TypeDesc::Tconstr { path, args, .. } => {
                        if path.name() == "option" && args.len() == 1 {
                            let a = ctx.repr(args[0]);
                            let ad = ctx.get_desc(a);
                            match &*ad {
                                TypeDesc::Tconstr { path, .. } => format!("option<{}>", path.name()),
                                _ => format!("option<ty#{}>", a.0),
                            }
                        } else {
                            path.name()
                        }
                    }
                    _ => format!("ty#{}", lbl_arg.0),
                }
            };
            eprintln!(
                "[label-intl] name={} target={} lbl_res={} lbl_arg={}",
                label_name, target, lbl_res_path, lbl_arg_path
            );
        } else {
            eprintln!("[label-intl] name={} target={} selected=<none>", label_name, target);
        }
    }

    selected
}

/// Type-directed constructor disambiguation.
///
/// When a constructor like `A` is used without qualification and is not found
/// in the local env, look at the expected type to find which type defines it.
/// For example, if the expected type is `M.t` and `M.t` is defined as `A | B(int)`,
/// we can resolve the unqualified `A` constructor.
fn qualify_module_local_type_paths_in_place<'a>(
    ctx: &'a crate::types::context::TypeContext<'a>,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ty: TypeExprRef,
    module_access_path: &Path,
    visited: &mut HashSet<TypeExprRef>,
) {
    use crate::types::type_expr::RowField;
    use crate::types::ModuleType;

    fn rewrite_path_prefix(path: &Path, old_prefix: &Path, new_prefix: &Path) -> Option<Path> {
        if path.same(old_prefix) {
            return Some(new_prefix.clone());
        }
        match path {
            Path::Pdot(prefix, name, pos) => rewrite_path_prefix(prefix, old_prefix, new_prefix)
                .map(|rewritten_prefix| Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)),
            _ => None,
        }
    }

    fn rewrite_flattened_head_prefix(path: &Path, flat_head: &str, new_prefix: &Path) -> Option<Path> {
        match path {
            Path::Pident(id) if id.name() == flat_head => Some(new_prefix.clone()),
            Path::Pdot(prefix, name, pos) => rewrite_flattened_head_prefix(prefix, flat_head, new_prefix)
                .map(|rewritten_prefix| Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)),
            _ => None,
        }
    }

    fn flatten_alias_head(path: &Path) -> Option<String> {
        let Ok((head, components)) = path.flatten() else {
            return None;
        };
        if components.is_empty() {
            return None;
        }

        let mut flat = head.name().to_string();
        for component in components {
            flat.push('_');
            flat.push_str(component);
        }
        Some(flat)
    }

    fn flattened_alias_heads_from_persistent(
        pers_env: &Option<crate::cmi::persistent_env::PersistentEnv>,
        qualified_path: &Path,
    ) -> Vec<String> {
        let Some(pers) = pers_env.as_ref() else {
            return Vec::new();
        };
        pers.flattened_alias_heads_for_path(qualified_path)
    }

    fn rewrite_with_flattened_heads(
        path: &Path,
        alias_path: &Path,
        module_access_path: &Path,
        pers_env: &Option<crate::cmi::persistent_env::PersistentEnv>,
    ) -> Option<Path> {
        let mut flat_heads = Vec::new();
        if let Some(flat) = flatten_alias_head(alias_path) {
            flat_heads.push(flat);
        }
        for flat in flattened_alias_heads_from_persistent(pers_env, alias_path) {
            if !flat_heads.iter().any(|existing| existing == &flat) {
                flat_heads.push(flat);
            }
        }

        for flat_head in flat_heads {
            let rewritten = rewrite_flattened_head_prefix(path, &flat_head, module_access_path);
            if rewritten.is_some() {
                return rewritten;
            }
        }
        None
    }

    let repr = ctx.repr(ty);
    if !visited.insert(repr) {
        return;
    }

    let desc = ctx.get_desc(repr).clone();
    match desc {
        TypeDesc::Tconstr { path, args, abbrev } => {
            for arg in &args {
                qualify_module_local_type_paths_in_place(
                    ctx,
                    env,
                    pers_env,
                    *arg,
                    module_access_path,
                    visited,
                );
            }
            let mut rewritten_path: Option<Path> = None;

            if let Path::Pident(module_id) = module_access_path {
                if let Ok(md) = env.find_module(module_id.name()) {
                    if let ModuleType::MtyAlias(_, alias_target) = &md.md_type {
                        let normalized_alias_target = env.normalize_path(alias_target);
                        rewritten_path = rewrite_path_prefix(&path, alias_target, module_access_path);
                        if rewritten_path.is_none() {
                            rewritten_path = rewrite_with_flattened_heads(
                                &path,
                                alias_target,
                                module_access_path,
                                pers_env,
                            );
                        }
                        if rewritten_path.is_none() && !normalized_alias_target.same(alias_target) {
                            rewritten_path = rewrite_with_flattened_heads(
                                &path,
                                &normalized_alias_target,
                                module_access_path,
                                pers_env,
                            );
                        }
                    }
                }
            }

            if rewritten_path.is_none() {
                if let Path::Pident(id) = &path {
                    let candidate = Path::pdot(module_access_path.clone(), id.name());
                    if lookup_type_decl_for_path(&candidate, env, pers_env, ctx).is_some() {
                        rewritten_path = Some(candidate);
                    }
                }
            }

            if let Some(rewritten) = rewritten_path {
                if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some()
                    && (path.last() == "t" || rewritten.last() == "t")
                {
                    eprintln!(
                        "[qualify-path] from={} module={} rewritten={}",
                        path.name(),
                        module_access_path.name(),
                        rewritten.name()
                    );
                }
                ctx.set_desc(
                    repr,
                    TypeDesc::Tconstr {
                        path: rewritten,
                        args,
                        abbrev,
                    },
                );
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                arg.typ,
                module_access_path,
                visited,
            );
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                ret,
                module_access_path,
                visited,
            );
        }
        TypeDesc::Ttuple(types) => {
            for item in &types {
                qualify_module_local_type_paths_in_place(
                    ctx,
                    env,
                    pers_env,
                    *item,
                    module_access_path,
                    visited,
                );
            }
        }
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                target,
                module_access_path,
                visited,
            );
        }
        TypeDesc::Tobject { fields, name } => {
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                fields,
                module_access_path,
                visited,
            );
            if let Some((_, args)) = name {
                for item in &args {
                    qualify_module_local_type_paths_in_place(
                        ctx,
                        env,
                        pers_env,
                        *item,
                        module_access_path,
                        visited,
                    );
                }
            }
        }
        TypeDesc::Tfield {
            typ, rest, ..
        } => {
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                typ,
                module_access_path,
                visited,
            );
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                rest,
                module_access_path,
                visited,
            );
        }
        TypeDesc::Tvariant(row) => {
            for (_label, field) in &row.row_fields {
                match field {
                    RowField::Rpresent(Some(ty)) => {
                        qualify_module_local_type_paths_in_place(
                            ctx,
                            env,
                            pers_env,
                            *ty,
                            module_access_path,
                            visited,
                        );
                    }
                    RowField::Reither { types, .. } => {
                        for ty in types {
                            qualify_module_local_type_paths_in_place(
                                ctx,
                                env,
                                pers_env,
                                *ty,
                                module_access_path,
                                visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                row.row_more,
                module_access_path,
                visited,
            );
            if let Some((_, args)) = &row.row_name {
                for item in args {
                    qualify_module_local_type_paths_in_place(
                        ctx,
                        env,
                        pers_env,
                        *item,
                        module_access_path,
                        visited,
                    );
                }
            }
        }
        TypeDesc::Tpoly { body, vars } => {
            qualify_module_local_type_paths_in_place(
                ctx,
                env,
                pers_env,
                body,
                module_access_path,
                visited,
            );
            for var in &vars {
                qualify_module_local_type_paths_in_place(
                    ctx,
                    env,
                    pers_env,
                    *var,
                    module_access_path,
                    visited,
                );
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for item in &args {
                qualify_module_local_type_paths_in_place(
                    ctx,
                    env,
                    pers_env,
                    *item,
                    module_access_path,
                    visited,
                );
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn lookup_constructor_by_expected_type<'b>(
    cstr_name: &str,
    expected_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'b crate::types::context::TypeContext<'b>,
) -> Option<(Path, crate::types::decl::ConstructorDescription)> {
    // Match OCaml's disambiguation behavior: first expand expected type aliases
    // (extract_concrete_variant), then inspect constructors on the concrete path.
    let type_path = extract_variant_type_path_from_expected_with_persistent_env(
        expected_ty,
        env,
        pers_env,
        ctx,
    )?;

    let Some((resolved_type_path, concrete_type_decl)) =
        resolve_variant_decl_for_path(&type_path, env, pers_env, ctx)
    else {
        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
            eprintln!(
                "[lookup-cstr-path] cstr={} type_path={} variant-decl=<none>",
                cstr_name,
                type_path.name(),
            );
        }
        return None;
    };
    // Prefer declaration-carried canonical path (e.g. opened `t` -> `J.t`)
    // so constructor result heads match OCaml's qualified paths.
    let concrete_type_path = match concrete_type_decl.type_path.as_ref() {
        // Keep qualified expected path (M.t) when the declaration carries only
        // a local self path (`t`), mirroring OCaml constructor result heads.
        Some(Path::Pident(local_id))
            if matches!(&resolved_type_path, Path::Pdot(_, type_name, _) if local_id.name() == type_name.as_str()) =>
        {
            resolved_type_path.clone()
        }
        // Prefer the expected qualified head when declaration path is a
        // canonical/module-alias equivalent.
        Some(path)
            if matches!(&resolved_type_path, Path::Pdot(..))
                && !path.same(&resolved_type_path)
                && compare_type_paths_for_disambiguation(
                    &resolved_type_path,
                    path,
                    env,
                    pers_env,
                    ctx,
                ) =>
        {
            resolved_type_path.clone()
        }
        Some(path) => path.clone(),
        None => resolved_type_path.clone(),
    };
    if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some() {
        if concrete_type_path.last() == "t"
            || cstr_name == "JSONObject"
            || cstr_name == "JSONArray"
            || cstr_name == "Update"
        {
            let decl_path = concrete_type_decl
                .type_path
                .as_ref()
                .map(|p| p.name())
                .unwrap_or_else(|| "<none>".to_string());
            eprintln!(
                "[lookup-cstr-path] cstr={} type_path={} decl.type_path={} concrete={}",
                cstr_name,
                type_path.name(),
                decl_path,
                concrete_type_path.name()
            );
        }
    }

    // Check if it's a variant type with a matching constructor
    if let crate::types::TypeKind::TypeVariant(ref constrs) = concrete_type_decl.type_kind {
        if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some()
            && (cstr_name == "Custom"
                || cstr_name == "JSONObject"
                || cstr_name == "JSONArray"
                || cstr_name == "Update")
        {
            let sample = constrs
                .iter()
                .take(16)
                .map(|c| c.cd_id.name().to_string())
                .collect::<Vec<_>>()
                .join(",");
            let has_exact = constrs.iter().any(|c| c.cd_id.name() == cstr_name);
            let has_lower = constrs
                .iter()
                .any(|c| c.cd_id.name().eq_ignore_ascii_case(cstr_name));
            eprintln!(
                "[lookup-cstr-variant] cstr={} path={} count={} has_exact={} has_casefold={} sample=[{}]",
                cstr_name,
                concrete_type_path.name(),
                constrs.len(),
                has_exact,
                has_lower,
                sample
            );
        }
        let num_consts = constrs.iter()
            .filter(|c| matches!(c.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && c.cd_res.is_none())
            .count() as i32;
        let num_nonconsts = constrs.len() as i32 - num_consts;
        let mut const_idx = 0i32;
        let mut block_idx = 0i32;
        for cd in constrs {
            let is_constant = matches!(cd.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty())
                && cd.cd_res.is_none();
            if cd.cd_id.name() == cstr_name {
                let mut inst_cache = HashMap::new();
                let tag = if is_constant {
                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                } else {
                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                };
                let module_access_path = concrete_type_path.parent();
                let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
                    crate::types::ConstructorArguments::CstrTuple(args) => {
                        let mut copied_args = Vec::with_capacity(args.len());
                        for arg in args {
                            let copied =
                                crate::types::ctype::copy_type_deep(ctx, *arg, &mut inst_cache);
                            if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some()
                                && (cstr_name == "JSONObject" || cstr_name == "JSONArray")
                            {
                                let copied_repr = ctx.repr(copied);
                                let copied_desc = ctx.get_desc(copied_repr);
                                let copied_head = match &*copied_desc {
                                    TypeDesc::Tconstr { path, .. } => path.name(),
                                    _ => format!("ty#{}", copied_repr.0),
                                };
                                eprintln!(
                                    "[lookup-cstr-arg] stage=before cstr={} module={} arg={} head={}",
                                    cstr_name,
                                    module_access_path
                                        .as_ref()
                                        .map(|p| p.name())
                                        .unwrap_or_else(|| "<none>".to_string()),
                                    copied_repr.0,
                                    copied_head
                                );
                            }
                            if let Some(module_path) = module_access_path.as_ref() {
                                let mut visited = HashSet::new();
                                qualify_module_local_type_paths_in_place(
                                    ctx,
                                    env,
                                    pers_env,
                                    copied,
                                    module_path,
                                    &mut visited,
                                );
                            }
                            if std::env::var_os("RUST_DEBUG_LOOKUP_CSTR_PATH").is_some()
                                && (cstr_name == "JSONObject" || cstr_name == "JSONArray")
                            {
                                let copied_repr = ctx.repr(copied);
                                let copied_desc = ctx.get_desc(copied_repr);
                                let copied_head = match &*copied_desc {
                                    TypeDesc::Tconstr { path, .. } => path.name(),
                                    _ => format!("ty#{}", copied_repr.0),
                                };
                                eprintln!(
                                    "[lookup-cstr-arg] stage=after cstr={} module={} arg={} head={}",
                                    cstr_name,
                                    module_access_path
                                        .as_ref()
                                        .map(|p| p.name())
                                        .unwrap_or_else(|| "<none>".to_string()),
                                    copied_repr.0,
                                    copied_head
                                );
                            }
                            copied_args.push(copied);
                        }
                        (copied_args, args.len() as i32, None)
                    }
                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                        let copied_labels: Vec<crate::types::decl::LabelDeclaration> = labels
                            .iter()
                            .map(|label| {
                                let mut copied = label.clone();
                                copied.ld_type = crate::types::ctype::copy_type_deep(
                                    ctx,
                                    label.ld_type,
                                    &mut inst_cache,
                                );
                                if let Some(module_path) = module_access_path.as_ref() {
                                    let mut visited = HashSet::new();
                                    qualify_module_local_type_paths_in_place(
                                        ctx,
                                        env,
                                        pers_env,
                                        copied.ld_type,
                                        module_path,
                                        &mut visited,
                                    );
                                }
                                copied
                            })
                            .collect();
                        // Use ORIGINAL labels for param detection (deep_occur
                        // needs physical identity between params and label types).
                        // Then deep-copy the detected params using the same cache
                        // so they match the copied labels.
                        let inline_params = inline_record_type_params(
                            ctx,
                            &concrete_type_decl.type_params,
                            labels,
                        )
                        .into_iter()
                        .map(|param| {
                            let copied =
                                crate::types::ctype::copy_type_deep(ctx, param, &mut inst_cache);
                            if let Some(module_path) = module_access_path.as_ref() {
                                let mut visited = HashSet::new();
                                qualify_module_local_type_paths_in_place(
                                    ctx,
                                    env,
                                    pers_env,
                                    copied,
                                    module_path,
                                    &mut visited,
                                );
                            }
                            copied
                        })
                        .collect::<Vec<_>>();
                        let inline_path =
                            Path::pdot(concrete_type_path.clone(), cstr_name.to_string());
                        let inline_constr =
                            ctx.new_generic_constr(inline_path, inline_params.clone());
                        let inline_decl = crate::types::TypeDeclaration {
                            type_params: inline_params.clone(),
                            type_arity: inline_params.len() as i32,
                            type_kind: crate::types::TypeKind::TypeRecord(
                                copied_labels,
                                crate::types::RecordRepresentation::RecordInlined {
                                    tag: block_idx,
                                    name: cstr_name.to_string(),
                                    num_nonconsts,
                                    attrs: cd.cd_attributes.clone(),
                                },
                            ),
                            type_private: concrete_type_decl.type_private,
                            type_manifest: None,
                            type_variance: inline_params
                                .iter()
                                .map(|_| crate::types::variance::Variance::full())
                                .collect(),
                            type_newtype_level: None,
                            type_loc: cd.cd_loc,
                            type_attributes: vec![],
                            type_immediate: false,
                            type_unboxed: crate::types::UnboxedStatus::default(),
                            type_inlined_types: vec![],
                            type_path: None,
                        };
                        (
                            vec![inline_constr],
                            1,
                            Some(Box::new(inline_decl)),
                        )
                    }
                };
                // Use the type path's head ident for the result type
                let cstr_res = if let Some(res) = cd.cd_res {
                    // Match lookup_constructor_in_module + OCaml substitution:
                    // when constructor result is a specialized Tconstr (GADT),
                    // remap the head path to the concrete expected type path,
                    // while preserving copied/shared argument nodes.
                    let res_repr = ctx.repr(res);
                    let res_desc = ctx.get_desc(res_repr);
                    match &*res_desc {
                        crate::types::TypeDesc::Tconstr { args, .. } => {
                            let args = args.clone();
                            drop(res_desc);
                            let mapped_args = args
                                .iter()
                                .map(|arg| {
                                    let copied = crate::types::ctype::copy_type_deep(
                                        ctx,
                                        *arg,
                                        &mut inst_cache,
                                    );
                                    if let Some(module_path) = module_access_path.as_ref() {
                                        let mut visited = HashSet::new();
                                        qualify_module_local_type_paths_in_place(
                                            ctx,
                                            env,
                                            pers_env,
                                            copied,
                                            module_path,
                                            &mut visited,
                                        );
                                    }
                                    copied
                                })
                                .collect();
                            ctx.new_generic_constr(concrete_type_path.clone(), mapped_args)
                        }
                        _ => {
                            drop(res_desc);
                            let copied =
                                crate::types::ctype::copy_type_deep(ctx, res, &mut inst_cache);
                            if let Some(module_path) = module_access_path.as_ref() {
                                let mut visited = HashSet::new();
                                qualify_module_local_type_paths_in_place(
                                    ctx,
                                    env,
                                    pers_env,
                                    copied,
                                    module_path,
                                    &mut visited,
                                );
                            }
                            copied
                        }
                    }
                } else {
                    let result_params = concrete_type_decl
                        .type_params
                        .iter()
                        .map(|param| {
                            let copied =
                                crate::types::ctype::copy_type_deep(ctx, *param, &mut inst_cache);
                            if let Some(module_path) = module_access_path.as_ref() {
                                let mut visited = HashSet::new();
                                qualify_module_local_type_paths_in_place(
                                    ctx,
                                    env,
                                    pers_env,
                                    copied,
                                    module_path,
                                    &mut visited,
                                );
                            }
                            copied
                        })
                        .collect();
                    ctx.new_generic_constr(concrete_type_path.clone(), result_params)
                };
                let desc = crate::types::decl::ConstructorDescription {
                    cstr_name: cstr_name.to_string(),
                    cstr_res,
                    cstr_existentials: vec![],
                    cstr_args,
                    cstr_arity,
                    cstr_tag: tag,
                    cstr_consts: num_consts,
                    cstr_nonconsts: num_nonconsts,
                    cstr_generalized: cd.cd_res.is_some(),
                    cstr_private: concrete_type_decl.type_private,
                    cstr_loc: cd.cd_loc,
                    cstr_attributes: cd.cd_attributes.clone(),
                    cstr_inlined,
                };
                let path = Path::pident(Ident::create_persistent(cstr_name));
                return Some((path, desc));
            }
            if is_constant {
                const_idx += 1;
            } else {
                block_idx += 1;
            }
        }
    }
    None
}

fn strengthen_type_decl_for_module_access_path<'a>(
    ctx: &'a crate::types::context::TypeContext<'a>,
    module_access_path: &Path,
    id: &Ident,
    decl: &crate::types::decl::TypeDeclaration,
) -> crate::types::decl::TypeDeclaration {
    // Match OCaml mtype.ml strengthen_sig:
    // keep existing manifests for public types and private record/variant
    // types; otherwise attach a self-manifest alias for this access path.
    let keep_manifest = matches!(
        (&decl.type_manifest, decl.type_private, &decl.type_kind),
        (Some(_), crate::types::PrivateFlag::Public, _)
            | (
                Some(_),
                crate::types::PrivateFlag::Private,
                crate::types::TypeKind::TypeRecord(..) | crate::types::TypeKind::TypeVariant(..),
            )
    );

    if keep_manifest {
        return decl.clone();
    }

    let mut strengthened = decl.clone();
    let manifest_path = Path::pdot(module_access_path.clone(), id.name());
    let manifest = ctx.new_generic_constr(manifest_path, decl.type_params.clone());
    strengthened.type_manifest = Some(manifest);
    if matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract) {
        strengthened.type_private = crate::types::PrivateFlag::Public;
    }
    strengthened
}

fn strengthen_signature_for_module_access_path<'a>(
    ctx: &'a crate::types::context::TypeContext<'a>,
    module_access_path: &Path,
    sig_items: &[crate::types::decl::SignatureItem],
) -> crate::types::decl::Signature {
    sig_items
        .iter()
        .map(|item| match item {
            crate::types::decl::SignatureItem::SigType(id, decl, rec_status) => {
                crate::types::decl::SignatureItem::SigType(
                    id.clone(),
                    strengthen_type_decl_for_module_access_path(ctx, module_access_path, id, decl),
                    *rec_status,
                )
            }
            _ => item.clone(),
        })
        .collect()
}

fn path_cache_key(path: &Path) -> String {
    match path {
        Path::Pident(id) => format!("{}#{}", id.name(), id.stamp()),
        Path::Pdot(parent, name, pos) => {
            format!("{}.{}@{}", path_cache_key(parent), name, pos)
        }
        Path::Papply(p1, p2) => {
            format!("{}({})", path_cache_key(p1), path_cache_key(p2))
        }
    }
}

fn resolve_module_signature_for_path<'a>(
    module_path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<(Path, crate::types::decl::Signature)> {
    use crate::types::decl::SignatureItem;

    // Check module signature cache first
    let module_key = path_cache_key(module_path);
    if let Some(cached) = ctx.find_resolved_module_sig(&module_key) {
        return Some(cached);
    }

    match module_path {
        Path::Pident(id) => {
            if let Ok(md) = env.find_module(id.name()) {
                let (sig, resolved_name) = env.resolve_module_type(&md.md_type, pers_env, ctx)?;
                let access_path = md
                    .md_path
                    .clone()
                    .unwrap_or_else(|| Path::pident(id.clone()));
                let mut sig = copy_lookup_signature_for_subst(&sig, ctx);
                if matches!(
                    &md.md_type,
                    crate::types::decl::ModuleType::MtyAlias(..)
                ) {
                    sig = strengthen_signature_for_module_access_path(ctx, &access_path, &sig);
                }
                if let Some(old_name) = resolved_name {
                    crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                        &sig,
                        &old_name,
                        &access_path,
                        ctx,
                    );
                }
                // Apply alias prefix rewriting for module aliases to nested modules
                // (e.g., module J = Js.Json where target is Pdot).
                // Skip for Pident targets (e.g., Date -> Stdlib_Date) — those are
                // handled by existing substitution mechanisms.
                if let crate::types::decl::ModuleType::MtyAlias(_, ref target) = md.md_type {
                    if matches!(target, Path::Pdot(..)) && !target.same(&access_path) {
                        crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                            &sig, target, &access_path, ctx,
                        );
                    }
                }
                crate::cmi::persistent_env::substitute_type_paths_in_sig(&sig, &access_path, ctx);
                ctx.register_resolved_module_sig(&module_key, access_path.clone(), sig.clone());
                if std::env::var_os("RUST_DEBUG_RESOLVE_MODSIG").is_some()
                    && (module_path.name().contains("NumberFormat")
                        || access_path.name().contains("NumberFormat"))
                {
                    eprintln!(
                        "[resolve-modsig] input={} access={}",
                        module_path.name(),
                        access_path.name()
                    );
                }
                return Some((access_path, sig));
            }
            if let Some(pers) = pers_env.as_mut() {
                if let Some(ps) = pers.find_pers_struct(id.name(), ctx) {
                    let access_path = Path::pident(Ident::create_persistent(id.name()));
                    return Some((access_path, ps.ps_sig.clone()));
                }
            }
            None
        }
        Path::Pdot(parent, submodule_name, _) => {
            let (resolved_parent_path, parent_sig) =
                resolve_module_signature_for_path(parent, env, pers_env, ctx)?;
            for item in &parent_sig {
                if let SignatureItem::SigModule(id, md, _) = item {
                    if id.name() == submodule_name.as_str() {
                        let (sig, resolved_name) =
                            env.resolve_module_type(&md.md_type, pers_env, ctx)?;
                        let access_path = md.md_path.clone().unwrap_or_else(|| {
                            Path::pdot(resolved_parent_path.clone(), submodule_name.as_str())
                        });
                        let alias_target = match &md.md_type {
                            crate::types::decl::ModuleType::MtyAlias(_, target) => {
                                if matches!(target, Path::Pdot(..))
                                    && !target.same(&access_path)
                                {
                                    Some(target.clone())
                                } else {
                                    None
                                }
                            }
                            _ => md.md_path.as_ref().and_then(|md_path| {
                                if matches!(md_path, Path::Pdot(..))
                                    && !md_path.same(&access_path)
                                {
                                    Some(md_path.clone())
                                } else {
                                    None
                                }
                            }),
                        };
                        let mut sig = copy_lookup_signature_for_subst(&sig, ctx);
                        if matches!(
                            &md.md_type,
                            crate::types::decl::ModuleType::MtyAlias(..)
                        ) {
                            sig =
                                strengthen_signature_for_module_access_path(ctx, &access_path, &sig);
                        }
                        if let Some(old_name) = resolved_name {
                            crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                                &sig,
                                &old_name,
                                &access_path,
                                ctx,
                            );
                        }
                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                            &sig,
                            &access_path,
                            ctx,
                        );
                        if let Some(ref target) = alias_target {
                            crate::cmi::persistent_env::rewrite_sig_by_path_prefix(
                                &sig,
                                target,
                                &access_path,
                                ctx,
                            );
                        }
                        ctx.register_resolved_module_sig(
                            &module_key,
                            access_path.clone(),
                            sig.clone(),
                        );
                        if std::env::var_os("RUST_DEBUG_RESOLVE_MODSIG").is_some()
                            && (module_path.name().contains("NumberFormat")
                                || access_path.name().contains("NumberFormat"))
                        {
                            eprintln!(
                                "[resolve-modsig] input={} access={}",
                                module_path.name(),
                                access_path.name()
                            );
                        }
                        return Some((access_path, sig));
                    }
                }
            }
            None
        }
        Path::Papply(_, _) => None,
    }
}

/// Look up a type declaration for a given path.
/// Tries env first, then the global type stores.
fn lookup_type_decl_for_path<'a>(
    type_path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::decl::TypeDeclaration> {
    let debug_lookup_options = std::env::var_os("RUST_DEBUG_LOOKUP_OPTIONS").is_some()
        && matches!(type_path.last(), "options" | "compactDisplay" | "currency");
    // Only use env.lookup_type directly for persistent simple identifiers.
    // For stamped local identifiers, prefer exact-ident (stamp) lookup first;
    // name fallback is unsound when many local modules expose `t`.
    if let Path::Pident(_) = type_path {
        let Path::Pident(id) = type_path else {
            unreachable!()
        };

        if id.stamp() != 0 {
            if let Some(decl) = ctx.find_type_decl_by_stamp(id.stamp()) {
                return Some(decl.clone());
            }
            if let Ok(decl) = env.lookup_type_by_ident_strict(id) {
                return Some(decl.clone());
            }
        } else if let Ok(decl) = env.lookup_type(type_path) {
            return Some(decl.clone());
        }
    }

    // Try path-based lookup for Pdot paths
    if let Path::Pdot(parent, type_name, _) = type_path {
        let mut deferred_self_manifest_decl: Option<crate::types::decl::TypeDeclaration> = None;

        // Check resolved-sig cache first to avoid re-creating fresh type copies.
        // This approximates OCaml's components_of_module_maker lazy caching.
        // Uses a separate cache from type_decl_by_path to avoid conflicts with
        // expand_head_once entries which have unqualified paths.
        let path_name = type_path.name();
        let path_key = path_cache_key(type_path);
        if let Some(decl) = ctx.find_resolved_pdot_type(&path_key) {
            if debug_lookup_options {
                eprintln!("[lookup-options] path={} source=resolved_pdot_cache", path_name);
            }
            return Some(decl);
        }

        // Resolve local module head paths using ident-stamp mappings first.
        // Example: `LayoutTransition.t` inside imported signatures where
        // `LayoutTransition` is relative to `Client__AIEdit`.
        if let Path::Pident(parent_id) = parent.as_ref() {
            if parent_id.stamp() != 0 {
                if let Some(mapped_parent) = ctx.find_module_path_by_stamp(parent_id.stamp()) {
                    let mapped_path = Path::pdot(mapped_parent, type_name.as_str());
                    if !mapped_path.same(type_path) {
                        if let Some(decl) =
                            lookup_type_decl_for_path(&mapped_path, env, pers_env, ctx)
                        {
                            ctx.register_resolved_pdot_type(&path_key, decl.clone());
                            return Some(decl);
                        }
                    }
                }
            }
        }

        // Inline-record constructor paths are type paths whose parent is also a type path:
        // `<type_path>.<Constructor>`. Rebuild the synthetic record declaration from
        // the parent variant declaration so label disambiguation can recover field types.
        if let Some(parent_decl) = lookup_type_decl_for_path(parent, env, pers_env, ctx) {
            if let crate::types::TypeKind::TypeVariant(ref constrs) = parent_decl.type_kind {
                let num_consts = constrs
                    .iter()
                    .filter(|c| {
                        matches!(
                            c.cd_args,
                            crate::types::ConstructorArguments::CstrTuple(ref args)
                                if args.is_empty()
                        ) && c.cd_res.is_none()
                    })
                    .count() as i32;
                let num_nonconsts = constrs.len() as i32 - num_consts;
                let mut block_idx = 0i32;
                for cd in constrs {
                    let is_constant = matches!(
                        cd.cd_args,
                        crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()
                    ) && cd.cd_res.is_none();

                    if cd.cd_id.name() == type_name.as_str() {
                        if let crate::types::ConstructorArguments::CstrRecord(labels) = &cd.cd_args
                        {
                            let inline_params = inline_record_type_params(
                                ctx,
                                &parent_decl.type_params,
                                labels,
                            );
                            return Some(crate::types::TypeDeclaration {
                                type_params: inline_params.clone(),
                                type_arity: inline_params.len() as i32,
                                type_kind: crate::types::TypeKind::TypeRecord(
                                    labels.clone(),
                                    crate::types::RecordRepresentation::RecordInlined {
                                        tag: block_idx,
                                        name: type_name.to_string(),
                                        num_nonconsts,
                                        attrs: cd.cd_attributes.clone(),
                                    },
                                ),
                                type_private: parent_decl.type_private,
                                type_manifest: None,
                                type_variance: inline_params
                                    .iter()
                                    .map(|_| crate::types::variance::Variance::full())
                                    .collect(),
                                type_newtype_level: None,
                                type_loc: cd.cd_loc,
                                type_attributes: vec![],
                                type_immediate: false,
                                type_unboxed: crate::types::UnboxedStatus::default(),
                                type_inlined_types: vec![],
                                type_path: None,
                            });
                        }
                    }

                    if !is_constant {
                        block_idx += 1;
                    }
                }
            }
        }

        // Resolve the parent module path through local aliases/signatures,
        // then read the type directly from that resolved signature.
        if let Some((resolved_parent_path, parent_sig)) =
            resolve_module_signature_for_path(parent, env, pers_env, ctx)
        {
            if debug_lookup_options {
                let names = parent_sig
                    .iter()
                    .filter_map(|item| {
                        if let crate::types::decl::SignatureItem::SigType(id, _, _) = item {
                            Some(id.name().to_string())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!(
                    "[lookup-options] path={} parent_sig_types=[{}]",
                    path_name, names
                );
            }
            for item in &parent_sig {
                if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item {
                    if id.name() == type_name.as_str() {
                        let mut decl_with_path = decl.clone();
                        if decl_with_path.type_path.is_none() {
                            decl_with_path.type_path =
                                Some(Path::pdot(resolved_parent_path.clone(), type_name.as_str()));
                        }
                        let self_manifest = decl
                            .type_manifest
                            .and_then(|manifest| {
                                let manifest_desc = ctx.get_desc(ctx.repr(manifest));
                                match &*manifest_desc {
                                    TypeDesc::Tconstr { path, .. } => Some(path.same(type_path)),
                                    _ => None,
                                }
                            })
                            .unwrap_or(false);

                        // Functor-application edge case: substituted signatures can expose
                        // `type t = M.t` self-manifests. Fall back to the module's raw
                        // signature declaration so manifest aliases (for example `Path.t`)
                        // remain visible to variant disambiguation.
                        if self_manifest {
                            if let Path::Pident(parent_id) = parent.as_ref() {
                                if let Ok(md) = env.find_module(parent_id.name()) {
                                    if let crate::types::decl::ModuleType::MtySignature(raw_sig) =
                                        &md.md_type
                                    {
                                        for raw_item in raw_sig {
                                            if let crate::types::decl::SignatureItem::SigType(
                                                raw_id,
                                                raw_decl,
                                                _,
                                            ) = raw_item
                                            {
                                                if raw_id.name() == type_name.as_str() {
                                                    let mut raw_decl = raw_decl.clone();
                                                    if raw_decl.type_path.is_none() {
                                                        raw_decl.type_path = Some(Path::pdot(
                                                            resolved_parent_path.clone(),
                                                            type_name.as_str(),
                                                        ));
                                                    }
                                                    return Some(raw_decl);
                                                }
                                            }
                                        }
                                    }
                                }
                            }

                            // Keep the substituted declaration as a last-resort fallback,
                            // but continue with alias/module resolution first so functor and
                            // module-alias paths can expose their concrete manifest.
                            deferred_self_manifest_decl = Some(decl_with_path);
                            break;
                        }

                        // Cache the resolved decl so subsequent lookups for the same
                        // Pdot path reuse the same type nodes (matching OCaml's
                        // components_of_module_maker lazy caching).
                        ctx.register_resolved_pdot_type(&path_key, decl_with_path.clone());
                        if debug_lookup_options {
                            eprintln!("[lookup-options] path={} source=resolved_parent_sig", path_name);
                        }
                        return Some(decl_with_path);
                    }
                }
            }
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
                        if let Some(decl) =
                            crate::types::ctype::resolve_type_through_modules(ctx, &resolved_path)
                        {
                            return Some(decl);
                        }
                    }
                    ModuleType::MtySignature(sig) => {
                        let module_path = Path::pident(parent_id.clone());
                        let sig = copy_lookup_signature_for_subst(sig, ctx);
                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                            &sig,
                            &module_path,
                            ctx,
                        );
                        for item in &sig {
                            if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item {
                                if id.name() == type_name.as_str() {
                                    let mut decl_with_path = decl.clone();
                                    if decl_with_path.type_path.is_none() {
                                        decl_with_path.type_path =
                                            Some(Path::pdot(module_path.clone(), type_name.as_str()));
                                    }
                                    // Cache for reuse (same as Pdot branch caching)
                                    ctx.register_resolved_pdot_type(
                                        &path_key,
                                        decl_with_path.clone(),
                                    );
                                    return Some(decl_with_path);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Prefer the substituted declaration we just resolved from the parent
        // signature over global path caches when we hit a self-manifest type.
        if let Some(decl) = deferred_self_manifest_decl.take() {
            if debug_lookup_options {
                eprintln!("[lookup-options] path={} source=deferred_self_manifest", path_name);
            }
            return Some(decl);
        }

        // Fall back to direct path lookup only after module-signature resolution.
        // OCaml's Env.components_of_module applies Subst.type_declaration before
        // exposing Sig_type entries; preferring substituted signatures first avoids
        // returning stale unqualified recursive paths (e.g. JSON.t self refs as Pident "t").
        if let Some(decl) = ctx.find_type_decl_by_path(&path_name) {
            let mut decl = decl.clone();
            if decl.type_path.is_none() {
                decl.type_path = Some(type_path.clone());
            }
            if debug_lookup_options {
                eprintln!("[lookup-options] path={} source=type_decl_by_path", path_name);
            }
            return Some(decl);
        }

        // Try resolving through modules (loading CMI files on demand)
        if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, type_path) {
            return Some(decl);
        }

        // Try Stdlib alias patterns as fallback.
        // Prefer dotted `Stdlib.X.t` over flattened `Stdlib_X.t` to match
        // OCaml path shapes in typedtree output when both are available.
        if let Path::Pident(parent_id) = parent.as_ref() {
            let stdlib_path = format!("Stdlib.{}.{}", parent_id.name(), type_name);
            if let Some(decl) = ctx.find_type_decl_by_path(&stdlib_path) {
                return Some(decl.clone());
            }
            let flat_name = format!("Stdlib_{}.{}", parent_id.name(), type_name);
            if let Some(decl) = ctx.find_type_decl_by_path(&flat_name) {
                return Some(decl.clone());
            }
            // Try loading CMI directly by module name
            let direct_path = Path::pdot(
                Path::Pident(Ident::create_persistent(parent_id.name())),
                type_name.as_str(),
            );
            if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, &direct_path)
            {
                return Some(decl);
            }
        }

        if let Some(decl) = deferred_self_manifest_decl {
            return Some(decl);
        }
    }

    // Only fall back to name-based lookup for simple identifiers.
    // For qualified paths (Pdot), a head-name fallback is unsound and can
    // resolve to an unrelated type that happens to share the same leaf name.
    if let Path::Pident(id) = type_path {
        if id.stamp() == 0 {
            if let Some(decl) = ctx.find_type_decl(id.name()) {
                let mut decl = decl.clone();
                if decl.type_path.is_none() {
                    decl.type_path = Some(Path::pident(id.clone()));
                }
                return Some(decl);
            }
        } else if id.name() != "t" {
            // Local/stamped ids can drift across copied signatures.
            // Fall back to current-scope by-name lookup for non-generic names.
            if let Ok(decl) = env.find_type(id.name()) {
                let mut decl = decl.clone();
                if decl.type_path.is_none() {
                    decl.type_path = Some(Path::pident(id.clone()));
                }
                if decl
                    .type_path
                    .as_ref()
                    .is_some_and(|path| path.last() == id.name())
                {
                    return Some(decl);
                }
            }
            if let Some(decl) = ctx.find_type_decl(id.name()) {
                let mut decl = decl.clone();
                if decl.type_path.is_none() {
                    decl.type_path = Some(Path::pident(id.clone()));
                }
                if decl
                    .type_path
                    .as_ref()
                    .is_some_and(|path| path.last() == id.name())
                {
                    return Some(decl);
                }
            }
        }
    }

    None
}

fn resolve_variant_decl_for_path<'a>(
    type_path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<(Path, crate::types::decl::TypeDeclaration)> {
    let mut current = type_path.clone();
    let mut visited = HashSet::new();

    for _ in 0..64 {
        if !visited.insert(current.name()) {
            return None;
        }

        let mut decl = lookup_type_decl_for_path(&current, env, pers_env, ctx)?;
        if decl.type_path.is_none() {
            decl.type_path = Some(current.clone());
        }

        match &decl.type_kind {
            crate::types::TypeKind::TypeVariant(_) => return Some((current, decl)),
            crate::types::TypeKind::TypeAbstract | crate::types::TypeKind::TypeOpen => {
                if let Some(manifest) = decl.type_manifest {
                    let manifest_desc = ctx.get_desc(ctx.repr(manifest));
                    if let TypeDesc::Tconstr { path: next_path, .. } = &*manifest_desc {
                        if !next_path.same(&current) {
                            current = next_path.clone();
                            continue;
                        }
                    }
                }

                if let Some(canonical_path) = decl.type_path.as_ref() {
                    if !canonical_path.same(&current) {
                        current = canonical_path.clone();
                        continue;
                    }
                }
                return None;
            }
            crate::types::TypeKind::TypeRecord(_, _) => return None,
        }
    }

    None
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
    fn test_convert_constant_large_fits_63bit() {
        // Values that fit in 63-bit should be preserved
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("99999999999999999"), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(99999999999999999));
    }

    #[test]
    fn test_convert_constant_overflow_too_large() {
        // Values that don't fit in i64 should still error
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("99999999999999999999999"), None);
        let result = convert_constant(&cst);
        assert!(matches!(result, Err(TypeCoreError::LiteralOverflow(_))));
    }

    #[test]
    fn test_convert_constant_underscores() {
        // 949460645006 fits in 63 bits, should be preserved
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("949_460_645_006"), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(949_460_645_006));
    }

    #[test]
    fn test_convert_constant_hex() {
        // 0xFFFFFFFF = 4294967295, fits in 63 bits
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("0xffff_ffff"), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(4294967295));
    }

    #[test]
    fn test_convert_constant_63bit_wrap() {
        // 4611686018427387904 = 2^62, wraps to -2^62 in 63-bit
        let cst = crate::parser::ast::Constant::Integer(Cow::Borrowed("4611686018427387904"), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(-4611686018427387904));
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
    fn test_convert_constant_bigint_removes_underscores() {
        let cst = crate::parser::ast::Constant::Integer(Cow::Owned("01_000_000".to_string()), Some('n'));
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::BigInt(true, d) if d == "1000000"));
    }

    #[test]
    fn test_convert_constant_bigint_preserves_non_decimal_heads() {
        let cst = crate::parser::ast::Constant::Integer(Cow::Owned("00x1_000_000".to_string()), Some('n'));
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::BigInt(true, d) if d == "00x1000000"));
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

    #[test]
    fn test_ocaml_hashtbl_hash_string_matches_ocaml() {
        assert_eq!(ocaml_hashtbl_hash_string("_self"), 448_023_825);
        assert_eq!(ocaml_hashtbl_hash_string("_blank"), 482_879_870);
        assert_eq!(ocaml_hashtbl_hash_string("_parent"), 914_286_090);
        assert_eq!(ocaml_hashtbl_hash_string("_top"), 861_764_747);
        assert_eq!(ocaml_hashtbl_hash_string("foo"), 763_646_369);
        assert_eq!(ocaml_hashtbl_hash_string("Some"), 26_923_831);
    }

    #[test]
    fn test_ocaml_hashtbl_fold_order_matches_ocaml() {
        let labels = vec![
            "_self".to_string(),
            "_blank".to_string(),
            "_parent".to_string(),
            "_top".to_string(),
        ];
        assert_eq!(
            ocaml_hashtbl_fold_order(&labels),
            vec![
                "_parent".to_string(),
                "_top".to_string(),
                "_self".to_string(),
                "_blank".to_string()
            ]
        );
    }

    #[test]
    fn test_ocaml_hashtbl_fold_order_pair_int_string() {
        // bs_unwrap_test: [#Pair(string, int) | #Int(int) | #String(string)]
        // OCaml output order: Pair, String, Int
        let labels = vec![
            "Pair".to_string(),
            "Int".to_string(),
            "String".to_string(),
        ];
        let result = ocaml_hashtbl_fold_order(&labels);
        assert_eq!(
            result,
            vec![
                "Pair".to_string(),
                "String".to_string(),
                "Int".to_string(),
            ]
        );
    }
}
