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
    ArgLabel, Expression as ParsedExpression, Pattern as ParsedPattern, RecFlag,
};
use crate::parser::longident::Longident;
use crate::types::typedtree::{
    ArrowArg, Constant, EnvRef, Expression, ExpressionDesc, Pattern, PatternDesc, ValueBinding,
};
use crate::types::{
    Env, Path, TypeContext, TypeDesc, TypeError, TypeExprRef, UnifyState, ValueDescription,
};
use std::collections::{HashMap, HashSet};

const DICT_PATTERN_ATTRIBUTE: &str = "res.dictPattern";
const DICT_MAGIC_FIELD_NAME: &str = "dictValuesType";
const DICT_TYPE_NAME: &str = "dict";
const PAT_VARIANT_SPREAD_ATTRIBUTE: &str = "res.patVariantSpread";

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
    path.last() == DICT_TYPE_NAME
}

fn resolve_package_modtype_path(lid: &Longident, env: &Env, arena: &ParseArena) -> Path {
    match lid {
        Longident::Lident(name) => {
            let name_str = arena.get_string(*name);
            if let Ok((id, _)) = env.find_modtype_with_id(name_str) {
                Path::pident(id.clone())
            } else {
                Path::pident(Ident::create_persistent(name_str))
            }
        }
        Longident::Ldot(prefix, name) => Path::pdot(
            crate::types::typemod::path_from_longident(prefix, |idx| arena.get_string(idx)),
            arena.get_string(*name),
        ),
        Longident::Lapply(functor, arg) => Path::papply(
            crate::types::typemod::path_from_longident(functor, |idx| arena.get_string(idx)),
            crate::types::typemod::path_from_longident(arg, |idx| arena.get_string(idx)),
        ),
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
    /// Recursion depth for currently-typed `let rec` groups.
    /// Used for recursive polymorphic-variant payload fallback.
    pub recursive_let_depth: usize,
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
            type_variables: HashMap::new(),
            recursive_let_depth: 0,
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
    // Reset used_variables for each top-level type translation (matches OCaml's transl_simple_type)
    tctx.used_variables.clear();
    let translated = transl_type_inner(tctx, env, styp)?;

    // Match OCaml typetexp `globalize_used_variables`: link variables seen in
    // this type expression back to declaration-bound variables when present.
    if !tctx.type_variables.is_empty() && !tctx.used_variables.is_empty() {
        let used_vars: Vec<(String, TypeExprRef)> = tctx
            .used_variables
            .iter()
            .map(|(name, ty)| (name.clone(), *ty))
            .collect();
        for (name, used_ty) in used_vars {
            if let Some(bound_ty) = tctx.type_variables.get(&name).copied() {
                let _ =
                    crate::types::unify(tctx.type_ctx, &mut tctx.unify_state, used_ty, bound_ty);
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
            match env.find_type_with_id(name) {
                Ok((id, decl)) => {
                    let path = decl
                        .type_path
                        .clone()
                        .unwrap_or_else(|| Path::pident(id.clone()));
                    (path, Some(decl.clone()))
                }
                Err(_) => (Path::pident(Ident::create_persistent(name)), None),
            }
        }
        Longident::Ldot(prefix, name_idx) => {
            let type_name = tctx.arena.get_string(*name_idx);
            if let Some((mod_path, sig)) = env.resolve_module_lid_raw(
                prefix,
                tctx.arena,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            ) {
                for item in &sig {
                    if let SignatureItem::SigType(id, decl, _) = item {
                        if id.name() == type_name {
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
            // OCaml treats locally abstract type binders (`(type t, ...)`) as
            // abstract type constructors in env rather than ordinary variables.
            // When such a type is in scope, resolve `t` to `Tconstr(Pident t,[])`.
            let ty = if let Ok((id, decl)) = env.find_type_with_id(name) {
                if decl.type_newtype_level.is_some() {
                    let path = decl
                        .type_path
                        .clone()
                        .unwrap_or_else(|| Path::pident(id.clone()));
                    ctx.new_constr(path, vec![])
                } else if let Some(&existing) = tctx.used_variables.get(name) {
                    existing
                } else {
                    let v = ctx.new_var(Some(name.clone()));
                    tctx.used_variables.insert(name.clone(), v);
                    v
                }
            } else if let Some(&existing) = tctx.used_variables.get(name) {
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
            let longident = tctx.arena.get_longident(lid.txt);
            let (path, type_decl) = resolve_type_constructor_path(tctx, env, longident);

            let mut parsed_args = args.clone();
            if let Some(decl) = &type_decl {
                // Match OCaml Typetexp: `t<_>` for arity>1 expands `_` to all params.
                if parsed_args.len() == 1
                    && matches!(parsed_args[0].ptyp_desc, CTD::Ptyp_any)
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
            let var_names: Vec<String> = vars
                .iter()
                .map(|v| tctx.arena.get_string(v.txt).to_string())
                .collect();

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
                        let (inherit_ctyp, inherit_ty) =
                            transl_type_inner(tctx, env, inherit_type)?;

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
                                        field_entries.push((name.clone(), *typ));
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

        CTD::Ptyp_variant(rows, closed, labels) => {
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
                            let (arg_ctyp, arg_ty) = transl_type_inner(tctx, env, arg)?;
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
                                link: crate::types::type_expr::RowFieldRef::null(),
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
                            label.txt.clone(),
                            row_field,
                        );

                        let typed_label = Located {
                            txt: label.txt.clone(),
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
                        let (inherit_ctyp, inherit_ty) =
                            transl_type_inner(tctx, env, inherit_type)?;

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
                                                link: crate::types::type_expr::RowFieldRef::null(),
                                            }
                                        }
                                        crate::types::type_expr::RowField::Rpresent(None) => {
                                            crate::types::type_expr::RowField::Reither {
                                                constant: true,
                                                types: vec![],
                                                matched: false,
                                                link: crate::types::type_expr::RowFieldRef::null(),
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
                            rf_loc: inherit_type.ptyp_loc.clone(),
                            rf_attributes: vec![],
                        });
                    }
                }
            }

            let ordered_labels = if styp.ptyp_attributes.is_empty() {
                ocaml_hashtbl_fold_order(&row_field_insertions)
            } else {
                row_field_insertions
            };
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
                ctyp_desc: TypedCoreTypeDesc::Ttyp_variant(typed_rows, *closed, labels.clone()),
                ctyp_type: variant_ty,
                ctyp_env: EnvRef(0),
                ctyp_loc: loc,
                ctyp_attributes: styp.ptyp_attributes.clone(),
            };
            Ok((ctyp, variant_ty))
        }

        CTD::Ptyp_package((mod_lid, constraints)) => {
            // Package type: (module S with type t = T)
            let longident = tctx.resolve_lid(mod_lid.txt);
            let pack_path = resolve_package_modtype_path(longident, env, tctx.arena);

            let mut typed_fields = Vec::with_capacity(constraints.len());
            let mut lids = Vec::with_capacity(constraints.len());
            let mut args = Vec::with_capacity(constraints.len());
            for (field_lid, field_ty) in constraints {
                let (typed_field_ty, field_type_ref) = transl_type_inner(tctx, env, field_ty)?;
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

fn extract_type_from_pat_variant_spread(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    lid: &Located<LidentIdx>,
) -> TypeCoreResult<(Path, Vec<crate::types::ConstructorDeclaration>, TypeExprRef)> {
    let ctx = tctx.type_ctx;
    let lid_txt = tctx.resolve_lid(lid.txt).clone();
    let spread_ct = crate::parser::ast::CoreType {
        ptyp_desc: crate::parser::ast::CoreTypeDesc::Ptyp_constr(*lid, vec![]),
        ptyp_loc: lid.loc,
        ptyp_attributes: vec![],
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
    let crate::parser::ast::PatternDesc::Ppat_type(lident) = &pat.ppat_desc else {
        return Ok(None);
    };
    if !has_res_pat_variant_spread_attribute(tctx.arena, &pat.ppat_attributes) {
        return Ok(None);
    }

    let (_path, constructors, spread_ty) = extract_type_from_pat_variant_spread(tctx, env, lident)?;
    let mut synthetic_patterns = Vec::with_capacity(constructors.len());
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
            _ => Some(Box::new(ParsedPattern {
                ppat_desc: crate::parser::ast::PatternDesc::Ppat_any,
                ppat_loc: LocIdx::none(),
                ppat_attributes: vec![],
            })),
        };
        synthetic_patterns.push(ParsedPattern {
            ppat_desc: crate::parser::ast::PatternDesc::Ppat_construct(cstr_lid, cstr_arg),
            ppat_loc: lident.loc,
            ppat_attributes: vec![],
        });
    }

    synthetic_patterns.reverse();
    let expanded_pattern = match synthetic_patterns
        .into_iter()
        .reduce(|lhs, rhs| ParsedPattern {
            ppat_desc: crate::parser::ast::PatternDesc::Ppat_or(Box::new(lhs), Box::new(rhs)),
            ppat_loc: pat.ppat_loc,
            ppat_attributes: vec![],
        }) {
        Some(pattern) => pattern,
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
    if !matches!(pat.ppat_desc, crate::parser::ast::PatternDesc::Ppat_type(_)) {
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

    let expanded_pat = maybe_expand_variant_spread_in_pattern(tctx, env, pat, expected_ty)?;
    let pat = expanded_pat.as_ref().unwrap_or(pat);
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
            let (expanded_inner, override_type_from_variant_spread) =
                if matches!(inner_pat.ppat_desc, PD::Ppat_type(_))
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

            // Build the as-type
            let ty_var = match override_type_from_variant_spread {
                Some(ty) => ty,
                None => build_as_type(tctx, env, &typed_inner)?,
            };

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

        PD::Ppat_unpack(name) => {
            // Module unpack pattern: module(M)
            let id = state.enter_variable(loc, name, expected_ty, false, true, tctx.arena)?;
            let typed_pat = Pattern::new(
                PatternDesc::Tpat_var(id, convert_located_stridx(name, tctx.arena)),
                loc,
                expected_ty,
                EnvRef(0),
                vec![],
            );
            Ok(typed_pat.with_pat_extra(
                crate::types::typedtree::PatExtra::Tpat_unpack,
                loc,
                pat.ppat_attributes.clone(),
            ))
        }

        // Remaining patterns - return wildcard for now
        PD::Ppat_type(_) | PD::Ppat_extension(_) => {
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
            let is_unresolved_local_ident = args.is_empty()
                && matches!(path, Path::Pident(_))
                && env.lookup_type(path).is_err();
            if args.is_empty()
                && (is_local_abstract_type_path(ctx, env, path) || is_unresolved_local_ident)
            {
                let fresh = ctx.new_var(Some(path.head_name().to_string()));
                cache.insert(ty, fresh);
                return fresh;
            }
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
        if let Some((path, desc)) =
            lookup_predef_option_constructor(lid_txt, tctx.arena, env, tctx.type_ctx)
        {
            (desc, path)
        } else {
        // Module-qualified: use direct lookup
        match lookup_constructor_in_module(
            lid_txt,
            tctx.arena,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        ) {
            Some((path, desc)) => (desc, path),
            None => match env.find_constructor(&lid_name) {
                Ok(desc) => (
                    desc.clone(),
                    Path::pident(Ident::create_persistent(&lid_name)),
                ),
                Err(_) => return Err(TypeCoreError::NotAVariantType(lid_txt.clone())),
            },
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
                link: crate::types::type_expr::RowFieldRef::null(),
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
    let has_dict_pattern_attr = has_dict_pattern_attribute(tctx.arena, &pat.ppat_attributes);

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

    // Type check each field pattern
    let mut typed_fields = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let field_name = tctx.longident_last_name(tctx.resolve_lid(field.lid.txt));

        // Create fresh type variable for the field
        let field_ty = ctx.new_var(None);

        // Try to look up the label from the environment for type info
        let label_desc = if let Some(env_label) = disambiguate_label(
            &field_name,
            record_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        ) {
                let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
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
        let typed_pat = if label_desc.lbl_optional && !field.opt {
            // field_ty is option<T> — extract T to type-check the inner pattern
            let inner_ty =
                crate::types::ctype::extract_option_type(ctx, field_ty).unwrap_or(field_ty);
            let typed_inner = type_pattern_inner(tctx, env, &field.pat, inner_ty, mode, state, 0)?;
            // Wrap in Tpat_construct("Some", [typed_inner]) with type option<T>
            let some_lid = Located {
                txt: tctx.arena.some_lid(),
                loc: field.pat.ppat_loc,
            };
            let some_cstr = make_some_constructor(ctx, field_ty);
            Pattern::new(
                PatternDesc::Tpat_construct(some_lid, some_cstr, vec![typed_inner]),
                field.pat.ppat_loc,
                field_ty,
                EnvRef(0),
                vec![],
            )
        } else {
            type_pattern_inner(tctx, env, &field.pat, field_ty, mode, state, 0)?
        };
        typed_fields.push((field.lid.clone(), label_desc, typed_pat, field.opt));
    }

    // OCaml unifies the inferred record type with the pattern expected type.
    unify_pattern_types(tctx, loc, record_ty, expected_ty)?;

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
    let (typed_ctype, ctype_ty) = transl_type(tctx, env, core_type)?;
    let var_level = ctx.current_level();
    ctx.end_def();
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
    let typed_inner = match typed_inner.pat_desc.clone() {
        crate::types::typedtree::PatternDesc::Tpat_var(id, name) => {
            let any_pat = Pattern {
                pat_desc: crate::types::typedtree::PatternDesc::Tpat_any,
                pat_attributes: vec![],
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

    match &expr.pexp_desc {
        ED::Pexp_ident(lid) => {
            // Identifier expression
            let longident = tctx.arena.get_longident(lid.txt);
            let (path, desc) = env.lookup_value_by_lid(
                longident,
                tctx.arena,
                &mut tctx.persistent_env,
                tctx.type_ctx,
            )?;

            // Match OCaml `instance` behavior for repeated local monomorphic
            // identifiers: keep non-generic ground constructor nodes by
            // identity so multiple occurrences can share through unification.
            let ty = {
                let source_ty = ctx.repr(desc.val_type);
                let reuse_local_ground = match &path {
                    Path::Pident(id) if !id.is_persistent() => {
                        if ctx.get_level(source_ty) != crate::types::GENERIC_LEVEL {
                            let desc = ctx.get_desc(source_ty);
                            matches!(&*desc, TypeDesc::Tconstr { args, .. } if args.is_empty())
                        } else {
                            false
                        }
                    }
                    _ => false,
                };
                if reuse_local_ground {
                    source_ty
                } else {
                    crate::types::instance(ctx, desc.val_type)
                }
            };

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
            let (typed_bindings, new_env, unpacks) =
                type_let_bindings(tctx, env, *rec_flag, bindings)?;

            // Type check body in extended environment
            let typed_body = type_expect(tctx, &new_env, body, expected_ty, None)?;
            let typed_body =
                wrap_module_unpacks_in_expression(tctx, &new_env, typed_body, &unpacks);
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
                    // OCaml uses rue here: type then-branch as unit, then unify
                    // the whole if-expression with the expected type.
                    let unit_ty = env.type_unit(ctx);
                    let typed_then = type_expect(tctx, env, then_branch, unit_ty, None)?;
                    let then_exp_type = typed_then.exp_type;
                    unify_expression_types(tctx, loc, then_exp_type, expected_ty, context)?;

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
                ExpressionDesc::Texp_construct(_, cd, _) if cd.cstr_name == "false" => expected_ty,
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
            // Match OCaml typecore.ml optional-default rewrite:
            //   fun ?x:(p=default) -> body
            // becomes
            //   fun ?x:*opt* ->
            //     let[@#default] p =
            //       match *opt* with Some *sth* -> *sth* | None -> default
            //     in
            //     body
            if arg_label.is_optional() {
                if let (
                    Some(default_expr),
                    crate::parser::ast::PatternDesc::Ppat_var(_),
                ) = (default.as_ref(), &lhs.ppat_desc)
                {
                    let default_loc = default_expr.pexp_loc;
                    let opt_name = tctx.arena.optional_default_opt_str();
                    let sth_name = tctx.arena.optional_default_sth_str();
                    let opt_lid = tctx.arena.optional_default_opt_lid();
                    let sth_lid = tctx.arena.optional_default_sth_lid();

                    let sloc = {
                        let sloc_start = tctx.arena.loc_start_idx(lhs.ppat_loc);
                        let sloc_end = tctx.arena.loc_end_idx(default_loc);
                        find_loc_idx_by_bounds(tctx.arena, sloc_start, sloc_end)
                            .unwrap_or(lhs.ppat_loc)
                    };

                    let matched_pat = ParsedPattern {
                        ppat_desc: crate::parser::ast::PatternDesc::Ppat_var(Located {
                            txt: sth_name,
                            loc: default_loc,
                        }),
                        ppat_loc: default_loc,
                        ppat_attributes: vec![],
                    };

                    let some_pat = ParsedPattern {
                        ppat_desc: crate::parser::ast::PatternDesc::Ppat_construct(
                            Located {
                                txt: tctx.arena.predef_some_lid(),
                                loc: default_loc,
                            },
                            Some(Box::new(matched_pat)),
                        ),
                        ppat_loc: default_loc,
                        ppat_attributes: vec![],
                    };

                    let none_pat = ParsedPattern {
                        ppat_desc: crate::parser::ast::PatternDesc::Ppat_construct(
                            Located {
                                txt: tctx.arena.predef_none_lid(),
                                loc: default_loc,
                            },
                            None,
                        ),
                        ppat_loc: default_loc,
                        ppat_attributes: vec![],
                    };

                    let some_rhs = ParsedExpression {
                        pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_ident(Located {
                            txt: sth_lid,
                            loc: default_loc,
                        }),
                        pexp_loc: default_loc,
                        pexp_attributes: vec![],
                    };

                    let match_expr = ParsedExpression {
                        pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_match(
                            Box::new(ParsedExpression {
                                pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_ident(
                                    Located {
                                        txt: opt_lid,
                                        loc,
                                    },
                                ),
                                pexp_loc: loc,
                                pexp_attributes: vec![],
                            }),
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
                                    pc_rhs: default_expr.as_ref().clone(),
                                },
                            ],
                        ),
                        pexp_loc: sloc,
                        pexp_attributes: vec![],
                    };

                    let default_attr = (
                        Located::mknoloc(tctx.arena.default_attr_str()),
                        crate::parser::ast::Payload::PStr(vec![]),
                    );

                    let rewritten_body = ParsedExpression {
                        pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_let(
                            RecFlag::Nonrecursive,
                            vec![crate::parser::ast::ValueBinding {
                                pvb_pat: lhs.clone(),
                                pvb_expr: match_expr,
                                pvb_attributes: vec![],
                                pvb_loc: tctx.arena.none_loc(),
                            }],
                            rhs.clone(),
                        ),
                        pexp_loc: loc,
                        pexp_attributes: vec![default_attr],
                    };

                    let opt_param = ParsedPattern {
                        ppat_desc: crate::parser::ast::PatternDesc::Ppat_var(Located {
                            txt: opt_name,
                            loc: sloc,
                        }),
                        ppat_loc: sloc,
                        ppat_attributes: vec![],
                    };

                    return type_function(
                        tctx,
                        env,
                        loc,
                        arg_label,
                        None,
                        &opt_param,
                        &rewritten_body,
                        *arity,
                        *is_async,
                        expected_ty,
                        &expr.pexp_attributes,
                    );
                }
            }

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
            let typed_field = type_field(
                tctx,
                env,
                loc,
                record_expr,
                field_lid,
                &expr.pexp_attributes,
            )?;
            unify_expression_types(tctx, loc, typed_field.exp_type, expected_ty, context)?;
            Ok(typed_field)
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

        ED::Pexp_open(override_flag, lid, body) => {
            // Open expression: M.{ E } or open M; E
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
                context,
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
        Err(_e) => Err(TypeCoreError::ExprTypeClash {
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
    args: &[(ArgLabel, ParsedExpression)],
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
            enforce_optional: bool,
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
        remaining_args: &[(ArgLabel, &ParsedExpression)],
        label_name: &str,
        arena: &ParseArena,
    ) -> Option<usize> {
        remaining_args
            .iter()
            .position(|(label, _)| parser_arg_label_name(label, arena) == label_name)
    }

    fn has_nolabel_arg(remaining_args: &[(ArgLabel, &ParsedExpression)]) -> bool {
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

    // Type check the function
    let funct_ty = ctx.new_var(None);
    let typed_funct = type_expect(tctx, env, funct, funct_ty, None)?;

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
        return result;
    }

    // Match OCaml's use of expand_head when deciding application behavior.
    let mut current_ty = typed_funct.exp_type;
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

    // Match labels by name (OCaml's extract_label) instead of consuming call args strictly
    // left-to-right.
    let mut remaining_args: Vec<(ArgLabel, &ParsedExpression)> = args
        .iter()
        .map(|(label, expr)| (label.clone(), expr))
        .collect();
    let mut pending_args: Vec<PendingApplyArg<'_>> = Vec::new();
    let mut omitted: Vec<(crate::types::ArgLabel, TypeExprRef)> = Vec::new();
    let mut consumed_optional_count = 0usize;
    let mut synthesized_optional_count = 0usize;

    while !remaining_args.is_empty() {
        let expanded_current_ty = crate::types::ctype::expand_head(ctx, env, current_ty);
        if let Some((fn_label, arg_ty, ret_ty)) =
            crate::types::ctype::split_arrow_with_label(ctx, expanded_current_ty)
        {
            let fn_label_name = fn_label.label_name().unwrap_or("");
            if let Some(match_idx) = extract_label_index(&remaining_args, fn_label_name, tctx.arena)
            {
                let (call_label, arg_expr) = remaining_args.remove(match_idx);
                let call_is_optional = call_label.is_optional();
                let effective_arg_ty = if fn_label.is_optional() && !call_is_optional {
                    crate::types::ctype::extract_option_type(ctx, arg_ty).unwrap_or(arg_ty)
                } else {
                    arg_ty
                };

                pending_args.push(PendingApplyArg::Provided {
                    label: apply_arg_label_for_param(&fn_label, &call_label, tctx.arena),
                    expr: arg_expr,
                    expected_ty: effective_arg_ty,
                    enforce_optional: fn_label.is_optional() && !call_is_optional,
                });
                current_ty = ret_ty;
                continue;
            }

            if fn_label.is_optional() && (total_app || has_nolabel_arg(&remaining_args)) {
                consumed_optional_count += 1;
                // OCaml type_application: consumed omitted optional labels still appear
                // in Texp_apply as explicit None arguments at Location.none.
                pending_args.push(PendingApplyArg::SynthOptionalNone {
                    label: fn_label.clone(),
                    option_ty: crate::types::instance(ctx, arg_ty),
                });
                synthesized_optional_count += 1;
                current_ty = ret_ty;
                continue;
            }

            pending_args.push(PendingApplyArg::Omitted {
                label: fn_label.clone(),
            });
            omitted.push((fn_label, arg_ty));
            current_ty = ret_ty;
            continue;
        }

        let (label, arg_expr) = remaining_args.remove(0);

        // OCaml special case: if all supplied args were optional defaults and
        // the final argument is `()`, treat it as an empty application.
        if consumed_optional_count > 0
            && omitted.is_empty()
            && remaining_args.is_empty()
            && label.is_nolabel()
            && pending_args.len() == synthesized_optional_count
        {
            if let crate::parser::ast::ExpressionDesc::Pexp_construct(lid, None) =
                &arg_expr.pexp_desc
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
        let arrow_ty = ctx.new_arrow(ctx_label, arg_ty, ret_ty, top_arity);
        unify_expression_types(tctx, loc, expanded_current_ty, arrow_ty, None)?;
        top_arity = None;

        pending_args.push(PendingApplyArg::Provided {
            label: convert_arg_label_for_ctx(&label, tctx.arena),
            expr: arg_expr,
            expected_ty: arg_ty,
            enforce_optional: label.is_optional(),
        });
        current_ty = ret_ty;
    }

    if total_app {
        // Match OCaml `type_unknown_args []`: for total applications, trailing
        // optional arrows are materialized as explicit `None` arguments.
        let mut applied_count = pending_args.len();
        while (applied_count as i32) < max_arity {
            let expanded_current_ty = crate::types::ctype::expand_head(ctx, env, current_ty);
            if let Some((fn_label, arg_ty, ret_ty)) =
                crate::types::ctype::split_arrow_with_label(ctx, expanded_current_ty)
            {
                if fn_label.is_optional() {
                    pending_args.push(PendingApplyArg::SynthOptionalNone {
                        label: fn_label.clone(),
                        option_ty: crate::types::instance(ctx, arg_ty),
                    });
                    current_ty = ret_ty;
                    applied_count += 1;
                    continue;
                }
            }
            break;
        }
    }

    let mut typed_args = Vec::with_capacity(pending_args.len());
    for pending_arg in pending_args {
        match pending_arg {
            PendingApplyArg::Provided {
                label,
                expr,
                expected_ty,
                enforce_optional,
            } => {
                let typed_arg = type_expect(
                    tctx,
                    env,
                    expr,
                    expected_ty,
                    Some(TypeClashContext::FunctionCall),
                )?;
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
                        vec![],
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
                    vec![],
                );
                typed_args.push(ApplyArg {
                    label,
                    expression: Some(none_expr),
                });
            }
            PendingApplyArg::Omitted { label } => {
                typed_args.push(ApplyArg {
                    label,
                    expression: None,
                });
            }
        }
    }

    // Re-wrap omitted parameters for partial/labeled applications.
    let mut result_ty = current_ty;
    for (label, arg_ty) in omitted.iter().rev() {
        result_ty = ctx.new_arrow(label.clone(), *arg_ty, result_ty, None);
    }

    // OCaml update_uncurried_arity: preserve remaining uncurried arity on
    // partially applied results.
    if let Some(arity) = function_arity {
        let applied_args = args.len() as i32 + consumed_optional_count as i32;
        let remaining_arity = arity - applied_args;
        if remaining_arity > 0 {
            let result_repr = ctx.repr(result_ty);
            if let TypeDesc::Tarrow { arg, ret, .. } = &*ctx.get_desc(result_repr) {
                result_ty = ctx.new_arrow(arg.lbl.clone(), arg.typ, *ret, Some(remaining_arity));
            }
        }
    }

    // Unify result with expected type
    unify_expression_types(tctx, loc, result_ty, expected_ty, context)?;

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

    // Match OCaml typecore/parmatch intent: when multiple polymorphic-variant
    // tags are constrained by the same match-pattern row, close that row in
    // typed patterns while leaving expression-side rows unchanged.
    close_multi_label_variant_rows_in_cases(tctx, env, &mut typed_cases);

    Ok(Expression::new(
        ExpressionDesc::Texp_match(
            Box::new(typed_scrutinee),
            typed_cases,
            vec![],
            Partial::Total, // TODO: implement proper exhaustiveness checking
        ),
        loc.clone(),
        expected_ty,
        EnvRef(0),
        attributes.to_vec(),
    ))
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

    let mut row = crate::types::btype::row_repr(ctx, &row);
    if !row.row_closed {
        row.row_closed = true;
        ctx.set_desc(repr, TypeDesc::Tvariant(row));
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

fn close_multi_label_variant_rows_in_cases(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    cases: &mut [crate::types::typedtree::Case],
) {
    let mut labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
    for case in cases.iter() {
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut labels_by_row);
    }

    let row_label_orders: HashMap<usize, Vec<String>> = labels_by_row
        .into_iter()
        .filter_map(|(row_key, labels)| (labels.len() > 1).then_some((row_key, labels)))
        .collect();
    if row_label_orders.is_empty() {
        return;
    }

    for case in cases.iter_mut() {
        reorder_multi_label_variant_rows_in_pattern(tctx, env, &mut case.c_lhs, &row_label_orders);
    }

    let mut copy_cache = HashMap::new();
    for case in cases.iter_mut() {
        copy_pattern_types(tctx, env, &mut case.c_lhs, &mut copy_cache);
    }

    let mut copied_labels_by_row: HashMap<usize, Vec<String>> = HashMap::new();
    for case in cases.iter() {
        collect_variant_row_labels_in_pattern(tctx, env, &case.c_lhs, &mut copied_labels_by_row);
    }
    let rows_to_close: HashSet<usize> = copied_labels_by_row
        .into_iter()
        .filter_map(|(row_key, labels)| (labels.len() > 1).then_some(row_key))
        .collect();
    if rows_to_close.is_empty() {
        return;
    }

    for case in cases.iter_mut() {
        close_multi_label_variant_rows_in_pattern(tctx, env, &mut case.c_lhs, &rows_to_close);
    }
}

fn pattern_contains_generalized_constructor(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    pat: &ParsedPattern,
) -> bool {
    match &pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_construct(lid, arg) => {
            let lid_txt = tctx.resolve_lid(lid.txt).clone();
            let lid_name = tctx.longident_last_name(&lid_txt);
            let is_qualified = matches!(lid_txt, Longident::Ldot(..));
            let is_generalized = if is_qualified {
                lookup_predef_option_constructor(&lid_txt, tctx.arena, env, tctx.type_ctx)
                    .map(|(_, desc)| desc.cstr_generalized)
                    .or_else(|| {
                        lookup_constructor_in_module(
                            &lid_txt,
                            tctx.arena,
                            env,
                            &mut tctx.persistent_env,
                            tctx.type_ctx,
                        )
                        .map(|(_, desc)| desc.cstr_generalized)
                    })
                    .or_else(|| {
                        env.find_constructor(&lid_name)
                            .ok()
                            .map(|desc| desc.cstr_generalized)
                    })
                    .unwrap_or(false)
            } else {
                env.find_constructor(&lid_name)
                    .map(|desc| desc.cstr_generalized)
                    .unwrap_or(false)
            };
            is_generalized
                || arg
                    .as_ref()
                    .is_some_and(|inner| pattern_contains_generalized_constructor(tctx, env, inner))
        }
        crate::parser::ast::PatternDesc::Ppat_alias(inner, _) => {
            pattern_contains_generalized_constructor(tctx, env, inner)
        }
        crate::parser::ast::PatternDesc::Ppat_tuple(items)
        | crate::parser::ast::PatternDesc::Ppat_array(items) => items
            .iter()
            .any(|item| pattern_contains_generalized_constructor(tctx, env, item)),
        crate::parser::ast::PatternDesc::Ppat_record(fields, _) => fields
            .iter()
            .any(|field| pattern_contains_generalized_constructor(tctx, env, &field.pat)),
        crate::parser::ast::PatternDesc::Ppat_or(left, right) => {
            pattern_contains_generalized_constructor(tctx, env, left)
                || pattern_contains_generalized_constructor(tctx, env, right)
        }
        crate::parser::ast::PatternDesc::Ppat_constraint(inner, _)
        | crate::parser::ast::PatternDesc::Ppat_exception(inner)
        | crate::parser::ast::PatternDesc::Ppat_open(_, inner) => {
            pattern_contains_generalized_constructor(tctx, env, inner)
        }
        _ => false,
    }
}

/// Type check a single case.
fn type_case(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    case: &crate::parser::ast::Case,
    scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
) -> TypeCoreResult<crate::types::typedtree::Case> {
    match type_case_impl(tctx, env, case, scrutinee_ty, body_ty, false) {
        Ok(case) => Ok(case),
        Err(TypeCoreError::PatternTypeClash(_)) => {
            type_case_impl(tctx, env, case, scrutinee_ty, body_ty, true)
        }
        Err(err) => Err(err),
    }
}

fn type_case_impl(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    case: &crate::parser::ast::Case,
    scrutinee_ty: TypeExprRef,
    body_ty: TypeExprRef,
    force_case_local_constraints: bool,
) -> TypeCoreResult<crate::types::typedtree::Case> {
    let mut case_env = env.clone();
    let needs_case_local_constraints = force_case_local_constraints
        || pattern_contains_generalized_constructor(tctx, env, &case.pc_lhs);
    let mut case_type_cache = HashMap::new();
    if needs_case_local_constraints {
        // OCaml type_cases duplicates identifier types for GADT cases so that
        // branch-local constraints don't leak to sibling branches.
        let mut duplicated_values: Vec<(Ident, ValueDescription)> = Vec::new();
        for (id, desc) in env.iter_values() {
            let mut seen = HashSet::new();
            if type_contains_tunivar(tctx.type_ctx, env, desc.val_type, &mut seen) {
                let mut duplicated_desc = desc.clone();
                duplicated_desc.val_type =
                    copy_case_type(tctx.type_ctx, env, desc.val_type, &mut case_type_cache);
                duplicated_values.push((id.clone(), duplicated_desc));
            }
        }
        for (id, desc) in duplicated_values {
            case_env.add_value(id, desc);
        }
    }

    let mut state = PatternState::new();
    let case_scrutinee_ty = if needs_case_local_constraints {
        copy_case_type(tctx.type_ctx, env, scrutinee_ty, &mut case_type_cache)
    } else {
        scrutinee_ty
    };

    // Type check the pattern
    let typed_pat = type_pattern(
        tctx,
        &case_env,
        &case.pc_lhs,
        case_scrutinee_ty,
        PatternMode::Normal,
        &mut state,
    )?;

    // Extend environment with pattern bindings
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
    is_async: bool,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    use crate::types::typedtree::{Case, FunctionParam, FunctionParamPattern, Partial};

    let ctx = tctx.type_ctx;

    // Convert arity to Option<i32> for the arrow type
    // Arity is now ArityIdx, look up from arena
    let arity_opt = tctx.arena.get_arity(arity);

    // Match OCaml's filter_arrow path: if expected type already expands to an
    // arrow with matching label, reuse its argument/result types directly.
    // Otherwise introduce a fresh arrow and unify against expected type.
    let ctx_label = convert_arg_label_for_ctx(arg_label, tctx.arena);
    let expected_inst = crate::types::instance(ctx, expected_ty);
    let expanded_expected = crate::types::ctype::expand_head(ctx, env, expected_inst);
    let expanded_desc = ctx.get_desc(expanded_expected);
    let mut expected_arrow = match &*expanded_desc {
        TypeDesc::Tarrow { arg, ret, .. } if arg.lbl == ctx_label => Some((arg.typ, *ret)),
        _ => None,
    };
    drop(expanded_desc);
    if expected_arrow.is_none() {
        let expected_repr = ctx.repr(expected_ty);
        let expected_desc = ctx.get_desc(expected_repr);
        let expected_path = match &*expected_desc {
            TypeDesc::Tconstr { path, .. } => Some(path.clone()),
            _ => None,
        };
        drop(expected_desc);
        if let Some(path) = expected_path {
            let mut manifest = env
                .lookup_type(&path)
                .ok()
                .and_then(|decl| decl.type_manifest);
            if manifest.is_none() {
                if let Path::Pident(id) = &path {
                    manifest = ctx
                        .find_type_decl_by_stamp(id.stamp())
                        .and_then(|decl| decl.type_manifest);
                }
            }
            if manifest.is_none() {
                manifest = ctx
                    .find_type_decl(path.head_name())
                    .and_then(|decl| decl.type_manifest);
            }
            if let Some(manifest) = manifest {
                let manifest_inst = crate::types::instance(ctx, manifest);
                let expanded_manifest = crate::types::ctype::expand_head(ctx, env, manifest_inst);
                let manifest_desc = ctx.get_desc(expanded_manifest);
                expected_arrow = match &*manifest_desc {
                    TypeDesc::Tarrow { arg, ret, .. } if arg.lbl == ctx_label => {
                        Some((arg.typ, *ret))
                    }
                    _ => None,
                };
            }
        }
    }
    let (mut param_ty, return_ty, _func_ty) = match expected_arrow {
        Some((param_ty, return_ty)) => {
            let func_ty = ctx.new_arrow(ctx_label.clone(), param_ty, return_ty, arity_opt);
            (param_ty, return_ty, func_ty)
        }
        _ => {
            let param_ty = ctx.new_var(None);
            let return_ty = ctx.new_var(None);
            let func_ty = ctx.new_arrow(ctx_label.clone(), param_ty, return_ty, arity_opt);
            unify_expression_types(tctx, loc, func_ty, expected_ty, None)?;
            (param_ty, return_ty, func_ty)
        }
    };

    if arg_label.is_optional() && default.is_none() {
        let tv = ctx.new_var(None);
        let option_ty = env.type_option(ctx, tv);
        unify_expression_types(tctx, loc, param_ty, option_ty, None)?;
        param_ty = option_ty;
    }

    // Type check parameter pattern
    let mut state = PatternState::new();
    state.reset(true);
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
        if pv.is_module {
            let module_type = module_type_from_package_binding(tctx, &body_env, pv.ty);
            body_env.add_module(
                pv.id.clone(),
                crate::types::decl::ModuleDeclaration {
                    md_type: module_type,
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
            );
        } else {
            let desc = ValueDescription {
                val_type: pv.ty,
                val_kind: crate::types::ValueKind::ValReg,
                val_loc: pv.loc.clone(),
                val_attributes: vec![],
                val_path: None,
            };
            body_env.add_value(pv.id.clone(), desc);
        }
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

    // OCaml typecore.ml builds a generic arrow and then instantiates it. Rust
    // currently over-copies non-generic nodes during instance(), which can
    // perturb alias path identity in emitted typedtree. Keep the freshly-built
    // generic arrow node here to preserve the original parameter path shape.
    let exp_type = ctx.new_generic_arrow(ctx_label, param_ty, return_ty, arity_opt);

    Ok(Expression::new(
        ExpressionDesc::Texp_function {
            params: vec![fp],
            body: cases,
            partial: Partial::Total,
            arity,
            async_: is_async,
        },
        loc.clone(),
        exp_type,
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
        if let Some((path, desc)) =
            lookup_predef_option_constructor(&longident, tctx.arena, env, tctx.type_ctx)
        {
            (path, desc)
        } else {
        // Module-qualified: use direct lookup
        match lookup_constructor_in_module(
            &longident,
            tctx.arena,
            env,
            &mut tctx.persistent_env,
            tctx.type_ctx,
        ) {
            Some((path, desc)) => (path, desc),
            None => match env.find_constructor(&lid_name) {
                Ok(desc) => (
                    Path::pident(Ident::create_persistent(lid_name)),
                    desc.clone(),
                ),
                Err(_) => return Err(TypeCoreError::NotAVariantType(longident)),
            },
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
                        .map(|(_, rf)| crate::types::btype::row_field_repr(rf));
                    let field0 = row0
                        .row_fields
                        .iter()
                        .find(|(l, _)| l == label)
                        .map(|(_, rf)| crate::types::btype::row_field_repr(rf));
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
                attributes.to_vec(),
            ));
        }

        let arg_ty = ctx.new_var(None);
        let typed_arg = type_expect(tctx, env, arg_expr, arg_ty, None)?;
        let use_recursive_payload_fallback = tctx.recursive_let_depth > 0
            && matches!(
                &arg_expr.pexp_desc,
                crate::parser::ast::ExpressionDesc::Pexp_ident(_)
            );
        let variant_ty = if use_recursive_payload_fallback {
            ctx.new_var(None)
        } else {
            ctx.new_variant(crate::types::type_expr::RowDesc {
                row_fields: vec![(
                    label.to_string(),
                    crate::types::type_expr::RowField::Reither {
                        constant: false,
                        types: vec![arg_ty],
                        matched: true,
                        link: crate::types::type_expr::RowFieldRef::null(),
                    },
                )],
                row_more: ctx.new_var(None),
                row_closed: false,
                row_fixed: false,
                row_name: None,
            })
        };
        unify_expression_types(tctx, loc, variant_ty, expected_ty, None)?;
        return Ok(Expression::new(
            ExpressionDesc::Texp_variant(label.to_string(), Some(Box::new(typed_arg))),
            loc.clone(),
            variant_ty,
            EnvRef(0),
            attributes.to_vec(),
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
    unify_expression_types(tctx, loc, variant_ty, expected_ty, None)?;

    Ok(Expression::new(
        ExpressionDesc::Texp_variant(label.to_string(), None),
        loc.clone(),
        variant_ty,
        EnvRef(0),
        attributes.to_vec(),
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

fn select_record_type_for_fields(
    tctx: &TypeCheckContext<'_>,
    env: &Env,
    field_names: &[String],
    expected_ty: TypeExprRef,
    base_ty: Option<TypeExprRef>,
    closed_record: bool,
) -> Option<TypeExprRef> {
    if field_names.len() <= 2 {
        return None;
    }

    let ctx = tctx.type_ctx;

    for candidate_ty in [Some(expected_ty), base_ty].into_iter().flatten() {
        if let Some(labels) = get_record_labels(ctx, env, candidate_ty) {
            if record_labels_match_ids(&labels, field_names, closed_record) {
                return Some(candidate_ty);
            }
        }
    }

    let first_name = field_names.first()?;
    let candidates = env.find_all_labels(first_name);
    let mut matching: Vec<(Option<Path>, TypeExprRef)> = Vec::new();
    for label in candidates.into_iter().rev() {
        if let Some(labels) = get_record_labels(ctx, env, label.lbl_res) {
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
    let placeholder_lid = tctx.arena.placeholder_located(loc);

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

    let field_names: Vec<String> = fields
        .iter()
        .map(|field| tctx.longident_last_name(tctx.resolve_lid(field.lid.txt)))
        .collect();
    let closed_record = typed_base.is_none();
    let disambiguation_ty = select_record_type_for_fields(
        tctx,
        env,
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

    // OCaml builds record definitions by label position over the full label set.
    // Keep explicit overrides keyed by lbl_pos so we can reconstruct full fields.
    let mut explicit_overrides: HashMap<
        i32,
        (
            Located<LidentIdx>,
            crate::types::LabelDescription,
            RecordLabelDefinition,
        ),
    > = HashMap::new();
    let mut explicit_overrides_by_name: HashMap<
        String,
        (
            Located<LidentIdx>,
            crate::types::LabelDescription,
            RecordLabelDefinition,
        ),
    > = HashMap::new();
    let mut explicit_overrides_in_order = Vec::new();
    let mut first_disambiguated_label: Option<crate::types::LabelDescription> = None;

    // Type check explicitly written fields.
    for (idx, field) in fields.iter().enumerate() {
        let field_name = tctx.longident_last_name(tctx.resolve_lid(field.lid.txt));
        let disambiguated = disambiguate_label(
            &field_name,
            disambiguation_ty,
            env,
            &mut tctx.persistent_env,
            ctx,
        );
        if first_disambiguated_label.is_none() {
            first_disambiguated_label = disambiguated.clone();
        }

        // Build label description (prefer env-disambiguated metadata).
        let (mut label_desc, field_input_ty) = if let Some(env_label) = disambiguated {
            let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
            let _ = crate::types::unify(ctx, &mut tctx.unify_state, ty_res, expected_ty);

            let input_ty = if env_label.lbl_optional && !field.opt {
                crate::types::ctype::extract_option_type(ctx, ty_arg).unwrap_or(ty_arg)
            } else {
                ty_arg
            };

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
            )
        };

        let typed_expr = type_expect(tctx, env, &field.expr, field_input_ty, None)?;

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
                vec![],
            )
        } else {
            typed_expr
        };

        let entry = (
            field.lid.clone(),
            label_desc.clone(),
            RecordLabelDefinition::Overridden(field.lid.clone(), final_expr),
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
        get_record_labels(ctx, env, disambiguation_ty)
    };
    if all_labels.is_none() {
        if let Some(base_expr) = typed_base.as_ref() {
            all_labels = get_record_labels(ctx, env, base_expr.exp_type);
        }
    }
    if all_labels.is_none() {
        if let Some(lbl) = first_disambiguated_label {
            all_labels = get_record_labels(ctx, env, lbl.lbl_res);
        }
    }
    if all_labels
        .as_ref()
        .is_some_and(|labels| labels.iter().any(|ld| ld.ld_id.name() == "..."))
    {
        all_labels = None;
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
                let disambiguated = disambiguate_label(
                    &label_name,
                    disambiguation_ty,
                    env,
                    &mut tctx.persistent_env,
                    ctx,
                );

            let label_desc = if let Some(env_label) = disambiguated {
                let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
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

            let key = label_desc.lbl_pos;
            if let Some(explicit) = explicit_overrides.remove(&key) {
                explicit_overrides_by_name.remove(&label_desc.lbl_name);
                typed_fields.push(explicit);
                continue;
            }
            if let Some(explicit) = explicit_overrides_by_name.remove(&label_desc.lbl_name) {
                typed_fields.push(explicit);
                continue;
            }

            if typed_base.is_some() {
                typed_fields.push((
                    placeholder_lid.clone(),
                    label_desc.clone(),
                    RecordLabelDefinition::Kept(label_desc.lbl_arg),
                ));
                continue;
            }

            if label_desc.lbl_optional {
                let option_ty = label_desc.lbl_arg;
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
                    vec![],
                );
                let mut synthesized_desc = label_desc;
                synthesized_desc.lbl_optional = false;
                typed_fields.push((
                    placeholder_lid.clone(),
                    synthesized_desc,
                    RecordLabelDefinition::Overridden(placeholder_lid.clone(), none_expr),
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

    // Disambiguate label: use the record expression's type to find the right label
    let env_label = disambiguate_label(
        &field_name,
        ty_exp,
        env,
        &mut tctx.persistent_env,
        ctx,
    );

    let label_desc = if let Some(env_label) = env_label {
        let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
        // Unify label's result type with the record's type
        unify_expression_types(tctx, loc, ty_res, record_ty, None)?;
        // Unify label's arg type with the field type
        unify_expression_types(tctx, loc, ty_arg, field_ty, None)?;
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
    // Match field-access disambiguation: type the record expression first,
    // then pick the label based on the resolved record type.
    let record_ty = ctx.new_var(None);
    let typed_record = type_expect(tctx, env, record_expr, record_ty, None)?;
    let ty_exp = typed_record.exp_type;
    let field_ty = ctx.new_var(None);

    let env_label = disambiguate_label(
        &field_name,
        ty_exp,
        env,
        &mut tctx.persistent_env,
        ctx,
    );
    let label_desc = if let Some(env_label) = env_label {
        let (ty_arg, ty_res) = crate::types::ctype::instance_label(ctx, &env_label);
        unify_expression_types(tctx, loc, ty_res, record_ty, None)?;
        unify_expression_types(tctx, loc, ty_arg, field_ty, None)?;
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
    let ctx = tctx.type_ctx;

    // Match OCaml typecore.ml Pexp_constraint:
    // begin_def; transl_simple_type; end_def; generalize_structure;
    // type_argument env sarg ty (instance env ty); exp_type = instance env ty.
    ctx.begin_def();
    let (typed_ctype, ctype_ty) = transl_type(tctx, env, core_type)?;
    let var_level = ctx.current_level();
    ctx.end_def();
    crate::types::generalize_structure(ctx, var_level, ctype_ty);

    let arg_expected_ty = ctype_ty;
    let arg_unify_ty = crate::types::instance(ctx, ctype_ty);

    let typed_inner = type_expect(tctx, env, inner_expr, arg_expected_ty, None)?;
    unify_expression_types(tctx, loc, typed_inner.exp_type, arg_unify_ty, None)?;
    let result_ty = crate::types::instance(ctx, ctype_ty);
    unify_expression_types(tctx, loc, result_ty, expected_ty, None)?;

    let mut result = typed_inner;
    result.exp_type = result_ty;
    let mut extras = Vec::with_capacity(result.exp_extra.len() + 1);
    extras.push((
        crate::types::typedtree::ExpExtra::Texp_constraint(typed_ctype),
        loc.clone(),
        attributes.to_vec(),
    ));
    extras.extend(result.exp_extra.into_iter());
    result.exp_extra = extras;
    Ok(result)
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
    override_flag: &crate::parser::ast::OverrideFlag,
    lid: &Located<LidentIdx>,
    body: &ParsedExpression,
    expected_ty: TypeExprRef,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    // Open the module's bindings into scope for the body
    let open_lid = tctx.arena.get_longident(lid.txt);
    let mut open_env = env.clone();

    // Resolve the module longident and open its signature
    let path =
        crate::types::typemod::path_from_longident(open_lid, |idx| tctx.arena.get_string(idx));
    let mod_type = crate::types::typemod::lookup_module_type_by_lid(
        open_lid,
        tctx.arena,
        env,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    );
    if let Some(ref mty) = mod_type {
        let sig = crate::types::typemod::resolve_mod_type_to_sig(
            mty,
            Some(env),
            &mut tctx.persistent_env,
            tctx.type_ctx,
        );
        if let Some(ref sig_items) = sig {
            crate::cmi::persistent_env::add_signature_to_env(
                sig_items,
                &path,
                &mut open_env,
                tctx.type_ctx,
                true,
            );
        }
    }

    // Type check the body expression in the extended environment
    let typed_body = type_expect(tctx, &open_env, body, expected_ty, None)?;

    // Return expression with Texp_open in exp_extra (matching OCaml)
    Ok(typed_body.with_exp_extra(
        crate::types::typedtree::ExpExtra::Texp_open(
            override_flag.clone(),
            path,
            lid.clone(),
            EnvRef(0),
        ),
        loc.clone(),
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

        // Subst.type_expr Subst.identity in OCaml: copy before rewriting.
        let rewritten_ty = crate::types::copy_type(ctx, typed_body.exp_type);

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

        unify_expression_types(tctx, loc, rewritten_ty, expected_ty, None)?;

        let mut result = typed_body.with_exp_extra(
            crate::types::typedtree::ExpExtra::Texp_newtype(name_str),
            loc,
            attributes.to_vec(),
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
        attributes.to_vec(),
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
    method: &Located<String>,
    expected_ty: TypeExprRef,
    context: Option<TypeClashContext>,
    attributes: &[crate::parser::ast::Attribute],
) -> TypeCoreResult<Expression> {
    let ctx = tctx.type_ctx;

    // Type the object expression first (OCaml `type_exp` path).
    let obj_ty = ctx.new_var(None);
    let typed_obj = type_expect(tctx, env, obj_expr, obj_ty, None)?;

    let use_precise_send_typing = {
        let expected_desc = ctx.get_desc(ctx.repr(expected_ty));
        matches!(&*expected_desc, TypeDesc::Tvar(_))
            && context.is_none()
            && method.txt.len() > 1
            && method_name_is_plain_ident(&method.txt)
    };
    if !use_precise_send_typing {
        return Ok(Expression::new(
            ExpressionDesc::Texp_send(
                Box::new(typed_obj),
                crate::types::typedtree::MethKind::Tmeth_name(method.txt.clone()),
                None,
            ),
            loc.clone(),
            expected_ty,
            EnvRef(0),
            attributes.to_vec(),
        ));
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
                        crate::types::typedtree::MethKind::Tmeth_name(method.txt.clone()),
                        None,
                    ),
                    loc.clone(),
                    expected_ty,
                    EnvRef(0),
                    attributes.to_vec(),
                ));
            }
            let alternatives = collect_public_methods_from_object_type(ctx, env, typed_obj.exp_type);
            return Err(TypeCoreError::UndefinedMethod {
                ty: typed_obj.exp_type,
                method: method.txt.clone(),
                alternatives,
            });
        }
    };

    if unify_expression_types(tctx, loc, method_result_ty, expected_ty, None).is_err() {
        return Ok(Expression::new(
            ExpressionDesc::Texp_send(
                Box::new(typed_obj),
                crate::types::typedtree::MethKind::Tmeth_name(method.txt.clone()),
                None,
            ),
            loc.clone(),
            expected_ty,
            EnvRef(0),
            attributes.to_vec(),
        ));
    }

    Ok(Expression::new(
        ExpressionDesc::Texp_send(
            Box::new(typed_obj),
            crate::types::typedtree::MethKind::Tmeth_name(method.txt.clone()),
            None,
        ),
        loc.clone(),
        method_result_ty,
        EnvRef(0),
        attributes.to_vec(),
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

    let (typed_args, typed_ret, ext_args, cstr_args, cstr_inlined, ext_ret_ty) =
        match &ext_constr.pext_kind {
            crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                let mut arg_ty_refs = Vec::new();
                let (typed_args, ext_args, cstr_args, cstr_inlined) = match args {
                    crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                        let mut typed = Vec::new();
                        for ty in types {
                            let (typed_ct, ty_ref) = transl_type(tctx, env, ty)?;
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
                            let (typed_ct, ty_ref) = transl_type(tctx, env, &label.pld_type)?;
                            let poly_ty_ref = ctx.new_poly(ty_ref, vec![]);
                            let poly_typed_ct = crate::types::typedtree::TypedCoreType {
                                ctyp_desc: crate::types::typedtree::TypedCoreTypeDesc::Ttyp_poly(
                                    vec![],
                                    Box::new(typed_ct.clone()),
                                ),
                                ctyp_type: poly_ty_ref,
                                ctyp_env: typed_ct.ctyp_env,
                                ctyp_loc: typed_ct.ctyp_loc,
                                ctyp_attributes: vec![],
                            };
                            typed_labels.push(crate::types::typedtree::LabelDeclaration {
                                ld_id: Ident::create_local(&label_name),
                                ld_name: crate::parse_arena::Located {
                                    txt: label_name.clone(),
                                    loc: label.pld_name.loc,
                                },
                                ld_mutable: label.pld_mutable,
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
                        let inline_ty = ctx.new_constr(inline_path.clone(), vec![]);
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
                        let (typed_ct, ty_ref) = transl_type(tctx, env, ct)?;
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

    let exn_ty = ctx.new_constr(Path::pident(Ident::create_persistent("exn")), vec![]);
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
            let ty_res = ctx.new_constr(Path::pident(id.clone()), inlined_decl.type_params.clone());
            for (pos, ld) in labels.iter().enumerate() {
                let lbl_desc = crate::types::LabelDescription {
                    lbl_name: ld.ld_id.name().to_string(),
                    lbl_res: ty_res,
                    lbl_arg: ld.ld_type,
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
    fn path_root_is_module(path: &Path, module_id: &Ident) -> bool {
        match path {
            Path::Pident(id) => id.same(module_id) || id.name() == module_id.name(),
            Path::Pdot(prefix, _, _) => path_root_is_module(prefix, module_id),
            Path::Papply(_, _) => false,
        }
    }

    fn replace_module_root_path(path: &Path, module_id: &Ident, alias_root: &Path) -> Path {
        match path {
            Path::Pident(id) => {
                if id.same(module_id) || id.name() == module_id.name() {
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
    ctx.begin_def();
    let scoped_result = (|| -> TypeCoreResult<(
        crate::types::typedtree::ModuleExpr,
        Env,
        Expression,
        TypeExprRef,
    )> {
        // Type check the module expression and build its signature for the env
        let (typed_mod, mut mod_sig) = match &module_expr.pmod_desc {
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
        let materialize_alias_sig = match &module_expr.pmod_desc {
            crate::parser::ast::ModuleExprDesc::Pmod_ident(_) => true,
            crate::parser::ast::ModuleExprDesc::Pmod_constraint(inner, _) => {
                matches!(inner.pmod_desc, crate::parser::ast::ModuleExprDesc::Pmod_ident(_))
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

        // Add the module to the environment so the body can access M.value
        let mut body_env = env.clone();
        let md_decl = crate::types::decl::ModuleDeclaration {
            md_type: mod_sig,
            md_attributes: vec![],
            md_loc: crate::location::Location::none(),
            md_path: None,
        };
        body_env.add_module(mod_id.clone(), md_decl);

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
        unify_expression_types(tctx, loc, rewritten_ty, expected_ty, None)?;
        Ok((typed_mod, body_env, typed_body, rewritten_ty))
    })();
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
                        binding.vb_expr.exp_type,
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

    let (pack_path, pack_lids, pack_args) = match package_info {
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
                    mod_attributes: vec![],
                })),
                loc,
                expected_ty,
                EnvRef(0),
                attributes.to_vec(),
            ));
        }
    };

    let typed_module = crate::types::typemod::type_module_expr(tctx, env, tctx.arena, module_expr)
        .map_err(|e| TypeCoreError::Other(format!("pack: {e:?}")))?;
    let typed_module_loc = typed_module.mod_loc;
    let package_mty = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_ident(
            pack_path.clone(),
            tctx.arena.placeholder_located(loc),
        ),
        mty_loc: loc,
        mty_attributes: vec![],
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
        mod_attributes: vec![],
    };
    let packed_type = ctx.new_type(TypeDesc::Tpackage {
        path: pack_path,
        lids: pack_lids,
        args: pack_args,
    });

    Ok(Expression::new(
        ExpressionDesc::Texp_pack(Box::new(wrapped_module)),
        loc,
        packed_type,
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
            TypeDesc::Tpackage { path, lids, args } => {
                Some((path.clone(), lids.clone(), args.clone()))
            }
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
            mty_attributes: vec![],
        },
        DeclMty::MtyAlias(_, path) => crate::types::typedtree::ModuleType {
            mty_desc: ModuleTypeDesc::Tmty_alias(path.clone(), arena.placeholder_located(loc)),
            mty_loc: loc,
            mty_attributes: vec![],
        },
        _ => crate::types::typedtree::ModuleType::placeholder(),
    }
}

fn wrap_module_unpacks_in_expression(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    mut body: Expression,
    unpacks: &[PatternVariable],
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

        let unpack_expr = Expression::new(
            ExpressionDesc::Texp_ident(Path::pident(unpack.id.clone()), located_lid, value_desc),
            unpack.loc_idx,
            unpack.ty,
            EnvRef(0),
            vec![],
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
            mod_attributes: vec![],
        };

        let wrapped_loc = body.exp_loc;
        let wrapped_ty = body.exp_type;
        let modulepat_attrs = vec![(
            Located {
                txt: ensure_string_idx(tctx.arena, "#modulepat"),
                loc: tctx.arena.none_loc(),
            },
            crate::parser::ast::Payload::PStr(vec![]),
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
            modulepat_attrs,
        );
    }

    body
}

fn extract_recursive_binding_name(
    pat: &crate::parser::ast::Pattern,
) -> Option<&crate::parser::ast::StringLoc> {
    match &pat.ppat_desc {
        crate::parser::ast::PatternDesc::Ppat_var(name) => Some(name),
        crate::parser::ast::PatternDesc::Ppat_constraint(inner, _) => {
            extract_recursive_binding_name(inner)
        }
        crate::parser::ast::PatternDesc::Ppat_alias(inner, alias_name) => {
            if matches!(inner.ppat_desc, crate::parser::ast::PatternDesc::Ppat_any) {
                Some(alias_name)
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
                .all(|(_, label, definition)| match definition {
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

    match &sty.ptyp_desc {
        CTD::Ptyp_arrow { arg, ret, arity } => {
            let arg_ty = if arg.lbl.is_optional() {
                env.type_option(ctx, ctx.new_var(None))
            } else {
                ctx.new_var(None)
            };
            let ret_ty = approx_type_for_rec_let(tctx, env, ret);
            let label = convert_arg_label_for_ctx(&arg.lbl, tctx.arena);
            ctx.new_arrow(label, arg_ty, ret_ty, tctx.arena.get_arity(*arity))
        }
        CTD::Ptyp_tuple(args) => {
            let tys = args
                .iter()
                .map(|arg| approx_type_for_rec_let(tctx, env, arg))
                .collect();
            ctx.new_tuple(tys)
        }
        CTD::Ptyp_constr(lid, args) => {
            let longident = tctx.resolve_lid(lid.txt).clone();
            let (path, decl) = resolve_type_constructor_path(tctx, env, &longident);
            if let Some(decl) = decl {
                if args.len() == decl.type_arity as usize {
                    let tys = args
                        .iter()
                        .map(|arg| approx_type_for_rec_let(tctx, env, arg))
                        .collect();
                    return ctx.new_constr(path, tys);
                }
            }
            ctx.new_var(None)
        }
        CTD::Ptyp_poly(_, inner) => approx_type_for_rec_let(tctx, env, inner),
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

    match &sexp.pexp_desc {
        ED::Pexp_let(_, _, body) => type_approx_for_rec_let(tctx, env, body),
        ED::Pexp_fun {
            arg_label,
            rhs,
            arity,
            ..
        } => {
            let arg_ty = if arg_label.is_optional() {
                env.type_option(ctx, ctx.new_var(None))
            } else {
                ctx.new_var(None)
            };
            let ret_ty = type_approx_for_rec_let(tctx, env, rhs)?;
            let label = convert_arg_label_for_ctx(arg_label, tctx.arena);
            Ok(ctx.new_arrow(label, arg_ty, ret_ty, tctx.arena.get_arity(*arity)))
        }
        ED::Pexp_match(_, cases) => match cases.first() {
            Some(case) => type_approx_for_rec_let(tctx, env, &case.pc_rhs),
            None => Ok(ctx.new_var(None)),
        },
        ED::Pexp_try(expr, _) => type_approx_for_rec_let(tctx, env, expr),
        ED::Pexp_tuple(items) => {
            let tys: TypeCoreResult<Vec<_>> = items
                .iter()
                .map(|item| type_approx_for_rec_let(tctx, env, item))
                .collect();
            Ok(ctx.new_tuple(tys?))
        }
        ED::Pexp_ifthenelse(_, then_expr, _) => type_approx_for_rec_let(tctx, env, then_expr),
        ED::Pexp_sequence(_, expr) => type_approx_for_rec_let(tctx, env, expr),
        ED::Pexp_constraint(expr, sty) => {
            let ty = type_approx_for_rec_let(tctx, env, expr)?;
            let ty1 = approx_type_for_rec_let(tctx, env, sty);
            unify_expression_types(tctx, loc, ty, ty1, None)?;
            Ok(ty1)
        }
        ED::Pexp_coerce(expr, _sty1, sty2) => {
            let ty = type_approx_for_rec_let(tctx, env, expr)?;
            let ty1 = ctx.new_var(None);
            let ty2 = approx_type_for_rec_let(tctx, env, sty2);
            unify_expression_types(tctx, loc, ty, ty1, None)?;
            Ok(ty2)
        }
        _ => Ok(ctx.new_var(None)),
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
        let typing_env = if rec_flag == RecFlag::Recursive {
            let mut new_env = env.clone();
            for (binding, ty) in bindings.iter().zip(binding_types.iter()) {
                if let Some(name) = extract_recursive_binding_name(&binding.pvb_pat) {
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
                &binding.pvb_pat,
                *ty,
                PatternMode::Normal,
                &mut state,
            )?;

            typed_patterns.push(typed_pat);

            // Save pattern variables from this binding
            all_pattern_vars.push(state.pattern_variables.clone());
        }

        if rec_flag == RecFlag::Recursive {
            for (typed_pat, binding) in typed_patterns.iter().zip(bindings.iter()) {
                let approx_ty = type_approx_for_rec_let(tctx, env, &binding.pvb_expr)?;
                unify_pattern_types(tctx, typed_pat.pat_loc, typed_pat.pat_type, approx_ty)?;
            }
        }

        // Type check expressions after recursive approximation unification.
        let mut typed_bindings = Vec::new();
        for ((binding, typed_pat), ty) in bindings
            .iter()
            .zip(typed_patterns.into_iter())
            .zip(binding_types.iter())
        {
            let typed_expr = type_expect(tctx, &typing_env, &binding.pvb_expr, *ty, None)?;
            typed_bindings.push(ValueBinding::new(
                typed_pat,
                typed_expr,
                binding.pvb_loc.clone(),
                binding.pvb_attributes.clone(),
            ));
        }

        // End definition level
        ctx.end_def();

        for (binding, ty) in typed_bindings.iter().zip(binding_types.iter()) {
            if !is_nonexpansive_expression(tctx, &binding.vb_expr) {
                crate::types::ctype::generalize_expansive(ctx, env, *ty);
            }
        }

        // Generalize types
        for ty in &binding_types {
            crate::types::generalize(ctx, *ty);
        }

        // Build final environment from all collected pattern variables.
        // Module unpack bindings are first bound as values (package type), then
        // lowered into nested Texp_letmodule wrappers around the let body.
        let mut new_env = env.clone();
        let mut unpacks: Vec<PatternVariable> = Vec::new();
        for pvars in all_pattern_vars.iter() {
            for pv in pvars {
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
                // Resolve the module prefix to get a signature and path
                let lid_str = Self::longident_to_string(lid, arena);
                if let Some((mod_path, sig)) = self.resolve_module_lid(prefix, arena, pers_env, ctx)
                {
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
    /// Applies path rewriting/substitution for downstream value/module lookups.
    fn resolve_module_lid<'b>(
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
                        let sig = if apply_subst {
                            copy_lookup_signature_for_subst(&sig, ctx)
                        } else {
                            sig
                        };
                        if apply_subst {
                            if let Some(ref old_name) = resolved_name {
                                crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                                    &sig, old_name, &path, ctx,
                                );
                            }
                            crate::cmi::persistent_env::substitute_type_paths_in_sig(
                                &sig, &path, ctx,
                            );
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
                    for sig_item in &parent_sig {
                        if let crate::types::decl::SignatureItem::SigModule(id, sub_md, _) =
                            sig_item
                        {
                            if id.name() == submod_name {
                                let sub_path = Path::pdot(parent_path, submod_name.to_string());
                                let result =
                                    self.resolve_module_type(&sub_md.md_type, pers_env, ctx);
                                if let Some((sig, resolved_name)) = result {
                                    // If an alias was followed, rewrite type paths from the
                                    // resolved module name to the access path.
                                    // E.g., Belt.Array aliases Belt_Array, so rewrite
                                    // Pdot(Pident("Belt_Array"), X) → Pdot(sub_path, X)
                                    let sig = if apply_subst {
                                        copy_lookup_signature_for_subst(&sig, ctx)
                                    } else {
                                        sig
                                    };
                                    if apply_subst {
                                        if let Some(ref old_name) = resolved_name {
                                            crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                                                &sig, old_name, &sub_path, ctx,
                                            );
                                        }
                                        crate::cmi::persistent_env::substitute_type_paths_in_sig(
                                            &sig, &sub_path, ctx,
                                        );
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
                    let modtype_name = id.name();
                    match env.find_modtype(modtype_name) {
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
                    parent_sig.iter().find_map(|sig_item| {
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
                    if let Ok(md) = env.find_module(mod_name) {
                        let result =
                            resolve_module_type_inner(env, &md.md_type, pers_env, ctx, visiting);
                        visiting.remove(path);
                        return result;
                    }
                    if let Some(pers) = pers_env.as_mut() {
                        if let Some(ps) = pers.find_pers_struct(mod_name, ctx) {
                            let result = Some((ps.ps_sig.clone(), Some(mod_name.to_string())));
                            visiting.remove(path);
                            return result;
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
                    for sig_item in &parent_sig {
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
            let (mod_path, sig) = env.resolve_module_lid(module_lid, arena, pers_env, ctx)?;
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
                            let is_constant = matches!(cd.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty())
                                && cd.cd_res.is_none();
                            if cd.cd_id.name() == cstr_name {
                                let tag = if is_constant {
                                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                                } else {
                                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                                };
                                let type_path =
                                    Path::pdot(mod_path.clone(), _id.name().to_string());
                                let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
                                    crate::types::ConstructorArguments::CstrTuple(args) => {
                                        (args.clone(), args.len() as i32, None)
                                    }
                                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                                        // Match OCaml Datarepr.constructor_args for Cstr_record:
                                        // cstr_args = [newgenconstr (type_path.cstr_name) type_params].
                                        let inline_params = type_decl.type_params.clone();
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
                                let cstr_res = cd.cd_res.unwrap_or_else(|| {
                                    ctx.new_generic_constr(
                                        type_path.clone(),
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
                                    cstr_generalized: cd.cd_res.is_some(),
                                    cstr_private: type_decl.type_private,
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
                }
                // Also search SigTypext for exception/extension constructors
                if let SignatureItem::SigTypext(id, ext, _status) = sig_item {
                    if id.name() == cstr_name {
                        let ext_path = Path::pident(Ident::create_persistent(cstr_name));
                        let (cstr_args, cstr_arity, cstr_inlined) = match &ext.ext_args {
                            crate::types::ConstructorArguments::CstrTuple(args) => {
                                (args.clone(), args.len() as i32, None)
                            }
                            crate::types::ConstructorArguments::CstrRecord(labels) => {
                                let inline_params = ext.ext_type_params.clone();
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
                        let cstr_res = ctx.new_generic_constr(
                            ext.ext_type_path.clone(),
                            ext.ext_type_params.clone(),
                        );
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
                        return Some((ext_path, desc));
                    }
                }
            }
            None
        }
        _ => None,
    }
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
    let opath =
        extract_type_path_from_expected_with_persistent_env(expected_ty, env, pers_env, ctx);

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
            if let TypeDesc::Tconstr {
                path: cstr_path, ..
            } = &*cstr_desc
            {
                if cstr_path.same(target_path) {
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
            return Some(result);
        }
    }

    // Step 4: Fall back to the most recent constructor (last in the list = most recently added)
    let cstr = all_constrs.last().unwrap();
    let path = Path::pident(Ident::create_persistent(cstr_name));
    Some((path, (*cstr).clone()))
}

/// Type-directed label disambiguation when the label is not in scope.
///
/// OCaml's `Label.disambiguate` can still resolve labels using `opath` even
/// when `find_all_labels` is empty. Mirror that by inspecting the expected
/// record type declaration directly.
fn lookup_label_by_expected_type<'a>(
    label_name: &str,
    record_ty: TypeExprRef,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<crate::types::LabelDescription> {
    let type_path =
        extract_type_path_from_expected_with_persistent_env(record_ty, env, pers_env, ctx)?;
    let type_decl = lookup_type_decl_for_path(&type_path, env, pers_env, ctx)?;
    let (labels, repr) = match &type_decl.type_kind {
        crate::types::TypeKind::TypeRecord(labels, repr) => (labels, repr),
        _ => return None,
    };
    let res_ty = ctx.new_generic_constr(type_path, type_decl.type_params.clone());
    for (pos, ld) in labels.iter().enumerate() {
        if ld.ld_id.name() == label_name {
            return Some(crate::types::LabelDescription {
                lbl_name: ld.ld_id.name().to_string(),
                lbl_res: res_ty,
                lbl_arg: ld.ld_type,
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

    if all_labels.is_empty() {
        let mut selected =
            lookup_label_by_expected_type(lookup_name, record_ty, env, pers_env, ctx);
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

    selected
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
    // Match OCaml's disambiguation behavior: first expand expected type aliases
    // (extract_concrete_variant), then inspect constructors on the concrete path.
    let type_path =
        extract_type_path_from_expected_with_persistent_env(expected_ty, env, pers_env, ctx)?;

    // Look up the type declaration
    let type_decl = lookup_type_decl_for_path(&type_path, env, pers_env, ctx)?;

    // Check if it's a variant type with a matching constructor
    if let crate::types::TypeKind::TypeVariant(ref constrs) = type_decl.type_kind {
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
                let tag = if is_constant {
                    crate::types::decl::ConstructorTag::CstrConstant(const_idx)
                } else {
                    crate::types::decl::ConstructorTag::CstrBlock(block_idx)
                };
                let (cstr_args, cstr_arity, cstr_inlined) = match &cd.cd_args {
                    crate::types::ConstructorArguments::CstrTuple(args) => {
                        (args.clone(), args.len() as i32, None)
                    }
                    crate::types::ConstructorArguments::CstrRecord(labels) => {
                        let inline_params = type_decl.type_params.clone();
                        let inline_path = Path::pdot(type_path.clone(), cstr_name.to_string());
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
                // Use the type path's head ident for the result type
                let cstr_res = cd.cd_res.unwrap_or_else(|| {
                    ctx.new_generic_constr(type_path.clone(), type_decl.type_params.clone())
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
                    cstr_generalized: cd.cd_res.is_some(),
                    cstr_private: type_decl.type_private,
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

fn resolve_module_signature_for_path<'a>(
    module_path: &Path,
    env: &Env,
    pers_env: &mut Option<crate::cmi::persistent_env::PersistentEnv>,
    ctx: &'a crate::types::context::TypeContext<'a>,
) -> Option<(Path, crate::types::decl::Signature)> {
    use crate::types::decl::SignatureItem;

    match module_path {
        Path::Pident(id) => {
            if let Ok(md) = env.find_module(id.name()) {
                let (sig, resolved_name) = env.resolve_module_type(&md.md_type, pers_env, ctx)?;
                let access_path = md
                    .md_path
                    .clone()
                    .unwrap_or_else(|| Path::pident(id.clone()));
                let sig = copy_lookup_signature_for_subst(&sig, ctx);
                if let Some(old_name) = resolved_name {
                    crate::cmi::persistent_env::rewrite_module_prefix_in_sig(
                        &sig,
                        &old_name,
                        &access_path,
                        ctx,
                    );
                }
                crate::cmi::persistent_env::substitute_type_paths_in_sig(&sig, &access_path, ctx);
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
                        let sig = copy_lookup_signature_for_subst(&sig, ctx);
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
    // Only use env.lookup_type directly for simple identifiers. For qualified
    // paths, env.lookup_type currently resolves by leaf name and can return an
    // unrelated declaration with the same type name.
    if let Path::Pident(_) = type_path {
        if let Ok(decl) = env.lookup_type(type_path) {
            return Some(decl.clone());
        }
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
                            return Some(crate::types::TypeDeclaration {
                                type_params: parent_decl.type_params.clone(),
                                type_arity: parent_decl.type_params.len() as i32,
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
                                type_variance: parent_decl
                                    .type_params
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
        if let Some((_resolved_parent_path, parent_sig)) =
            resolve_module_signature_for_path(parent, env, pers_env, ctx)
        {
            for item in &parent_sig {
                if let crate::types::decl::SignatureItem::SigType(id, decl, _) = item {
                    if id.name() == type_name.as_str() {
                        return Some(decl.clone());
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
            if let Some(decl) = crate::types::ctype::resolve_type_through_modules(ctx, &direct_path)
            {
                return Some(decl);
            }
        }
    }

    // Only fall back to name-based lookup for simple identifiers.
    // For qualified paths (Pdot), a head-name fallback is unsound and can
    // resolve to an unrelated type that happens to share the same leaf name.
    if let Path::Pident(id) = type_path {
        if let Some(decl) = ctx.find_type_decl(id.name()) {
            return Some(decl.clone());
        }
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
    fn test_convert_constant_large_fits_63bit() {
        // Values that fit in 63-bit should be preserved
        let cst = crate::parser::ast::Constant::Integer("99999999999999999".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(99999999999999999));
    }

    #[test]
    fn test_convert_constant_overflow_too_large() {
        // Values that don't fit in i64 should still error
        let cst =
            crate::parser::ast::Constant::Integer("99999999999999999999999".to_string(), None);
        let result = convert_constant(&cst);
        assert!(matches!(result, Err(TypeCoreError::LiteralOverflow(_))));
    }

    #[test]
    fn test_convert_constant_underscores() {
        // 949460645006 fits in 63 bits, should be preserved
        let cst = crate::parser::ast::Constant::Integer("949_460_645_006".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(949_460_645_006));
    }

    #[test]
    fn test_convert_constant_hex() {
        // 0xFFFFFFFF = 4294967295, fits in 63 bits
        let cst = crate::parser::ast::Constant::Integer("0xffff_ffff".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(4294967295));
    }

    #[test]
    fn test_convert_constant_63bit_wrap() {
        // 4611686018427387904 = 2^62, wraps to -2^62 in 63-bit
        let cst = crate::parser::ast::Constant::Integer("4611686018427387904".to_string(), None);
        let result = convert_constant(&cst).unwrap();
        assert_eq!(result, Constant::Int(-4611686018427387904));
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
    fn test_convert_constant_bigint_removes_underscores() {
        let cst = crate::parser::ast::Constant::Integer("01_000_000".to_string(), Some('n'));
        let result = convert_constant(&cst).unwrap();
        assert!(matches!(result, Constant::BigInt(true, d) if d == "1000000"));
    }

    #[test]
    fn test_convert_constant_bigint_preserves_non_decimal_heads() {
        let cst = crate::parser::ast::Constant::Integer("00x1_000_000".to_string(), Some('n'));
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
}
