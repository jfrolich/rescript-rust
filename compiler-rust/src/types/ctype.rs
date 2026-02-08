//! Core type operations.
//!
//! This module provides the main type operations used in type checking:
//!
//! - **Unification**: Making two types equal by finding substitutions
//! - **Instantiation**: Creating fresh instances of polymorphic types
//! - **Generalization**: Abstracting types to polymorphic forms
//! - **Type expansion**: Following type abbreviations
//!
//! # Unification Algorithm
//!
//! The unification algorithm follows the standard union-find approach with
//! several optimizations for the OCaml type system:
//!
//! 1. Path compression (in `repr`)
//! 2. Occurs check to prevent infinite types
//! 3. Level-based generalization tracking
//! 4. Special handling for row types (objects, variants)
//!
//! # Error Handling
//!
//! Type errors are represented as `TypeError` with detailed information
//! about what went wrong during unification or other operations.

use super::btype::{iter_type_expr, row_more, row_repr};
use super::context::TypeContext;
use super::env::Env;
use super::path::Path;
use super::type_expr::{GENERIC_LEVEL, RowDesc, RowField, TypeDesc, TypeExprRef};
use std::collections::HashSet;

// ============================================================================
// Type Errors
// ============================================================================

/// A pair of types that failed to unify.
pub type TypePair = (TypeExprRef, TypeExprRef);

/// Error during type checking.
#[derive(Debug, Clone)]
pub enum TypeError {
    /// Failed to unify two types.
    Unify(Vec<TypePair>),

    /// Recursive type detected (occurs check failed).
    RecursiveType(TypeExprRef),

    /// Recursive abbreviation detected.
    RecursiveAbbrev,

    /// Cannot expand a type abbreviation.
    CannotExpand,

    /// Cannot apply a type constructor.
    CannotApply,

    /// Type tags conflict in polymorphic variant.
    TagsConflict(String, String),

    /// Subtype constraint violated.
    Subtype {
        trace: Vec<TypePair>,
        context: Option<SubtypeContext>,
    },
}

/// Context for subtype errors.
#[derive(Debug, Clone)]
pub enum SubtypeContext {
    /// Generic error with error code.
    Generic { error_code: String },

    /// Different type kinds.
    DifferentTypeKinds {
        left_typename: Path,
        right_typename: Path,
    },
}

/// Result type for type operations.
pub type TypeResult<T> = Result<T, TypeError>;

// ============================================================================
// Unification Mode
// ============================================================================

/// Unification mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnifyMode {
    /// Expression mode: standard unification.
    Expression,
    /// Pattern mode: generate equations for GADTs.
    Pattern,
}

// ============================================================================
// Unification State
// ============================================================================

/// State for unification operations.
///
/// This tracks the state needed during unification, including:
/// - Already unified pairs (to handle cycles)
/// - Current unification mode
/// - Backtracking information
pub struct UnifyState {
    /// Set of already unified type pairs.
    unified_pairs: HashSet<(usize, usize)>,

    /// Current unification mode.
    mode: UnifyMode,

    /// Whether we're generating equations (for GADTs).
    generate_equations: bool,

    /// Whether to assume type constructors are injective.
    assume_injective: bool,

    /// Environment for type alias expansion during unification.
    /// Stored as a raw pointer to avoid lifetime parameter on UnifyState.
    /// Safety: the env must outlive the UnifyState (which it always does since
    /// UnifyState is created and used within a single type-checking call).
    env_ptr: Option<*const Env>,
}

impl UnifyState {
    /// Create a new unify state.
    pub fn new() -> Self {
        UnifyState {
            unified_pairs: HashSet::new(),
            mode: UnifyMode::Expression,
            generate_equations: false,
            assume_injective: false,
            env_ptr: None,
        }
    }

    /// Create a state for pattern matching.
    pub fn pattern_mode() -> Self {
        UnifyState {
            unified_pairs: HashSet::new(),
            mode: UnifyMode::Pattern,
            generate_equations: true,
            assume_injective: false,
            env_ptr: None,
        }
    }

    /// Set the environment for type alias expansion.
    /// Safety: the env must outlive this UnifyState.
    pub fn set_env(&mut self, env: &Env) {
        self.env_ptr = Some(env as *const Env);
    }

    /// Get the environment reference, if set.
    fn env(&self) -> Option<&Env> {
        self.env_ptr.map(|ptr| unsafe { &*ptr })
    }

    /// Check if two types have already been unified.
    pub fn already_unified(&self, t1: TypeExprRef, t2: TypeExprRef) -> bool {
        let key = if t1.0 < t2.0 {
            (t1.0, t2.0)
        } else {
            (t2.0, t1.0)
        };
        self.unified_pairs.contains(&key)
    }

    /// Mark two types as unified.
    pub fn mark_unified(&mut self, t1: TypeExprRef, t2: TypeExprRef) {
        let key = if t1.0 < t2.0 {
            (t1.0, t2.0)
        } else {
            (t2.0, t1.0)
        };
        self.unified_pairs.insert(key);
    }
}

impl Default for UnifyState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Occurs Check
// ============================================================================

/// Check if a type variable occurs in another type.
///
/// This is the occurs check that prevents infinite types.
/// Returns `true` if `needle` occurs in `haystack`.
pub fn occurs(ctx: &TypeContext<'_>, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    let needle = ctx.repr(needle);
    let haystack = ctx.repr(haystack);

    if needle == haystack {
        return true;
    }

    // Check if needle occurs in any child of haystack
    let mut found = false;
    iter_type_expr(ctx, haystack, |child| {
        if !found && occurs(ctx, needle, child) {
            found = true;
        }
    });
    found
}

/// Deep occur check - follows type constructors.
pub fn deep_occur(ctx: &TypeContext<'_>, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    let needle = ctx.repr(needle);
    let haystack = ctx.repr(haystack);

    if needle == haystack {
        return true;
    }

    let desc = ctx.get_desc(haystack);
    match &*desc {
        TypeDesc::Tconstr { args, .. } => args.iter().any(|arg| deep_occur(ctx, needle, *arg)),
        _ => {
            drop(desc);
            let mut found = false;
            iter_type_expr(ctx, haystack, |child| {
                if !found && deep_occur(ctx, needle, child) {
                    found = true;
                }
            });
            found
        }
    }
}

// ============================================================================
// Link Types
// ============================================================================

/// Link two types together (for unification).
///
/// This makes `t1` point to `t2`, effectively making them the same type.
/// The level of `t2` is updated to be the minimum of both levels.
pub fn link_type(ctx: &TypeContext<'_>, t1: TypeExprRef, t2: TypeExprRef) {
    let level1 = ctx.get_level(t1);
    let level2 = ctx.get_level(t2);

    // Update level to minimum
    if level1 < level2 {
        ctx.set_level(t2, level1);
    }

    // Make t1 point to t2
    ctx.set_desc(t1, TypeDesc::Tlink(t2));
}

/// Update the level of a type and its children.
pub fn update_level(ctx: &TypeContext<'_>, level: i32, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let current = ctx.get_level(ty);

    if level < current {
        ctx.set_level(ty, level);

        // Recursively update children
        iter_type_expr(ctx, ty, |child| {
            update_level(ctx, level, child);
        });
    }
}

// ============================================================================
// Predef Type Names
// ============================================================================

/// Check if a type name is a predef (builtin) type.
/// Predef types may appear under different paths (e.g., `ref` vs `Pervasives.ref`)
/// but should be treated as the same type during unification.
fn is_predef_type_name(name: &str) -> bool {
    matches!(name,
        "int" | "char" | "float" | "bool" | "unit" | "exn" | "array" |
        "list" | "option" | "nativeint" | "int32" | "int64" | "lazy_t" |
        "bytes" | "string" | "ref" | "result" | "dict" | "promise" |
        "unknown" | "bigint" | "symbol" | "regexp"
    )
}

// ============================================================================
// Type Alias Expansion
// ============================================================================

/// Resolve a type declaration by walking through module signatures.
///
/// For a path like `Pdot(Pdot(Pident(Js), "Promise"), "t")`:
/// 1. Load the root module's CMI (`Js.cmi`)
/// 2. Find the sub-module `Promise` in its signature
/// 3. If it's an alias, load the aliased module
/// 4. Find type `t` in the resolved module's signature
///
/// Returns the type declaration and caches it in the path store.
pub fn resolve_type_through_modules<'a>(
    ctx: &'a TypeContext<'a>,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    use crate::cmi::{cmi_format, sig_reader::SigReadContext};
    use crate::types::decl::{ModuleType, SignatureItem};

    // Flatten the path to get root ident and component list
    let (root_id, components) = path.flatten().ok()?;
    if components.is_empty() {
        return None; // Not a Pdot path
    }

    let load_paths = ctx.load_paths();
    if load_paths.is_empty() {
        return None;
    }

    // Load the root module's CMI
    let root_name = root_id.name();
    let cmi_filename = format!("{}.cmi", root_name);
    let full_path = {
        let mut found = None;
        for dir in load_paths.iter() {
            let exact = dir.join(&cmi_filename);
            if exact.exists() {
                found = Some(exact.to_string_lossy().into_owned());
                break;
            }
            if let Some(first_char) = cmi_filename.chars().next() {
                if first_char.is_ascii_uppercase() {
                    let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &cmi_filename[1..]);
                    let uncap_path = dir.join(&uncap);
                    if uncap_path.exists() {
                        found = Some(uncap_path.to_string_lossy().into_owned());
                        break;
                    }
                }
            }
        }
        found
    }?;

    let cmi = cmi_format::read_cmi(&full_path).ok()?;
    let mut sig_ctx = SigReadContext::new(ctx);
    let root_sig = sig_ctx.read_signature(&cmi.cmi_sign);

    // Walk through the components to find the type
    // components = ["Promise", "t"] for Js.Promise.t
    let type_name = components.last()?; // "t"
    let module_components = &components[..components.len() - 1]; // ["Promise"]

    // Navigate to the right sub-module
    let mut current_sig = root_sig;
    for &module_name in module_components {
        let mut found_sig = None;
        for item in &current_sig {
            if let SignatureItem::SigModule(id, md, _) = item {
                if id.name() == module_name {
                    match &md.md_type {
                        ModuleType::MtySignature(sub_sig) => {
                            found_sig = Some(sub_sig.clone());
                        }
                        ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                            // Resolve the alias by loading the aliased module's CMI
                            if let Path::Pident(alias_id) = alias_path {
                                let alias_cmi = format!("{}.cmi", alias_id.name());
                                let alias_full_path = {
                                    let mut f = None;
                                    for dir in load_paths.iter() {
                                        let exact = dir.join(&alias_cmi);
                                        if exact.exists() {
                                            f = Some(exact.to_string_lossy().into_owned());
                                            break;
                                        }
                                        if let Some(first_char) = alias_cmi.chars().next() {
                                            if first_char.is_ascii_uppercase() {
                                                let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &alias_cmi[1..]);
                                                let uncap_path = dir.join(&uncap);
                                                if uncap_path.exists() {
                                                    f = Some(uncap_path.to_string_lossy().into_owned());
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    f
                                };
                                if let Some(alias_fp) = alias_full_path {
                                    if let Ok(alias_cmi_data) = cmi_format::read_cmi(&alias_fp) {
                                        let mut alias_sig_ctx = SigReadContext::new(ctx);
                                        found_sig = Some(alias_sig_ctx.read_signature(&alias_cmi_data.cmi_sign));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    break;
                }
            }
        }
        current_sig = found_sig?;
    }

    // Register ALL types in the final signature by stamp for future lookups.
    // This is important because type manifests may reference sibling types
    // (e.g., type component<'a> = componentLike<'a, element>), and those
    // sibling types need to be available for expansion later.
    let mut result = None;
    for item in &current_sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            // Register every type by stamp
            if id.stamp() != 0 {
                ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
            }
            if id.name() == *type_name {
                // Cache the target type in the path store
                let path_name = path.name();
                ctx.register_type_decl_by_path(&path_name, decl.clone());
                result = Some(decl.clone());
            }
        }
    }

    result
}

/// Try to expand a type alias (type abbreviation).
///
/// If the type is `Tconstr(path, args)` and the type declaration for `path`
/// Resolve a type through local environment modules.
/// For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
/// get its signature, and find type t in it.
fn resolve_type_through_env<'a>(
    ctx: &'a TypeContext<'a>,
    env: &super::env::Env,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    use super::decl::{ModuleType, SignatureItem};

    let (root_id, components) = path.flatten().ok()?;
    if components.is_empty() {
        return None;
    }

    let type_name = *components.last()?;
    let module_components = &components[..components.len() - 1];

    // Look up the root module in the env
    let root_module = env.find_module(root_id.name()).ok()?;
    let mut current_md_type = &root_module.md_type;

    // Navigate through sub-modules
    for &mod_name in module_components {
        match current_md_type {
            ModuleType::MtySignature(sig) => {
                let mut found = false;
                for item in sig {
                    if let SignatureItem::SigModule(id, md, _) = item {
                        if id.name() == mod_name {
                            current_md_type = &md.md_type;
                            found = true;
                            break;
                        }
                    }
                }
                if !found {
                    return None;
                }
            }
            ModuleType::MtyAlias(_, alias_path) => {
                // Need to resolve through persistent env, which we can't do here.
                // Fall through to CMI resolution.
                let _ = alias_path;
                return None;
            }
            _ => return None,
        }
    }

    // Now find the type in the current signature
    match current_md_type {
        ModuleType::MtySignature(sig) => {
            for item in sig {
                if let SignatureItem::SigType(id, decl, _) = item {
                    if id.name() == type_name {
                        return Some(decl.clone());
                    }
                }
            }
            None
        }
        ModuleType::MtyAlias(_, alias_path) => {
            // Module is an alias — try resolving the type through the aliased CMI module
            resolve_type_through_modules(ctx, &Path::pdot(alias_path.clone(), type_name.to_string()))
        }
        _ => None,
    }
}

/// has a manifest (i.e., `type t = <body>`), expand it by substituting
/// the type parameters with the given arguments.
///
/// Returns `Some(expanded)` if expansion was possible, `None` otherwise.
fn try_expand_head<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let name = path.head_name().to_string();
            let args = args.clone();
            let path = path.clone();

            // Try stamp-based lookup first (most precise, handles CMI-loaded types)
            let stamp = match &path {
                Path::Pident(id) if id.stamp() != 0 => Some(id.stamp()),
                _ => None,
            };

            // For Pdot paths, get the full path name for qualified lookup
            let full_path_name = match &path {
                Path::Pdot(_, _, _) => Some(path.name()),
                _ => None,
            };

            drop(desc);

            // 1. Try stamp-based global store (precise, for CMI types with non-zero stamps)
            if let Some(stamp) = stamp {
                if let Some(store_decl) = ctx.find_type_decl_by_stamp(stamp) {
                    if let Some(manifest) = store_decl.type_manifest {
                        let params = &store_decl.type_params;
                        if params.is_empty() {
                            return Some(manifest);
                        } else if params.len() == args.len() {
                            return Some(subst_type(ctx, &params.clone(), &args, manifest));
                        }
                    }
                    return None;
                }
            }

            // 2. Try full qualified path lookup (for Pdot paths like Js.Promise.t)
            if let Some(ref _path_name) = full_path_name {
                // First check cached path store
                if let Some(store_decl) = ctx.find_type_decl_by_path(_path_name) {
                    if let Some(manifest) = store_decl.type_manifest {
                        let params = &store_decl.type_params;
                        if params.is_empty() {
                            return Some(manifest);
                        } else if params.len() == args.len() {
                            return Some(subst_type(ctx, &params.clone(), &args, manifest));
                        }
                    }
                    return None;
                }

                // Not cached — resolve by loading CMI files and walking module signatures
                if let Some(resolved_decl) = resolve_type_through_modules(ctx, &path) {
                    if let Some(manifest) = resolved_decl.type_manifest {
                        let params = &resolved_decl.type_params;
                        if params.is_empty() {
                            return Some(manifest);
                        } else if params.len() == args.len() {
                            return Some(subst_type(ctx, &params.clone(), &args, manifest));
                        }
                    }
                    return None;
                }

                // 2c. Try resolving Pdot paths through local env modules
                // For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
                // get its signature, and find type t in it
                if let Some(decl) = resolve_type_through_env(ctx, env, &path) {
                    if let Some(manifest) = decl.type_manifest {
                        let params = &decl.type_params;
                        if params.is_empty() {
                            return Some(manifest);
                        } else if params.len() == args.len() {
                            return Some(subst_type(ctx, &params.clone(), &args, manifest));
                        }
                    }
                    return None;
                }
            }

            // 3. Try env by path (ident-based first, then name fallback)
            if let Ok(env_decl) = env.lookup_type(&path) {
                if let Some(manifest) = env_decl.type_manifest {
                    let params = &env_decl.type_params;
                    if params.is_empty() {
                        return Some(manifest);
                    } else if params.len() == args.len() {
                        return Some(subst_type(ctx, &params.clone(), &args, manifest));
                    }
                    return None;
                }
                // Type found in env but no manifest — abstract type, fall through
            }

            // 4. Fall back to name-based global type declaration store
            if let Some(store_decl) = ctx.find_type_decl(&name) {
                if let Some(manifest) = store_decl.type_manifest {
                    let params = &store_decl.type_params;
                    if params.is_empty() {
                        return Some(manifest);
                    } else if params.len() == args.len() {
                        return Some(subst_type(ctx, &params.clone(), &args, manifest));
                    }
                }
            }

            None
        }
        _ => None,
    }
}

/// Fully expand a type through all aliases until it can't be expanded further.
/// Like OCaml's expand_head_opt: repeatedly calls try_expand_head until stable.
pub fn expand_head<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
) -> TypeExprRef {
    let mut current = ctx.repr(ty);
    // Limit iterations to prevent infinite loops
    for _ in 0..20 {
        match try_expand_head(ctx, env, current) {
            Some(expanded) => {
                let expanded = ctx.repr(expanded);
                if expanded == current {
                    break;
                }
                current = expanded;
            }
            None => break,
        }
    }
    current
}

/// Substitute type parameters in a type expression.
///
/// Given a mapping from parameter type refs to argument type refs,
/// create a copy of `ty` with all occurrences of parameters replaced by arguments.
fn subst_type(
    ctx: &TypeContext<'_>,
    params: &[TypeExprRef],
    args: &[TypeExprRef],
    ty: TypeExprRef,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    // Check if this type is one of the parameters
    for (i, param) in params.iter().enumerate() {
        if ctx.repr(*param) == ty {
            return args[i];
        }
    }

    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => {
            // Not a parameter, return as-is
            ty
        }
        TypeDesc::Tconstr { path, args: inner_args, .. } => {
            let new_args: Vec<TypeExprRef> = inner_args
                .iter()
                .map(|a| subst_type(ctx, params, args, *a))
                .collect();
            if new_args.iter().zip(inner_args.iter()).all(|(a, b)| *a == *b) {
                // No change
                ty
            } else {
                let path = path.clone();
                drop(desc);
                ctx.new_constr(path, new_args)
            }
        }
        TypeDesc::Tarrow { arg, ret, arity, .. } => {
            let new_arg_typ = subst_type(ctx, params, args, arg.typ);
            let new_ret = subst_type(ctx, params, args, *ret);
            if new_arg_typ == arg.typ && new_ret == *ret {
                ty
            } else {
                let lbl = arg.lbl.clone();
                let arity = *arity;
                drop(desc);
                ctx.new_arrow(lbl, new_arg_typ, new_ret, arity)
            }
        }
        TypeDesc::Ttuple(tl) => {
            let new_tl: Vec<TypeExprRef> = tl
                .iter()
                .map(|t| subst_type(ctx, params, args, *t))
                .collect();
            if new_tl.iter().zip(tl.iter()).all(|(a, b)| *a == *b) {
                ty
            } else {
                drop(desc);
                ctx.new_tuple(new_tl)
            }
        }
        _ => {
            // For other cases (Tpoly, Tvariant, Tobject, etc.), return as-is for now.
            // Full substitution would be more complex but these cases are rare for type aliases.
            ty
        }
    }
}

// ============================================================================
// Core Unification
// ============================================================================

/// Unify two types.
///
/// This is the main entry point for unification. It attempts to make
/// `t1` and `t2` equal by finding substitutions for type variables.
///
/// # Errors
///
/// Returns `TypeError::Unify` if the types cannot be unified.
pub fn unify<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    // Fast path: same reference
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);

    if t1 == t2 {
        return Ok(());
    }

    // Check if already unified (for cycles)
    if state.already_unified(t1, t2) {
        return Ok(());
    }

    // Mark as being unified
    state.mark_unified(t1, t2);

    // Get descriptors
    let result = unify_types(ctx, state, t1, t2);

    if let Err(TypeError::Unify(trace)) = &result {
        // Add this pair to the trace
        let mut new_trace = vec![(t1, t2)];
        new_trace.extend(trace.iter().cloned());
        return Err(TypeError::Unify(new_trace));
    }

    result
}

/// Internal unification logic.
fn unify_types<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    let desc1 = ctx.get_desc(t1);
    let desc2 = ctx.get_desc(t2);

    // Match on both descriptors
    match (&*desc1, &*desc2) {
        // Type variable on left - occurs check and link
        (TypeDesc::Tvar(_), _) => {
            drop(desc1);
            drop(desc2);

            if occurs(ctx, t1, t2) {
                return Err(TypeError::RecursiveType(t1));
            }

            update_level(ctx, ctx.get_level(t1), t2);
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Type variable on right - occurs check and link
        (_, TypeDesc::Tvar(_)) => {
            drop(desc1);
            drop(desc2);

            if occurs(ctx, t2, t1) {
                return Err(TypeError::RecursiveType(t2));
            }

            update_level(ctx, ctx.get_level(t2), t1);
            link_type(ctx, t2, t1);
            Ok(())
        }

        // Universal type variables
        (TypeDesc::Tunivar(n1), TypeDesc::Tunivar(n2)) if n1 == n2 => {
            drop(desc1);
            drop(desc2);
            update_level(ctx, ctx.get_level(t1), t2);
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Arrow types
        (
            TypeDesc::Tarrow {
                arg: arg1,
                ret: ret1,
                ..
            },
            TypeDesc::Tarrow {
                arg: arg2,
                ret: ret2,
                ..
            },
        ) => {
            let arg1_typ = arg1.typ;
            let ret1 = *ret1;
            let arg2_typ = arg2.typ;
            let ret2 = *ret2;
            drop(desc1);
            drop(desc2);

            // Unify argument types
            unify(ctx, state, arg1_typ, arg2_typ)?;
            // Unify return types
            unify(ctx, state, ret1, ret2)?;

            link_type(ctx, t1, t2);
            Ok(())
        }

        // Tuple types
        (TypeDesc::Ttuple(tl1), TypeDesc::Ttuple(tl2)) => {
            if tl1.len() != tl2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let pairs: Vec<_> = tl1.iter().zip(tl2.iter()).map(|(&a, &b)| (a, b)).collect();
            drop(desc1);
            drop(desc2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

            link_type(ctx, t1, t2);
            Ok(())
        }

        // Type constructors
        (
            TypeDesc::Tconstr {
                path: path1,
                args: args1,
                ..
            },
            TypeDesc::Tconstr {
                path: path2,
                args: args2,
                ..
            },
        ) => {
            if !path1.same(path2) {
                // Paths differ — check if they resolve to the same type name
                let name1 = path1.head_name();
                let name2 = path2.head_name();
                // Same name with different stamps: handles predef types (ref/Pervasives.ref),
                // and locally-defined types where stamp differences arise between
                // the type declaration and constructor return types
                if name1 == name2 && args1.len() == args2.len() {
                    let pairs: Vec<_> = args1.iter().zip(args2.iter()).map(|(&a, &b)| (a, b)).collect();
                    drop(desc1);
                    drop(desc2);
                    for (a, b) in pairs {
                        unify(ctx, state, a, b)?;
                    }
                    link_type(ctx, t1, t2);
                    return Ok(());
                }

                // Try fully expanding type aliases before giving up
                drop(desc1);
                drop(desc2);
                if let Some(env) = state.env() {
                    let exp1 = expand_head(ctx, env, t1);
                    let exp2 = expand_head(ctx, env, t2);
                    if exp1 != t1 || exp2 != t2 {
                        return unify(ctx, state, exp1, exp2);
                    }
                }
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            if args1.len() != args2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();
            drop(desc1);
            drop(desc2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

            link_type(ctx, t1, t2);
            Ok(())
        }

        // Polymorphic types
        (
            TypeDesc::Tpoly {
                body: body1,
                vars: vars1,
            },
            TypeDesc::Tpoly {
                body: body2,
                vars: vars2,
            },
        ) => {
            if vars1.len() != vars2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let body1 = *body1;
            let body2 = *body2;
            let var_pairs: Vec<_> = vars1
                .iter()
                .zip(vars2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();
            drop(desc1);
            drop(desc2);

            // First unify the bound variables
            for (v1, v2) in var_pairs {
                unify(ctx, state, v1, v2)?;
            }

            // Then unify the bodies
            unify(ctx, state, body1, body2)?;

            link_type(ctx, t1, t2);
            Ok(())
        }

        // Nil types (for objects)
        (TypeDesc::Tnil, TypeDesc::Tnil) => {
            drop(desc1);
            drop(desc2);
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Variant types
        (TypeDesc::Tvariant(row1), TypeDesc::Tvariant(row2)) => {
            let row1 = row1.clone();
            let row2 = row2.clone();
            drop(desc1);
            drop(desc2);

            unify_rows(ctx, state, &row1, &row2)?;
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Object types
        (
            TypeDesc::Tobject {
                fields: fields1, ..
            },
            TypeDesc::Tobject {
                fields: fields2, ..
            },
        ) => {
            let fields1 = *fields1;
            let fields2 = *fields2;
            drop(desc1);
            drop(desc2);

            unify_object_fields(ctx, state, fields1, fields2)?;
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Field types (for objects)
        (
            TypeDesc::Tfield {
                name: n1,
                typ: typ1,
                rest: rest1,
                ..
            },
            TypeDesc::Tfield {
                name: n2,
                typ: typ2,
                rest: rest2,
                ..
            },
        ) => {
            if n1 != n2 {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let typ1 = *typ1;
            let typ2 = *typ2;
            let rest1 = *rest1;
            let rest2 = *rest2;
            drop(desc1);
            drop(desc2);

            unify(ctx, state, typ1, typ2)?;
            unify(ctx, state, rest1, rest2)?;
            link_type(ctx, t1, t2);
            Ok(())
        }

        // Package types
        (
            TypeDesc::Tpackage {
                path: path1,
                args: args1,
                ..
            },
            TypeDesc::Tpackage {
                path: path2,
                args: args2,
                ..
            },
        ) => {
            if !path1.same(path2) {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            if args1.len() != args2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();
            drop(desc1);
            drop(desc2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

            link_type(ctx, t1, t2);
            Ok(())
        }

        // Substitution types (used during copying)
        (TypeDesc::Tsubst(sub1), _) => {
            let sub1 = *sub1;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, sub1, t2)
        }

        (_, TypeDesc::Tsubst(sub2)) => {
            let sub2 = *sub2;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, t1, sub2)
        }

        // Link types (should have been resolved by repr)
        (TypeDesc::Tlink(link1), _) => {
            let link1 = *link1;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, link1, t2)
        }

        (_, TypeDesc::Tlink(link2)) => {
            let link2 = *link2;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, t1, link2)
        }

        // Tpoly with empty vars: unwrap and retry
        (TypeDesc::Tpoly { body, vars }, _) if vars.is_empty() => {
            let body = *body;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, body, t2)
        }
        (_, TypeDesc::Tpoly { body, vars }) if vars.is_empty() => {
            let body = *body;
            drop(desc1);
            drop(desc2);
            unify(ctx, state, t1, body)
        }

        // Types don't match — try fully expanding type aliases as last resort
        _ => {
            let is_constr1 = matches!(&*desc1, TypeDesc::Tconstr { .. });
            let is_constr2 = matches!(&*desc2, TypeDesc::Tconstr { .. });
            drop(desc1);
            drop(desc2);

            if (is_constr1 || is_constr2) {
                if let Some(env) = state.env() {
                    // Fully expand both sides through all aliases
                    let exp1 = if is_constr1 { expand_head(ctx, env, t1) } else { t1 };
                    let exp2 = if is_constr2 { expand_head(ctx, env, t2) } else { t2 };
                    // Only retry if at least one side actually changed
                    if exp1 != t1 || exp2 != t2 {
                        return unify(ctx, state, exp1, exp2);
                    }
                }
            }

            Err(TypeError::Unify(vec![(t1, t2)]))
        }
    }
}

// ============================================================================
// Row Unification
// ============================================================================

/// Unify two row types (for polymorphic variants).
fn unify_rows<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    row1: &RowDesc,
    row2: &RowDesc,
) -> TypeResult<()> {
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);

    // Unify the fields
    for (label, field1) in &row1.row_fields {
        // Find matching field in row2
        if let Some((_, field2)) = row2.row_fields.iter().find(|(l, _)| l == label) {
            unify_row_field(ctx, state, field1, field2)?;
        } else if row2.row_closed {
            // Field not found and row is closed - error
            return Err(TypeError::Unify(vec![]));
        }
        // If row is open, the field might be added later
    }

    // Check the reverse
    for (label, _field2) in &row2.row_fields {
        if !row1.row_fields.iter().any(|(l, _)| l == label) && row1.row_closed {
            return Err(TypeError::Unify(vec![]));
        }
    }

    // Unify the "more" types
    let more1 = row_more(ctx, &row1);
    let more2 = row_more(ctx, &row2);
    unify(ctx, state, more1, more2)
}

/// Unify two row fields.
fn unify_row_field<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    field1: &RowField,
    field2: &RowField,
) -> TypeResult<()> {
    match (field1, field2) {
        (RowField::Rpresent(Some(t1)), RowField::Rpresent(Some(t2))) => unify(ctx, state, *t1, *t2),
        (RowField::Rpresent(None), RowField::Rpresent(None)) => Ok(()),
        (RowField::Rabsent, RowField::Rabsent) => Ok(()),
        (RowField::Reither { types: types1, .. }, RowField::Rpresent(t2_opt)) => {
            if let Some(t2) = t2_opt {
                for t1 in types1 {
                    unify(ctx, state, *t1, *t2)?;
                }
            }
            Ok(())
        }
        (RowField::Rpresent(t1_opt), RowField::Reither { types: types2, .. }) => {
            if let Some(t1) = t1_opt {
                for t2 in types2 {
                    unify(ctx, state, *t1, *t2)?;
                }
            }
            Ok(())
        }
        (
            RowField::Reither {
                constant: c1,
                types: types1,
                ..
            },
            RowField::Reither {
                constant: c2,
                types: types2,
                ..
            },
        ) => {
            if c1 != c2 {
                return Err(TypeError::Unify(vec![]));
            }
            for (t1, t2) in types1.iter().zip(types2.iter()) {
                unify(ctx, state, *t1, *t2)?;
            }
            Ok(())
        }
        _ => Err(TypeError::Unify(vec![])),
    }
}

/// Unify object fields.
fn unify_object_fields<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    fields1: TypeExprRef,
    fields2: TypeExprRef,
) -> TypeResult<()> {
    let fields1 = ctx.repr(fields1);
    let fields2 = ctx.repr(fields2);

    // Get field descriptors
    let desc1 = ctx.get_desc(fields1);
    let desc2 = ctx.get_desc(fields2);

    match (&*desc1, &*desc2) {
        (TypeDesc::Tnil, TypeDesc::Tnil) => {
            drop(desc1);
            drop(desc2);
            Ok(())
        }
        (
            TypeDesc::Tfield {
                name: n1,
                typ: t1,
                rest: r1,
                ..
            },
            TypeDesc::Tfield {
                name: n2,
                typ: t2,
                rest: r2,
                ..
            },
        ) if n1 == n2 => {
            let t1 = *t1;
            let t2 = *t2;
            let r1 = *r1;
            let r2 = *r2;
            drop(desc1);
            drop(desc2);

            unify(ctx, state, t1, t2)?;
            unify_object_fields(ctx, state, r1, r2)
        }
        _ => {
            drop(desc1);
            drop(desc2);
            Err(TypeError::Unify(vec![(fields1, fields2)]))
        }
    }
}

// ============================================================================
// Generalization
// ============================================================================

/// Generalize a type.
///
/// This marks all type variables at or above the current level as generic,
/// making the type polymorphic.
pub fn generalize(ctx: &TypeContext<'_>, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    let current = ctx.current_level();

    if level > current {
        // Mark as generic
        ctx.set_level(ty, GENERIC_LEVEL);
    }

    // Recursively generalize children
    iter_type_expr(ctx, ty, |child| {
        generalize(ctx, child);
    });
}

/// Generalize the structure of a type at a given level.
pub fn generalize_structure(ctx: &TypeContext<'_>, var_level: i32, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);

    if level > var_level {
        ctx.set_level(ty, var_level);
    }

    // Recursively process children
    iter_type_expr(ctx, ty, |child| {
        generalize_structure(ctx, var_level, child);
    });
}

// ============================================================================
// Instantiation
// ============================================================================

/// Create an instance of a type by copying it.
///
/// This replaces all generic type variables with fresh ones,
/// creating a new instance of a polymorphic type.
pub fn instance(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = std::collections::HashMap::new();
    copy_type_cached(ctx, ty, &mut cache)
}

/// Instantiate a constructor description, creating fresh type variables for its
/// result type and argument types while sharing the same variable substitutions.
/// Matches OCaml's Ctype.instance_constructor.
pub fn instance_constructor(ctx: &TypeContext<'_>, cstr: &super::ConstructorDescription) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = std::collections::HashMap::new();
    let ty_res = copy_type_cached(ctx, cstr.cstr_res, &mut cache);
    let ty_args: Vec<TypeExprRef> = cstr.cstr_args.iter()
        .map(|&arg| copy_type_cached(ctx, arg, &mut cache))
        .collect();
    (ty_args, ty_res)
}

/// Instantiate a label description, creating fresh type variables for its
/// result type (record type) and argument type (field type) while sharing
/// the same variable substitutions between them.
/// Handles Tpoly unwrapping like OCaml's instance_label in ctype.ml.
pub fn instance_label(ctx: &TypeContext<'_>, lbl: &super::LabelDescription) -> (TypeExprRef, TypeExprRef) {
    let mut cache = std::collections::HashMap::new();
    let ty_res = copy_type_deep(ctx, lbl.lbl_res, &mut cache);
    // OCaml's instance_label unwraps Tpoly before copying the field type
    let arg_repr = ctx.repr(lbl.lbl_arg);
    let ty_arg = {
        let desc = ctx.get_desc(arg_repr);
        match &*desc {
            super::TypeDesc::Tpoly { body, .. } => {
                copy_type_deep(ctx, *body, &mut cache)
            }
            _ => copy_type_deep(ctx, lbl.lbl_arg, &mut cache),
        }
    };
    (ty_arg, ty_res)
}

/// Deep copy a type, creating fresh type variables regardless of level.
/// Used for label instantiation where types may not be at GENERIC_LEVEL
/// but still need fresh copies to avoid sharing across different uses.
pub fn copy_type_deep(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    if let Some(&cached) = cache.get(&ty) {
        return cached;
    }

    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvar(_name) => {
            // OCaml's copy_type creates anonymous type variables (None name)
            // for fresh copies, matching the Tvar None in the sexp output
            let fresh = ctx.new_var(None);
            cache.insert(ty, fresh);
            fresh
        }
        TypeDesc::Tarrow { arg, ret, arity, .. } => {
            // Create placeholder first to handle cycles
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let arg_lbl = arg.lbl.clone();
            let new_arg_typ = copy_type_deep(ctx, arg.typ, cache);
            let new_ret = copy_type_deep(ctx, *ret, cache);
            let new_ty = ctx.new_arrow(arg_lbl, new_arg_typ, new_ret, *arity);
            // Update placeholder to point to the real type
            ctx.set_desc(placeholder, TypeDesc::Tlink(new_ty));
            cache.insert(ty, new_ty);
            new_ty
        }
        TypeDesc::Ttuple(types) => {
            let new_types: Vec<_> = types.iter().map(|t| copy_type_deep(ctx, *t, cache)).collect();
            ctx.new_tuple(new_types)
        }
        TypeDesc::Tconstr { path, args, .. } => {
            let new_args: Vec<_> = args.iter().map(|t| copy_type_deep(ctx, *t, cache)).collect();
            ctx.new_constr(path.clone(), new_args)
        }
        TypeDesc::Tpoly { body, vars } => {
            let new_vars: Vec<_> = vars.iter().map(|t| copy_type_deep(ctx, *t, cache)).collect();
            let new_body = copy_type_deep(ctx, *body, cache);
            ctx.new_poly(new_body, new_vars)
        }
        TypeDesc::Tlink(target) => copy_type_deep(ctx, *target, cache),
        TypeDesc::Tnil | TypeDesc::Tunivar(_) => ty, // Return as-is
        _ => ty, // For other types, return as-is for now
    }
}

/// Copy a type, creating fresh type variables for generic ones.
pub fn copy_type(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = std::collections::HashMap::new();
    copy_type_cached(ctx, ty, &mut cache)
}

/// Copy a type with a cache to preserve sharing for type variables.
/// Only Tvar nodes are cached (to preserve sharing for polymorphic types like 'a -> 'a -> 'a).
/// Tconstr and other structural nodes are NOT cached, creating fresh copies each time.
/// This matches OCaml's behavior where Tsubst markers preserve sharing for Tvars
/// but the resulting type structure after unification has distinct Tconstr nodes.
fn copy_type_cached(ctx: &TypeContext<'_>, ty: TypeExprRef, cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>) -> TypeExprRef {
    let ty = ctx.repr(ty);

    // Check cache first — but only for Tvar (to preserve polymorphic sharing)
    if let Some(&cached) = cache.get(&ty) {
        return cached;
    }
    let level = ctx.get_level(ty);

    // Enum to hold what action to take, avoiding borrow issues
    enum CopyAction {
        NewVar(Option<String>),
        NewUnivar(Option<String>),
        Arrow {
            arg_lbl: super::asttypes::ArgLabel,
            arg_typ: TypeExprRef,
            ret: TypeExprRef,
            arity: Option<i32>,
        },
        Tuple(Vec<TypeExprRef>),
        Constr {
            path: Path,
            args: Vec<TypeExprRef>,
        },
        Poly {
            body: TypeExprRef,
            vars: Vec<TypeExprRef>,
        },
        Variant(RowDesc),
        Link(TypeExprRef),
        ReturnSelf,
    }

    // Determine action based on type level and descriptor
    let action = {
        let desc = ctx.get_desc(ty);

        // If the type is generic, create a fresh variable
        if level == GENERIC_LEVEL {
            match &*desc {
                TypeDesc::Tvar(_name) => CopyAction::NewVar(None), // OCaml creates anonymous copies
                TypeDesc::Tunivar(name) => CopyAction::NewUnivar(name.clone()),
                _ => {
                    // Fall through to structural copy
                    match &*desc {
                        TypeDesc::Tarrow {
                            arg, ret, arity, ..
                        } => CopyAction::Arrow {
                            arg_lbl: arg.lbl.clone(),
                            arg_typ: arg.typ,
                            ret: *ret,
                            arity: *arity,
                        },
                        TypeDesc::Ttuple(types) => CopyAction::Tuple(types.clone()),
                        TypeDesc::Tconstr { path, args, .. } => CopyAction::Constr {
                            path: path.clone(),
                            args: args.clone(),
                        },
                        TypeDesc::Tpoly { body, vars } => CopyAction::Poly {
                            body: *body,
                            vars: vars.clone(),
                        },
                        TypeDesc::Tvariant(row) => CopyAction::Variant(row.clone()),
                        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                            CopyAction::Link(*target)
                        }
                        _ => CopyAction::ReturnSelf,
                    }
                }
            }
        } else {
            // Not generic, copy structure
            match &*desc {
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => CopyAction::ReturnSelf,
                TypeDesc::Tarrow {
                    arg, ret, arity, ..
                } => CopyAction::Arrow {
                    arg_lbl: arg.lbl.clone(),
                    arg_typ: arg.typ,
                    ret: *ret,
                    arity: *arity,
                },
                TypeDesc::Ttuple(types) => CopyAction::Tuple(types.clone()),
                TypeDesc::Tconstr { path, args, .. } => CopyAction::Constr {
                    path: path.clone(),
                    args: args.clone(),
                },
                TypeDesc::Tpoly { body, vars } => CopyAction::Poly {
                    body: *body,
                    vars: vars.clone(),
                },
                TypeDesc::Tvariant(row) => CopyAction::Variant(row.clone()),
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => CopyAction::Link(*target),
                _ => CopyAction::ReturnSelf,
            }
        }
    };

    // Track if this is a Tvar copy (for caching)
    let is_var_copy = matches!(action, CopyAction::NewVar(_));

    // Execute the action without holding the borrow
    let result = match action {
        CopyAction::NewVar(name) => ctx.new_var(name),
        CopyAction::NewUnivar(name) => ctx.new_univar(name),
        CopyAction::Arrow {
            arg_lbl,
            arg_typ,
            ret,
            arity,
        } => {
            let arg_copy = copy_type_cached(ctx, arg_typ, cache);
            let ret_copy = copy_type_cached(ctx, ret, cache);
            ctx.new_arrow(arg_lbl, arg_copy, ret_copy, arity)
        }
        CopyAction::Tuple(types) => {
            let types_copy: Vec<_> = types.iter().map(|t| copy_type_cached(ctx, *t, cache)).collect();
            ctx.new_tuple(types_copy)
        }
        CopyAction::Constr { path, args } => {
            let args_copy: Vec<_> = args.iter().map(|t| copy_type_cached(ctx, *t, cache)).collect();
            ctx.new_constr(path, args_copy)
        }
        CopyAction::Poly { body, vars } => {
            let body_copy = copy_type_cached(ctx, body, cache);
            let vars_copy: Vec<_> = vars.iter().map(|v| copy_type_cached(ctx, *v, cache)).collect();
            ctx.new_poly(body_copy, vars_copy)
        }
        CopyAction::Variant(row) => {
            let row_copy = copy_row_cached(ctx, &row, cache);
            ctx.new_variant(row_copy)
        }
        CopyAction::Link(target) => copy_type_cached(ctx, target, cache),
        CopyAction::ReturnSelf => ty,
    };

    // Only cache Tvar copies to preserve sharing for polymorphic types.
    // We DON'T cache Tconstr/Tarrow/etc so each copy is fresh, avoiding
    // artificial sharing that would cause incorrect cycle detection.
    if is_var_copy {
        cache.insert(ty, result);
    }
    result
}

/// Copy a row descriptor.
fn copy_row_cached(ctx: &TypeContext<'_>, row: &RowDesc, cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>) -> RowDesc {
    RowDesc {
        row_fields: row
            .row_fields
            .iter()
            .map(|(label, field)| (label.clone(), copy_row_field_cached(ctx, field, cache)))
            .collect(),
        row_more: copy_type_cached(ctx, row.row_more, cache),
        row_closed: row.row_closed,
        row_fixed: row.row_fixed,
        row_name: row.row_name.as_ref().map(|(path, types)| {
            (
                path.clone(),
                types.iter().map(|t| copy_type_cached(ctx, *t, cache)).collect(),
            )
        }),
    }
}

/// Copy a row field.
fn copy_row_field_cached(ctx: &TypeContext<'_>, field: &RowField, cache: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>) -> RowField {
    match field {
        RowField::Rpresent(Some(ty)) => RowField::Rpresent(Some(copy_type_cached(ctx, *ty, cache))),
        RowField::Rpresent(None) => RowField::Rpresent(None),
        RowField::Rabsent => RowField::Rabsent,
        RowField::Reither {
            constant,
            types,
            matched,
            link,
        } => RowField::Reither {
            constant: *constant,
            types: types.iter().map(|t| copy_type_cached(ctx, *t, cache)).collect(),
            matched: *matched,
            link: *link,
        },
    }
}

// ============================================================================
// Type Checking Helpers
// ============================================================================

/// Check if a type is a function type.
pub fn is_function(ctx: &TypeContext<'_>, ty: TypeExprRef) -> bool {
    let ty = ctx.repr(ty);
    matches!(*ctx.get_desc(ty), TypeDesc::Tarrow { .. })
}

/// Get the arity of a function type (number of arguments).
pub fn function_arity(ctx: &TypeContext<'_>, ty: TypeExprRef) -> usize {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tarrow { ret, .. } => {
            let ret = *ret;
            drop(desc);
            1 + function_arity(ctx, ret)
        }
        _ => 0,
    }
}

/// Extract the argument and return types from an arrow type.
pub fn split_arrow(ctx: &TypeContext<'_>, ty: TypeExprRef) -> Option<(TypeExprRef, TypeExprRef)> {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tarrow { arg, ret, .. } => Some((arg.typ, *ret)),
        _ => None,
    }
}

/// Extract the argument type, label, and return type from an arrow type.
pub fn split_arrow_with_label(ctx: &TypeContext<'_>, ty: TypeExprRef) -> Option<(super::ArgLabel, TypeExprRef, TypeExprRef)> {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tarrow { arg, ret, .. } => Some((arg.lbl.clone(), arg.typ, *ret)),
        _ => None,
    }
}

/// Extract the inner type from option<T>, returning T.
/// Returns None if the type is not option<T>.
pub fn extract_option_type(ctx: &TypeContext<'_>, ty: TypeExprRef) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if path.head_name() == "option" && args.len() == 1 {
                Some(args[0])
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Get the element types of a tuple.
pub fn tuple_elements(ctx: &TypeContext<'_>, ty: TypeExprRef) -> Option<Vec<TypeExprRef>> {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Ttuple(types) => Some(types.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::ident::Ident;

    #[test]
    fn test_unify_same_type() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let mut state = UnifyState::new();

        let t = ctx.new_var(None);
        assert!(unify(&ctx, &mut state, t, t).is_ok());
    }

    #[test]
    fn test_unify_var_with_type() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let mut state = UnifyState::new();

        let var = ctx.new_var(None);
        let int_id = Ident::create_persistent("int");
        let int_path = Path::pident(int_id);
        let int_type = ctx.new_constr(int_path, vec![]);

        assert!(unify(&ctx, &mut state, var, int_type).is_ok());

        // After unification, var should point to int_type
        assert_eq!(ctx.repr(var), int_type);
    }

    #[test]
    fn test_unify_tuples() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let mut state = UnifyState::new();

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let tuple1 = ctx.new_tuple(vec![a, b]);
        let tuple2 = ctx.new_tuple(vec![a, b]);

        assert!(unify(&ctx, &mut state, tuple1, tuple2).is_ok());
    }

    #[test]
    fn test_unify_tuple_length_mismatch() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);
        let mut state = UnifyState::new();

        let a = ctx.new_var(None);
        let tuple1 = ctx.new_tuple(vec![a]);
        let tuple2 = ctx.new_tuple(vec![a, a]);

        assert!(unify(&ctx, &mut state, tuple1, tuple2).is_err());
    }

    #[test]
    fn test_occurs_check() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let tuple = ctx.new_tuple(vec![a, b]);

        assert!(!occurs(&ctx, a, b));
        assert!(occurs(&ctx, a, a));
        assert!(occurs(&ctx, a, tuple));
    }

    #[test]
    fn test_generalize_and_instance() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

        // Create a type at the current level
        ctx.begin_def();
        let a = ctx.new_var(Some("a".to_string()));
        ctx.end_def();

        // Generalize it
        generalize(&ctx, a);
        assert_eq!(ctx.get_level(a), GENERIC_LEVEL);

        // Create an instance
        let a_instance = instance(&ctx, a);
        assert_ne!(a, a_instance);
    }

    #[test]
    fn test_is_function() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(a, b);

        assert!(!is_function(&ctx, a));
        assert!(is_function(&ctx, arrow));
    }

    #[test]
    fn test_function_arity() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let c = ctx.new_var(None);

        // a -> b
        let f1 = ctx.new_arrow_simple(a, b);
        assert_eq!(function_arity(&ctx, f1), 1);

        // a -> b -> c
        let f2 = ctx.new_arrow_simple(a, ctx.new_arrow_simple(b, c));
        assert_eq!(function_arity(&ctx, f2), 2);
    }
}
