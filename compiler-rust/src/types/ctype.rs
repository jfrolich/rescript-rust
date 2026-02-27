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

use super::btype::{iter_type_expr, row_fixed, row_more, row_repr};
use super::context::TypeContext;
use super::env::Env;
use super::path::Path;
use super::type_expr::{FieldKind, GENERIC_LEVEL, RowDesc, RowField, TypeDesc, TypeExprRef};
use super::variance::{Variance, VarianceFlag};
use std::collections::{HashMap, HashSet};

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
    pub mode: UnifyMode,

    /// Whether we're generating equations (for GADTs).
    pub generate_equations: bool,

    /// Whether to assume type constructors are injective.
    pub assume_injective: bool,

    /// Environment snapshot for type alias expansion during unification.
    /// Store an owned clone to avoid dangling pointers when nested typing
    /// temporarily switches environments.
    env: Option<Env>,

    /// Current recursive call depth in `unify`.
    recursion_depth: usize,
}

impl UnifyState {
    /// Create a new unify state.
    pub fn new() -> Self {
        UnifyState {
            unified_pairs: HashSet::new(),
            mode: UnifyMode::Expression,
            generate_equations: false,
            assume_injective: false,
            env: None,
            recursion_depth: 0,
        }
    }

    /// Create a state for pattern matching.
    pub fn pattern_mode() -> Self {
        UnifyState {
            unified_pairs: HashSet::new(),
            mode: UnifyMode::Pattern,
            generate_equations: true,
            assume_injective: false,
            env: None,
            recursion_depth: 0,
        }
    }

    /// Set the environment snapshot for type alias expansion.
    pub fn set_env(&mut self, env: &Env) {
        self.env = Some(env.clone());
    }

    /// Get the environment reference, if set.
    pub fn env(&self) -> Option<&Env> {
        self.env.as_ref()
    }

    /// Get a mutable reference to the environment, if set.
    pub fn env_mut(&mut self) -> Option<&mut Env> {
        self.env.as_mut()
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
// GADT Equation Support
// ============================================================================

/// Check if a type path points to an instantiable newtype (abstract type with
/// newtype_level set). Matches OCaml's `is_instantiable` in ctype.ml.
fn is_instantiable(env: &Env, path: &Path) -> bool {
    // Check local constraints first (GADT equations may have been added)
    if let Some(decl) = env.find_local_constraint(path) {
        return matches!(decl.type_kind, super::TypeKind::TypeAbstract)
            && decl.type_manifest.is_none()
            && decl.type_newtype_level.is_some();
    }
    // Then check normal type table by name
    let name = path.head_name();
    if let Ok(decl) = env.find_type(name) {
        matches!(decl.type_kind, super::TypeKind::TypeAbstract)
            && decl.type_manifest.is_none()
            && decl.type_newtype_level.is_some()
    } else {
        false
    }
}

/// Add a GADT equation: source_path = destination type.
/// Creates a local constraint with a manifest type declaration.
/// Matches OCaml's `add_gadt_equation` in ctype.ml.
fn add_gadt_equation(
    ctx: &TypeContext<'_>,
    env: &mut Env,
    source_path: &Path,
    destination: TypeExprRef,
) {
    // local_non_recursive_abbrev check: destination must not reference source
    let dest_repr = ctx.repr(destination);
    let is_recursive = matches!(
        &*ctx.get_desc(dest_repr),
        TypeDesc::Tconstr { path, .. } if path.same(source_path)
    );
    if is_recursive {
        return;
    }

    // duplicate_type: structural copy of destination
    let destination_copy = subst_identity_copy(ctx, destination);

    // Find the newtype level from the source declaration
    let source_lev = env
        .find_local_constraint(source_path)
        .or_else(|| env.find_type(source_path.head_name()).ok())
        .and_then(|decl| decl.type_newtype_level);

    // Create a new declaration with manifest = destination_copy
    let decl = super::TypeDeclaration {
        type_params: vec![],
        type_arity: 0,
        type_kind: super::TypeKind::TypeAbstract,
        type_private: super::PrivateFlag::Public,
        type_manifest: Some(destination_copy),
        type_variance: vec![],
        type_newtype_level: source_lev,
        type_loc: crate::location::Location::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_unboxed: super::UnboxedStatus::FALSE_FALSE,
        type_inlined_types: vec![],
        type_path: None,
    };

    // Add as a local constraint
    env.add_local_constraint(source_path.clone(), decl);
}

// ============================================================================
// Occurs Check
// ============================================================================

/// Check if a type variable occurs in another type.
///
/// This is the occurs check that prevents infinite types.
/// Returns `true` if `needle` occurs in `haystack`.
pub fn occurs(ctx: &TypeContext<'_>, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    fn occurs_rec(
        ctx: &TypeContext<'_>,
        needle: TypeExprRef,
        haystack: TypeExprRef,
        visited: &mut HashSet<TypeExprRef>,
    ) -> bool {
        let haystack = ctx.repr(haystack);
        if needle == haystack {
            return true;
        }
        if !visited.insert(haystack) {
            return false;
        }

        // OCaml ctype.ml occur_rec does not recurse into object/variant nodes
        // for regular expression-mode occurs checks.
        let should_recurse = {
            let desc = ctx.get_desc(haystack);
            !matches!(&*desc, TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_))
        };
        if !should_recurse {
            return false;
        }

        let mut found = false;
        iter_type_expr(ctx, haystack, |child| {
            if !found && occurs_rec(ctx, needle, child, visited) {
                found = true;
            }
        });
        found
    }

    let needle = ctx.repr(needle);
    let mut visited = HashSet::new();
    occurs_rec(ctx, needle, haystack, &mut visited)
}

/// Deep occur check - follows type constructors.
pub fn deep_occur(ctx: &TypeContext<'_>, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    fn deep_occur_rec(
        ctx: &TypeContext<'_>,
        needle: TypeExprRef,
        haystack: TypeExprRef,
        visited: &mut HashSet<TypeExprRef>,
    ) -> bool {
        let haystack = ctx.repr(haystack);
        if needle == haystack {
            return true;
        }
        if !visited.insert(haystack) {
            return false;
        }

        let desc = ctx.get_desc(haystack);
        match &*desc {
            TypeDesc::Tconstr { args, .. } => args
                .iter()
                .any(|arg| deep_occur_rec(ctx, needle, *arg, visited)),
            _ => {
                drop(desc);
                let mut found = false;
                iter_type_expr(ctx, haystack, |child| {
                    if !found && deep_occur_rec(ctx, needle, child, visited) {
                        found = true;
                    }
                });
                found
            }
        }
    }

    let needle = ctx.repr(needle);
    let mut visited = HashSet::new();
    deep_occur_rec(ctx, needle, haystack, &mut visited)
}

// ============================================================================
// Link Types
// ============================================================================

/// Link two types together (for unification).
///
/// This makes `t1` point to `t2`, effectively making them the same type.
/// The level of `t2` is updated to be the minimum of both levels.
pub fn link_type(ctx: &TypeContext<'_>, t1: TypeExprRef, t2: TypeExprRef) {
    let t1_repr = ctx.repr(t1);
    let t2_repr = ctx.repr(t2);
    let source_name = {
        let desc = ctx.get_desc(t1_repr);
        match &*desc {
            TypeDesc::Tvar(name) => Some(name.clone()),
            _ => None,
        }
    };
    let target_name = {
        let desc = ctx.get_desc(t2_repr);
        match &*desc {
            TypeDesc::Tvar(name) => Some(name.clone()),
            _ => None,
        }
    };

    // Match OCaml Btype.link_type naming behavior:
    // - propagate source name to an anonymous target variable
    // - when both are named, keep source name if source level is lower
    match (source_name, target_name) {
        (Some(Some(name)), Some(None)) => {
            ctx.set_desc(t2_repr, TypeDesc::Tvar(Some(name)));
        }
        (Some(Some(name)), Some(Some(_existing))) => {
            if ctx.get_level(t1_repr) < ctx.get_level(t2_repr) {
                ctx.set_desc(t2_repr, TypeDesc::Tvar(Some(name)));
            }
        }
        _ => {}
    }

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

/// Environment-aware update_level matching OCaml ctype.ml:652-676.
/// When lowering the level of a Tconstr whose constructor's binding level
/// is above the target, expand the abbreviation and link the original type
/// to its expansion. This normalizes module-alias paths (e.g.,
/// `Pdot(Pident("U"), "t")` → `Pident("list")`).
pub fn update_level_expand<'a>(ctx: &'a TypeContext<'a>, env: &Env, level: i32, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let current = ctx.get_level(ty);

    if level < current {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, .. } => {
                let path = path.clone();
                // OCaml ctype.ml:659: when level < get_level env p, try to expand.
                // get_level returns Path.binding_time which is the root ident's stamp.
                let binding_time = path_binding_time(&path);
                let should_try_expand = current != GENERIC_LEVEL && level < binding_time;
                drop(desc);
                // Guard: skip expansion for all local Pident types (not predef).
                // OCaml's update_level tries expansion but often fails for local types
                // (Env.find_type raises Not_found). In Rust, try_expand_head succeeds
                // more often, causing unwanted alias expansion that changes type identity.
                // Preserving local Pident aliases matches OCaml's effective behavior.
                let is_local_pident = matches!(&path, Path::Pident(id) if id.stamp() != 0 && !is_predef_type_name(id.name()));
                if should_try_expand && !is_local_pident {
                    if let Some(expanded) = try_expand_head(ctx, env, ty) {
                        let expanded = ctx.repr(expanded);
                        if should_preserve_local_t_alias_during_level_update(
                            ctx, &path, expanded,
                        )
                        {
                            ctx.set_level(ty, level);
                            iter_type_expr(ctx, ty, |child| {
                                update_level_expand(ctx, env, level, child);
                            });
                            return;
                        }
                        if expanded != ty && !deep_occur(ctx, ty, expanded) {
                            link_type(ctx, ty, expanded);
                            // Recursively update the expansion
                            update_level_expand(ctx, env, level, expanded);
                            return;
                        }
                    }
                }
                // Couldn't expand; just set level and recurse
                ctx.set_level(ty, level);
                iter_type_expr(ctx, ty, |child| {
                    update_level_expand(ctx, env, level, child);
                });
            }
            _ => {
                drop(desc);
                ctx.set_level(ty, level);
                iter_type_expr(ctx, ty, |child| {
                    update_level_expand(ctx, env, level, child);
                });
            }
        }
    }
}

/// Get the binding time of a path (matches OCaml's Path.binding_time).
/// Returns the stamp of the root identifier.
fn path_binding_time(path: &Path) -> i32 {
    match path {
        Path::Pident(id) => id.stamp() as i32,
        Path::Pdot(parent, _, _) => path_binding_time(parent),
        Path::Papply(p1, p2) => {
            std::cmp::max(path_binding_time(p1), path_binding_time(p2))
        }
    }
}

/// Check if a path is "local" (non-persistent root identifier with non-zero stamp).
/// Matches OCaml's `Path.binding_time > 0` — local module aliases and type aliases
/// have high stamps, while persistent (CMI-loaded) modules have stamp 0.
fn is_local_path(path: &Path) -> bool {
    match path {
        Path::Pident(id) => id.stamp() != 0,
        Path::Pdot(parent, _, _) => is_local_path(parent),
        Path::Papply(p1, p2) => is_local_path(p1) || is_local_path(p2),
    }
}

// ============================================================================
// Predef Type Names
// ============================================================================

/// Check if a type name is a predef (builtin) type.
/// Predef types may appear under different paths (e.g., `ref` vs `Pervasives.ref`)
/// but should be treated as the same type during unification.
fn is_predef_type_name(name: &str) -> bool {
    matches!(
        name,
        "int"
            | "char"
            | "float"
            | "bool"
            | "unit"
            | "exn"
            | "array"
            | "list"
            | "option"
            | "nativeint"
            | "int32"
            | "int64"
            | "lazy_t"
            | "bytes"
            | "string"
            | "ref"
            | "result"
            | "dict"
            | "promise"
            | "unknown"
            | "bigint"
            | "symbol"
            | "regexp"
    )
}

fn should_preserve_local_t_alias_during_level_update(
    ctx: &TypeContext<'_>,
    original_path: &Path,
    expanded: TypeExprRef,
) -> bool {
    let is_local_t_path = matches!(
        original_path,
        Path::Pdot(parent, name, _) if name == "t" && is_local_path(parent)
    );
    let is_local_cmp_path = matches!(
        original_path,
        Path::Pdot(parent, name, _) if name == "cmp" && is_local_path(parent)
    );
    if !is_local_t_path && !is_local_cmp_path {
        return false;
    }

    let expanded = ctx.repr(expanded);
    let desc = ctx.get_desc(expanded);
    matches!(&*desc, TypeDesc::Tconstr { path, .. } if {
        if is_local_t_path {
            let head = path.head_name();
            head == "array" || head == "int"
        } else {
            path.last() == "cmp"
        }
    })
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
fn find_cmi_file(load_paths: &[std::path::PathBuf], module_name: &str) -> Option<String> {
    let cmi_filename = format!("{}.cmi", module_name);
    for dir in load_paths {
        let exact = dir.join(&cmi_filename);
        if exact.exists() {
            return Some(exact.to_string_lossy().into_owned());
        }
        if let Some(first_char) = cmi_filename.chars().next() {
            if first_char.is_ascii_uppercase() {
                let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &cmi_filename[1..]);
                let uncap_path = dir.join(&uncap);
                if uncap_path.exists() {
                    return Some(uncap_path.to_string_lossy().into_owned());
                }
            }
        }
    }
    None
}

fn resolve_module_signature_through_cmi<'a>(
    ctx: &'a TypeContext<'a>,
    load_paths: &[std::path::PathBuf],
    module_path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<super::decl::Signature> {
    use crate::cmi::{cmi_format, sig_reader::SigReadContext};
    use crate::types::decl::{ModuleType, SignatureItem};

    // Keep visited module paths for the full resolution walk. Removing entries
    // re-opens alias cycles (`A -> B -> A`) and can recurse until stack overflow.
    if !visiting.insert(module_path.clone()) {
        return None;
    }

    let result = match module_path {
        Path::Pident(id) => {
            let full_path = find_cmi_file(load_paths, id.name())?;
            let cmi = cmi_format::read_cmi(&full_path).ok()?;
            let mut sig_ctx = SigReadContext::new(ctx);
            Some(sig_ctx.read_signature(&cmi.cmi_sign))
        }
        Path::Pdot(parent, module_name, _) => {
            let parent_sig =
                resolve_module_signature_through_cmi(ctx, load_paths, parent, visiting)?;
            parent_sig.into_iter().find_map(|item| match item {
                SignatureItem::SigModule(id, md, _) if id.name() == module_name => match md.md_type
                {
                    ModuleType::MtySignature(sig) => Some(sig),
                    ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                        resolve_module_signature_through_cmi(ctx, load_paths, &alias_path, visiting)
                    }
                    _ => None,
                },
                _ => None,
            })
        }
        Path::Papply(_, _) => None,
    };

    result
}

pub fn resolve_type_through_modules<'a>(
    ctx: &'a TypeContext<'a>,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    use crate::types::decl::SignatureItem;

    let (module_path, type_name) = match path {
        Path::Pdot(parent, name, _) => (parent.as_ref(), name.as_str()),
        _ => return None,
    };

    let load_paths = ctx.load_paths();
    if load_paths.is_empty() {
        return None;
    }

    let mut visiting = HashSet::new();
    let current_sig =
        resolve_module_signature_through_cmi(ctx, &load_paths, module_path, &mut visiting)?;

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
            if id.name() == type_name {
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
fn resolve_module_type_through_env_path<'a>(
    ctx: &'a TypeContext<'a>,
    env: &super::env::Env,
    path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<super::decl::ModuleType> {
    use super::decl::SignatureItem;

    // Keep visited paths for the entire alias-resolution chain; this mirrors
    // OCaml's cycle-safe alias scraping and prevents re-entering `Mty_ident`
    // loops through `resolve_signature_through_env_module_type`.
    if !visiting.insert(path.clone()) {
        return None;
    }

    let result = match path {
        Path::Pident(id) => {
            let name = id.name();
            if let Ok(md) = env.find_module(name) {
                Some(md.md_type.clone())
            } else if let Ok(mtd) = env.find_modtype(name) {
                mtd.mtd_type.clone()
            } else {
                let load_paths = ctx.load_paths();
                if load_paths.is_empty() {
                    None
                } else {
                    // Mirror OCaml's persistent-module lookup in Env.find_module:
                    // if not found in local env, consult .cmi signatures.
                    let mut cmi_visiting = HashSet::new();
                    resolve_module_signature_through_cmi(ctx, &load_paths, path, &mut cmi_visiting)
                        .map(super::decl::ModuleType::MtySignature)
                }
            }
        }
        Path::Pdot(parent, name, _) => {
            let parent_mty = resolve_module_type_through_env_path(ctx, env, parent, visiting)?;
            let parent_sig =
                resolve_signature_through_env_module_type(ctx, env, &parent_mty, visiting)?;
            parent_sig.into_iter().find_map(|item| match item {
                SignatureItem::SigModule(id, md, _) if id.name() == name => Some(md.md_type),
                SignatureItem::SigModtype(id, mtd) if id.name() == name => mtd.mtd_type,
                _ => None,
            })
        }
        Path::Papply(_, _) => None,
    };

    result
}

fn resolve_signature_through_env_module_type<'a>(
    ctx: &'a TypeContext<'a>,
    env: &super::env::Env,
    mty: &super::decl::ModuleType,
    visiting: &mut HashSet<Path>,
) -> Option<super::decl::Signature> {
    use super::decl::ModuleType;

    match mty {
        ModuleType::MtySignature(sig) => Some(sig.clone()),
        ModuleType::MtyAlias(_, path) | ModuleType::MtyIdent(path) => {
            let resolved = resolve_module_type_through_env_path(ctx, env, path, visiting)?;
            resolve_signature_through_env_module_type(ctx, env, &resolved, visiting)
        }
        _ => None,
    }
}

/// Resolve a type through local environment modules.
/// For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
/// follow aliases (MtyAlias/MtyIdent), and then find type t in its signature.
fn resolve_type_through_env<'a>(
    ctx: &'a TypeContext<'a>,
    env: &super::env::Env,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    use super::decl::SignatureItem;

    let (module_path, type_name) = match path {
        Path::Pdot(parent, name, _) => (parent.as_ref(), name.as_str()),
        _ => return None,
    };

    let mut visiting = HashSet::new();
    let module_mty = resolve_module_type_through_env_path(ctx, env, module_path, &mut visiting)?;
    let module_sig =
        resolve_signature_through_env_module_type(ctx, env, &module_mty, &mut visiting)?;

    for item in &module_sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            if id.name() == type_name {
                return Some(decl.clone());
            }
        }
    }

    // Fall back to CMI-based resolution if local env-based lookup didn't find
    // the type item (e.g. when only the persistent path is available).
    resolve_type_through_modules(ctx, path)
}

/// Normalize a path by following module aliases, using both the local env
/// and persistent environment (CMI files) for module lookup.
///
/// This is equivalent to OCaml's `Env.normalize_path` but with access to
/// the full module resolution machinery. For `Pdot(p, s)`, it:
/// 1. Recursively normalizes the prefix `p`
/// 2. Looks up the module at the path (checking env + CMI)
/// 3. If the module is an alias (`MtyAlias`), follows it
fn normalize_path_full<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    path: &Path,
) -> Path {
    normalize_path_full_inner(ctx, env, path, 0, &mut HashSet::new())
}

fn normalize_path_full_inner<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    path: &Path,
    depth: usize,
    visiting: &mut HashSet<Path>,
) -> Path {
    if depth > 20 {
        return path.clone();
    }

    // First, recursively normalize the prefix for Pdot paths
    let path = match path {
        Path::Pdot(p, s, pos) => {
            let p_norm = normalize_path_full_inner(ctx, env, p, depth + 1, visiting);
            if p_norm == **p {
                path.clone()
            } else {
                Path::Pdot(Box::new(p_norm), s.clone(), *pos)
            }
        }
        _ => path.clone(),
    };

    // Then check if the path itself is a module alias.
    // First try the simple env lookup (handles Pident and some Pdot paths).
    if let Ok(md) = env.lookup_module(&path) {
        if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
            return normalize_path_full_inner(ctx, env, alias_path, depth + 1, visiting);
        }
    }

    // For Pdot paths not found in env, use the full module resolution machinery
    // (navigates module signatures from env modules and CMI files).
    if matches!(path, Path::Pdot(..)) {
        if !visiting.insert(path.clone()) {
            return path;
        }
        let mut resolve_visiting = HashSet::new();
        if let Some(mty) =
            resolve_module_type_through_env_path(ctx, env, &path, &mut resolve_visiting)
        {
            if let super::decl::ModuleType::MtyAlias(_, alias_path) = &mty {
                return normalize_path_full_inner(ctx, env, alias_path, depth + 1, visiting);
            }
        }
    }

    path
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
    // OCaml ctype.ml: expand_abbrev_gen starts with check_abbrev_env env.
    // This keeps simple_abbrevs scoped to the current env identity.
    ctx.check_abbrev_env(env);

    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let args = args.clone();
            let path = path.clone();
            let memorize_simple_abbrev = || {
                // OCaml ctype.ml proper_abbrevs routes nullary non-object aliases
                // through simple_abbrevs during abbreviation expansion (subst).
                if args.is_empty() && !path.head_name().starts_with('#') {
                    ctx.memorize_simple_abbrev(path.clone(), ty);
                }
            };

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

            // 0. Check local constraints first (GADT equations)
            if let Some(constraint_decl) = env.find_local_constraint(&path) {
                if let Some(manifest) = constraint_decl.type_manifest {
                    let params = &constraint_decl.type_params;
                    if params.is_empty() {
                        memorize_simple_abbrev();
                        return Some(instance_for_expansion(ctx, manifest));
                    } else if params.len() == args.len() {
                        let (fresh_params, fresh_body) =
                            instance_parameterized_type(ctx, params, manifest);
                        memorize_simple_abbrev();
                        return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                    }
                }
            }

            // 1. Prefer environment lookup for simple identifiers.
            // OCaml expand_head is path-based (Env.find_type_expansion path env):
            // for qualified paths, leaf-name lookup can pick an unrelated local
            // declaration (e.g. local `type t` instead of `Belt.Array.t`).
            if let Path::Pident(_) = &path {
                if let Ok(env_decl) = env.lookup_type(&path) {
                    if let Some(manifest) = env_decl.type_manifest {
                        let params = &env_decl.type_params;
                        if params.is_empty() {
                            memorize_simple_abbrev();
                            return Some(instance_for_expansion(ctx, manifest));
                        } else if params.len() == args.len() {
                            // Use instance_parameterized_type to create a full fresh copy
                            // of both params and body (sharing the copy cache). This matches
                            // OCaml's expand_abbrev which uses instance_parameterized_type
                            // to ensure the expansion is independent of any prior unification
                            // linkings on the manifest.
                            let (fresh_params, fresh_body) =
                                instance_parameterized_type(ctx, params, manifest);
                            memorize_simple_abbrev();
                            return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                        }
                        return None;
                    }
                    // Type found in env but no manifest => abstract type.
                    return None;
                }
            }

            // 2. Try stamp-based global store (for CMI types with non-zero stamps)
            if let Some(stamp) = stamp {
                if let Some(store_decl) = ctx.find_type_decl_by_stamp(stamp) {
                    if let Some(manifest) = store_decl.type_manifest {
                        let params = &store_decl.type_params;
                        if params.is_empty() {
                            memorize_simple_abbrev();
                            return Some(instance_for_expansion(ctx, manifest));
                        } else if params.len() == args.len() {
                            let (fresh_params, fresh_body) =
                                instance_parameterized_type(ctx, params, manifest);
                            memorize_simple_abbrev();
                            return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                        }
                    }
                }
            }

            // 3. Try full qualified path lookup (for Pdot paths like Js.Promise.t)
            if let Some(ref _path_name) = full_path_name {
                // First check cached path store
                if let Some(store_decl) = ctx.find_type_decl_by_path(_path_name) {
                    if let Some(manifest) = store_decl.type_manifest {
                        let params = &store_decl.type_params;
                        if params.is_empty() {
                            memorize_simple_abbrev();
                            return Some(instance_for_expansion(ctx, manifest));
                        } else if params.len() == args.len() {
                            let (fresh_params, fresh_body) =
                                instance_parameterized_type(ctx, params, manifest);
                            memorize_simple_abbrev();
                            return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                        }
                    }
                }

                // Not cached — resolve by loading CMI files and walking module signatures
                if let Some(resolved_decl) = resolve_type_through_modules(ctx, &path) {
                    if let Some(manifest) = resolved_decl.type_manifest {
                        let params = &resolved_decl.type_params;
                        if params.is_empty() {
                            memorize_simple_abbrev();
                            return Some(instance_for_expansion(ctx, manifest));
                        } else if params.len() == args.len() {
                            let (fresh_params, fresh_body) =
                                instance_parameterized_type(ctx, params, manifest);
                            memorize_simple_abbrev();
                            return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                        }
                    }
                }

                // 3c. Try resolving Pdot paths through local env modules
                // For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
                // get its signature, and find type t in it
                if let Some(decl) = resolve_type_through_env(ctx, env, &path) {
                    if let Some(manifest) = decl.type_manifest {
                        let params = &decl.type_params;
                        if params.is_empty() {
                            memorize_simple_abbrev();
                            return Some(instance_for_expansion(ctx, manifest));
                        } else if params.len() == args.len() {
                            let (fresh_params, fresh_body) =
                                instance_parameterized_type(ctx, params, manifest);
                            memorize_simple_abbrev();
                            return Some(subst_type(ctx, &fresh_params, &args, fresh_body));
                        }
                    }
                }
            }

            // 4. Path normalization fallback (OCaml ctype.ml:1315).
            // When all expansion attempts fail, try normalizing the path by
            // following module aliases. If the normalized path differs, create
            // a new Tconstr with the normalized path so the next expansion
            // attempt can find the type declaration.
            let path_norm = normalize_path_full(ctx, env, &path);
            if path_norm != path {
                Some(ctx.new_constr(path_norm, args.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Fully expand a type through all aliases until it can't be expanded further.
/// Like OCaml's expand_head_opt: repeatedly calls try_expand_head until stable.
pub fn expand_head_once<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    try_expand_head(ctx, env, ty).map(|expanded| ctx.repr(expanded))
}

/// Fully expand a type through all aliases until it can't be expanded further.
/// Like OCaml's expand_head_opt: repeatedly calls try_expand_head until stable.
pub fn expand_head<'a>(ctx: &'a TypeContext<'a>, env: &Env, ty: TypeExprRef) -> TypeExprRef {
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

// ============================================================================
// Method Filtering (Objects)
// ============================================================================

fn filter_method_field<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    method_name: &str,
    ty: TypeExprRef,
) -> TypeResult<TypeExprRef> {
    let ty = expand_head(ctx, env, ty);

    enum FieldAction {
        FreshField {
            level: i32,
        },
        ExistingField {
            name: String,
            kind: FieldKind,
            typ: TypeExprRef,
            rest: TypeExprRef,
        },
        Error,
    }

    let action = {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvar(_) => FieldAction::FreshField {
                level: ctx.get_level(ty),
            },
            TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => FieldAction::ExistingField {
                name: name.clone(),
                kind: kind.clone(),
                typ: *typ,
                rest: *rest,
            },
            _ => FieldAction::Error,
        }
    };

    match action {
        FieldAction::FreshField { level } => {
            let field_ty = ctx.new_var(None);
            let rest_ty = ctx.new_var(None);
            ctx.set_level(field_ty, level);
            ctx.set_level(rest_ty, level);

            let linked = ctx.new_type(TypeDesc::Tfield {
                name: method_name.to_string(),
                kind: FieldKind::Fpresent,
                typ: field_ty,
                rest: rest_ty,
            });
            ctx.set_level(linked, level);
            link_type(ctx, ty, linked);
            Ok(field_ty)
        }
        FieldAction::ExistingField {
            name,
            kind,
            typ,
            rest,
        } => {
            let is_absent = matches!(kind, FieldKind::Fabsent);
            if name == method_name && !is_absent {
                Ok(typ)
            } else {
                filter_method_field(ctx, env, method_name, rest)
            }
        }
        FieldAction::Error => Err(TypeError::Unify(vec![])),
    }
}

/// Unify `ty` with an object type that contains method `method_name` and
/// return the method type.
///
/// This mirrors OCaml `Ctype.filter_method` for the public method-send path.
pub fn filter_method<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    method_name: &str,
    ty: TypeExprRef,
) -> TypeResult<TypeExprRef> {
    let ty = expand_head(ctx, env, ty);

    enum MethodAction {
        FreshObject {
            level: i32,
        },
        ExistingObject {
            fields: TypeExprRef,
        },
        Error,
    }

    let action = {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvar(_) => MethodAction::FreshObject {
                level: ctx.get_level(ty),
            },
            TypeDesc::Tobject { fields, .. } => MethodAction::ExistingObject { fields: *fields },
            _ => MethodAction::Error,
        }
    };

    match action {
        MethodAction::FreshObject { level } => {
            let fields_ty = ctx.new_var(None);
            ctx.set_level(fields_ty, level);
            let object_ty = ctx.new_type(TypeDesc::Tobject {
                fields: fields_ty,
                name: None,
            });
            update_level(ctx, level, object_ty);
            link_type(ctx, ty, object_ty);
            filter_method_field(ctx, env, method_name, fields_ty)
        }
        MethodAction::ExistingObject { fields } => {
            filter_method_field(ctx, env, method_name, fields)
        }
        MethodAction::Error => Err(TypeError::Unify(vec![])),
    }
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
        TypeDesc::Tconstr {
            path,
            args: inner_args,
            ..
        } => {
            let new_args: Vec<TypeExprRef> = inner_args
                .iter()
                .map(|a| subst_type(ctx, params, args, *a))
                .collect();
            if new_args
                .iter()
                .zip(inner_args.iter())
                .all(|(a, b)| *a == *b)
            {
                // No change
                ty
            } else {
                let path = path.clone();
                drop(desc);
                ctx.new_constr(path, new_args)
            }
        }
        TypeDesc::Tarrow {
            arg, ret, arity, ..
        } => {
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
        TypeDesc::Tpackage {
            path,
            lids,
            args: package_args,
        } => {
            let new_args: Vec<TypeExprRef> = package_args
                .iter()
                .map(|arg| subst_type(ctx, params, args, *arg))
                .collect();
            if new_args
                .iter()
                .zip(package_args.iter())
                .all(|(new_arg, old_arg)| *new_arg == *old_arg)
            {
                ty
            } else {
                let path = path.clone();
                let lids = lids.clone();
                drop(desc);
                ctx.new_type(TypeDesc::Tpackage {
                    path,
                    lids,
                    args: new_args,
                })
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
    // Guard against non-terminating row-unification recursion. Without this,
    // pathological cycles can overflow the stack before producing a type error.
    const MAX_UNIFY_RECURSION_DEPTH: usize = 2048;
    state.recursion_depth += 1;
    if state.recursion_depth > MAX_UNIFY_RECURSION_DEPTH {
        state.recursion_depth -= 1;
        return Err(TypeError::Unify(vec![]));
    }

    // Fast path: same reference
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);

    if t1 == t2 {
        state.recursion_depth -= 1;
        return Ok(());
    }

    // Check if already unified (for cycles)
    if state.already_unified(t1, t2) {
        state.recursion_depth -= 1;
        return Ok(());
    }

    // Mark as being unified
    state.mark_unified(t1, t2);

    // Get descriptors
    let result = unify_types(ctx, state, t1, t2);

    let result = if let Err(TypeError::Unify(trace)) = &result {
        // Add this pair to the trace
        let mut new_trace = vec![(t1, t2)];
        new_trace.extend(trace.iter().cloned());
        Err(TypeError::Unify(new_trace))
    } else {
        result
    };

    state.recursion_depth -= 1;
    result
}

// Match OCaml ctype.ml unify2/unify3 alias-expansion linking direction.
// OCaml still picks a relinking direction when both sides expanded:
//   if t1 == t1' || t2 != t2' then unify3 t1 t1' t2 t2'
//   else unify3 t2 t2' t1 t1'
// and unify3 links t1' -> t2 for expression-mode unification.
// We mirror that branch choice so alias identity is preserved for both
// one-sided and two-sided expansion cases.
fn unify_after_expansion<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t1_expanded: TypeExprRef,
    t2: TypeExprRef,
    t2_expanded: TypeExprRef,
) -> TypeResult<()> {
    let t1_changed = t1_expanded != t1;
    let t2_changed = t2_expanded != t2;
    if !t1_changed && !t2_changed {
        return unify(ctx, state, t1_expanded, t2_expanded);
    }

    // OCaml (unify3) does: link_type t1' t2 — linking the expanded representative
    // to the original non-expanded side, preserving alias-path identity.
    // We only do this when the expanded side is a Tconstr (type alias) to avoid
    // creating cycles with structural types.
    //
    // CRITICAL: OCaml's unify3 fallthrough (| _ ->) does:
    //   Expression mode: link_type t1' t2 (link expanded to original)
    //   Pattern mode:    add_type_equality t1' t2' (no linking, just record)
    // In Pattern mode (GADT unification), linking must be skipped to avoid
    // creating cycles between locally abstract types and their equation targets
    // (e.g., linking bool → a when a has GADT equation a = bool).
    let is_pattern_mode = state.mode == crate::types::UnifyMode::Pattern;

    let (from_expanded, to_original) = if t2_changed {
        (t1_expanded, t2)
    } else {
        (t2_expanded, t1)
    };
    let changed_ty = if t2_changed { t2 } else { t1 };
    let should_relink = if is_pattern_mode {
        false // OCaml: add_type_equality, not link_type
    } else {
        let desc = ctx.get_desc(changed_ty);
        matches!(&*desc, TypeDesc::Tconstr { .. })
    };

    let t1_expanded = ctx.repr(t1_expanded);
    let t2_expanded = ctx.repr(t2_expanded);
    if t1_expanded == t2_expanded {
        if should_relink {
            let from_ty = ctx.repr(from_expanded);
            let to_ty = ctx.repr(to_original);
            if from_ty != to_ty && !deep_occur(ctx, from_ty, to_ty) {
                link_type(ctx, from_ty, to_ty);
            }
        }
        return Ok(());
    }

    unify(ctx, state, t1_expanded, t2_expanded)?;

    if should_relink {
        let from_ty = ctx.repr(from_expanded);
        let to_ty = ctx.repr(to_original);
        if from_ty != to_ty && !deep_occur(ctx, from_ty, to_ty) {
            link_type(ctx, from_ty, to_ty);
        }
    }

    Ok(())
}

/// Internal unification logic.
fn unify_types<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    // OCaml unify2 (ctype.ml:2283-2292): before structural unification,
    // update levels of both sides. This triggers expansion+linking for
    // Tconstr types whose binding time exceeds the target level,
    // normalizing module-alias paths (e.g., U.t → list).
    if let Some(env) = state.env() {
        let lv1 = ctx.get_level(t1);
        let lv2 = ctx.get_level(t2);
        let lv = std::cmp::min(lv1, lv2);
        // Use repr to get current representatives, since update_level_expand
        // may modify them via link_type.
        update_level_expand(ctx, env, lv, t2);
        update_level_expand(ctx, env, lv, t1);
    }

    // Re-repr after update_level_expand may have linked types
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }

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

            let t1_level = ctx.get_level(t1);
            update_level(ctx, t1_level, t2);
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

            let t2_level = ctx.get_level(t2);
            update_level(ctx, t2_level, t1);
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

        // Arrow types - propagate arity during unification
        (
            TypeDesc::Tarrow {
                arg: arg1,
                ret: ret1,
                arity: a1,
                ..
            },
            TypeDesc::Tarrow {
                arg: arg2,
                ret: ret2,
                arity: a2,
                ..
            },
        ) => {
            // Check arities: if both have explicit arities, they must match
            // (matches OCaml's `when a1 = a2` guard behavior)
            if a1.is_some() && a2.is_some() && a1 != a2 {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let arg1_typ = arg1.typ;
            let ret1 = *ret1;
            let arg2_typ = arg2.typ;
            let ret2 = *ret2;
            // Propagate arity: if one side has arity and the other doesn't,
            // we need to update the surviving side (t2) to carry the arity.
            let need_arity_update = a1.is_some() && a2.is_none();
            let arity_to_set = *a1;
            drop(desc1);
            drop(desc2);

            // OCaml links t1'→t2 BEFORE recursing (unify3 line 2341).
            // This affects cycle detection: child unifications see t1 already resolved to t2.
            link_type(ctx, t1, t2);

            // Unify argument types
            unify(ctx, state, arg1_typ, arg2_typ)?;
            // Unify return types
            unify(ctx, state, ret1, ret2)?;

            // Propagate arity from t1 to t2 if t2 lacks it
            if need_arity_update {
                let desc = ctx.get_desc(t2);
                if let TypeDesc::Tarrow {
                    arg,
                    ret,
                    commutable,
                    ..
                } = &*desc
                {
                    let new_desc = TypeDesc::Tarrow {
                        arg: arg.clone(),
                        ret: *ret,
                        commutable: commutable.clone(),
                        arity: arity_to_set,
                    };
                    drop(desc);
                    ctx.set_desc(t2, new_desc);
                } else {
                    drop(desc);
                }
            }

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

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

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
                // Paths differ. Match OCaml flow by attempting alias expansion
                // before any same-name fallback.
                let name1 = path1.head_name();
                let name2 = path2.head_name();
                let same_name_fallback = name1 == name2 && args1.len() == args2.len();
                let local_t_alias_fallback = same_name_fallback
                    && name1 == "t"
                    && matches!(
                        (path1, path2),
                        (Path::Pdot(p1, _, _), Path::Pdot(p2, _, _))
                            if !p1.head().is_persistent() && !p2.head().is_persistent()
                    );
                let alias_binding_time = if local_t_alias_fallback {
                    Some((path1.head().binding_time(), path2.head().binding_time()))
                } else {
                    None
                };
                // Extract paths for potential GADT equation handling (nullary Tconstr only)
                let gadt_path1 = if args1.is_empty() { Some(path1.clone()) } else { None };
                let gadt_path2 = if args2.is_empty() { Some(path2.clone()) } else { None };
                let pairs: Vec<_> = if same_name_fallback {
                    args1.iter()
                        .zip(args2.iter())
                        .map(|(&a, &b)| (a, b))
                        .collect()
                } else {
                    Vec::new()
                };

                drop(desc1);
                drop(desc2);

                if let Some(env) = state.env() {
                    let exp1 = expand_head(ctx, env, t1);
                    let exp2 = expand_head(ctx, env, t2);
                    if exp1 != t1 || exp2 != t2 {
                        return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                    }
                }

                // Same name with different stamps: handles predef types
                // (ref/Pervasives.ref), and locally-defined types where stamp
                // differences arise between declarations and constructor returns.
                if same_name_fallback {
                    if local_t_alias_fallback {
                        // For local dotted aliases (M.t vs Path.t, Array.t vs Int32Array.t),
                        // keep the newer local alias as representative.
                        let (bt1, bt2) = alias_binding_time.unwrap_or((0, 0));
                        if bt1 > bt2 {
                            link_type(ctx, t2, t1);
                        } else {
                            link_type(ctx, t1, t2);
                        }
                    } else {
                        // OCaml links t1'→t2 BEFORE recursing into children.
                        link_type(ctx, t1, t2);
                    }
                    for (a, b) in pairs {
                        unify(ctx, state, a, b)?;
                    }
                    return Ok(());
                }

                // GADT equation handling for Tconstr with different paths
                if state.generate_equations {
                    if let Some(ref p1) = gadt_path1 {
                        if let Some(ref p2) = gadt_path2 {
                            if let Some(env) = state.env_mut() {
                                let inst1 = is_instantiable(env, p1);
                                let inst2 = is_instantiable(env, p2);
                                if inst1 && inst2 {
                                    let lev1 = env.find_local_constraint(p1)
                                        .or_else(|| env.find_type(p1.head_name()).ok())
                                        .and_then(|d| d.type_newtype_level);
                                    let lev2 = env.find_local_constraint(p2)
                                        .or_else(|| env.find_type(p2.head_name()).ok())
                                        .and_then(|d| d.type_newtype_level);
                                    let (source, dest) = if lev1 > lev2 {
                                        (p1.clone(), t2)
                                    } else {
                                        (p2.clone(), t1)
                                    };
                                    add_gadt_equation(ctx, env, &source, dest);
                                    return Ok(());
                                } else if inst1 {
                                    add_gadt_equation(ctx, env, p1, t2);
                                    return Ok(());
                                } else if inst2 {
                                    add_gadt_equation(ctx, env, p2, t1);
                                    return Ok(());
                                }
                            }
                        } else if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p1) {
                                add_gadt_equation(ctx, env, p1, t2);
                                return Ok(());
                            }
                        }
                    } else if let Some(ref p2) = gadt_path2 {
                        if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p2) {
                                add_gadt_equation(ctx, env, p2, t1);
                                return Ok(());
                            }
                        }
                    }
                }

                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            if args1.len() != args2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }

            let args1 = args1.clone();
            let args2 = args2.clone();
            drop(desc1);
            drop(desc2);

            // OCaml ctype.ml unify3: for same-path Tconstr, just unify args.
            // OCaml's unify2 expands abbreviations BEFORE unify3, but the
            // same-path case in unify3 simply does `unify_list env tl1 tl2`.
            // We cannot expand here because recursive type aliases like
            // `type rec vlist<'a> = [#Nil | #Cons('a, vlist<'a>)]` would
            // infinite-loop: each expansion creates fresh Tconstr nodes that
            // get expanded again without termination. OCaml avoids this via
            // abbreviation memoization (expand_abbrev + proper_abbrevs) that
            // Rust doesn't fully have yet.
            //
            // For non-recursive polyvariant aliases with phantom parameters,
            // the catch-all expansion in the _ => branch handles the case
            // when one side is Tconstr and the other is a different type.
            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

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

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            // First unify the bound variables
            for (v1, v2) in var_pairs {
                unify(ctx, state, v1, v2)?;
            }

            // Then unify the bodies
            unify(ctx, state, body1, body2)?;

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

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            let merged_row = unify_rows(ctx, state, &row1, &row2)?;
            // Keep the unified representative row shape (OCaml `unify_row` merges
            // disjoint labels through row-more links, so the resulting repr exposes
            // the union of labels rather than whichever side happened to be linked).
            ctx.set_desc(t2, TypeDesc::Tvariant(merged_row));
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

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            unify_object_fields(ctx, state, fields1, fields2)?;
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

            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            for (a, b) in pairs {
                unify(ctx, state, a, b)?;
            }

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
            // Extract paths for GADT equation checks (nullary Tconstr only)
            let path1_for_gadt = match &*desc1 {
                TypeDesc::Tconstr { path, args, .. } if args.is_empty() => Some(path.clone()),
                _ => None,
            };
            let path2_for_gadt = match &*desc2 {
                TypeDesc::Tconstr { path, args, .. } if args.is_empty() => Some(path.clone()),
                _ => None,
            };
            drop(desc1);
            drop(desc2);

            if is_constr1 || is_constr2 {
                if let Some(env) = state.env() {
                    // Fully expand both sides through all aliases
                    let exp1 = if is_constr1 {
                        expand_head(ctx, env, t1)
                    } else {
                        t1
                    };
                    let exp2 = if is_constr2 {
                        expand_head(ctx, env, t2)
                    } else {
                        t2
                    };
                    // Only retry if at least one side actually changed
                    if exp1 != t1 || exp2 != t2 {
                        return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                    }
                }
            }

            // GADT equation handling (OCaml ctype.ml:2385-2408)
            // When generate_equations is true and one/both sides are instantiable
            // newtypes, add a type equation instead of failing.
            if state.generate_equations {
                if let Some(ref p1) = path1_for_gadt {
                    if let Some(ref p2) = path2_for_gadt {
                        // Both are nullary Tconstr
                        if let Some(env) = state.env_mut() {
                            let inst1 = is_instantiable(env, p1);
                            let inst2 = is_instantiable(env, p2);
                            if inst1 && inst2 {
                                // Both instantiable: equation from higher to lower newtype level
                                let lev1 = env.find_local_constraint(p1)
                                    .or_else(|| env.find_type(p1.head_name()).ok())
                                    .and_then(|d| d.type_newtype_level);
                                let lev2 = env.find_local_constraint(p2)
                                    .or_else(|| env.find_type(p2.head_name()).ok())
                                    .and_then(|d| d.type_newtype_level);
                                let (source, dest) = if lev1 > lev2 {
                                    (p1.clone(), t2)
                                } else {
                                    (p2.clone(), t1)
                                };
                                add_gadt_equation(ctx, env, &source, dest);
                                return Ok(());
                            } else if inst1 {
                                add_gadt_equation(ctx, env, p1, t2);
                                return Ok(());
                            } else if inst2 {
                                add_gadt_equation(ctx, env, p2, t1);
                                return Ok(());
                            }
                        }
                    } else {
                        // Only left is nullary Tconstr
                        if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p1) {
                                add_gadt_equation(ctx, env, p1, t2);
                                return Ok(());
                            }
                        }
                    }
                } else if let Some(ref p2) = path2_for_gadt {
                    // Only right is nullary Tconstr
                    if let Some(env) = state.env_mut() {
                        if is_instantiable(env, p2) {
                            add_gadt_equation(ctx, env, p2, t1);
                            return Ok(());
                        }
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
) -> TypeResult<RowDesc> {
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);

    // Preserve left-row label order: OCaml `unify_row` updates row-more links and
    // `row_repr` exposes fields in a left-biased order, not lexicographic order.
    let mut merged_fields = row1.row_fields.clone();
    // OCaml's unify_row_field keeps Reither as Reither during unification
    // (see ctype.ml:2701-2704). We must NOT convert Reither to Rpresent here.
    let prefer_field = |left: &RowField, right: &RowField| -> RowField {
        match (left, right) {
            // Keep present fields when available (mirrors OCaml row-field linking where
            // Reither can be rewritten to Rpresent during unification).
            (RowField::Rpresent(_), _) => left.clone(),
            (_, RowField::Rpresent(_)) => right.clone(),
            // For Reither/Reither, keep the representative-side field (right).
            // OCaml links t1 -> t2 before row unification and row-field refs preserve
            // side-specific residual type lists; selecting left here drops right-side
            // payload lists and produces `Reither ... ()` drift in typedtree output.
            (RowField::Reither { .. }, RowField::Reither { .. }) => right.clone(),
            _ => left.clone(),
        }
    };

    let fixed1 = row_fixed(ctx, &row1);
    let fixed2 = row_fixed(ctx, &row2);

    // Unify the fields
    for (label, field1) in &row1.row_fields {
        // Find matching field in row2
        if let Some((_, field2)) = row2.row_fields.iter().find(|(l, _)| l == label) {
            unify_row_field(ctx, state, fixed1, fixed2, field1, field2)?;
            if let Some((_, merged_field)) = merged_fields.iter_mut().find(|(l, _)| l == label) {
                *merged_field = prefer_field(field1, field2);
            }
        } else if row2.row_closed {
            // Field not found and row is closed - error
            return Err(TypeError::Unify(vec![]));
        } else {
            merged_fields.push((label.clone(), field1.clone()));
        }
        // If row is open, the field might be added later through row-more.
    }

    // Check the reverse
    for (label, field2) in &row2.row_fields {
        if !row1.row_fields.iter().any(|(l, _)| l == label) {
            if row1.row_closed {
                return Err(TypeError::Unify(vec![]));
            }
            merged_fields.push((label.clone(), field2.clone()));
        }
    }

    // Unify the "more" types
    let more1 = row_more(ctx, &row1);
    let more2 = row_more(ctx, &row2);
    unify(ctx, state, more1, more2)?;

    // `row_repr` may produce duplicate labels through nested row flattening.
    // Keep first occurrence to match OCaml lookup semantics.
    let mut seen = HashSet::new();
    merged_fields.retain(|(label, _)| seen.insert(label.clone()));

    Ok(RowDesc {
        row_fields: merged_fields,
        row_more: ctx.repr(more2),
        row_closed: row1.row_closed || row2.row_closed,
        row_fixed: row1.row_fixed || row2.row_fixed,
        row_name: row2.row_name.clone().or_else(|| row1.row_name.clone()),
    })
}

/// Unify two row fields.
/// Infrastructure for row field links (alloc_row_field, set_row_field, row_field_repr
/// link following) is in place but link-setting is disabled — enabling causes
/// regressions because Rust's row_fixed diverges from OCaml's.
fn unify_row_field<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    _fixed1: bool,
    _fixed2: bool,
    field1: &RowField,
    field2: &RowField,
) -> TypeResult<()> {
    // Follow links before matching, like OCaml does
    let f1 = super::btype::row_field_repr(ctx, field1);
    let f2 = super::btype::row_field_repr(ctx, field2);
    match (&f1, &f2) {
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
        // Reither + Rabsent
        (RowField::Reither { .. }, RowField::Rabsent) | (RowField::Rabsent, RowField::Reither { .. }) => {
            Ok(())
        }
        _ => Err(TypeError::Unify(vec![])),
    }
}

/// Unify object fields.
/// Flatten an object field chain into a sorted list of (name, kind, type) + rest.
/// Matches OCaml `flatten_fields` in ctype.ml.
fn flatten_fields(ctx: &TypeContext<'_>, ty: TypeExprRef) -> (Vec<(String, FieldKind, TypeExprRef)>, TypeExprRef) {
    let mut fields = Vec::new();
    let mut current = ctx.repr(ty);
    loop {
        let desc = ctx.get_desc(current);
        match &*desc {
            TypeDesc::Tfield { name, kind, typ, rest } => {
                fields.push((name.clone(), kind.clone(), *typ));
                let next = ctx.repr(*rest);
                drop(desc);
                current = next;
            }
            _ => {
                drop(desc);
                break;
            }
        }
    }
    fields.sort_by(|a, b| a.0.cmp(&b.0));
    (fields, current)
}

/// Associate two sorted field lists by name.
/// Returns (paired, surplus_from_1, surplus_from_2).
/// Matches OCaml `associate_fields` in ctype.ml.
fn associate_fields(
    fields1: Vec<(String, FieldKind, TypeExprRef)>,
    fields2: Vec<(String, FieldKind, TypeExprRef)>,
) -> (
    Vec<(String, FieldKind, TypeExprRef, FieldKind, TypeExprRef)>,
    Vec<(String, FieldKind, TypeExprRef)>,
    Vec<(String, FieldKind, TypeExprRef)>,
) {
    let mut pairs = Vec::new();
    let mut miss1 = Vec::new();
    let mut miss2 = Vec::new();
    let mut i1 = 0;
    let mut i2 = 0;
    while i1 < fields1.len() && i2 < fields2.len() {
        let (ref n1, ref k1, t1) = fields1[i1];
        let (ref n2, ref k2, t2) = fields2[i2];
        match n1.cmp(n2) {
            std::cmp::Ordering::Equal => {
                pairs.push((n1.clone(), k1.clone(), t1, k2.clone(), t2));
                i1 += 1;
                i2 += 1;
            }
            std::cmp::Ordering::Less => {
                miss1.push((n1.clone(), k1.clone(), t1));
                i1 += 1;
            }
            std::cmp::Ordering::Greater => {
                miss2.push((n2.clone(), k2.clone(), t2));
                i2 += 1;
            }
        }
    }
    while i1 < fields1.len() {
        let (ref n, ref k, t) = fields1[i1];
        miss1.push((n.clone(), k.clone(), t));
        i1 += 1;
    }
    while i2 < fields2.len() {
        let (ref n, ref k, t) = fields2[i2];
        miss2.push((n.clone(), k.clone(), t));
        i2 += 1;
    }
    (pairs, miss1, miss2)
}

/// Build a Tfield chain from a list of fields with a given rest.
/// Matches OCaml `build_fields` in ctype.ml.
fn build_fields(ctx: &TypeContext<'_>, level: i32, fields: &[(String, FieldKind, TypeExprRef)], rest: TypeExprRef) -> TypeExprRef {
    let mut current = rest;
    for (name, kind, typ) in fields.iter().rev() {
        current = ctx.alloc_type_at_level(
            TypeDesc::Tfield {
                name: name.clone(),
                kind: kind.clone(),
                typ: *typ,
                rest: current,
            },
            level,
        );
    }
    current
}

/// Unify two object field chains using OCaml's field-order-independent algorithm.
/// Matches OCaml `unify_fields` in ctype.ml.
fn unify_object_fields<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    fields1: TypeExprRef,
    fields2: TypeExprRef,
) -> TypeResult<()> {
    // Flatten both field chains into sorted lists + rest
    let (flds1, rest1) = flatten_fields(ctx, fields1);
    let (flds2, rest2) = flatten_fields(ctx, fields2);

    // Associate fields by name
    let (pairs, miss1, miss2) = associate_fields(flds1, flds2);

    // Determine levels
    let l1 = ctx.get_level(ctx.repr(fields1));
    let l2 = ctx.get_level(ctx.repr(fields2));
    let min_level = std::cmp::min(l1, l2);

    // Create shared row variable (OCaml make_rowvar)
    let va = if miss2.is_empty() {
        rest1
    } else if miss1.is_empty() {
        rest2
    } else {
        ctx.alloc_type_at_level(TypeDesc::Tvar(None), min_level)
    };

    // Build extended field chains with surplus fields
    // unify(build_fields miss1 va, rest2) — rest2 must absorb miss1 fields
    let extended1 = build_fields(ctx, l1, &miss1, va);
    unify(ctx, state, extended1, rest2)?;

    // unify(rest1, build_fields miss2 va) — rest1 must absorb miss2 fields
    let extended2 = build_fields(ctx, l2, &miss2, va);
    unify(ctx, state, rest1, extended2)?;

    // Unify paired fields (matching names from both sides)
    for (_name, _k1, t1, _k2, t2) in &pairs {
        // OCaml also calls unify_kind here, but Rust FieldKind handling is simpler
        unify(ctx, state, *t1, *t2)?;
    }

    Ok(())
}

// ============================================================================
// Generalization
// ============================================================================

/// Generalize a type.
///
/// This marks all type variables at or above the current level as generic,
/// making the type polymorphic.
fn generalize_rec(ctx: &TypeContext<'_>, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    let current = ctx.current_level();

    if level > current && level != GENERIC_LEVEL {
        // Mark as generic
        ctx.set_level(ty, GENERIC_LEVEL);
        // Recursively generalize children only when this node is promoted,
        // matching OCaml's recursive generalize implementation.
        iter_type_expr(ctx, ty, |child| {
            generalize_rec(ctx, child);
        });
    }
}

pub fn generalize(ctx: &TypeContext<'_>, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    generalize_rec(ctx, ty);
}

fn lower_nongen_type_expr_rec(
    ctx: &TypeContext<'_>,
    nglev: i32,
    ty: TypeExprRef,
    seen: &mut HashSet<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }

    let level = ctx.get_level(ty);
    let is_tvar = {
        let desc = ctx.get_desc(ty);
        matches!(&*desc, TypeDesc::Tvar(_))
    };
    if is_tvar && level < GENERIC_LEVEL && level > nglev {
        ctx.set_level(ty, nglev);
    }

    let mut children = Vec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        lower_nongen_type_expr_rec(ctx, nglev, child, seen);
    }
}

fn lower_nongen_type_decl_rec(
    ctx: &TypeContext<'_>,
    nglev: i32,
    decl: &crate::types::decl::TypeDeclaration,
    seen: &mut HashSet<TypeExprRef>,
) {
    use crate::types::decl::ConstructorArguments;
    use crate::types::decl::TypeInlinedType;
    use crate::types::decl::TypeKind;

    for &param in &decl.type_params {
        lower_nongen_type_expr_rec(ctx, nglev, param, seen);
    }
    if let Some(manifest) = decl.type_manifest {
        lower_nongen_type_expr_rec(ctx, nglev, manifest, seen);
    }
    match &decl.type_kind {
        TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                lower_nongen_type_expr_rec(ctx, nglev, label.ld_type, seen);
            }
        }
        TypeKind::TypeVariant(constructors) => {
            for cstr in constructors {
                match &cstr.cd_args {
                    ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            lower_nongen_type_expr_rec(ctx, nglev, arg, seen);
                        }
                    }
                    ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            lower_nongen_type_expr_rec(ctx, nglev, label.ld_type, seen);
                        }
                    }
                }
                if let Some(ret) = cstr.cd_res {
                    lower_nongen_type_expr_rec(ctx, nglev, ret, seen);
                }
            }
        }
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
    }
    for inlined in &decl.type_inlined_types {
        match inlined {
            TypeInlinedType::Record { labels, .. } => {
                for label in labels {
                    lower_nongen_type_expr_rec(ctx, nglev, label.ld_type, seen);
                }
            }
        }
    }
}

fn lower_nongen_extension_constructor_rec(
    ctx: &TypeContext<'_>,
    nglev: i32,
    ext: &crate::types::decl::ExtensionConstructor,
    seen: &mut HashSet<TypeExprRef>,
) {
    use crate::types::decl::ConstructorArguments;

    for &param in &ext.ext_type_params {
        lower_nongen_type_expr_rec(ctx, nglev, param, seen);
    }
    match &ext.ext_args {
        ConstructorArguments::CstrTuple(args) => {
            for &arg in args {
                lower_nongen_type_expr_rec(ctx, nglev, arg, seen);
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels {
                lower_nongen_type_expr_rec(ctx, nglev, label.ld_type, seen);
            }
        }
    }
    if let Some(ret) = ext.ext_ret_type {
        lower_nongen_type_expr_rec(ctx, nglev, ret, seen);
    }
}

fn lower_nongen_module_type_rec(
    ctx: &TypeContext<'_>,
    nglev: i32,
    mty: &crate::types::decl::ModuleType,
    seen: &mut HashSet<TypeExprRef>,
) {
    use crate::types::decl::ModuleType;
    use crate::types::decl::SignatureItem;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig_items) => {
            for item in sig_items {
                match item {
                    SignatureItem::SigValue(_, vd) => {
                        lower_nongen_type_expr_rec(ctx, nglev, vd.val_type, seen);
                    }
                    SignatureItem::SigType(_, decl, _) => {
                        lower_nongen_type_decl_rec(ctx, nglev, decl, seen);
                    }
                    SignatureItem::SigTypext(_, ext, _) => {
                        lower_nongen_extension_constructor_rec(ctx, nglev, ext, seen);
                    }
                    SignatureItem::SigModule(_, md, _) => {
                        lower_nongen_module_type_rec(ctx, nglev, &md.md_type, seen);
                    }
                    SignatureItem::SigModtype(_, mtd) => {
                        if let Some(inner) = &mtd.mtd_type {
                            lower_nongen_module_type_rec(ctx, nglev, inner, seen);
                        }
                    }
                    SignatureItem::SigClass | SignatureItem::SigClassType => {}
                }
            }
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_mty) = param_type.as_deref() {
                lower_nongen_module_type_rec(ctx, nglev, param_mty, seen);
            }
            lower_nongen_module_type_rec(ctx, nglev, result, seen);
        }
    }
}

pub fn lower_nongen_module_type(
    ctx: &TypeContext<'_>,
    nglev: i32,
    mty: &crate::types::decl::ModuleType,
) {
    let mut seen = HashSet::new();
    lower_nongen_module_type_rec(ctx, nglev, mty, &mut seen);
}

fn force_generalize_sig_type_rec(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    seen: &mut HashSet<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }

    // Keep nullary constructors at their original level so alias identity is
    // preserved (avoids LetUnwrap/find_simple_abbrev regressions).
    let preserve_level = {
        let desc = ctx.get_desc(ty);
        matches!(&*desc, TypeDesc::Tconstr { args, .. } if args.is_empty())
    };
    if !preserve_level && ctx.get_level(ty) != GENERIC_LEVEL {
        ctx.set_level(ty, GENERIC_LEVEL);
    }

    let mut children = Vec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        force_generalize_sig_type_rec(ctx, child, seen);
    }
}

fn force_generalize_module_type_rec(
    ctx: &TypeContext<'_>,
    mty: &crate::types::decl::ModuleType,
    seen: &mut HashSet<TypeExprRef>,
) {
    use crate::types::decl::ModuleType;
    use crate::types::decl::SignatureItem;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig_items) => {
            for item in sig_items {
                match item {
                    SignatureItem::SigValue(_, vd) => {
                        force_generalize_sig_type_rec(ctx, vd.val_type, seen);
                    }
                    SignatureItem::SigModule(_, md, _) => {
                        force_generalize_module_type_rec(ctx, &md.md_type, seen);
                    }
                    SignatureItem::SigModtype(_, mtd) => {
                        if let Some(inner) = &mtd.mtd_type {
                            force_generalize_module_type_rec(ctx, inner, seen);
                        }
                    }
                    _ => {}
                }
            }
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_mty) = param_type.as_deref() {
                force_generalize_module_type_rec(ctx, param_mty, seen);
            }
            force_generalize_module_type_rec(ctx, result, seen);
        }
    }
}

pub fn force_generalize_module_sig_values(
    ctx: &TypeContext<'_>,
    mty: &crate::types::decl::ModuleType,
) {
    ctx.clear_simple_abbrevs();
    let mut seen = HashSet::new();
    force_generalize_module_type_rec(ctx, mty, &mut seen);
}

/// Generalize the structure of a type at a given level.
fn generalize_structure_rec(ctx: &TypeContext<'_>, var_level: i32, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);

    if level == GENERIC_LEVEL {
        return;
    }

    enum Action {
        LowerVar,
        PromoteAndRecurse(Vec<TypeExprRef>),
        Noop,
    }

    let action = {
        let desc = ctx.get_desc(ty);
        if matches!(&*desc, TypeDesc::Tvar(_)) && level > var_level {
            Action::LowerVar
        } else if level > ctx.current_level() {
            match &*desc {
                // Match OCaml ctype.ml is_object_type path guard in generalize_structure:
                // object types (names starting with '#') are not promoted here.
                TypeDesc::Tconstr { path, .. } if path.head_name().starts_with('#') => {
                    Action::Noop
                }
                _ => {
                    let mut children = Vec::new();
                    iter_type_expr(ctx, ty, |child| children.push(child));
                    Action::PromoteAndRecurse(children)
                }
            }
        } else {
            Action::Noop
        }
    };

    match action {
        Action::LowerVar => {
            ctx.set_level(ty, var_level);
        }
        Action::PromoteAndRecurse(children) => {
            ctx.set_level(ty, GENERIC_LEVEL);
            for child in children {
                generalize_structure_rec(ctx, var_level, child);
            }
        }
        Action::Noop => {}
    }
}

pub fn generalize_structure(ctx: &TypeContext<'_>, var_level: i32, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    generalize_structure_rec(ctx, var_level, ty);
}

fn generalize_expansive_rec(
    ctx: &TypeContext<'_>,
    env: &Env,
    var_level: i32,
    visited: &mut HashSet<TypeExprRef>,
    ty: TypeExprRef,
) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    if level == GENERIC_LEVEL || level <= var_level {
        return;
    }
    if !visited.insert(ty) {
        return;
    }

    enum Action {
        Constr { path: Path, args: Vec<TypeExprRef> },
        Package { args: Vec<TypeExprRef> },
        Arrow { arg: TypeExprRef, ret: TypeExprRef },
        Recurse(Vec<TypeExprRef>),
    }

    let action = {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => Action::Constr {
                path: path.clone(),
                args: args.clone(),
            },
            TypeDesc::Tpackage { args, .. } => Action::Package { args: args.clone() },
            TypeDesc::Tarrow { arg, ret, .. } => Action::Arrow {
                arg: arg.typ,
                ret: *ret,
            },
            _ => {
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                Action::Recurse(children)
            }
        }
    };

    match action {
        Action::Constr { path, args } => {
            let variances = env
                .lookup_type(&path)
                .map(|decl| decl.type_variance.clone())
                .unwrap_or_else(|_| vec![Variance::MAY_INV; args.len()]);
            for (index, arg) in args.iter().enumerate() {
                let variance = variances.get(index).copied().unwrap_or(Variance::MAY_INV);
                if variance.mem(VarianceFlag::MayWeak) {
                    generalize_structure(ctx, var_level, *arg);
                } else {
                    generalize_expansive_rec(ctx, env, var_level, visited, *arg);
                }
            }
        }
        Action::Package { args } => {
            for arg in args {
                generalize_structure(ctx, var_level, arg);
            }
        }
        Action::Arrow { arg, ret } => {
            generalize_structure(ctx, var_level, arg);
            generalize_expansive_rec(ctx, env, var_level, visited, ret);
        }
        Action::Recurse(children) => {
            for child in children {
                generalize_expansive_rec(ctx, env, var_level, visited, child);
            }
        }
    }
}

pub fn generalize_expansive(ctx: &TypeContext<'_>, env: &Env, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    let mut visited = HashSet::new();
    generalize_expansive_rec(ctx, env, ctx.nongen_level(), &mut visited, ty);
}

/// OCaml's lower_args: walk an arrow type, expanding each component with
/// expand_head. This triggers type alias expansion for function argument/return
/// types, matching OCaml's behavior during Pexp_apply processing.
pub fn lower_args<'a>(ctx: &'a TypeContext<'a>, env: &Env, ty: TypeExprRef) {
    let mut seen = Vec::new();
    let mut current = ty;
    loop {
        let expanded = expand_head(ctx, env, current);
        if seen.iter().any(|&s| s == expanded) {
            return;
        }
        let arrow = {
            let desc = ctx.get_desc(expanded);
            if let TypeDesc::Tarrow { arg, ret, .. } = &*desc {
                Some((arg.typ, *ret))
            } else {
                None
            }
        };
        let Some((arg_ty, ret_ty)) = arrow else {
            return;
        };

        // OCaml typecore.ml lower_args:
        //   try unify_var env (newvar ()) arg.typ with Unify _ -> assert false
        let fresh = ctx.new_var(None);
        let mut state = UnifyState::new();
        state.set_env(env);
        if unify(ctx, &mut state, fresh, arg_ty).is_err() {
            unreachable!("lower_args failed to unify fresh var with arrow arg")
        }

        seen.push(expanded);
        current = ret_ty;
    }
}

// ============================================================================
// Instantiation
// ============================================================================

/// Create an instance of a type by copying it.
///
/// This replaces all generic type variables with fresh ones,
/// creating a new instance of a polymorphic type.
pub fn instance(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = CopyCache::new();
    copy_type_cached(ctx, ty, &mut cache)
}

/// Like instance(), but guarantees a fresh top-level node is returned.
/// Used in try_expand_head to prevent manifest corruption: when instance()
/// returns identity (same node) for non-generic types, subsequent unification
/// can link the original manifest node, creating self-referential expansion
/// loops. This creates a shallow copy of the top-level node when identity
/// is returned, protecting the original declaration's manifest.
fn instance_for_expansion(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let result = instance(ctx, ty);
    let result_repr = ctx.repr(result);
    let ty_repr = ctx.repr(ty);
    if result_repr == ty_repr {
        // instance returned identity — create a shallow copy to protect the original
        let desc = ctx.get_desc(result_repr);
        ctx.new_type((*desc).clone())
    } else {
        result
    }
}

/// Instantiate a list of types, sharing variable substitutions across all of them.
/// Matches OCaml's Ctype.instance_list.
pub fn instance_list(ctx: &TypeContext<'_>, types: &[TypeExprRef]) -> Vec<TypeExprRef> {
    let mut cache = CopyCache::new();
    types
        .iter()
        .map(|&ty| copy_type_cached(ctx, ty, &mut cache))
        .collect()
}

/// Instantiate a parameterized type, creating fresh copies of both the parameters
/// and the body while sharing the same copy cache. This matches OCaml's
/// `instance_parameterized_type` which ensures the copied params and body are
/// completely independent of the originals, preventing issues where prior
/// unification linkings corrupt the manifest.
///
/// Returns (fresh_params, fresh_body).
pub fn instance_parameterized_type(
    ctx: &TypeContext<'_>,
    params: &[TypeExprRef],
    body: TypeExprRef,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new();
    let fresh_params: Vec<TypeExprRef> = params
        .iter()
        .map(|&p| copy_type_cached(ctx, p, &mut cache))
        .collect();
    let fresh_body = copy_type_cached(ctx, body, &mut cache);
    (fresh_params, fresh_body)
}

fn diff_bound_list(bound: &[TypeExprRef], bound_t: &[TypeExprRef]) -> Vec<TypeExprRef> {
    if bound == bound_t {
        return vec![];
    }

    if bound.len() >= bound_t.len() {
        let split = bound.len() - bound_t.len();
        if bound[split..] == *bound_t {
            return bound[..split].to_vec();
        }
    }

    debug_assert!(
        false,
        "invalid bound-list relation in instance_poly copy_sep"
    );
    vec![]
}

fn bound_conflicts(
    ctx: &TypeContext<'_>,
    free_univars: &HashSet<TypeExprRef>,
    bound: &[TypeExprRef],
) -> bool {
    bound.iter().any(|ty| free_univars.contains(&ctx.repr(*ty)))
}

fn build_inverse_type_graph(
    ctx: &TypeContext<'_>,
    parent: Option<TypeExprRef>,
    ty: TypeExprRef,
    inverted: &mut HashMap<TypeExprRef, Vec<TypeExprRef>>,
) {
    let ty = ctx.repr(ty);

    if let Some(parents) = inverted.get_mut(&ty) {
        if let Some(parent) = parent {
            parents.push(parent);
        }
        return;
    }

    let mut parents = Vec::new();
    if let Some(parent) = parent {
        parents.push(parent);
    }
    inverted.insert(ty, parents);

    let mut children = Vec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        build_inverse_type_graph(ctx, Some(ty), child, inverted);
    }
}

fn add_univar_to_parents(
    ctx: &TypeContext<'_>,
    univar: TypeExprRef,
    node: TypeExprRef,
    inverted: &HashMap<TypeExprRef, Vec<TypeExprRef>>,
    node_univars: &mut HashMap<TypeExprRef, HashSet<TypeExprRef>>,
) {
    let node = ctx.repr(node);
    let univar = ctx.repr(univar);

    let desc = ctx.get_desc(node);
    let is_locally_bound = match &*desc {
        TypeDesc::Tpoly { vars, .. } => vars.iter().any(|var| ctx.repr(*var) == univar),
        _ => false,
    };
    drop(desc);

    if is_locally_bound {
        return;
    }

    let inserted = node_univars.entry(node).or_default().insert(univar);
    if !inserted {
        return;
    }

    if let Some(parents) = inverted.get(&node) {
        for parent in parents {
            add_univar_to_parents(ctx, univar, *parent, inverted, node_univars);
        }
    }
}

fn compute_univars_per_node(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
) -> HashMap<TypeExprRef, HashSet<TypeExprRef>> {
    let mut inverted: HashMap<TypeExprRef, Vec<TypeExprRef>> = HashMap::new();
    build_inverse_type_graph(ctx, None, ty, &mut inverted);

    let mut node_univars: HashMap<TypeExprRef, HashSet<TypeExprRef>> = HashMap::new();
    let nodes: Vec<TypeExprRef> = inverted.keys().copied().collect();
    for node in nodes {
        let node = ctx.repr(node);
        let desc = ctx.get_desc(node);
        let is_univar = matches!(&*desc, TypeDesc::Tunivar(_));
        drop(desc);
        if is_univar {
            add_univar_to_parents(ctx, node, node, &inverted, &mut node_univars);
        }
    }
    node_univars
}

#[derive(Clone)]
struct CopySepVisitedEntry {
    ty: TypeExprRef,
    copied: TypeExprRef,
    bound: Vec<TypeExprRef>,
}

fn copy_sep_row(
    ctx: &TypeContext<'_>,
    row: &RowDesc,
    fixed: bool,
    keep: bool,
    more: TypeExprRef,
    free_univars: &HashMap<TypeExprRef, HashSet<TypeExprRef>>,
    bound: &[TypeExprRef],
    visited: &[CopySepVisitedEntry],
    delayed_copy: &mut Vec<(TypeExprRef, TypeExprRef)>,
) -> RowDesc {
    RowDesc {
        row_fields: row
            .row_fields
            .iter()
            .map(|(label, field)| {
                let field = super::btype::row_field_repr(ctx, field);
                let copied = match field {
                    RowField::Rpresent(Some(ty)) => RowField::Rpresent(Some(copy_sep_inner(
                        ctx,
                        ty,
                        fixed,
                        free_univars,
                        bound,
                        visited,
                        delayed_copy,
                    ))),
                    RowField::Reither {
                        constant,
                        types,
                        matched,
                        link,
                    } => RowField::Reither {
                        constant,
                        types: types
                            .iter()
                            .map(|t| {
                                copy_sep_inner(
                                    ctx,
                                    *t,
                                    fixed,
                                    free_univars,
                                    bound,
                                    visited,
                                    delayed_copy,
                                )
                            })
                            .collect(),
                        matched: if row.row_fixed { fixed } else { matched },
                        link: if keep { link } else { ctx.alloc_row_field(None) },
                    },
                    _ => field,
                };
                (label.clone(), copied)
            })
            .collect(),
        row_more: more,
        row_closed: row.row_closed,
        row_fixed: row.row_fixed && fixed,
        row_name: row.row_name.as_ref().map(|(path, types)| {
            (
                path.clone(),
                types
                    .iter()
                    .map(|t| {
                        copy_sep_inner(ctx, *t, fixed, free_univars, bound, visited, delayed_copy)
                    })
                    .collect(),
            )
        }),
    }
}

fn copy_sep_inner(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    fixed: bool,
    free_univars: &HashMap<TypeExprRef, HashSet<TypeExprRef>>,
    bound: &[TypeExprRef],
    visited: &[CopySepVisitedEntry],
    delayed_copy: &mut Vec<(TypeExprRef, TypeExprRef)>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty).clone();

    if let TypeDesc::Tsubst(target) = desc {
        return copy_sep_inner(
            ctx,
            target,
            fixed,
            free_univars,
            bound,
            visited,
            delayed_copy,
        );
    }

    let node_univars = free_univars.get(&ty).cloned().unwrap_or_default();
    if node_univars.is_empty() {
        if ctx.get_level(ty) != GENERIC_LEVEL {
            return ty;
        }
        let fresh = ctx.new_var(None);
        delayed_copy.push((fresh, ty));
        return fresh;
    }

    let ty_is_tunivar = matches!(desc, TypeDesc::Tunivar(_));
    for entry in visited {
        if entry.ty == ty {
            let dl = if ty_is_tunivar {
                vec![]
            } else {
                diff_bound_list(bound, &entry.bound)
            };
            if dl.is_empty() || !bound_conflicts(ctx, &node_univars, &dl) {
                return entry.copied;
            }
        }
    }

    let fresh = ctx.new_var(None);
    let mut visited_for_children = visited.to_vec();
    if matches!(
        desc,
        TypeDesc::Tarrow { .. }
            | TypeDesc::Ttuple(_)
            | TypeDesc::Tvariant(_)
            | TypeDesc::Tconstr { .. }
            | TypeDesc::Tobject { .. }
            | TypeDesc::Tpackage { .. }
    ) {
        visited_for_children.insert(
            0,
            CopySepVisitedEntry {
                ty,
                copied: fresh,
                bound: bound.to_vec(),
            },
        );
    }

    let copied_desc = match desc {
        TypeDesc::Tvar(_) => TypeDesc::Tvar(None),
        TypeDesc::Tarrow { arg, ret, arity, .. } => TypeDesc::Tarrow {
            arg: super::type_expr::TypeArg {
                lbl: arg.lbl,
                typ: copy_sep_inner(
                    ctx,
                    arg.typ,
                    fixed,
                    free_univars,
                    bound,
                    &visited_for_children,
                    delayed_copy,
                ),
            },
            ret: copy_sep_inner(
                ctx,
                ret,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
            commutable: super::type_expr::Commutable::Cok,
            arity,
        },
        TypeDesc::Ttuple(types) => TypeDesc::Ttuple(
            types
                .iter()
                .map(|t| {
                    copy_sep_inner(
                        ctx,
                        *t,
                        fixed,
                        free_univars,
                        bound,
                        &visited_for_children,
                        delayed_copy,
                    )
                })
                .collect(),
        ),
        TypeDesc::Tconstr { path, args, .. } => TypeDesc::Tconstr {
            path,
            args: args
                .iter()
                .map(|t| {
                    copy_sep_inner(
                        ctx,
                        *t,
                        fixed,
                        free_univars,
                        bound,
                        &visited_for_children,
                        delayed_copy,
                    )
                })
                .collect(),
            abbrev: ctx.alloc_abbrev_nil(),
        },
        TypeDesc::Tobject { fields, name } => TypeDesc::Tobject {
            fields: copy_sep_inner(
                ctx,
                fields,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
            name: name.map(|(path, types)| {
                (
                    path,
                    types
                        .iter()
                        .map(|t| {
                            copy_sep_inner(
                                ctx,
                                *t,
                                fixed,
                                free_univars,
                                bound,
                                &visited_for_children,
                                delayed_copy,
                            )
                        })
                        .collect(),
                )
            }),
        },
        TypeDesc::Tfield {
            name,
            kind,
            typ,
            rest,
        } => TypeDesc::Tfield {
            name,
            kind,
            typ: copy_sep_inner(
                ctx,
                typ,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
            rest: copy_sep_inner(
                ctx,
                rest,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
        },
        TypeDesc::Tnil => TypeDesc::Tnil,
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            return copy_sep_inner(
                ctx,
                target,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            );
        }
        TypeDesc::Tunivar(name) => TypeDesc::Tunivar(name),
        TypeDesc::Tvariant(row0) => {
            let row = row_repr(ctx, &row0);
            let more = ctx.repr(row.row_more);
            let keep = super::btype::is_tvar(ctx, more) && ctx.get_level(more) != GENERIC_LEVEL;
            let more_copy = copy_sep_inner(
                ctx,
                more,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            );
            let fixed_prime = fixed && super::btype::is_tvar(ctx, ctx.repr(more_copy));
            TypeDesc::Tvariant(copy_sep_row(
                ctx,
                &row,
                fixed_prime,
                keep,
                more_copy,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ))
        }
        TypeDesc::Tpoly { body, vars } => {
            let vars: Vec<_> = vars.into_iter().map(|v| ctx.repr(v)).collect();
            let fresh_vars: Vec<_> = vars
                .iter()
                .map(|v| {
                    let copied = ctx.get_desc(*v).clone();
                    ctx.new_type(copied)
                })
                .collect();

            let mut bound_prime = vars.clone();
            bound_prime.extend_from_slice(bound);

            let mut visited_poly: Vec<_> = vars
                .iter()
                .zip(fresh_vars.iter())
                .map(|(src, copied)| CopySepVisitedEntry {
                    ty: *src,
                    copied: *copied,
                    bound: bound_prime.clone(),
                })
                .collect();
            visited_poly.extend(visited_for_children);

            TypeDesc::Tpoly {
                body: copy_sep_inner(
                    ctx,
                    body,
                    fixed,
                    free_univars,
                    &bound_prime,
                    &visited_poly,
                    delayed_copy,
                ),
                vars: fresh_vars,
            }
        }
        TypeDesc::Tpackage { path, lids, args } => TypeDesc::Tpackage {
            path,
            lids,
            args: args
                .iter()
                .map(|t| {
                    copy_sep_inner(
                        ctx,
                        *t,
                        fixed,
                        free_univars,
                        bound,
                        &visited_for_children,
                        delayed_copy,
                    )
                })
                .collect(),
        },
    };

    ctx.set_desc(fresh, copied_desc);
    fresh
}

/// Instantiate a polymorphic type with free universal variables.
/// Matches OCaml's `instance_poly` / `copy_sep` behavior.
pub fn instance_poly(
    ctx: &TypeContext<'_>,
    keep_names: bool,
    fixed: bool,
    univars: &[TypeExprRef],
    sch: TypeExprRef,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let univars: Vec<_> = univars.iter().map(|u| ctx.repr(*u)).collect();
    let vars: Vec<TypeExprRef> = univars
        .iter()
        .map(|u| {
            let desc = ctx.get_desc(*u);
            match &*desc {
                TypeDesc::Tunivar(name) => {
                    if keep_names {
                        ctx.new_type(TypeDesc::Tvar(name.clone()))
                    } else {
                        ctx.new_var(None)
                    }
                }
                _ => {
                    debug_assert!(false, "instance_poly expects Tunivar inputs");
                    ctx.new_var(None)
                }
            }
        })
        .collect();

    let free_univars = compute_univars_per_node(ctx, sch);
    let mut delayed_copy = Vec::new();
    let visited_pairs: Vec<_> = univars
        .iter()
        .zip(vars.iter())
        .map(|(u, v)| CopySepVisitedEntry {
            ty: *u,
            copied: *v,
            bound: vec![],
        })
        .collect();

    let instantiated = copy_sep_inner(
        ctx,
        sch,
        fixed,
        &free_univars,
        &[],
        &visited_pairs,
        &mut delayed_copy,
    );

    // OCaml pushes delayed copies onto a list head (`::`) and forces them in
    // list order, so materialization runs in reverse discovery order under one
    // shared copy window.
    let mut delayed_cache = CopyCache::new();
    for (stub, source) in delayed_copy.into_iter().rev() {
        let copied = copy_type_cached(ctx, source, &mut delayed_cache);
        ctx.set_desc(stub, TypeDesc::Tlink(copied));
    }

    (vars, instantiated)
}

/// Instantiate a constructor description, creating fresh type variables for its
/// result type and argument types while sharing the same variable substitutions.
/// Matches OCaml's Ctype.instance_constructor.
pub fn instance_constructor(
    ctx: &TypeContext<'_>,
    cstr: &super::ConstructorDescription,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new();
    let ty_res = copy_type_cached(ctx, cstr.cstr_res, &mut cache);
    let ty_args: Vec<TypeExprRef> = cstr
        .cstr_args
        .iter()
        .map(|&arg| copy_type_cached(ctx, arg, &mut cache))
        .collect();
    (ty_args, ty_res)
}

/// Instantiate a constructor description in a pattern context, processing GADT
/// existential type variables. For each existential, creates an abstract type
/// `$ConstructorName_'varname` and links the copied existential to it.
/// Matches OCaml's Ctype.instance_constructor ~in_pattern:(env, newtype_lev).
pub fn instance_constructor_in_pattern(
    ctx: &TypeContext<'_>,
    env: &mut super::env::Env,
    newtype_lev: i32,
    cstr: &super::ConstructorDescription,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new();

    // Process existential type variables before copying cstr_res/cstr_args.
    // This ensures the copy cache maps existential Tvars to abstract Tconstr nodes.
    for &existential in &cstr.cstr_existentials {
        let existential_repr = ctx.repr(existential);
        let name = {
            let desc = ctx.get_desc(existential_repr);
            match &*desc {
                super::type_expr::TypeDesc::Tvar(Some(name)) => {
                    format!("${}_'{}", cstr.cstr_name, name)
                }
                _ => format!("${}", cstr.cstr_name),
            }
        };

        // Create abstract type declaration
        let decl = super::TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: super::TypeKind::TypeAbstract,
            type_private: super::asttypes::PrivateFlag::Public,
            type_manifest: None,
            type_variance: vec![],
            type_newtype_level: Some((newtype_lev, newtype_lev)),
            type_loc: crate::location::Location::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_unboxed: super::decl::UnboxedStatus {
                unboxed: false,
                default: false,
            },
            type_inlined_types: vec![],
            type_path: None,
        };

        // Create path and add to environment
        let path = super::path::Path::pident(crate::ident::Ident::create_local(&name));
        env.add_local_constraint(path.clone(), decl);

        // Create Tconstr pointing to the abstract type
        let to_unify = ctx.new_constr(path, vec![]);

        // Copy the existential (adds it to cache), then link the copy to the Tconstr
        let tv = copy_type_cached(ctx, existential, &mut cache);
        link_type(ctx, tv, to_unify);
    }

    let ty_res = copy_type_cached(ctx, cstr.cstr_res, &mut cache);
    let ty_args: Vec<TypeExprRef> = cstr
        .cstr_args
        .iter()
        .map(|&arg| copy_type_cached(ctx, arg, &mut cache))
        .collect();
    (ty_args, ty_res)
}

/// Remap named type variables in a label type to the declaration's canonical
/// type parameter nodes. This keeps `lbl_arg` and `lbl_res` sharing the same
/// type parameter identities when labels are rebuilt from declarations.
pub fn remap_label_type_to_params(
    ctx: &TypeContext<'_>,
    label_ty: TypeExprRef,
    type_params: &[TypeExprRef],
) -> TypeExprRef {
    let label_ty = ctx.repr(label_ty);
    let desc = ctx.get_desc(label_ty);
    match &*desc {
        TypeDesc::Tvar(Some(name)) | TypeDesc::Tunivar(Some(name)) => {
            for &param in type_params {
                let param = ctx.repr(param);
                let param_desc = ctx.get_desc(param);
                match &*param_desc {
                    TypeDesc::Tvar(Some(param_name)) | TypeDesc::Tunivar(Some(param_name))
                        if param_name == name =>
                    {
                        return param;
                    }
                    _ => {}
                }
            }
            label_ty
        }
        TypeDesc::Tpoly { body, vars } => {
            let body = ctx.repr(*body);
            let vars = vars.clone();
            drop(desc);

            if vars.iter().any(|v| ctx.repr(*v) == body) {
                return label_ty;
            }

            let body_desc = ctx.get_desc(body);
            let body_name = match &*body_desc {
                TypeDesc::Tvar(Some(name)) | TypeDesc::Tunivar(Some(name)) => Some(name.clone()),
                _ => None,
            };
            drop(body_desc);

            let Some(body_name) = body_name else {
                return label_ty;
            };

            for &param in type_params {
                let param = ctx.repr(param);
                let param_desc = ctx.get_desc(param);
                match &*param_desc {
                    TypeDesc::Tvar(Some(param_name)) | TypeDesc::Tunivar(Some(param_name))
                        if *param_name == body_name =>
                    {
                        if param == body {
                            return label_ty;
                        }
                        let remapped = ctx.new_poly(param, vars);
                        let level = ctx.get_level(label_ty);
                        if ctx.get_level(remapped) != level {
                            ctx.set_level(remapped, level);
                        }
                        return remapped;
                    }
                    _ => {}
                }
            }

            label_ty
        }
        _ => label_ty,
    }
}

/// Instantiate a label description, creating fresh type variables for its
/// result type (record type) and argument type (field type) while sharing
/// the same variable substitutions between them.
/// Handles Tpoly unwrapping like OCaml's instance_label in ctype.ml.
pub fn instance_label(
    ctx: &TypeContext<'_>,
    lbl: &super::LabelDescription,
) -> (Vec<TypeExprRef>, TypeExprRef, TypeExprRef) {
    // OCaml ctype.ml instance_label: `copy lbl.lbl_res` sets Tsubst markers
    // that persist when copying lbl.lbl_arg. Shared nodes get the SAME copy
    // target. We model this with a shared HashMap cache.
    let mut cache = std::collections::HashMap::new();
    let ty_res = copy_type_deep(ctx, lbl.lbl_res, &mut cache);
    // OCaml's instance_label unwraps Tpoly before copying the field type.
    // For each Tunivar in the poly vars, pre-seed the cache with a fresh Tvar
    // so that Tunivar → Tvar conversion happens during the copy (like instance_poly).
    let arg_repr = ctx.repr(lbl.lbl_arg);
    let (poly_vars, ty_arg) = {
        let desc = ctx.get_desc(arg_repr);
        match &*desc {
            super::TypeDesc::Tpoly { body, vars } => {
                let body = *body;
                let vars = vars.clone();
                drop(desc);
                let mut fresh_vars = Vec::new();
                for v in &vars {
                    let v_repr = ctx.repr(*v);
                    let fresh = ctx.new_var(None);
                    cache.insert(v_repr, fresh);
                    fresh_vars.push(fresh);
                }
                (fresh_vars, copy_type_deep(ctx, body, &mut cache))
            }
            _ => {
                drop(desc);
                (vec![], copy_type_deep(ctx, lbl.lbl_arg, &mut cache))
            }
        }
    };
    (poly_vars, ty_arg, ty_res)
}

/// OCaml's check_univars: after typing a polymorphic field value,
/// convert any still-unresolved fresh Tvars back to Tunivar.
/// This preserves the universal quantification in the typed tree.
pub fn check_univars(ctx: &TypeContext<'_>, vars: &[TypeExprRef]) {
    for &v in vars {
        let v = ctx.repr(v);
        let desc = ctx.get_desc(v);
        match &*desc {
            super::TypeDesc::Tvar(name) => {
                let name = name.clone();
                drop(desc);
                ctx.set_desc(v, super::TypeDesc::Tunivar(name));
            }
            _ => {}
        }
    }
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
        TypeDesc::Tarrow {
            arg, ret, arity, ..
        } => {
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
            let new_types: Vec<_> = types
                .iter()
                .map(|t| copy_type_deep(ctx, *t, cache))
                .collect();
            let result = ctx.new_tuple(new_types);
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tconstr { path, args, .. } => {
            let new_args: Vec<_> = args
                .iter()
                .map(|t| copy_type_deep(ctx, *t, cache))
                .collect();
            let result = ctx.new_constr(path.clone(), new_args);
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tpoly { body, vars } => {
            let new_vars: Vec<_> = vars
                .iter()
                .map(|t| copy_type_deep(ctx, *t, cache))
                .collect();
            let new_body = copy_type_deep(ctx, *body, cache);
            let result = ctx.new_poly(new_body, new_vars);
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tvariant(row) => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let row = row_repr(ctx, row);
            let new_row_more = copy_type_deep(ctx, row.row_more, cache);
            let new_row_fields: Vec<_> = row
                .row_fields
                .iter()
                .map(|(label, field)| {
                    let repr_field = super::btype::row_field_repr(ctx, field);
                    let new_field = match repr_field {
                        crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
                            crate::types::type_expr::RowField::Rpresent(Some(copy_type_deep(
                                ctx, ty, cache,
                            )))
                        }
                        crate::types::type_expr::RowField::Rpresent(None) => {
                            crate::types::type_expr::RowField::Rpresent(None)
                        }
                        crate::types::type_expr::RowField::Reither {
                            constant,
                            types,
                            matched,
                            ..
                        } => crate::types::type_expr::RowField::Reither {
                            constant,
                            types: types
                                .iter()
                                .map(|t| copy_type_deep(ctx, *t, cache))
                                .collect(),
                            matched,
                            link: ctx.alloc_row_field(None),
                        },
                        crate::types::type_expr::RowField::Rabsent => {
                            crate::types::type_expr::RowField::Rabsent
                        }
                    };
                    (label.clone(), new_field)
                })
                .collect();
            let new_row_name = row.row_name.as_ref().map(|(path, args)| {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|t| copy_type_deep(ctx, *t, cache))
                    .collect();
                (path.clone(), new_args)
            });
            let new_row = crate::types::type_expr::RowDesc {
                row_fields: new_row_fields,
                row_more: new_row_more,
                row_closed: row.row_closed,
                row_fixed: row.row_fixed,
                row_name: new_row_name,
            };
            let result = ctx.new_variant(new_row);
            ctx.set_desc(placeholder, TypeDesc::Tlink(result));
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tobject { fields, name } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let new_fields = copy_type_deep(ctx, *fields, cache);
            let result = ctx.new_type(TypeDesc::Tobject {
                fields: new_fields,
                name: name.as_ref().map(|(path, args)| {
                    let new_args: Vec<_> = args.iter().map(|t| copy_type_deep(ctx, *t, cache)).collect();
                    (path.clone(), new_args)
                }),
            });
            ctx.set_desc(placeholder, TypeDesc::Tlink(result));
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tfield { name, kind, typ, rest } => {
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let name = name.clone();
            let kind = kind.clone();
            let new_typ = copy_type_deep(ctx, *typ, cache);
            let new_rest = copy_type_deep(ctx, *rest, cache);
            let result = ctx.new_type(TypeDesc::Tfield {
                name,
                kind,
                typ: new_typ,
                rest: new_rest,
            });
            ctx.set_desc(placeholder, TypeDesc::Tlink(result));
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tsubst(target) => copy_type_deep(ctx, *target, cache),
        TypeDesc::Tlink(target) => copy_type_deep(ctx, *target, cache),
        TypeDesc::Tnil | TypeDesc::Tunivar(_) => ty, // Return as-is
        TypeDesc::Tpackage { path, lids, args } => {
            let new_args: Vec<_> = args
                .iter()
                .map(|t| copy_type_deep(ctx, *t, cache))
                .collect();
            let result = ctx.new_type(TypeDesc::Tpackage {
                path: path.clone(),
                lids: lids.clone(),
                args: new_args,
            });
            cache.insert(ty, result);
            result
        }
    }
}

/// Cache for copy_type_cached: tracks node identity to preserve sharing.
struct CopyCache {
    /// Node identity cache: maps original TypeExprRef → copied TypeExprRef.
    /// Ensures that if the same node is visited twice, we reuse the copy.
    nodes: std::collections::HashMap<TypeExprRef, TypeExprRef>,

    /// Scoped marker table for OCaml Ctype.copy variant recursion handling.
    /// Mirrors `more.desc <- Tsubst(Ttuple [more'; t])` without mutating
    /// shared type descriptors in-place.
    row_more_markers: std::collections::HashMap<TypeExprRef, CopyRowMoreMarker>,
}

impl CopyCache {
    fn new() -> Self {
        CopyCache {
            nodes: std::collections::HashMap::new(),
            row_more_markers: std::collections::HashMap::new(),
        }
    }
}

#[derive(Clone, Copy)]
struct CopyRowMoreMarker {
    tuple: TypeExprRef,
    variant: TypeExprRef,
}

fn type_expr_contains_ident_stamp(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    target_stamp: i32,
    seen: &mut HashSet<TypeExprRef>,
) -> bool {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return false;
    }

    match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, args, .. } => {
            matches!(path, Path::Pident(id) if id.stamp() == target_stamp)
                || args
                    .iter()
                    .copied()
                    .any(|arg| type_expr_contains_ident_stamp(ctx, arg, target_stamp, seen))
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            type_expr_contains_ident_stamp(ctx, arg.typ, target_stamp, seen)
                || type_expr_contains_ident_stamp(ctx, *ret, target_stamp, seen)
        }
        TypeDesc::Ttuple(types) => types
            .iter()
            .copied()
            .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen)),
        TypeDesc::Tobject { fields, name } => {
            type_expr_contains_ident_stamp(ctx, *fields, target_stamp, seen)
                || name.as_ref().is_some_and(|(_, args)| {
                    args.iter()
                        .copied()
                        .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen))
                })
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            type_expr_contains_ident_stamp(ctx, *typ, target_stamp, seen)
                || type_expr_contains_ident_stamp(ctx, *rest, target_stamp, seen)
        }
        TypeDesc::Tvariant(row) => {
            type_expr_contains_ident_stamp(ctx, row.row_more, target_stamp, seen)
                || row.row_fields.iter().any(|(_, field)| match field {
                    RowField::Rpresent(Some(ty)) => {
                        type_expr_contains_ident_stamp(ctx, *ty, target_stamp, seen)
                    }
                    RowField::Reither { types, .. } => types
                        .iter()
                        .copied()
                        .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen)),
                    _ => false,
                })
                || row.row_name.as_ref().is_some_and(|(_, args)| {
                    args.iter()
                        .copied()
                        .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen))
                })
        }
        TypeDesc::Tpoly { body, vars } => {
            type_expr_contains_ident_stamp(ctx, *body, target_stamp, seen)
                || vars
                    .iter()
                    .copied()
                    .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen))
        }
        TypeDesc::Tpackage { args, .. } => args
            .iter()
            .copied()
            .any(|ty| type_expr_contains_ident_stamp(ctx, ty, target_stamp, seen)),
        TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
            type_expr_contains_ident_stamp(ctx, *target, target_stamp, seen)
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => false,
    }
}

pub(crate) fn is_recursive_local_type_for_identity(ctx: &TypeContext<'_>, path: &Path) -> bool {
    let Path::Pident(id) = path else {
        return false;
    };

    if id.is_persistent() || id.stamp() == 0 {
        return false;
    }

    let Some(decl) = ctx.find_type_decl_by_stamp(id.stamp()) else {
        return false;
    };

    let contains_self = |ty: TypeExprRef| {
        let mut seen = HashSet::new();
        type_expr_contains_ident_stamp(ctx, ty, id.stamp(), &mut seen)
    };

    match &decl.type_kind {
        super::decl::TypeKind::TypeVariant(constructors) => constructors.iter().any(|ctor| {
            let args_has_self = match &ctor.cd_args {
                super::decl::ConstructorArguments::CstrTuple(args) => {
                    args.iter().copied().any(contains_self)
                }
                super::decl::ConstructorArguments::CstrRecord(labels) => {
                    labels.iter().any(|label| contains_self(label.ld_type))
                }
            };
            args_has_self || ctor.cd_res.is_some_and(contains_self)
        }),
        super::decl::TypeKind::TypeRecord(labels, _) => {
            labels.iter().any(|label| contains_self(label.ld_type))
        }
        super::decl::TypeKind::TypeAbstract => decl.type_manifest.is_some_and(contains_self),
        super::decl::TypeKind::TypeOpen => false,
    }
}

fn is_recursive_local_nullary_type_for_identity(ctx: &TypeContext<'_>, path: &Path) -> bool {
    let Path::Pident(_) = path else {
        return false;
    };

    is_recursive_local_type_for_identity(ctx, path)
}

/// Check if a type is a local TypeAbstract Pident. These are safe to return
/// identity for in copy because they have no structural content (no variant
/// constructors, no record fields). Includes both opaque types (`type t`) and
/// type aliases (`type t = int`).
fn is_local_abstract_type(ctx: &TypeContext<'_>, path: &Path) -> bool {
    let Path::Pident(id) = path else {
        return false;
    };
    if id.is_persistent() || id.stamp() == 0 {
        return false;
    }
    let Some(decl) = ctx.find_type_decl_by_stamp(id.stamp()) else {
        return false;
    };
    matches!(decl.type_kind, super::decl::TypeKind::TypeAbstract)
}

/// Copy a type, creating fresh type variables for generic ones.
pub fn copy_type(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = CopyCache::new();
    copy_type_cached(ctx, ty, &mut cache)
}

/// Full structural copy of a type, copying ALL nodes regardless of level.
/// Matches OCaml's `Subst.type_expr Subst.identity` which creates fresh
/// nodes for everything except Tvars/Tunivar.
/// Used in type_newtype to ensure replace_newtype_path doesn't corrupt
/// shared pattern types.
pub fn subst_identity_copy(ctx: &TypeContext<'_>, ty: TypeExprRef) -> TypeExprRef {
    let mut seen = std::collections::HashMap::new();
    // OCaml Subst.typexp uses a temporary `row_more.desc <- Tsubst(Ttuple [...])`
    // marker window to preserve recursive row sharing while copying.
    // Keep the same lifetime semantics in a scoped side table.
    let mut row_more_markers = std::collections::HashMap::new();
    subst_identity_copy_rec(ctx, ty, &mut seen, &mut row_more_markers)
}

#[derive(Clone, Copy)]
struct SubstRowMoreMarker {
    tuple: TypeExprRef,
    variant: TypeExprRef,
}

fn subst_identity_copy_rec(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    seen: &mut std::collections::HashMap<TypeExprRef, TypeExprRef>,
    row_more_markers: &mut std::collections::HashMap<TypeExprRef, SubstRowMoreMarker>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    // OCaml Subst.typexp temporarily sets `more.desc <- Tsubst(Ttuple [more'; ty'])`.
    // During that scoped marker window, copying `more` returns the tuple target.
    if let Some(marker) = row_more_markers.get(&ty).copied() {
        return marker.tuple;
    }

    if let Some(&cached) = seen.get(&ty) {
        return cached;
    }

    let desc = ctx.get_desc(ty);
    match &*desc {
        // OCaml Subst.typexp returns identity for Tvar/Tunivar
        // (when not for_saving and id >= 0)
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {
            drop(desc);
            ty
        }
        _ => {
            drop(desc);
            // Create placeholder for cycle handling
            let placeholder = ctx.new_var(None);
            let level = ctx.get_level(ty);
            if level != GENERIC_LEVEL {
                ctx.set_level(placeholder, level);
            }
            seen.insert(ty, placeholder);

            let desc = ctx.get_desc(ty);
            let new_desc = match &*desc {
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => unreachable!(),
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                    let target = *target;
                    drop(desc);
                    return subst_identity_copy_rec(ctx, target, seen, row_more_markers);
                }
                TypeDesc::Tarrow { arg, ret, arity, .. } => {
                    let arg_typ = arg.typ;
                    let arg_lbl = arg.lbl.clone();
                    let ret = *ret;
                    let arity = *arity;
                    drop(desc);
                    let arg_copy = subst_identity_copy_rec(ctx, arg_typ, seen, row_more_markers);
                    let ret_copy = subst_identity_copy_rec(ctx, ret, seen, row_more_markers);
                    TypeDesc::Tarrow {
                        arg: crate::types::type_expr::TypeArg {
                            lbl: arg_lbl,
                            typ: arg_copy,
                        },
                        ret: ret_copy,
                        commutable: crate::types::type_expr::Commutable::Cok,
                        arity,
                    }
                }
                TypeDesc::Ttuple(types) => {
                    let types = types.clone();
                    drop(desc);
                    let types_copy: Vec<_> = types
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, seen, row_more_markers))
                        .collect();
                    TypeDesc::Ttuple(types_copy)
                }
                TypeDesc::Tconstr { path, args, .. } => {
                    let path = path.clone();
                    let args = args.clone();
                    drop(desc);
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tconstr {
                        path,
                        args: args_copy,
                        abbrev: ctx.alloc_abbrev_nil(),
                    }
                }
                TypeDesc::Tobject { fields, name } => {
                    let fields = *fields;
                    let name = name.clone();
                    drop(desc);
                    let fields_copy = subst_identity_copy_rec(ctx, fields, seen, row_more_markers);
                    let name_copy = name.map(|(path, args)| {
                        (
                            path,
                            args.iter()
                                .map(|t| {
                                    subst_identity_copy_rec(ctx, *t, seen, row_more_markers)
                                })
                                .collect(),
                        )
                    });
                    TypeDesc::Tobject {
                        fields: fields_copy,
                        name: name_copy,
                    }
                }
                TypeDesc::Tfield { name, kind, typ, rest } => {
                    let is_absent = matches!(kind, crate::types::type_expr::FieldKind::Fabsent);
                    let name = name.clone();
                    let kind = kind.clone();
                    let typ = *typ;
                    let rest = *rest;
                    drop(desc);
                    let rest_copy = subst_identity_copy_rec(ctx, rest, seen, row_more_markers);
                    if is_absent {
                        TypeDesc::Tlink(rest_copy)
                    } else {
                        let typ_copy = subst_identity_copy_rec(ctx, typ, seen, row_more_markers);
                        TypeDesc::Tfield {
                            name,
                            kind,
                            typ: typ_copy,
                            rest: rest_copy,
                        }
                    }
                }
                TypeDesc::Tpoly { body, vars } => {
                    let body = *body;
                    let vars = vars.clone();
                    drop(desc);
                    let body_copy = subst_identity_copy_rec(ctx, body, seen, row_more_markers);
                    let vars_copy: Vec<_> = vars
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tpoly {
                        body: body_copy,
                        vars: vars_copy,
                    }
                }
                TypeDesc::Tvariant(row) => {
                    let row = row.clone();
                    drop(desc);
                    let row = row_repr(ctx, &row);
                    let more = ctx.repr(row.row_more);
                    if let Some(marker) = row_more_markers.get(&more).copied() {
                        // OCaml Subst.typexp fast-path:
                        // more.desc = Tsubst(Ttuple [more'; ty']) => reuse ty'
                        // and remap future visits of this source node to ty'
                        // within the same copy window.
                        seen.insert(ty, marker.variant);
                        TypeDesc::Tlink(marker.variant)
                    } else {
                    let (dup, more_copy) = {
                        let more_desc = ctx.get_desc(more).clone();
                        let more_is_constr = matches!(&more_desc, TypeDesc::Tconstr { .. });
                        let dup = ctx.get_level(more) == GENERIC_LEVEL
                            || super::btype::static_row(ctx, &row)
                            || more_is_constr;
                        let more_copy = match more_desc {
                            TypeDesc::Tsubst(target) => target,
                            TypeDesc::Tconstr { .. } | TypeDesc::Tnil => {
                                subst_identity_copy_rec(ctx, more, seen, row_more_markers)
                            }
                            TypeDesc::Tunivar(_) => more,
                            TypeDesc::Tvar(name) => {
                                if dup {
                                    ctx.new_generic_type(TypeDesc::Tvar(name))
                                } else {
                                    more
                                }
                            }
                            TypeDesc::Tlink(target) => {
                                subst_identity_copy_rec(ctx, target, seen, row_more_markers)
                            }
                            _ => panic!("unexpected row_more in subst_identity_copy_rec"),
                        };
                        (dup, more_copy)
                    };
                    let marker_tuple =
                        ctx.new_generic_type(TypeDesc::Ttuple(vec![more_copy, placeholder]));
                    // OCaml Subst.typexp keeps `more.desc <- Tsubst(Ttuple [...])`
                    // alive until the outer cleanup window, not just this
                    // single variant-copy branch. Keep the marker for the
                    // entire subst_identity_copy traversal.
                    row_more_markers.insert(
                        more,
                        SubstRowMoreMarker {
                            tuple: marker_tuple,
                            variant: placeholder,
                        },
                    );
                    let keep_reither_link = !dup;
                    let fields_copy: Vec<_> = row
                        .row_fields
                        .iter()
                        .map(|(name, field)| {
                            let repr_field = super::btype::row_field_repr(ctx, field);
                            let field_copy = match repr_field {
                                crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
                                    crate::types::type_expr::RowField::Rpresent(
                                        Some(subst_identity_copy_rec(
                                            ctx,
                                            ty,
                                            seen,
                                            row_more_markers,
                                        )),
                                    )
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
                                    constant,
                                    types: types
                                        .iter()
                                        .map(|t| {
                                            subst_identity_copy_rec(
                                                ctx,
                                                *t,
                                                seen,
                                                row_more_markers,
                                            )
                                        })
                                        .collect(),
                                    matched: if row.row_fixed { true } else { matched },
                                    link: if keep_reither_link {
                                        link
                                    } else {
                                        ctx.alloc_row_field(None)
                                    },
                                },
                                crate::types::type_expr::RowField::Rabsent => {
                                    crate::types::type_expr::RowField::Rabsent
                                }
                            };
                            (name.clone(), field_copy)
                        })
                        .collect();
                    let name_copy = row.row_name.map(|(path, args)| {
                        (
                            path,
                            args.iter()
                                .map(|t| {
                                    subst_identity_copy_rec(
                                        ctx,
                                        *t,
                                        seen,
                                        row_more_markers,
                                    )
                                })
                                .collect(),
                        )
                    });
                    let row_copy = TypeDesc::Tvariant(RowDesc {
                        row_fields: fields_copy,
                        row_more: more_copy,
                        row_closed: row.row_closed,
                        row_fixed: row.row_fixed,
                        row_name: name_copy,
                    });
                    row_copy
                    }
                }
                TypeDesc::Tpackage { path, lids, args } => {
                    let path = path.clone();
                    let lids = lids.clone();
                    let args = args.clone();
                    drop(desc);
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tpackage {
                        path,
                        lids,
                        args: args_copy,
                    }
                }
            };
            ctx.set_desc(placeholder, new_desc);
            placeholder
        }
    }
}

/// Copy a type for instantiation.
///
/// OCaml `Ctype.copy` only duplicates nodes at `generic_level` and returns
/// non-generic nodes unchanged (`partial = None` case used by `instance`).
/// For duplicated generic nodes, sharing is preserved across the copied graph.
fn copy_type_cached(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    cache: &mut CopyCache,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    // OCaml Ctype.copy marker precedence:
    // if `more.desc` is temporarily `Tsubst(Ttuple [more'; t])`,
    // copying `more` itself must yield the tuple target.
    if let Some(marker) = cache.row_more_markers.get(&ty).copied() {
        return marker.tuple;
    }

    // Preserve sharing for already-copied nodes (OCaml Tsubst behavior).
    if let Some(&cached) = cache.nodes.get(&ty) {
        return cached;
    }

    // OCaml ctype.ml copy fast-path for recursive variants:
    // if row_more currently carries a temporary marker, reuse the
    // already-registered variant copy directly.
    if ctx.get_level(ty) == GENERIC_LEVEL {
        if let TypeDesc::Tvariant(row0) = &*ctx.get_desc(ty) {
            let row = row_repr(ctx, row0);
            let more = ctx.repr(row.row_more);
            if let Some(marker) = cache.row_more_markers.get(&more).copied() {
                cache.nodes.insert(ty, marker.variant);
                return marker.variant;
            }
        }
    }

    // Enum to hold what action to take, avoiding borrow issues.
    enum CopyAction {
        ReturnSelf,
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
        Object {
            fields: TypeExprRef,
            name: Option<(Path, Vec<TypeExprRef>)>,
        },
        Field {
            name: String,
            kind: super::type_expr::FieldKind,
            typ: TypeExprRef,
            rest: TypeExprRef,
        },
        Nil,
        Poly {
            body: TypeExprRef,
            vars: Vec<TypeExprRef>,
        },
        Variant(RowDesc),
        Package {
            path: Path,
            lids: Vec<crate::parser::longident::Longident>,
            args: Vec<TypeExprRef>,
        },
        Link(TypeExprRef),
    }

    let level = ctx.get_level(ty);

    // Determine action based on type level and descriptor.
    let action = {
        let desc = ctx.get_desc(ty);

        if level != GENERIC_LEVEL {
            match &*desc {
                // Identity for all non-Tconstr types — matches OCaml's copy
                // which returns identity for ALL non-generic types.
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => CopyAction::ReturnSelf,
                TypeDesc::Ttuple(_) => CopyAction::ReturnSelf,
                TypeDesc::Tobject { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tvariant(_) => CopyAction::ReturnSelf,
                TypeDesc::Tpoly { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tpackage { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tarrow { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tfield { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tnil => CopyAction::ReturnSelf,
                // Tconstr: selective identity to avoid functor/variant crashes
                TypeDesc::Tconstr { path, args, .. }
                    if is_predef_type_name(path.head_name())
                        && args.iter().copied().all(|arg| {
                            !matches!(
                                &*ctx.get_desc(ctx.repr(arg)),
                                TypeDesc::Tvariant(_)
                            )
                        }) =>
                {
                    CopyAction::ReturnSelf
                }
                TypeDesc::Tconstr { path, args, .. }
                    if (args.is_empty() && (is_recursive_local_nullary_type_for_identity(ctx, path) || is_local_abstract_type(ctx, path)))
                        || (!args.is_empty()
                            && is_recursive_local_type_for_identity(ctx, path)
                            && args.iter().copied().all(|arg| {
                                matches!(
                                    &*ctx.get_desc(ctx.repr(arg)),
                                    TypeDesc::Tvar(None) | TypeDesc::Tunivar(None)
                                )
                            })) =>
                {
                    CopyAction::ReturnSelf
                }
                TypeDesc::Tconstr { path, args, .. } => CopyAction::Constr {
                    path: path.clone(),
                    args: args.clone(),
                },
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => CopyAction::Link(*target),
            }
        } else {
            match &*desc {
                TypeDesc::Tvar(_) => CopyAction::NewVar(None),
                TypeDesc::Tunivar(name) => CopyAction::NewUnivar(name.clone()),
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
                TypeDesc::Tobject { fields, name } => CopyAction::Object {
                    fields: *fields,
                    name: name.clone(),
                },
                TypeDesc::Tfield {
                    name,
                    kind,
                    typ,
                    rest,
                } => {
                    if matches!(kind, crate::types::type_expr::FieldKind::Fabsent) {
                        CopyAction::Link(*rest)
                    } else {
                        CopyAction::Field {
                            name: name.clone(),
                            kind: kind.clone(),
                            typ: *typ,
                            rest: *rest,
                        }
                    }
                }
                TypeDesc::Tnil => CopyAction::Nil,
                TypeDesc::Tpoly { body, vars } => CopyAction::Poly {
                    body: *body,
                    vars: vars.clone(),
                },
                TypeDesc::Tvariant(row) => CopyAction::Variant(row.clone()),
                TypeDesc::Tpackage { path, lids, args } => CopyAction::Package {
                    path: path.clone(),
                    lids: lids.clone(),
                    args: args.clone(),
                },
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => CopyAction::Link(*target),
            }
        }
    };

    // Execute the action without holding the borrow.
    match action {
        CopyAction::ReturnSelf => ty,
        CopyAction::Link(target) => copy_type_cached(ctx, target, cache),
        CopyAction::NewVar(name) => {
            // OCaml preserves Tvar names in copy: newvar2 ~name:(match ty.desc with Tvar name -> name | _ -> None)
            let fresh = ctx.new_var(name);
            cache.nodes.insert(ty, fresh);
            fresh
        }
        CopyAction::NewUnivar(name) => {
            let fresh = ctx.new_univar(name);
            cache.nodes.insert(ty, fresh);
            fresh
        }
        // Generic structural nodes must be registered before recursion so
        // recursive references can reuse the same node.
        structural => {
            let placeholder = ctx.new_var(None);
            if level != GENERIC_LEVEL {
                ctx.set_level(placeholder, level);
            }
            cache.nodes.insert(ty, placeholder);
            let copied_desc = match structural {
                CopyAction::Arrow {
                    arg_lbl,
                    arg_typ,
                    ret,
                    arity,
                } => {
                    let arg_copy = copy_type_cached(ctx, arg_typ, cache);
                    let ret_copy = copy_type_cached(ctx, ret, cache);
                    TypeDesc::Tarrow {
                        arg: crate::types::type_expr::TypeArg {
                            lbl: arg_lbl,
                            typ: arg_copy,
                        },
                        ret: ret_copy,
                        commutable: crate::types::type_expr::Commutable::Cok,
                        arity,
                    }
                }
                CopyAction::Tuple(types) => {
                    let types_copy: Vec<_> = types
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();
                    TypeDesc::Ttuple(types_copy)
                }
                CopyAction::Constr { path, args } => {
                    if args.is_empty() && level == GENERIC_LEVEL {
                        // Check simple_abbrevs (cross-instance sharing from lower_args)
                        if let Some(abbrev_ty) = ctx.find_simple_abbrev(&path) {
                            if ctx.repr(abbrev_ty) != placeholder {
                                TypeDesc::Tlink(abbrev_ty)
                            } else {
                                TypeDesc::Tconstr {
                                    path,
                                    args: vec![],
                                    abbrev: ctx.alloc_abbrev_nil(),
                                }
                            }
                        } else {
                            TypeDesc::Tconstr {
                                path,
                                args: vec![],
                                abbrev: ctx.alloc_abbrev_nil(),
                            }
                        }
                    } else {
                        let args_copy: Vec<_> = args
                            .iter()
                            .map(|t| copy_type_cached(ctx, *t, cache))
                            .collect();
                        TypeDesc::Tconstr {
                            path,
                            args: args_copy,
                            abbrev: ctx.alloc_abbrev_nil(),
                        }
                    }
                }
                CopyAction::Object { fields, name } => {
                    let fields_copy = copy_type_cached(ctx, fields, cache);
                    let name_copy = name.map(|(path, args)| {
                        (
                            path,
                            args.iter()
                                .map(|t| copy_type_cached(ctx, *t, cache))
                                .collect(),
                        )
                    });
                    TypeDesc::Tobject {
                        fields: fields_copy,
                        name: name_copy,
                    }
                }
                CopyAction::Field {
                    name,
                    kind,
                    typ,
                    rest,
                } => {
                    let typ_copy = copy_type_cached(ctx, typ, cache);
                    let rest_copy = copy_type_cached(ctx, rest, cache);
                    TypeDesc::Tfield {
                        name,
                        kind,
                        typ: typ_copy,
                        rest: rest_copy,
                    }
                }
                CopyAction::Nil => TypeDesc::Tnil,
                CopyAction::Poly { body, vars } => {
                    let body_copy = copy_type_cached(ctx, body, cache);
                    let vars_copy: Vec<_> = vars
                        .iter()
                        .map(|v| copy_type_cached(ctx, *v, cache))
                        .collect();
                    TypeDesc::Tpoly {
                        body: body_copy,
                        vars: vars_copy,
                    }
                }
                CopyAction::Variant(row) => {
                    // OCaml Ctype.copy uses copy_row with keep/fixed semantics
                    // derived from row_more, not a plain structural field copy.
                    let row = row_repr(ctx, &row);
                    let more = ctx.repr(row.row_more);
                    let more_level = ctx.get_level(more);
                    let keep = super::btype::is_tvar(ctx, more) && more_level != GENERIC_LEVEL;
                    let more_copy = match ctx.get_desc(more).clone() {
                        TypeDesc::Tconstr { .. } | TypeDesc::Tnil => {
                            copy_type_cached(ctx, more, cache)
                        }
                        TypeDesc::Tvar(name) => {
                            if keep {
                                more
                            } else {
                                let fresh = ctx.new_var(name);
                                if more_level != GENERIC_LEVEL {
                                    ctx.set_level(fresh, more_level);
                                }
                                fresh
                            }
                        }
                        TypeDesc::Tunivar(name) => {
                            if keep {
                                more
                            } else {
                                let fresh = ctx.new_univar(name);
                                if more_level != GENERIC_LEVEL {
                                    ctx.set_level(fresh, more_level);
                                }
                                fresh
                            }
                        }
                        TypeDesc::Tsubst(target) | TypeDesc::Tlink(target) => {
                            copy_type_cached(ctx, target, cache)
                        }
                        _ => copy_type_cached(ctx, more, cache),
                    };
                    let marker_tuple =
                        ctx.new_generic_type(TypeDesc::Ttuple(vec![more_copy, placeholder]));
                    let prev_marker = cache.row_more_markers.insert(
                        more,
                        CopyRowMoreMarker {
                            tuple: marker_tuple,
                            variant: placeholder,
                        },
                    );
                    let fixed = super::btype::is_tvar(ctx, ctx.repr(more_copy));
                    let mut row_copy = copy_row_cached(ctx, &row, fixed, keep, more_copy, cache);
                    match prev_marker {
                        Some(prev) => {
                            cache.row_more_markers.insert(more, prev);
                        }
                        None => {
                            cache.row_more_markers.remove(&more);
                        }
                    }

                    // OCaml ctype.ml PR#6163: promote copied rows to fixed when
                    // copied row_more is a constructor.
                    if !row_copy.row_fixed {
                        let more_desc = ctx.get_desc(ctx.repr(more_copy));
                        let more_is_constr = matches!(&*more_desc, TypeDesc::Tconstr { .. });
                        drop(more_desc);
                        if more_is_constr {
                            row_copy.row_fixed = true;
                            for (_, field) in row_copy.row_fields.iter_mut() {
                                if let RowField::Reither { matched, .. } = field {
                                    *matched = true;
                                }
                            }
                        }
                    }
                    TypeDesc::Tvariant(row_copy)
                }
                CopyAction::Package { path, lids, args } => {
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();
                    TypeDesc::Tpackage {
                        path,
                        lids,
                        args: args_copy,
                    }
                }
                CopyAction::ReturnSelf
                | CopyAction::NewVar(_)
                | CopyAction::NewUnivar(_)
                | CopyAction::Link(_) => unreachable!(),
            };
            ctx.set_desc(placeholder, copied_desc);
            placeholder
        }
    }
}

/// Copy a row descriptor.
fn copy_row_cached(
    ctx: &TypeContext<'_>,
    row: &RowDesc,
    fixed: bool,
    keep: bool,
    more: TypeExprRef,
    cache: &mut CopyCache,
) -> RowDesc {
    RowDesc {
        row_fields: row
            .row_fields
            .iter()
            .map(|(label, field)| {
                let field = super::btype::row_field_repr(ctx, field);
                let copied = match field {
                    RowField::Rpresent(Some(ty)) => {
                        RowField::Rpresent(Some(copy_type_cached(ctx, ty, cache)))
                    }
                    RowField::Reither {
                        constant,
                        types,
                        matched,
                        link,
                    } => RowField::Reither {
                        constant,
                        types: types
                            .iter()
                            .map(|t| copy_type_cached(ctx, *t, cache))
                            .collect(),
                        matched: if row.row_fixed { fixed } else { matched },
                        link: if keep { link } else { ctx.alloc_row_field(None) },
                    },
                    _ => field,
                };
                (label.clone(), copied)
            })
            .collect(),
        row_more: more,
        row_closed: row.row_closed,
        row_fixed: row.row_fixed && fixed,
        row_name: row.row_name.as_ref().map(|(path, types)| {
            (
                path.clone(),
                types
                    .iter()
                    .map(|t| copy_type_cached(ctx, *t, cache))
                    .collect(),
            )
        }),
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
pub fn split_arrow_with_label(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
) -> Option<(super::ArgLabel, TypeExprRef, TypeExprRef)> {
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
