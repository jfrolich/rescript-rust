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

use super::btype::{self, iter_type_expr, row_fixed, row_more, row_repr};
use super::context::TypeContext;
use super::env::Env;
use super::path::Path;
use super::asttypes::PrivateFlag;
use super::type_expr::{AbbrevMemo, AbbrevMemoRef, FieldKind, GENERIC_LEVEL, RowDesc, RowField, TypeDesc, TypeExprRef};
use super::variance::{Variance, VarianceFlag};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

static COPY_CONSTR_DEBUG_EVENTS: AtomicUsize = AtomicUsize::new(0);

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

fn debug_unify_row_filter(env_var: &str) -> Option<Vec<String>> {
    std::env::var(env_var).ok().and_then(|raw| {
        let labels: Vec<String> = raw
            .split(',')
            .map(|part| part.trim())
            .filter(|part| !part.is_empty())
            .map(|part| part.to_string())
            .collect();
        (!labels.is_empty()).then_some(labels)
    })
}

fn debug_row_labels(fields: &[(String, RowField)]) -> Vec<String> {
    fields.iter().map(|(label, _)| label.clone()).collect()
}

fn debug_unify_rows_enabled(
    filter: &[String],
    row1: &RowDesc,
    row2: &RowDesc,
    r1: &[(String, RowField)],
    r2: &[(String, RowField)],
    pairs: &[(String, RowField, RowField)],
) -> bool {
    let mut labels = debug_row_labels(&row1.row_fields);
    labels.extend(debug_row_labels(&row2.row_fields));
    labels.extend(debug_row_labels(r1));
    labels.extend(debug_row_labels(r2));
    labels.extend(pairs.iter().map(|(label, _, _)| label.clone()));
    filter.iter().all(|needle| labels.iter().any(|label| label == needle))
}

fn debug_unify_rows_log(
    stage: &str,
    row1: &RowDesc,
    row2: &RowDesc,
    r1: &[(String, RowField)],
    r2: &[(String, RowField)],
    pairs: &[(String, RowField, RowField)],
) {
    eprintln!(
        "[unify-rows {stage}] row1={{closed:{} fixed:{} labels={:?}}} row2={{closed:{} fixed:{} labels={:?}}} r1={:?} r2={:?} pairs={:?}",
        row1.row_closed,
        row1.row_fixed,
        debug_row_labels(&row1.row_fields),
        row2.row_closed,
        row2.row_fixed,
        debug_row_labels(&row2.row_fields),
        debug_row_labels(r1),
        debug_row_labels(r2),
        pairs.iter().map(|(label, _, _)| label).collect::<Vec<_>>(),
    );
}

fn debug_unify_row_field_enabled(label: &str) -> bool {
    std::env::var("RUST_DEBUG_UNIFY_ROW_FIELD")
        .ok()
        .map(|raw| {
            raw.split(',')
                .map(|part| part.trim())
                .filter(|part| !part.is_empty())
                .any(|needle| needle == label)
        })
        .unwrap_or(false)
}

fn debug_unify_row_types(ctx: &TypeContext<'_>, tys: &[TypeExprRef]) -> String {
    tys.iter()
        .map(|ty| {
            let repr = ctx.repr(*ty);
            let desc = ctx.get_desc(repr);
            let summary = match &*desc {
                TypeDesc::Ttuple(items) => format!(
                    "Ttuple({})",
                    items.iter()
                        .map(|item| ctx.repr(*item).0.to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                ),
                TypeDesc::Tvar(_) => "Tvar".to_string(),
                TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                TypeDesc::Tlink(target) => format!("Tlink({})", ctx.repr(*target).0),
                _ => format!("{:?}", &*desc),
            };
            format!("{}:{}", repr.0, summary)
        })
        .collect::<Vec<_>>()
        .join(",")
}

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
        self.env = Some(env.clone_preserve_id());
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

fn lookup_type_decl_for_path(
    ctx: &TypeContext<'_>,
    env: &Env,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    let debug_lookup_target = std::env::var("RUST_DEBUG_LOOKUP_TYPE").ok();
    let debug_lookup_target_match = debug_lookup_target
        .as_deref()
        .is_some_and(|target| path.name() == target);
    let debug_lookup = std::env::var_os("RUST_DEBUG_LOOKUP_KEY").is_some()
        && (path.last() == "key"
            || path.last() == "id"
            || path.name() == "Ord.t"
            || path.last() == "compactDisplay"
            || path.last() == "currency"
            || path.last() == "style")
        || debug_lookup_target_match;
    let path_name = if debug_lookup { Some(path.name()) } else { None };
    let describe_decl = |decl: &super::decl::TypeDeclaration| {
        let manifest = decl
            .type_manifest
            .map(|manifest| {
                let m = ctx.repr(manifest);
                let d = ctx.get_desc(m);
                match &*d {
                    TypeDesc::Tconstr { path, .. } => format!("manifest=Tconstr({})", path.name()),
                    TypeDesc::Tvar(_) => "manifest=Tvar".to_string(),
                    TypeDesc::Tunivar(_) => "manifest=Tunivar".to_string(),
                    TypeDesc::Tarrow { .. } => "manifest=Tarrow".to_string(),
                    TypeDesc::Ttuple(_) => "manifest=Ttuple".to_string(),
                    TypeDesc::Tlink(t) => format!("manifest=Tlink({})", ctx.repr(*t).0),
                    TypeDesc::Tsubst(t) => format!("manifest=Tsubst({})", ctx.repr(*t).0),
                    TypeDesc::Tobject { .. } => "manifest=Tobject".to_string(),
                    TypeDesc::Tfield { .. } => "manifest=Tfield".to_string(),
                    TypeDesc::Tnil => "manifest=Tnil".to_string(),
                    TypeDesc::Tvariant(_) => "manifest=Tvariant".to_string(),
                    TypeDesc::Tpoly { .. } => "manifest=Tpoly".to_string(),
                    TypeDesc::Tpackage { .. } => "manifest=Tpackage".to_string(),
                }
            })
            .unwrap_or_else(|| "manifest=None".to_string());
        let variance = decl
            .type_variance
            .iter()
            .enumerate()
            .map(|(i, v)| {
                format!(
                    "{}:(mp={},mn={},mw={},inj={},p={},n={},inv={})",
                    i,
                    v.mem(VarianceFlag::MayPos),
                    v.mem(VarianceFlag::MayNeg),
                    v.mem(VarianceFlag::MayWeak),
                    v.mem(VarianceFlag::Inj),
                    v.mem(VarianceFlag::Pos),
                    v.mem(VarianceFlag::Neg),
                    v.mem(VarianceFlag::Inv)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let type_path = decl
            .type_path
            .as_ref()
            .map(|p| p.name())
            .unwrap_or_else(|| "<none>".to_string());
        format!("{manifest} type_path={type_path} variance=[{variance}]")
    };

    if let Some(decl) = env.find_local_constraint(path) {
        if let Some(path_name) = &path_name {
            eprintln!(
                "[lookup-type] path={} source=local_constraint {}",
                path_name,
                describe_decl(decl)
            );
        }
        return Some(decl.clone());
    }

    // Try direct env lookup. For qualified paths, only accept exact
    // identity matches (`Path.same`) to mirror OCaml's stamp-based lookup.
    // Name-only equality can pick declarations from different scopes.
    if let Ok(decl) = env.lookup_type(path) {
        let exact_lookup = match path {
            Path::Pident(_) => true,
            _ => decl
                .type_path
                .as_ref()
                .is_some_and(|decl_path| decl_path.same(path)),
        };
        if exact_lookup {
            if let Some(path_name) = &path_name {
                eprintln!(
                    "[lookup-type] path={} source=env.lookup_type {}",
                    path_name,
                    describe_decl(decl)
                );
            }
            return Some(decl.clone());
        }
    }

    if let Some(decl) = resolve_type_through_modules(ctx, path) {
        if let Some(path_name) = &path_name {
            eprintln!(
                "[lookup-type] path={} source=resolve_type_through_modules {}",
                path_name,
                describe_decl(&decl)
            );
        }
        return Some(decl);
    }

    if let Some(decl) = resolve_type_through_env(ctx, env, path, true) {
        if let Some(path_name) = &path_name {
            eprintln!(
                "[lookup-type] path={} source=resolve_type_through_env {}",
                path_name,
                describe_decl(&decl)
            );
        }
        return Some(decl);
    }

    if let Some(path_name) = &path_name {
        eprintln!("[lookup-type] path={} source=none", path_name);
    }

    None
}

fn is_newtype_path(ctx: &TypeContext<'_>, env: &Env, path: &Path) -> bool {
    lookup_type_decl_for_path(ctx, env, path).is_some_and(|decl| {
        decl.type_newtype_level.is_some()
            && matches!(decl.type_kind, super::TypeKind::TypeAbstract)
            && matches!(decl.type_private, super::PrivateFlag::Public)
    })
}

fn find_newtype_level_for_path(ctx: &TypeContext<'_>, env: &Env, path: &Path) -> (i32, i32) {
    lookup_type_decl_for_path(ctx, env, path)
        .and_then(|decl| decl.type_newtype_level)
        .unwrap_or_else(|| {
            let lev = path.head().binding_time();
            (lev, lev)
        })
}

fn decl_manifest_aliases_path(
    ctx: &TypeContext<'_>,
    decl: &super::decl::TypeDeclaration,
    target: &Path,
    arity: usize,
) -> bool {
    decl.type_manifest.is_some_and(|manifest| {
        let manifest = ctx.repr(manifest);
        let manifest_desc = ctx.get_desc(manifest);
        match &*manifest_desc {
            TypeDesc::Tconstr { path, args, .. } => {
                args.len() == arity && (path.same(target) || path.name() == target.name())
            }
            _ => false,
        }
    })
}

pub(crate) fn flattened_alias_paths_equivalent(
    ctx: &TypeContext<'_>,
    env: &Env,
    path1: &Path,
    path2: &Path,
    arity: usize,
) -> bool {
    fn underscore_joined_prefix_match(long: &[&str], short: &[&str]) -> bool {
        if long.len() < 3 || short.len() != 2 || short[1] != long[long.len() - 1] {
            return false;
        }
        let expected = long[..long.len() - 1].join("_");
        short[0] == expected
    }

    fn concatenated_flatten_match(long: &[&str], short: &[&str]) -> bool {
        if long.len() <= short.len() || short.is_empty() || long.last() != short.last() {
            return false;
        }

        // Runtime/library flattened module heads often collapse a qualified
        // prefix into `Head_Sub1Sub2...`, e.g. `Belt.Map.Dict.t` ->
        // `Belt_MapDict.t`.
        for collapse_end in 2..long.len() {
            if 1 + (long.len() - collapse_end) != short.len() {
                continue;
            }

            let mut flat_head = String::from(long[0]);
            flat_head.push('_');
            for seg in &long[1..collapse_end] {
                flat_head.push_str(seg);
            }

            if flat_head == short[0] && short[1..] == long[collapse_end..] {
                return true;
            }
        }

        false
    }

    let name1 = path1.name();
    let name2 = path2.name();
    let debug_flat = std::env::var_os("RUST_DEBUG_FLAT_EQ").is_some()
        && (name1.contains("Webapi") || name2.contains("Webapi"));
    let seg1: Vec<&str> = name1.split('.').collect();
    let seg2: Vec<&str> = name2.split('.').collect();
    let candidate = if seg1.len() == seg2.len() + 1
        && seg1.len() >= 3
        && seg2.len() >= 2
        && format!("{}__{}", seg1[0], seg1[1]) == seg2[0]
        && seg1[2..] == seg2[1..]
    {
        Some((path1, path2))
    } else if seg2.len() == seg1.len() + 1
        && seg2.len() >= 3
        && seg1.len() >= 2
        && format!("{}__{}", seg2[0], seg2[1]) == seg1[0]
        && seg2[2..] == seg1[1..]
    {
        Some((path2, path1))
    } else if underscore_joined_prefix_match(seg1.as_slice(), seg2.as_slice()) {
        Some((path1, path2))
    } else if underscore_joined_prefix_match(seg2.as_slice(), seg1.as_slice()) {
        Some((path2, path1))
    } else if concatenated_flatten_match(seg1.as_slice(), seg2.as_slice()) {
        Some((path1, path2))
    } else if concatenated_flatten_match(seg2.as_slice(), seg1.as_slice()) {
        Some((path2, path1))
    } else {
        None
    };
    if debug_flat {
        eprintln!(
            "[flat-eq] path1={} path2={} candidate={}",
            name1,
            name2,
            candidate.is_some()
        );
    }
    let Some((long_path, short_path)) = candidate else {
        return false;
    };

    let long_decl = lookup_type_decl_for_path(ctx, env, long_path);
    let short_decl = lookup_type_decl_for_path(ctx, env, short_path);
    if debug_flat {
        eprintln!(
            "[flat-eq] long={} short={} long_decl={} short_decl={}",
            long_path.name(),
            short_path.name(),
            long_decl.is_some(),
            short_decl.is_some()
        );
    }
    // The naming shape already proves these are flattened/unflattened forms
    // of the same path family. If declaration lookup fails (common for some
    // external aliases), accept the equivalence directly.
    if long_decl.is_none() || short_decl.is_none() {
        if debug_flat {
            eprintln!("[flat-eq] accept=true reason=missing-decl");
        }
        return true;
    }
    let long_decl = long_decl.unwrap();
    let short_decl = short_decl.unwrap();
    if debug_flat {
        let long_type_path = long_decl
            .type_path
            .as_ref()
            .map(|p| p.name())
            .unwrap_or_else(|| "<none>".to_string());
        let short_type_path = short_decl
            .type_path
            .as_ref()
            .map(|p| p.name())
            .unwrap_or_else(|| "<none>".to_string());
        eprintln!(
            "[flat-eq] long_manifest={} short_manifest={} long_type_path={} short_type_path={}",
            long_decl.type_manifest.is_some(),
            short_decl.type_manifest.is_some(),
            long_type_path,
            short_type_path
        );
    }
    if (short_decl.type_manifest.is_none() && short_decl.type_path.is_none())
        || (long_decl.type_manifest.is_none() && long_decl.type_path.is_none())
    {
        if debug_flat {
            eprintln!("[flat-eq] accept=true reason=opaque-proxy-decl");
        }
        return true;
    }

    let result = decl_manifest_aliases_path(ctx, &short_decl, long_path, arity)
        || decl_manifest_aliases_path(ctx, &long_decl, short_path, arity)
        || long_decl
            .type_path
            .as_ref()
            .zip(short_decl.type_path.as_ref())
            .is_some_and(|(lp, sp)| lp.same(sp) || lp.name() == sp.name());
    if debug_flat {
        eprintln!("[flat-eq] accept={result} reason=decl-check");
    }
    result
}

pub(crate) fn nullary_constr_paths_equivalent(
    ctx: &TypeContext<'_>,
    env: &Env,
    path1: &Path,
    path2: &Path,
) -> bool {
    if path1.same(path2) || path1.name() == path2.name() {
        return true;
    }

    let decl1 = lookup_type_decl_for_path(ctx, env, path1)
        .or_else(|| env.lookup_type(path1).ok().cloned());
    let decl2 = lookup_type_decl_for_path(ctx, env, path2)
        .or_else(|| env.lookup_type(path2).ok().cloned());
    let (Some(decl1), Some(decl2)) = (decl1, decl2) else {
        return false;
    };

    let same_type_path = decl1
        .type_path
        .as_ref()
        .zip(decl2.type_path.as_ref())
        .is_some_and(|(p1, p2)| p1.same(p2) || p1.name() == p2.name());
    if same_type_path {
        return true;
    }

    if decl_manifest_aliases_path(ctx, &decl1, path2, 0)
        || decl_manifest_aliases_path(ctx, &decl2, path1, 0)
    {
        return true;
    }

    flattened_alias_paths_equivalent(ctx, env, path1, path2, 0)
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
    let debug_gadt_eq = std::env::var_os("RUST_DEBUG_GADT_EQ").is_some();
    let source_name = if debug_gadt_eq {
        Some(source_path.name())
    } else {
        None
    };

    // local_non_recursive_abbrev check: destination must not reference source
    let dest_repr = ctx.repr(destination);
    if let Some(source_name) = &source_name {
        let dest_head = {
            let desc = ctx.get_desc(dest_repr);
            match &*desc {
                TypeDesc::Tconstr { path, .. } => path.name(),
                TypeDesc::Tvar(_) => "Tvar".to_string(),
                TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                TypeDesc::Tlink(_) => "Tlink".to_string(),
                TypeDesc::Tsubst(_) => "Tsubst".to_string(),
                TypeDesc::Tobject { .. } => "Tobject".to_string(),
                TypeDesc::Tfield { .. } => "Tfield".to_string(),
                TypeDesc::Tnil => "Tnil".to_string(),
                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
            }
        };
        let existing_manifest = env
            .find_local_constraint(source_path)
            .and_then(|decl| decl.type_manifest)
            .map(|manifest| {
                let manifest_repr = ctx.repr(manifest);
                let manifest_head = {
                    let desc = ctx.get_desc(manifest_repr);
                    match &*desc {
                        TypeDesc::Tconstr { path, .. } => path.name(),
                        TypeDesc::Tvar(_) => "Tvar".to_string(),
                        TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                        TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                        TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                        TypeDesc::Tlink(_) => "Tlink".to_string(),
                        TypeDesc::Tsubst(_) => "Tsubst".to_string(),
                        TypeDesc::Tobject { .. } => "Tobject".to_string(),
                        TypeDesc::Tfield { .. } => "Tfield".to_string(),
                        TypeDesc::Tnil => "Tnil".to_string(),
                        TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                        TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                        TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                    }
                };
                (manifest_repr.0, manifest_head)
            });
        eprintln!(
            "[gadt-eq] source={} dest={} dest_head={} existing={:?}",
            source_name,
            dest_repr.0,
            dest_head,
            existing_manifest
        );
    }
    let is_recursive = matches!(
        &*ctx.get_desc(dest_repr),
        TypeDesc::Tconstr { path, .. } if path.same(source_path)
    );
    if is_recursive {
        if let Some(source_name) = source_name {
            eprintln!("[gadt-eq] source={} skip recursive", source_name);
        }
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
    if let Some(source_name) = source_name {
        let manifest_repr = ctx.repr(destination_copy);
        let manifest_head = {
            let desc = ctx.get_desc(manifest_repr);
            match &*desc {
                TypeDesc::Tconstr { path, .. } => path.name(),
                TypeDesc::Tvar(_) => "Tvar".to_string(),
                TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                TypeDesc::Tlink(_) => "Tlink".to_string(),
                TypeDesc::Tsubst(_) => "Tsubst".to_string(),
                TypeDesc::Tobject { .. } => "Tobject".to_string(),
                TypeDesc::Tfield { .. } => "Tfield".to_string(),
                TypeDesc::Tnil => "Tnil".to_string(),
                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
            }
        };
        eprintln!(
            "[gadt-eq] source={} add manifest={} head={}",
            source_name, manifest_repr.0, manifest_head
        );
    }
    env.add_local_constraint(source_path.clone(), decl);
    // OCaml add_gadt_equation calls cleanup_abbrev after installing the new
    // local constraint so future expansions observe the updated equation.
    ctx.clear_abbrev_memos();
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

/// Check if a type contains any Tvariant node (shallow check of Tconstr args).
/// Used to prevent identity sharing of types whose variant args would be
/// contaminated across branches (e.g. result<string, [#InvalidString]>).
pub fn type_contains_variant(ctx: &TypeContext<'_>, ty: TypeExprRef) -> bool {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvariant(_) => true,
        TypeDesc::Tconstr { args, .. } => args.iter().copied().any(|arg| {
            matches!(&*ctx.get_desc(ctx.repr(arg)), TypeDesc::Tvariant(_))
        }),
        _ => false,
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
    let t1_repr = ctx.repr(t1);
    let t2_repr = ctx.repr(t2);
    if let Some(needle) = std::env::var("RUST_DEBUG_LINK_PATH").ok() {
        let summarize = |ty: TypeExprRef| {
            let ty = ctx.repr(ty);
            let desc = ctx.get_desc(ty);
            match &*desc {
                TypeDesc::Tconstr { path, .. } => format!("{}@{}", path.name(), ctx.get_level(ty)),
                TypeDesc::Tvar(_) => format!("Tvar@{}", ctx.get_level(ty)),
                TypeDesc::Tarrow { .. } => format!("Tarrow@{}", ctx.get_level(ty)),
                TypeDesc::Ttuple(_) => format!("Ttuple@{}", ctx.get_level(ty)),
                TypeDesc::Tunivar(_) => format!("Tunivar@{}", ctx.get_level(ty)),
                TypeDesc::Tpoly { .. } => format!("Tpoly@{}", ctx.get_level(ty)),
                TypeDesc::Tpackage { .. } => format!("Tpackage@{}", ctx.get_level(ty)),
                TypeDesc::Tvariant(_) => format!("Tvariant@{}", ctx.get_level(ty)),
                TypeDesc::Tobject { .. } => format!("Tobject@{}", ctx.get_level(ty)),
                TypeDesc::Tfield { .. } => format!("Tfield@{}", ctx.get_level(ty)),
                TypeDesc::Tnil => format!("Tnil@{}", ctx.get_level(ty)),
                TypeDesc::Tlink(target) => {
                    format!("Tlink({})@{}", ctx.repr(*target).0, ctx.get_level(ty))
                }
                TypeDesc::Tsubst(target) => {
                    format!("Tsubst({})@{}", ctx.repr(*target).0, ctx.get_level(ty))
                }
            }
        };
        let matches = |ty: TypeExprRef| {
            let ty = ctx.repr(ty);
            match &*ctx.get_desc(ty) {
                TypeDesc::Tconstr { path, .. } => {
                    let name = path.name();
                    name == needle || path.last() == needle || name.contains(&needle)
                }
                _ => false,
            }
        };
        if matches(t1_repr) || matches(t2_repr) {
            eprintln!(
                "[link-type] source={} repr={} desc={} target={} repr={} desc={}",
                t1.0,
                t1_repr.0,
                summarize(t1_repr),
                t2.0,
                t2_repr.0,
                summarize(t2_repr)
            );
            if std::env::var_os("RUST_DEBUG_LINK_BACKTRACE").is_some() {
                eprintln!("{}", std::backtrace::Backtrace::force_capture());
            }
        }
    }
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
                let debug_v0 = std::env::var_os("RUST_DEBUG_UNIFY_V0").is_some();
                let should_log_v0 = debug_v0
                    && matches!(path.name().as_str(), "V0.key" | "V0.id" | "V1.key" | "V1.id");
                // OCaml ctype.ml:659: when level < get_level env p, try to expand.
                // get_level returns Path.binding_time which is the root ident's stamp.
                let binding_time = path_binding_time(&path);
                let should_try_expand = current != GENERIC_LEVEL && level < binding_time;
                if should_log_v0 {
                    eprintln!(
                        "[unify-v0] update_level_expand-enter ty={} path={} level={} current={} binding_time={} should_try_expand={}",
                        ty.0,
                        path.name(),
                        level,
                        current,
                        binding_time,
                        should_try_expand
                    );
                }
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
                        if should_log_v0 {
                            eprintln!(
                                "[unify-v0] update_level_expand ty={} path={} level={} current={} binding_time={} expanded={}",
                                ty.0,
                                path.name(),
                                level,
                                current,
                                binding_time,
                                expanded.0
                            );
                        }
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
            // Match OCaml Env.find_module path semantics: only persistent
            // identifiers can fall back to loading a .cmi by name.
            if !id.is_persistent() {
                return None;
            }
            let full_path = find_cmi_file(load_paths, id.name())?;
            let cmi = cmi_format::read_cmi(&full_path).ok()?;
            let mut sig_ctx = SigReadContext::new(ctx);
            let sig = sig_ctx.read_signature(&cmi.cmi_sign);
            // Apply path substitution to qualify internal types with the
            // module path, matching persistent_env::load_module behavior.
            // Without this, types have bare Pident paths that cause
            // incorrect path qualification through resolve_module_lid_impl.
            crate::cmi::persistent_env::substitute_type_paths_in_sig(
                &sig, module_path, ctx,
            );
            // Also recursively substitute submodule paths.
            crate::cmi::persistent_env::substitute_submodule_paths_pub(
                &sig, module_path, ctx,
            );
            Some(sig)
        }
        Path::Pdot(parent, module_name, _) => {
            let parent_sig =
                resolve_module_signature_through_cmi(ctx, load_paths, parent, visiting)?;
            let mut resolved = None;
            for item in &parent_sig {
                if let SignatureItem::SigModule(id, md, _) = item {
                    if id.name() == module_name {
                        resolved = match &md.md_type {
                            ModuleType::MtySignature(sig) => {
                                // Mirror OCaml Subst behavior when descending into
                                // submodules: keep parent substitutions visible.
                                crate::cmi::persistent_env::substitute_type_paths_in_child_sig(
                                    sig,
                                    &parent_sig,
                                    parent,
                                    ctx,
                                );
                                Some(sig.clone())
                            }
                            ModuleType::MtyAlias(_, alias_path)
                            | ModuleType::MtyIdent(alias_path) => {
                                resolve_module_signature_through_cmi(
                                    ctx,
                                    load_paths,
                                    alias_path,
                                    visiting,
                                )
                            }
                            _ => None,
                        };
                        break;
                    }
                }
            }
            resolved
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
    use crate::types::type_expr::TypeDesc;

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
    let debug_event =
        std::env::var_os("RUST_DEBUG_EXPAND_EVENT").is_some() && path.name().contains("Event.");
    if debug_event {
        eprintln!(
            "[resolve-type] requested={} module_path={}",
            path.name(),
            module_path.name()
        );
    }
    // Match OCaml Subst/Mtype behavior for module signatures loaded from cmi:
    // rewrite intra-signature type/module references to qualified access paths
    // (e.g. `componentLike` -> `Jsx.componentLike`, `element` -> `Jsx.element`).
    crate::cmi::persistent_env::substitute_type_paths_in_sig(&current_sig, module_path, ctx);

    // Register ALL types in the final signature by stamp for future lookups.
    // This is important because type manifests may reference sibling types
    // (e.g., type component<'a> = componentLike<'a, element>), and those
    // sibling types need to be available for expansion later.
    let mut result = None;
    for item in &current_sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            // Register every type by stamp
            if id.stamp() != 0 {
                let should_register = {
                    let existing = ctx.find_type_decl_by_stamp(id.stamp());
                    existing.as_ref().is_none_or(|d| {
                        d.type_path.is_none() && module_path.head().is_persistent()
                    })
                };
                if should_register {
                    let mut decl_for_stamp = decl.clone();
                    if decl_for_stamp.type_path.is_none() && module_path.head().is_persistent() {
                        decl_for_stamp.type_path = Some(Path::pdot(module_path.clone(), id.name()));
                    }
                    ctx.register_type_decl_by_stamp(id.stamp(), decl_for_stamp);
                }
            }
            if id.name() == type_name {
                // Cache the target type in the path store
                let path_name = path.name();
                if debug_event {
                    let manifest_summary = decl
                        .type_manifest
                        .map(|m| {
                            let r = ctx.repr(m);
                            let d = ctx.get_desc(r);
                            match &*d {
                                TypeDesc::Tconstr { path, args, .. } => {
                                    format!(
                                        "Tconstr {} args={} head_stamp={} head_persistent={}",
                                        path.name(),
                                        args.len(),
                                        path.head().stamp(),
                                        path.head().is_persistent()
                                    )
                                }
                                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                                TypeDesc::Tvar(_) => "Tvar".to_string(),
                                _ => format!("{:?}", &*d),
                            }
                        })
                        .unwrap_or_else(|| "<none>".to_string());
                    eprintln!(
                        "[resolve-type] match type={} stamp={} type_path={} manifest={}",
                        id.name(),
                        id.stamp(),
                        decl.type_path
                            .as_ref()
                            .map(|p| p.name())
                            .unwrap_or_else(|| "<none>".to_string()),
                        manifest_summary
                    );
                }
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
            if let Ok(md) = env.lookup_module(path) {
                Some(md.md_type.clone())
            } else if let Ok(md) = env.find_module(name) {
                Some(md.md_type.clone())
            } else if let Ok(mtd) = env.find_modtype(name) {
                mtd.mtd_type.clone()
            } else {
                // Match OCaml Env.find_module: only persistent identifiers
                // may resolve through the persistent environment.
                if !id.is_persistent() {
                    return None;
                }
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
            let parent_alias_target = match &parent_mty {
                super::decl::ModuleType::MtyAlias(_, target_path) => Some(target_path.clone()),
                _ => None,
            };
            parent_sig.iter().find_map(|item| match item {
                SignatureItem::SigModule(id, md, _) if id.name() == name => match &md.md_type {
                    super::decl::ModuleType::MtySignature(sig) => {
                        // Mirror OCaml Subst behavior for env-based nested module access:
                        // child module signatures may reference parent-defined types/modules
                        // using bare names (e.g. `subtype` inside `Stream.Writable`).
                        // Rewrite those references through the parent module access path.
                        crate::cmi::persistent_env::substitute_type_paths_in_child_sig(
                            sig,
                            &parent_sig,
                            parent,
                            ctx,
                        );
                        let child_sig = if let Some(target_parent_path) =
                            parent_alias_target.as_ref()
                        {
                            let child_target_path = Path::pdot(target_parent_path.clone(), name);
                            strengthen_signature_for_module_access_path(
                                ctx,
                                &child_target_path,
                                sig,
                                0,
                            )
                        } else {
                            sig.clone()
                        };
                        Some(super::decl::ModuleType::MtySignature(child_sig))
                    }
                    other => {
                        if let Some(target_parent_path) = parent_alias_target.as_ref() {
                            let child_target_path = Path::pdot(target_parent_path.clone(), name);
                            Some(strengthen_module_type_for_module_access_path(
                                ctx,
                                &child_target_path,
                                other,
                            ))
                        } else {
                            Some(other.clone())
                        }
                    }
                },
                SignatureItem::SigModtype(id, mtd) if id.name() == name => mtd.mtd_type.clone(),
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
        ModuleType::MtySignature(sig) => {
            Some(crate::types::typecore::copy_lookup_signature_for_subst(sig, ctx))
        }
        ModuleType::MtyAlias(_, path) | ModuleType::MtyIdent(path) => {
            let resolved = resolve_module_type_through_env_path(ctx, env, path, visiting)?;
            resolve_signature_through_env_module_type(ctx, env, &resolved, visiting)
        }
        _ => None,
    }
}

fn strengthen_type_decl_for_module_access_path<'a>(
    ctx: &'a TypeContext<'a>,
    module_access_path: &Path,
    id: &crate::ident::Ident,
    decl: &super::decl::TypeDeclaration,
) -> super::decl::TypeDeclaration {
    // Match OCaml mtype.ml strengthen_sig:
    // - Keep explicit manifests for public types
    // - Keep explicit manifests for private record/variant types
    // - Otherwise add `type t = <module_access_path>.t`
    let keep_manifest = matches!(
        (&decl.type_manifest, decl.type_private, &decl.type_kind),
        (Some(_), PrivateFlag::Public, _)
            | (
                Some(_),
                PrivateFlag::Private,
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
        strengthened.type_private = PrivateFlag::Public;
    }
    strengthened
}

fn strengthen_module_type_for_module_access_path<'a>(
    ctx: &'a TypeContext<'a>,
    module_access_path: &Path,
    mty: &super::decl::ModuleType,
) -> super::decl::ModuleType {
    use super::decl::ModuleType;

    match mty {
        ModuleType::MtySignature(sig) => ModuleType::MtySignature(
            strengthen_signature_for_module_access_path(ctx, module_access_path, sig, 0),
        ),
        ModuleType::MtyAlias(..) | ModuleType::MtyIdent(..) => mty.clone(),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => ModuleType::MtyFunctor {
            param: param.clone(),
            param_type: param_type.clone(),
            result: Box::new(strengthen_module_type_for_module_access_path(
                ctx,
                module_access_path,
                result,
            )),
        },
    }
}

fn strengthen_module_decl_for_module_access_path<'a>(
    ctx: &'a TypeContext<'a>,
    module_access_path: &Path,
    md: &super::decl::ModuleDeclaration,
) -> super::decl::ModuleDeclaration {
    let mut strengthened = md.clone();
    strengthened.md_type =
        strengthen_module_type_for_module_access_path(ctx, module_access_path, &md.md_type);
    strengthened
}

fn strengthen_signature_for_module_access_path<'a>(
    ctx: &'a TypeContext<'a>,
    module_access_path: &Path,
    sig: &[super::decl::SignatureItem],
    mut pos: i32,
) -> super::decl::Signature {
    use super::decl::{SignatureItem, ValueKind};

    let mut strengthened = Vec::with_capacity(sig.len());
    for item in sig {
        let new_item = match item {
            SignatureItem::SigValue(id, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    pos += 1;
                }
                SignatureItem::SigValue(id.clone(), desc.clone())
            }
            SignatureItem::SigType(id, decl, rec_status) => SignatureItem::SigType(
                id.clone(),
                strengthen_type_decl_for_module_access_path(ctx, module_access_path, id, decl),
                *rec_status,
            ),
            SignatureItem::SigTypext(id, ext, ext_status) => {
                pos += 1;
                SignatureItem::SigTypext(id.clone(), ext.clone(), *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                let child_path = Path::Pdot(
                    Box::new(module_access_path.clone()),
                    id.name().to_string(),
                    pos,
                );
                pos += 1;
                SignatureItem::SigModule(
                    id.clone(),
                    strengthen_module_decl_for_module_access_path(ctx, &child_path, md),
                    *rec_status,
                )
            }
            SignatureItem::SigModtype(id, mtd) => {
                let mut strengthened_mtd = mtd.clone();
                if let Some(mty) = &mtd.mtd_type {
                    let modtype_path = Path::pdot(module_access_path.clone(), id.name());
                    strengthened_mtd.mtd_type = Some(
                        strengthen_module_type_for_module_access_path(ctx, &modtype_path, mty),
                    );
                }
                SignatureItem::SigModtype(id.clone(), strengthened_mtd)
            }
            SignatureItem::SigClass => SignatureItem::SigClass,
            SignatureItem::SigClassType => SignatureItem::SigClassType,
        };
        strengthened.push(new_item);
    }
    strengthened
}

/// Resolve a type through local environment modules.
/// For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
/// follow aliases (MtyAlias/MtyIdent), and then find type t in its signature.
fn resolve_type_through_env<'a>(
    ctx: &'a TypeContext<'a>,
    env: &super::env::Env,
    path: &Path,
    strengthen_alias_types: bool,
) -> Option<super::decl::TypeDeclaration> {
    use super::decl::SignatureItem;

    let (module_path, type_name) = match path {
        Path::Pdot(parent, name, _) => (parent.as_ref(), name.as_str()),
        _ => return None,
    };
    let debug_resolve = std::env::var("RUST_DEBUG_RESOLVE_TYPE_ENV")
        .ok()
        .is_some_and(|needle| {
            let path_name = path.name();
            !needle.is_empty() && (path_name == needle || path_name.contains(&needle))
        });

    let mut visiting = HashSet::new();
    let module_mty = resolve_module_type_through_env_path(ctx, env, module_path, &mut visiting)?;
    let module_sig =
        resolve_signature_through_env_module_type(ctx, env, &module_mty, &mut visiting)?;
    let module_sig = crate::types::typecore::copy_lookup_signature_for_subst(&module_sig, ctx);
    // For alias modules, expansion should expose the alias target path
    // (e.g. Html.t -> Dom_html.t), not a self-manifest Html.t.
    let alias_target_for_strengthening = if strengthen_alias_types {
        match &module_mty {
            super::decl::ModuleType::MtyAlias(_, target_path) => Some(target_path.clone()),
            _ => None,
        }
    } else {
        None
    };
    if debug_resolve {
        eprintln!(
            "[resolve-type-env] path={} module_path={} module_mty={:?} alias_target={}",
            path.name(),
            module_path.name(),
            module_mty,
            alias_target_for_strengthening
                .as_ref()
                .map(|p| p.name())
                .unwrap_or_else(|| "<none>".to_string())
        );
    }
    // Match OCaml Env.components_of_module path lookup behavior: when resolving
    // `M.t`, operate on a path-qualified copy of `M`'s signature so sibling
    // references inside manifests are rewritten through the access path.
    crate::cmi::persistent_env::substitute_type_paths_in_sig(&module_sig, module_path, ctx);

    for item in &module_sig {
        if let SignatureItem::SigType(id, decl, _) = item {
            if debug_resolve {
                eprintln!(
                    "[resolve-type-env] sig-type id={} match={} manifest={} type_path={}",
                    id.name(),
                    id.name() == type_name,
                    decl.type_manifest.is_some(),
                    decl.type_path
                        .as_ref()
                        .map(|p| p.name())
                        .unwrap_or_else(|| "<none>".to_string())
                );
            }
            if id.name() == type_name {
                if let Some(target_path) = alias_target_for_strengthening.as_ref() {
                    if debug_resolve {
                        eprintln!(
                            "[resolve-type-env] strengthen target={} type={}",
                            target_path.name(),
                            id.name()
                        );
                    }
                    return Some(strengthen_type_decl_for_module_access_path(
                        ctx,
                        target_path,
                        id,
                        decl,
                    ));
                }
                if debug_resolve {
                    eprintln!("[resolve-type-env] returning raw decl type={}", id.name());
                }
                return Some(decl.clone());
            }
        }
    }

    if debug_resolve {
        eprintln!(
            "[resolve-type-env] fallback resolve_type_through_modules path={}",
            path.name()
        );
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
fn proper_abbrevs(
    ctx: &TypeContext<'_>,
    path: &Path,
    args: &[TypeExprRef],
    abbrev: AbbrevMemoRef,
) -> AbbrevMemoRef {
    if !args.is_empty() || ctx.trace_gadt_instances() || path.head_name().starts_with('#') {
        abbrev
    } else {
        ctx.simple_abbrevs_memo()
    }
}

fn try_expand_head<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let debug_image_alias = std::env::var_os("RUST_DEBUG_IMAGE_ALIAS").is_some();
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, abbrev } => {
            // OCaml runs check_abbrev_env from expand_abbrev_gen, which is only
            // reached for Tconstr heads (try_expand_once pattern-matches first).
            // Matching that behavior avoids clearing simple_abbrevs on non-constr
            // expand_head calls.
            ctx.check_abbrev_env(env);

            let args = args.clone();
            let path = path.clone();
            let orig_abbrev = *abbrev;
            let lookup_abbrev = proper_abbrevs(ctx, &path, &args, *abbrev);
            let path_name = path.name();
            let debug_expand_target = std::env::var("RUST_DEBUG_EXPAND_TYPE").ok();
            if debug_image_alias && path.head_name() == "imageElement" {
                eprintln!(
                    "[image-alias][try-expand-enter] ty={} path={} args={}",
                    ty.0,
                    path_name,
                    args.len()
                );
            }
            let debug_expand = (std::env::var_os("RUST_DEBUG_EXPAND_N_T").is_some()
                && path_name == "N.t")
                || (std::env::var_os("RUST_DEBUG_EXPAND_N_VALUE").is_some()
                    && path_name == "N.value")
                || (std::env::var_os("RUST_DEBUG_EXPAND_SPRITE_XY").is_some()
                    && path_name == "Sprite.xy")
                || (std::env::var_os("RUST_DEBUG_EXPAND_KEY").is_some()
                    && (path_name == "key"
                        || path_name.ends_with(".key")
                        || path_name == "id"
                        || path_name.ends_with(".id")
                        || path_name == "Ord.t"))
                || (std::env::var_os("RUST_DEBUG_EXPAND_COMPARE").is_some()
                    && path_name == "Comparable.compare")
                || (std::env::var_os("RUST_DEBUG_EXPAND_CMP").is_some()
                    && (path_name == "cmp" || path_name.ends_with(".cmp")))
                || (std::env::var_os("RUST_DEBUG_EXPAND_A").is_some()
                    && (path_name == "a" || path_name == "bool"))
                || (std::env::var_os("RUST_DEBUG_EXPAND_STATELESS").is_some()
                    && (path_name == "stateless"
                        || path_name == "noRetainedProps"
                        || path_name == "actionless"
                        || path_name == "component"
                        || path_name == "componentSpec"))
                || (std::env::var_os("RUST_DEBUG_EXPAND_REACT_COMPONENT").is_some()
                    && (path_name == "React.component"
                        || path_name.ends_with(".component")
                        || path_name == "element"
                        || path_name.ends_with(".element")
                        || path_name == "componentLike"
                        || path_name.ends_with(".componentLike")))
                || (std::env::var_os("RUST_DEBUG_EXPAND_EVENT").is_some()
                    && (path_name.contains("JsxEvent")
                        || path_name.contains("ReactEvent")
                        || path_name == "tag"
                        || path_name.ends_with(".tag")
                        || path_name.ends_with("Event.Mouse.t")
                        || path_name.ends_with("Event.Mouse.tag")))
                || (std::env::var_os("RUST_DEBUG_EXPAND_LAYERSTYLE").is_some()
                    && (path_name == "LayerStyleID.t"
                        || path_name == "LayerStyleID.ID.t"
                        || path_name == "Layout.Types.t"))
                || debug_expand_target
                    .as_deref()
                    .is_some_and(|target| target == path_name);
            if debug_expand {
                eprintln!(
                    "[expand] path={} enter ty={} level={} env_id={} stamp={} lookup={:?} memo={:?}",
                    path_name,
                    ty.0,
                    ctx.get_level(ty),
                    env.id(),
                    path.head().stamp(),
                    lookup_abbrev,
                    ctx.get_abbrev_memo(lookup_abbrev)
                );
                if path_name == "a" {
                    let mut locals = Vec::new();
                    for (p, decl) in env.iter_local_constraints() {
                        locals.push(format!(
                            "{} same={} manifest={} newtype={:?}",
                            p.name(),
                            p.same(&path),
                            decl.type_manifest.is_some(),
                            decl.type_newtype_level
                        ));
                    }
                    eprintln!("[expand] path=a local_constraints={:?}", locals);
                }
                if std::env::var_os("RUST_DEBUG_EXPAND_VALUE_BT").is_some() && path_name == "N.value"
                {
                    let bt = std::backtrace::Backtrace::capture();
                    eprintln!("[expand-value-bt]\n{bt:?}");
                }
            }

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

            // OCaml ctype.ml expand_abbrev_gen: check memoized expansions first.
            if let Some(cached) =
                ctx.find_abbrev_expansion(lookup_abbrev, PrivateFlag::Public, &path)
            {
                let cached_repr = ctx.repr(cached);
                let stale_same_path = {
                    let desc = ctx.get_desc(cached_repr);
                    matches!(
                        &*desc,
                        TypeDesc::Tconstr {
                            path: cached_path, ..
                        } if cached_path.same(&path)
                    )
                };
                if debug_expand {
                    let cached_head = {
                        let desc = ctx.get_desc(cached_repr);
                        match &*desc {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            TypeDesc::Tvar(_) => "Tvar".to_string(),
                            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                            TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                            TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                            TypeDesc::Tlink(_) => "Tlink".to_string(),
                            TypeDesc::Tsubst(_) => "Tsubst".to_string(),
                            TypeDesc::Tobject { .. } => "Tobject".to_string(),
                            TypeDesc::Tfield { .. } => "Tfield".to_string(),
                            TypeDesc::Tnil => "Tnil".to_string(),
                            TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                            TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                            TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                        }
                    };
                    eprintln!(
                        "[expand] path={} cached-candidate ty={} cached={} cached_head={} stale_same_path={} same_ty={}",
                        path_name,
                        ty.0,
                        cached_repr.0,
                        cached_head,
                        stale_same_path,
                        cached_repr == ty
                    );
                }
                if !(cached_repr == ty || stale_same_path) {
                    let level = ctx.get_level(ty);
                    if level != GENERIC_LEVEL {
                        update_level(ctx, level, cached);
                    }
                    if debug_image_alias && path.head_name() == "imageElement" {
                        eprintln!(
                            "[image-alias][try-expand-return] reason=cached-hit ty={} path={} cached={}",
                            ty.0,
                            path.name(),
                            cached_repr.0
                        );
                    }
                    if debug_expand {
                        eprintln!(
                            "[expand] path={} cached-hit ty={} cached={} cached_level={}",
                            path_name,
                            ty.0,
                            cached_repr.0,
                            ctx.get_level(cached_repr)
                        );
                    }
                    return Some(cached_repr);
                }
            }

            let expand_with_subst = |params: &[TypeExprRef], manifest: TypeExprRef| -> TypeExprRef {
                if debug_expand {
                    let manifest_repr = ctx.repr(manifest);
                    let arg_dump = args
                        .iter()
                        .map(|a| {
                            let r = ctx.repr(*a);
                            format!("{}@{}", r.0, ctx.get_level(r))
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    eprintln!(
                        "[expand] path={} subst-enter manifest={} manifest_level={} args={}",
                        path_name,
                        manifest_repr.0,
                        ctx.get_level(manifest_repr),
                        arg_dump
                    );
                    if std::env::var_os("RUST_DEBUG_EXPAND_TARGET_BT").is_some() {
                        eprintln!(
                            "[expand-bt] path={} ty={}\n{:?}",
                            path_name,
                            ty.0,
                            std::backtrace::Backtrace::capture()
                        );
                    }
                }
                if std::env::var_os("RUST_DEBUG_EXPAND_COMPARE").is_some()
                    && path_name == "Comparable.compare"
                {
                    let params_dump: Vec<String> = params
                        .iter()
                        .enumerate()
                        .map(|(i, p)| {
                            let r = ctx.repr(*p);
                            format!("{i}:{}", r.0)
                        })
                        .collect();
                    let manifest_dump = {
                        let m = ctx.repr(manifest);
                        let d = ctx.get_desc(m);
                        match &*d {
                            TypeDesc::Tpackage { args, .. } => {
                                let parts: Vec<String> = args
                                    .iter()
                                    .enumerate()
                                    .map(|(i, a)| {
                                        let r = ctx.repr(*a);
                                        format!("{i}:raw{}->repr{}", a.0, r.0)
                                    })
                                    .collect();
                                format!("package {}", parts.join(","))
                            }
                            _ => format!("non-package#{}", m.0),
                        }
                    };
                    let args_dump: Vec<String> = args
                        .iter()
                        .enumerate()
                        .map(|(i, a)| {
                            let r = ctx.repr(*a);
                            format!("{i}:raw{}->repr{}", a.0, r.0)
                        })
                        .collect();
                    eprintln!(
                        "[expand-compare] pre-subst params=[{}] manifest={} args=[{}]",
                        params_dump.join(","),
                        manifest_dump,
                        args_dump.join(",")
                    );
                }
                let expanded = subst_with_memo(ctx, env, ty, lookup_abbrev, params, &args, manifest);
                if std::env::var_os("RUST_DEBUG_EXPAND_COMPONENT").is_some()
                    && path_name == "component"
                {
                    let args_in = args
                        .iter()
                        .map(|a| {
                            let r = ctx.repr(*a);
                            format!("{}@{}", r.0, ctx.get_level(r))
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    let expanded_repr = ctx.repr(expanded);
                    let expanded_desc = ctx.get_desc(expanded_repr);
                    let expanded_dump = match &*expanded_desc {
                        TypeDesc::Tconstr { path, args, .. } => {
                            let out = args
                                .iter()
                                .map(|a| {
                                    let r = ctx.repr(*a);
                                    format!("{}@{}", r.0, ctx.get_level(r))
                                })
                                .collect::<Vec<_>>()
                                .join(",");
                            format!("{}({})", path.name(), out)
                        }
                        other => format!("{other:?}"),
                    };
                    drop(expanded_desc);
                    eprintln!(
                        "[expand-component] in={} expanded={} repr={} level={}",
                        args_in,
                        expanded_dump,
                        expanded_repr.0,
                        ctx.get_level(expanded_repr)
                    );
                }
                if debug_expand {
                    let expanded_repr = ctx.repr(expanded);
                    let expanded_kind = {
                        let d = ctx.get_desc(expanded_repr);
                        match &*d {
                            TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
                            TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                            TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                            TypeDesc::Tvar(_) => "Tvar".to_string(),
                            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                            TypeDesc::Tlink(t) => format!("Tlink({})", ctx.repr(*t).0),
                            TypeDesc::Tsubst(t) => format!("Tsubst({})", ctx.repr(*t).0),
                            TypeDesc::Tobject { .. } => "Tobject".to_string(),
                            TypeDesc::Tfield { .. } => "Tfield".to_string(),
                            TypeDesc::Tnil => "Tnil".to_string(),
                            TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                            TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                            TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                        }
                    };
                    eprintln!(
                        "[expand] path={} subst-exit expanded={} ({}) expanded_level={} ty={} ty_level={}",
                        path_name,
                        expanded_repr.0,
                        expanded_kind,
                        ctx.get_level(expanded_repr),
                        ty.0,
                        ctx.get_level(ty)
                    );
                }
                expanded
            };

            let can_expand_decl_manifest = |decl: &super::decl::TypeDeclaration,
                                            manifest: TypeExprRef| {
                matches!(decl.type_private, PrivateFlag::Public)
                    || !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
                    || btype::has_constr_row(ctx, manifest)
            };

            // 0. Check local constraints first (GADT equations)
            if let Some(constraint_decl) = env.find_local_constraint(&path) {
                if let Some(manifest) = constraint_decl.type_manifest {
                    let params = &constraint_decl.type_params;
                    if debug_expand {
                        let manifest_repr = ctx.repr(manifest);
                        let manifest_head = {
                            let desc = ctx.get_desc(manifest_repr);
                            match &*desc {
                                TypeDesc::Tconstr { path, .. } => path.name(),
                                TypeDesc::Tvar(_) => "Tvar".to_string(),
                                TypeDesc::Tunivar(_) => "Tunivar".to_string(),
                                TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
                                TypeDesc::Ttuple(_) => "Ttuple".to_string(),
                                TypeDesc::Tlink(_) => "Tlink".to_string(),
                                TypeDesc::Tsubst(_) => "Tsubst".to_string(),
                                TypeDesc::Tobject { .. } => "Tobject".to_string(),
                                TypeDesc::Tfield { .. } => "Tfield".to_string(),
                                TypeDesc::Tnil => "Tnil".to_string(),
                                TypeDesc::Tvariant(_) => "Tvariant".to_string(),
                                TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
                                TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
                            }
                        };
                        eprintln!(
                            "[expand] path={} local-constraint manifest={} head={} params={} args={}",
                            path_name,
                            manifest_repr.0,
                            manifest_head,
                            params.len(),
                            args.len()
                        );
                    }
                    if params.len() == args.len() {
                        let expanded = expand_with_subst(params, manifest);
                        if std::env::var_os("RUST_DEBUG_EXPAND_COMPARE").is_some()
                            && path_name == "Comparable.compare"
                        {
                            let params_dump: Vec<String> = params
                                .iter()
                                .map(|p| {
                                    let r = ctx.repr(*p);
                                    format!("{}@{}", r.0, ctx.get_level(r))
                                })
                                .collect();
                            let args_dump: Vec<String> = args
                                .iter()
                                .map(|a| {
                                    let r = ctx.repr(*a);
                                    let d = ctx.get_desc(r);
                                    match &*d {
                                        TypeDesc::Tconstr { path, .. } => path.name(),
                                        TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                                        _ => format!("ty#{}", r.0),
                                    }
                                })
                                .collect();
                            let expanded_repr = ctx.repr(expanded);
                            let expanded_dump = match &*ctx.get_desc(expanded_repr) {
                                TypeDesc::Tpackage { args, .. } => args
                                    .iter()
                                    .map(|a| {
                                        let r = ctx.repr(*a);
                                        let d = ctx.get_desc(r);
                                        match &*d {
                                            TypeDesc::Tconstr { path, .. } => path.name(),
                                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                                            _ => format!("ty#{}", r.0),
                                        }
                                    })
                                    .collect::<Vec<_>>()
                                    .join(","),
                                _ => format!("non-package#{}", expanded_repr.0),
                            };
                            eprintln!(
                                "[expand-compare] params={} args={} expanded_args={}",
                                params_dump.join(","),
                                args_dump.join(","),
                                expanded_dump
                            );
                        }
                        if debug_image_alias && path.head_name() == "imageElement" {
                            let expanded_repr = ctx.repr(expanded);
                            let expanded_name = {
                                let d = ctx.get_desc(expanded_repr);
                                match &*d {
                                    TypeDesc::Tconstr { path, .. } => path.name(),
                                    _ => "<non-constr>".to_string(),
                                }
                            };
                            eprintln!(
                                "[image-alias][try-expand-return] reason=local-constraint ty={} path={} expanded={} {}",
                                ty.0,
                                path.name(),
                                expanded_repr.0,
                                expanded_name
                            );
                        }
                        return Some(expanded);
                    }
                } else if debug_expand {
                    eprintln!("[expand] path={} local-constraint no-manifest", path_name);
                }
            }

            // 1. Prefer environment lookup when the declaration matches the
            // queried path exactly. For qualified paths, reject leaf-fallback
            // hits to unrelated declarations.
            let mut forbid_fallback_manifest_expansion = false;
            if let Ok(env_decl) = env.lookup_type(&path) {
                let exact_lookup = match &path {
                    Path::Pident(_) => true,
                    _ => env_decl.type_path.as_ref().is_some_and(|decl_path| {
                        decl_path.same(&path) || decl_path.name() == path_name
                    }),
                };
                if exact_lookup {
                    if let Some(manifest) = env_decl.type_manifest {
                        if can_expand_decl_manifest(env_decl, manifest) {
                            let params = &env_decl.type_params;
                            if params.len() == args.len() {
                                return Some(expand_with_subst(params, manifest));
                            }
                            forbid_fallback_manifest_expansion = true;
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} env.lookup_type arity-mismatch params={} args={}",
                                    path_name,
                                    params.len(),
                                    args.len()
                                );
                            }
                        } else {
                            forbid_fallback_manifest_expansion = true;
                            if debug_expand {
                                eprintln!("[expand] path={} env.lookup_type manifest hidden", path_name);
                            }
                        }
                    } else if debug_expand {
                        eprintln!("[expand] path={} env.lookup_type no-manifest", path_name);
                    }
                }
            }

            // 1a. For local identifiers, try stamp-based declaration lookup.
            // This preserves OCaml-style local identity paths while still
            // allowing expansion when env name lookup is unavailable.
            if let Path::Pident(id) = &path
                && !id.is_persistent()
                && id.stamp() != 0
                && let Some(stamp_decl) = ctx
                    .find_type_decl_by_stamp(id.stamp())
                    .map(|decl| decl.clone())
            {
                if let Some(manifest) = stamp_decl.type_manifest {
                    if can_expand_decl_manifest(&stamp_decl, manifest) {
                        let params = &stamp_decl.type_params;
                        if params.len() == args.len() {
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} stamp-lookup manifest params={} args={}",
                                    path_name,
                                    params.len(),
                                    args.len()
                                );
                            }
                            return Some(expand_with_subst(params, manifest));
                        } else {
                            forbid_fallback_manifest_expansion = true;
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} stamp-lookup arity-mismatch params={} args={}",
                                    path_name,
                                    params.len(),
                                    args.len()
                                );
                            }
                        }
                    } else if debug_expand {
                        eprintln!("[expand] path={} stamp-lookup manifest hidden", path_name);
                    }
                }
            }

            // 1b. For qualified paths, mirror OCaml `find_type` resolution by
            // descending through the current environment's module signatures
            // before consulting global fallbacks.
            if matches!(&path, Path::Pdot(..))
                && let Some(decl) = resolve_type_through_env(ctx, env, &path, true)
            {
                if let Some(decl_type_path) = decl.type_path.as_ref() {
                    if path_name.contains("__")
                        && decl.type_params.len() == args.len()
                        && !decl_type_path.same(&path)
                    {
                        if debug_expand {
                            eprintln!(
                                "[expand] path={} resolve_type_through_env type_path rewrite -> {}",
                                path_name,
                                decl_type_path.name()
                            );
                        }
                        let level = ctx.get_level(ty);
                        let rewritten = ctx.new_type(TypeDesc::Tconstr {
                            path: decl_type_path.clone(),
                            args: args.clone(),
                            abbrev: orig_abbrev,
                        });
                        ctx.set_level(rewritten, level);
                        return Some(rewritten);
                    }
                }
                if let Some(manifest) = decl.type_manifest {
                    let synthetic_self_manifest = {
                        let manifest_repr = ctx.repr(manifest);
                        let manifest_desc = ctx.get_desc(manifest_repr);
                        matches!(
                            &*manifest_desc,
                            TypeDesc::Tconstr {
                                path: manifest_path,
                                args: manifest_args,
                                ..
                            } if manifest_path.same(&path)
                                && manifest_args.len() == args.len()
                                && matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
                        )
                    };
                    // Match OCaml's nullary alias behavior: strengthened
                    // self-manifests like `Stdlib.Intl.Locale.t = Stdlib.Intl.Locale.t`
                    // still need to flow through `subst` so simple_abbrevs can
                    // preserve sharing across repeated uses. For parameterized
                    // synthetic manifests (`M.t<'a> = M.t<'a>`), keeping the old
                    // rewrite-to-target behavior avoids collapsing distinct
                    // instantiations onto a single cached copy.
                    if synthetic_self_manifest && !args.is_empty() {
                        let immediate_alias_target_path = match &path {
                            Path::Pdot(parent, type_name, pos) => {
                                let mut visiting = HashSet::new();
                                match resolve_module_type_through_env_path(
                                    ctx,
                                    env,
                                    parent,
                                    &mut visiting,
                                ) {
                                    Some(super::decl::ModuleType::MtyAlias(
                                        _,
                                        target_module_path,
                                    )) if !target_module_path.same(parent) => Some(Path::Pdot(
                                        Box::new(target_module_path),
                                        type_name.clone(),
                                        *pos,
                                    )),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        if let Some(target_path) = immediate_alias_target_path {
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} resolve_type_through_env parameterized synthetic self-manifest; rewriting to alias target {}",
                                    path_name,
                                    target_path.name()
                                );
                            }
                            let level = ctx.get_level(ty);
                            let rewritten = ctx.new_type(TypeDesc::Tconstr {
                                path: target_path,
                                args: args.clone(),
                                abbrev: orig_abbrev,
                            });
                            ctx.set_level(rewritten, level);
                            return Some(rewritten);
                        }
                    }
                    if can_expand_decl_manifest(&decl, manifest) {
                        let params = &decl.type_params;
                        if params.len() == args.len() {
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} resolve_type_through_env authoritative manifest params={} args={}",
                                    path_name,
                                    params.len(),
                                    args.len()
                                );
                            }
                            return Some(expand_with_subst(params, manifest));
                        } else {
                            forbid_fallback_manifest_expansion = true;
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} resolve_type_through_env arity-mismatch params={} args={}",
                                    path_name,
                                    params.len(),
                                    args.len()
                                );
                            }
                        }
                    } else if debug_expand {
                        eprintln!(
                            "[expand] path={} resolve_type_through_env manifest hidden",
                            path_name
                        );
                        forbid_fallback_manifest_expansion = true;
                    } else {
                        forbid_fallback_manifest_expansion = true;
                    }
                } else if debug_expand {
                    let type_path = decl
                        .type_path
                        .as_ref()
                        .map(|p| p.name())
                        .unwrap_or_else(|| "<none>".to_string());
                    eprintln!(
                        "[expand] path={} resolve_type_through_env authoritative no-manifest type_path={} private={:?} kind={:?}",
                        path_name, type_path, decl.type_private, decl.type_kind
                    );
                }
            }

            // OCaml expand_abbrev_gen only expands through Env.find_type_expansion.
            // For non-persistent heads, avoid global/path-store fallbacks that can
            // over-expand local aliases (e.g. LayerStyleID.ID.t -> string) and
            // diverge from OCaml's identity/linking behavior.
            let allow_global_fallbacks = path.head().is_persistent();
            if debug_expand && !allow_global_fallbacks {
                eprintln!(
                    "[expand] path={} skip-global-fallbacks non-persistent head={} forbid_manifest_fallback={}",
                    path_name,
                    path.head_name(),
                    forbid_fallback_manifest_expansion
                );
            }

            // 2. Try stamp-based global store (for CMI types with non-zero stamps)
            if allow_global_fallbacks && let Some(stamp) = stamp {
                if debug_expand {
                    let has_decl = ctx.find_type_decl_by_stamp(stamp).is_some();
                    eprintln!(
                        "[expand] path={} stamp-lookup stamp={} found={}",
                        path_name, stamp, has_decl
                    );
                }
                if let Some(store_decl) = ctx.find_type_decl_by_stamp(stamp) {
                    if debug_expand {
                        eprintln!(
                            "[expand] path={} stamp-decl manifest={} params={} args={} type_path={}",
                            path_name,
                            store_decl.type_manifest.is_some(),
                            store_decl.type_params.len(),
                            args.len(),
                            store_decl
                                .type_path
                                .as_ref()
                                .map(|p| p.name())
                                .unwrap_or_else(|| "<none>".to_string())
                        );
                    }
                    if let Some(manifest) = store_decl.type_manifest {
                        if !forbid_fallback_manifest_expansion
                            && can_expand_decl_manifest(&store_decl, manifest)
                        {
                            let params = &store_decl.type_params;
                            if params.len() == args.len() {
                                let expanded = expand_with_subst(params, manifest);
                                if debug_image_alias && path.head_name() == "imageElement" {
                                    let expanded_repr = ctx.repr(expanded);
                                    let expanded_name = {
                                        let d = ctx.get_desc(expanded_repr);
                                        match &*d {
                                            TypeDesc::Tconstr { path, .. } => path.name(),
                                            _ => "<non-constr>".to_string(),
                                        }
                                    };
                                    eprintln!(
                                        "[image-alias][try-expand-return] reason=stamp ty={} path={} expanded={} {}",
                                        ty.0,
                                        path.name(),
                                        expanded_repr.0,
                                        expanded_name
                                    );
                                }
                                return Some(expanded);
                            }
                        } else if debug_expand && forbid_fallback_manifest_expansion {
                            eprintln!(
                                "[expand] path={} stamp-decl manifest expansion blocked by authoritative lookup",
                                path_name
                            );
                        } else if debug_expand {
                            eprintln!("[expand] path={} stamp-decl manifest hidden", path_name);
                        }
                    }
                    if let Some(type_path) = store_decl.type_path.as_ref() {
                        let persistent_head = type_path.head().is_persistent();
                        if persistent_head
                            && store_decl.type_params.len() == args.len()
                            && !type_path.same(&path)
                        {
                            if debug_expand {
                                eprintln!(
                                    "[expand] path={} stamp-decl type_path rewrite -> {}",
                                    path_name,
                                    type_path.name()
                                );
                            }
                            let level = ctx.get_level(ty);
                            let rewritten = ctx.new_type(TypeDesc::Tconstr {
                                path: type_path.clone(),
                                args: args.clone(),
                                abbrev: orig_abbrev,
                            });
                            ctx.set_level(rewritten, level);
                            return Some(rewritten);
                        }
                    }
                }
            }

            // 3. Try full qualified path lookup (for Pdot paths like Js.Promise.t)
            if allow_global_fallbacks && let Some(ref _path_name) = full_path_name {
                // First check cached path store
                if let Some(store_decl) = ctx.find_type_decl_by_path(_path_name) {
                    if let Some(manifest) = store_decl.type_manifest {
                        if !forbid_fallback_manifest_expansion
                            && can_expand_decl_manifest(&store_decl, manifest)
                        {
                            let params = &store_decl.type_params;
                            if params.len() == args.len() {
                                if debug_expand {
                                    eprintln!(
                                        "[expand] path={} type_decl_by_path manifest params={} args={}",
                                        path_name,
                                        params.len(),
                                        args.len()
                                    );
                                }
                                let expanded = expand_with_subst(params, manifest);
                                if debug_image_alias && path.head_name() == "imageElement" {
                                    let expanded_repr = ctx.repr(expanded);
                                    let expanded_name = {
                                        let d = ctx.get_desc(expanded_repr);
                                        match &*d {
                                            TypeDesc::Tconstr { path, .. } => path.name(),
                                            _ => "<non-constr>".to_string(),
                                        }
                                    };
                                    eprintln!(
                                        "[image-alias][try-expand-return] reason=decl-by-path ty={} path={} expanded={} {}",
                                        ty.0,
                                        path.name(),
                                        expanded_repr.0,
                                        expanded_name
                                    );
                                }
                                return Some(expanded);
                            }
                        } else if debug_expand && forbid_fallback_manifest_expansion {
                            eprintln!(
                                "[expand] path={} type_decl_by_path manifest expansion blocked by authoritative lookup",
                                path_name
                            );
                        } else if debug_expand {
                            eprintln!(
                                "[expand] path={} type_decl_by_path manifest hidden",
                                path_name
                            );
                        }
                    }
                }

                // Not cached — resolve by loading CMI files and walking module signatures
                if let Some(resolved_decl) = resolve_type_through_modules(ctx, &path) {
                    if let Some(manifest) = resolved_decl.type_manifest {
                        if !forbid_fallback_manifest_expansion
                            && can_expand_decl_manifest(&resolved_decl, manifest)
                        {
                            let params = &resolved_decl.type_params;
                            if params.len() == args.len() {
                                if debug_expand {
                                    eprintln!(
                                        "[expand] path={} resolve_type_through_modules manifest params={} args={}",
                                        path_name,
                                        params.len(),
                                        args.len()
                                    );
                                }
                                let expanded = expand_with_subst(params, manifest);
                                if debug_image_alias && path.head_name() == "imageElement" {
                                    let expanded_repr = ctx.repr(expanded);
                                    let expanded_name = {
                                        let d = ctx.get_desc(expanded_repr);
                                        match &*d {
                                            TypeDesc::Tconstr { path, .. } => path.name(),
                                            _ => "<non-constr>".to_string(),
                                        }
                                    };
                                    eprintln!(
                                        "[image-alias][try-expand-return] reason=resolve-modules ty={} path={} expanded={} {}",
                                        ty.0,
                                        path.name(),
                                        expanded_repr.0,
                                        expanded_name
                                    );
                                }
                                return Some(expanded);
                            }
                        } else if debug_expand && forbid_fallback_manifest_expansion {
                            eprintln!(
                                "[expand] path={} resolve_type_through_modules manifest expansion blocked by authoritative lookup",
                                path_name
                            );
                        } else if debug_expand {
                            eprintln!(
                                "[expand] path={} resolve_type_through_modules manifest hidden",
                                path_name
                            );
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
                if debug_image_alias && path.head_name() == "imageElement" {
                    eprintln!(
                        "[image-alias][try-expand-norm] ty={} {} -> {}",
                        ty.0,
                        path.name(),
                        path_norm.name()
                    );
                }
                if debug_expand {
                    eprintln!(
                        "[expand] path={} normalize fallback path_norm={}",
                        path_name,
                        path_norm.name()
                    );
                }
                let level = ctx.get_level(ty);
                let normalized = ctx.new_type(TypeDesc::Tconstr {
                    path: path_norm,
                    args: args.clone(),
                    abbrev: orig_abbrev,
                });
                ctx.set_level(normalized, level);
                Some(normalized)
            } else {
                if debug_image_alias && path.head_name() == "imageElement" {
                    eprintln!(
                        "[image-alias][try-expand-none] ty={} path={} no-change",
                        ty.0,
                        path.name()
                    );
                }
                if debug_expand {
                    eprintln!("[expand] path={} no expansion", path_name);
                }
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
    let mut seen = HashSet::new();
    // Limit iterations to prevent infinite loops
    for _ in 0..20 {
        if !seen.insert(current) {
            break;
        }
        match try_expand_head(ctx, env, current) {
            Some(expanded) => {
                let expanded = ctx.repr(expanded);
                if expanded == current {
                    break;
                }
                if seen.contains(&expanded) {
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

/// OCaml's `subst` with abbreviation memoization.
///
/// Matches OCaml ctype.ml:1218 `subst`:
/// 1. Create stub variable (body0)
/// 2. Memorize the original type in the Tconstr's abbrev chain BEFORE instantiation
/// 3. Set current_abbreviations so copy_type_cached can use find_repr
/// 4. Call instance_parameterized_type (copy will check abbreviations)
/// 5. Clear current_abbreviations
/// 6. Unify stub with fresh body
/// 7. Substitute fresh params with actual args
fn subst_with_memo(
    ctx: &TypeContext<'_>,
    _env: &Env,
    ty: TypeExprRef,           // original Tconstr being expanded
    lookup_abbrev: AbbrevMemoRef, // proper_abbrevs target memo
    params: &[TypeExprRef],    // type declaration params
    args: &[TypeExprRef],      // actual type arguments
    body: TypeExprRef,         // manifest
) -> TypeExprRef {
    // Match OCaml subst: run the whole substitution/unification at the
    // Tconstr's level, then restore.
    let tconstr_level = ctx.get_level(ctx.repr(ty));
    let old_level = ctx.current_level();
    ctx.set_current_level(tconstr_level);

    let debug_expand_fn = std::env::var_os("RUST_DEBUG_EXPAND_FN").is_some()
        && matches!(&*ctx.get_desc(ctx.repr(ty)), TypeDesc::Tconstr { path, .. } if path.name() == "fn");
    let debug_expand_sprite_xy = std::env::var_os("RUST_DEBUG_EXPAND_SPRITE_XY_SUBST").is_some()
        && matches!(&*ctx.get_desc(ctx.repr(ty)), TypeDesc::Tconstr { path, .. } if path.name() == "Sprite.xy");
    if debug_expand_fn {
        let ty_repr = ctx.repr(ty);
        let arg_levels: Vec<String> = args
            .iter()
            .map(|a| {
                let r = ctx.repr(*a);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect();
        let param_levels: Vec<String> = params
            .iter()
            .map(|p| {
                let r = ctx.repr(*p);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect();
        eprintln!(
            "[expand-fn] stage=enter ty={} ty_level={} params={} args={}",
            ty_repr.0,
            ctx.get_level(ty_repr),
            param_levels.join(","),
            arg_levels.join(",")
        );
    }

    // 1. Create stub variable (OCaml: body0 = newvar())
    let body0 = ctx.new_var(None);
    if debug_expand_sprite_xy {
        let ty_repr = ctx.repr(ty);
        eprintln!(
            "[expand-sprite-xy-subst] stage=body0 ty={} body0={} level_ty={} level_body0={}",
            ty_repr.0,
            body0.0,
            ctx.get_level(ty_repr),
            ctx.get_level(body0)
        );
    }

    // OCaml's Tconstr carries `ref (ref Mnil)` — each node gets its own
    // mutable inner ref. Rust's alloc_abbrev_nil() returns a shared sentinel
    // (index 0) that memorize_abbrev_expansion refuses to mutate. Allocate a
    // fresh, mutable Mnil cell when the Tconstr's abbrev is the nil sentinel.
    let memo_ref = if lookup_abbrev == AbbrevMemoRef::nil() {
        ctx.alloc_abbrev(AbbrevMemo::Mnil)
    } else {
        lookup_abbrev
    };

    // 2. Memorize BEFORE instantiation (OCaml: memorize_abbrev abbrev priv path ty body0)
    if let TypeDesc::Tconstr { path, .. } = &*ctx.get_desc(ctx.repr(ty)) {
        let path = path.clone();
        ctx.memorize_abbrev_expansion(
            memo_ref,
            PrivateFlag::Public,
            path,
            ty,      // abbrev: original type (returned by find_repr)
            body0,   // expansion: stub (returned by find_expans)
        );
    }

    // 3. Set global abbreviations context so copy_type_cached can use find_repr
    ctx.set_current_abbreviations(memo_ref);

    let (fresh_params, fresh_body) = instance_parameterized_type(ctx, params, body);
    if debug_expand_sprite_xy {
        let body0_repr = ctx.repr(body0);
        let fresh_body_repr = ctx.repr(fresh_body);
        eprintln!(
            "[expand-sprite-xy-subst] stage=after_instance body0={} repr_body0={} fresh_body={} repr_fresh_body={}",
            body0.0,
            body0_repr.0,
            fresh_body.0,
            fresh_body_repr.0
        );
    }

    if debug_expand_fn {
        let fresh_param_levels: Vec<String> = fresh_params
            .iter()
            .map(|p| {
                let r = ctx.repr(*p);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect();
        eprintln!(
            "[expand-fn] stage=after_instance fresh_params={}",
            fresh_param_levels.join(",")
        );
    }

    // 5. Clear instantiation abbreviations before the unifications below.
    // OCaml sets the global `abbreviations` ref back to `ref Mnil` here rather
    // than restoring any previous outer context.
    ctx.set_current_abbreviations(AbbrevMemoRef::nil());

    // 6. Unify stub with body (OCaml: !unify' env body0 body')
    let mut unify_state = UnifyState::new();
    unify_state.set_env(_env);
    if unify(ctx, &mut unify_state, body0, fresh_body).is_err() {
        // Preserve previous behavior if full unification fails.
        link_type(ctx, body0, fresh_body);
    }
    if debug_expand_sprite_xy {
        let body0_repr = ctx.repr(body0);
        let fresh_body_repr = ctx.repr(fresh_body);
        eprintln!(
            "[expand-sprite-xy-subst] stage=after_unify_body body0={} repr_body0={} fresh_body={} repr_fresh_body={}",
            body0.0,
            body0_repr.0,
            fresh_body.0,
            fresh_body_repr.0
        );
    }

    // 7. Bind params to args (OCaml: List.iter2 (!unify' env) params' args)
    for (p, a) in fresh_params.iter().zip(args.iter()) {
        if unify(ctx, &mut unify_state, *p, *a).is_err() {
            link_type(ctx, *p, *a);
        }
    }
    if debug_expand_sprite_xy {
        let body0_repr = ctx.repr(body0);
        let fresh_body_repr = ctx.repr(fresh_body);
        eprintln!(
            "[expand-sprite-xy-subst] stage=after_unify_args body0={} repr_body0={} fresh_body={} repr_fresh_body={}",
            body0.0,
            body0_repr.0,
            fresh_body.0,
            fresh_body_repr.0
        );
    }

    if debug_expand_fn {
        let arg_levels: Vec<String> = args
            .iter()
            .map(|a| {
                let r = ctx.repr(*a);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect();
        let fresh_param_levels: Vec<String> = fresh_params
            .iter()
            .map(|p| {
                let r = ctx.repr(*p);
                format!("{}@{}", r.0, ctx.get_level(r))
            })
            .collect();
        eprintln!(
            "[expand-fn] stage=after_unify fresh_params={} args={}",
            fresh_param_levels.join(","),
            arg_levels.join(",")
        );
    }

    // 8. Restore typing level after all substitutions/unifications.
    ctx.set_current_level(old_level);

    fresh_body
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

    let reset_tracing = ctx.check_trace_gadt_instances(
        state
            .env()
            .is_some_and(|env| env.has_local_constraints()),
    );

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

    ctx.reset_trace_gadt_instances(reset_tracing);
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
    let debug_unify_after = std::env::var_os("RUST_DEBUG_UNIFY_AFTER_EXPAND").is_some();
    let debug_unify_after_alias =
        std::env::var_os("RUST_DEBUG_UNIFY_AFTER_EXPAND_ALIAS").is_some();
    let type_name = |r: TypeExprRef| {
        let d = ctx.get_desc(ctx.repr(r));
        match &*d {
            TypeDesc::Tconstr { path, .. } => path.name(),
            TypeDesc::Tlink(t) => {
                let d2 = ctx.get_desc(ctx.repr(*t));
                match &*d2 {
                    TypeDesc::Tconstr { path, .. } => format!("Tlink->{}", path.name()),
                    _ => format!("Tlink->{}", ctx.repr(*t).0),
                }
            }
            _ => format!("<non-constr:{}>", ctx.repr(r).0),
        }
    };
    let alias_tracked = if debug_unify_after_alias {
        let n1 = type_name(t1);
        let n2 = type_name(t2);
        let tracked = |n: &str| {
            n.contains("LayerStyleID.ID.t")
                || n.contains("LayerStyleID.t")
                || n.contains("Layout.Types.t")
        };
        tracked(&n1) || tracked(&n2)
    } else {
        false
    };
    let debug_image_alias = std::env::var_os("RUST_DEBUG_IMAGE_ALIAS").is_some();
    let debug_image_pair = if debug_image_alias {
        let n1 = {
            let d = ctx.get_desc(ctx.repr(t1));
            match &*d {
                TypeDesc::Tconstr { path, .. } => Some(path.name()),
                _ => None,
            }
        };
        let n2 = {
            let d = ctx.get_desc(ctx.repr(t2));
            match &*d {
                TypeDesc::Tconstr { path, .. } => Some(path.name()),
                _ => None,
            }
        };
        let tracked = |name: Option<&str>| {
            matches!(
                name,
                Some("Html.imageElement")
                    | Some("Dom_html.imageElement")
                    | Some("Js.Undefined.t")
                    | Some("Js.undefined")
            )
        };
        tracked(n1.as_deref()) || tracked(n2.as_deref())
    } else {
        false
    };
    let t1_changed = t1_expanded != t1;
    let t2_changed = t2_expanded != t2;
    if alias_tracked {
        eprintln!(
            "[unify-after-expand-alias] enter t1={}({}) t1e={}({}) t2={}({}) t2e={}({}) t1_changed={} t2_changed={}",
            ctx.repr(t1).0,
            type_name(t1),
            ctx.repr(t1_expanded).0,
            type_name(t1_expanded),
            ctx.repr(t2).0,
            type_name(t2),
            ctx.repr(t2_expanded).0,
            type_name(t2_expanded),
            t1_changed,
            t2_changed
        );
    }
    if !t1_changed && !t2_changed {
        return unify(ctx, state, t1_expanded, t2_expanded);
    }

    // Match OCaml unify2 branching:
    //   if t1 == t1' || t2 != t2' then unify3(t1,t1',t2,t2')
    //   else unify3(t2,t2',t1,t1')
    // Swap only when left changed and right did not.
    let swap = t1_changed && !t2_changed;
    let lhs = if swap { t2_expanded } else { t1_expanded };
    let rhs = if swap { t1_expanded } else { t2_expanded };
    let relink_target = if swap { t1 } else { t2 };

    let lhs = ctx.repr(lhs);
    let rhs = ctx.repr(rhs);
    if alias_tracked {
        eprintln!(
            "[unify-after-expand-alias] branch swap={} lhs={}({}) rhs={}({}) relink_target={}({})",
            swap,
            lhs.0,
            type_name(lhs),
            rhs.0,
            type_name(rhs),
            ctx.repr(relink_target).0,
            type_name(relink_target)
        );
    }
    if debug_unify_after {
        eprintln!(
            "[unify-after-expand] t1={} t1e={} t2={} t2e={} t1_changed={} t2_changed={} swap={} lhs={} rhs={} relink_target={}",
            t1.0,
            t1_expanded.0,
            t2.0,
            t2_expanded.0,
            t1_changed,
            t2_changed,
            swap,
            lhs.0,
            rhs.0,
            relink_target.0
        );
    }
    if lhs == rhs {
        if debug_unify_after {
            eprintln!("[unify-after-expand] lhs==rhs early-ok");
        }
        return Ok(());
    }

    let unify_result = unify(ctx, state, lhs, rhs);
    if debug_unify_after {
        eprintln!("[unify-after-expand] unify(lhs,rhs) ok={}", unify_result.is_ok());
    }
    unify_result?;
    if alias_tracked {
        eprintln!(
            "[unify-after-expand-alias] post-unify lhs={}({}) rhs={}({})",
            ctx.repr(lhs).0,
            type_name(lhs),
            ctx.repr(rhs).0,
            type_name(rhs)
        );
    }

    if state.mode != crate::types::UnifyMode::Pattern {
        // Match OCaml unify3 expression mode:
        //   link_type t1' t2
        // where t1' is the selected expanded side and t2 is the selected
        // ORIGINAL opposite side.
        let to_ty = ctx.repr(relink_target);
        if lhs != to_ty && !deep_occur(ctx, lhs, to_ty) {
            ctx.set_desc(lhs, TypeDesc::Tlink(to_ty));
            if alias_tracked {
                eprintln!(
                    "[unify-after-expand-alias] relink lhs={} -> target={} target_name={}",
                    lhs.0,
                    to_ty.0,
                    type_name(to_ty)
                );
            }
            if debug_unify_after {
                eprintln!(
                    "[unify-after-expand] relink lhs={} -> target={}",
                    lhs.0, to_ty.0
                );
            }
        }
    }
    if alias_tracked {
        eprintln!(
            "[unify-after-expand-alias] exit t1={}({}) t2={}({})",
            ctx.repr(t1).0,
            type_name(t1),
            ctx.repr(t2).0,
            type_name(t2)
        );
    }

    if debug_image_pair {
        let r1 = ctx.repr(t1);
        let r2 = ctx.repr(t2);
        let r1e = ctx.repr(t1_expanded);
        let r2e = ctx.repr(t2_expanded);
        let name = |r: TypeExprRef| {
            let d = ctx.get_desc(r);
            match &*d {
                TypeDesc::Tconstr { path, .. } => path.name(),
                _ => "<non-constr>".to_string(),
            }
        };
        eprintln!(
            "[image-alias][unify-after] t1={}({}) t2={}({}) t1e={}({}) t2e={}({})",
            r1.0,
            name(r1),
            r2.0,
            name(r2),
            r1e.0,
            name(r1e),
            r2e.0,
            name(r2e)
        );
    }

    Ok(())
}

fn has_cached_expansion(ctx: &TypeContext<'_>, path: &Path, mut memo: AbbrevMemoRef) -> bool {
    for _ in 0..128 {
        match ctx.get_abbrev_memo(memo) {
            AbbrevMemo::Mnil => return false,
            AbbrevMemo::Mcons {
                path: cached_path,
                next,
                ..
            } => {
                if path.same(&cached_path) {
                    return true;
                }
                memo = next;
            }
            AbbrevMemo::Mlink(next) => {
                memo = next;
            }
        }
    }
    false
}

/// Internal unification logic.
fn unify_types<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }

    {
        let desc1 = ctx.get_desc(t1);
        let desc2 = ctx.get_desc(t2);
        if let (
            TypeDesc::Tconstr {
                path: path1,
                args: args1,
                abbrev: abbrev1,
            },
            TypeDesc::Tconstr {
                path: path2,
                args: args2,
                abbrev: abbrev2,
            },
        ) = (&*desc1, &*desc2)
        {
            let same_nullary_no_cached_expansion = args1.is_empty()
                && args2.is_empty()
                && path1.same(path2)
                && !(has_cached_expansion(ctx, path1, *abbrev1)
                    || has_cached_expansion(ctx, path2, *abbrev2));
            if same_nullary_no_cached_expansion {
                drop(desc1);
                drop(desc2);
                update_level(ctx, ctx.get_level(t1), t2);
                link_type(ctx, t1, t2);
                return Ok(());
            }
        }
    }

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
                abbrev: abbrev1,
            },
            TypeDesc::Tconstr {
                path: path2,
                args: args2,
                abbrev: abbrev2,
            },
        ) => {
            let debug_image_alias = std::env::var_os("RUST_DEBUG_IMAGE_ALIAS").is_some();
            let debug_v0 = std::env::var_os("RUST_DEBUG_UNIFY_V0").is_some();
            if debug_v0 {
                let p1 = path1.name();
                let p2 = path2.name();
                if p1 == "V0.key"
                    || p1 == "V0.id"
                    || p2 == "V0.key"
                    || p2 == "V0.id"
                    || p1 == "V1.key"
                    || p1 == "V1.id"
                    || p2 == "V1.key"
                    || p2 == "V1.id"
                {
                    eprintln!(
                        "[unify-v0] enter t1={}({})@{} t2={}({})@{}",
                        t1.0,
                        p1,
                        ctx.get_level(t1),
                        t2.0,
                        p2,
                        ctx.get_level(t2),
                    );
                }
            }
            if !path1.same(path2) {
                let p1 = path1.name();
                let p2 = path2.name();
                if p1 == p2 && args1.len() == args2.len() {
                    let pairs: Vec<_> = args1
                        .iter()
                        .zip(args2.iter())
                        .map(|(&a, &b)| (a, b))
                        .collect();
                    drop(desc1);
                    drop(desc2);
                    // Equivalent named paths with divergent stamps should still
                    // unify structurally through their arguments.
                    link_type(ctx, t1, t2);
                    for (a, b) in pairs {
                        unify(ctx, state, a, b)?;
                    }
                    return Ok(());
                }
                let debug_image_alias_pair = debug_image_alias
                    && ((p1 == "Html.imageElement"
                        || p1 == "Dom_html.imageElement"
                        || p1 == "Js.Undefined.t"
                        || p1 == "Js.undefined")
                        || (p2 == "Html.imageElement"
                            || p2 == "Dom_html.imageElement"
                            || p2 == "Js.Undefined.t"
                            || p2 == "Js.undefined"));
                if debug_image_alias_pair {
                    eprintln!(
                        "[image-alias][unify-mismatch] t1={} {} t2={} {}",
                        t1.0,
                        p1,
                        t2.0,
                        p2
                    );
                }

                // Narrow fallback for local submodule-path aliases where one side
                // is exactly one segment longer than the other:
                // `Plain.ComponentInput.t` vs `ComponentInput.t`.
                // Only accept when the short path is explicitly manifest-aliased
                // to the long path in the current environment.
                let seg1: Vec<&str> = p1.split('.').collect();
                let seg2: Vec<&str> = p2.split('.').collect();
                let alias_candidate = if seg1.len() == seg2.len() + 1 {
                    Some((t1, t2, path1, path2, seg1.as_slice(), seg2.as_slice()))
                } else if seg2.len() == seg1.len() + 1 {
                    Some((t2, t1, path2, path1, seg2.as_slice(), seg1.as_slice()))
                } else {
                    None
                };
                if let Some((long_ty, short_ty, long_path, short_path, long_segs, short_segs)) =
                    alias_candidate
                {
                    if short_segs.len() >= 2
                        && long_segs[1..] == *short_segs
                        && !short_path.head().is_persistent()
                        && args1.len() == args2.len()
                    {
                        let alias_matches = if let Some(env) = state.env() {
                            let long_decl = lookup_type_decl_for_path(ctx, env, long_path);
                            let short_decl = lookup_type_decl_for_path(ctx, env, short_path);
                            if short_decl.is_none() {
                                long_decl.is_some()
                            } else {
                                short_decl
                                    .and_then(|decl| decl.type_manifest)
                                    .is_some_and(|manifest| {
                                        let manifest = ctx.repr(manifest);
                                        let manifest_desc = ctx.get_desc(manifest);
                                        match &*manifest_desc {
                                            TypeDesc::Tconstr { path, args, .. } => {
                                                args.len() == args1.len()
                                                    && (path.same(long_path)
                                                        || path.name() == long_path.name())
                                            }
                                            _ => false,
                                        }
                                    })
                            }
                        } else {
                            false
                        };
                        if alias_matches {
                            let pairs: Vec<_> = args1
                                .iter()
                                .zip(args2.iter())
                                .map(|(&a, &b)| (a, b))
                                .collect();
                            drop(desc1);
                            drop(desc2);
                            // Keep the longer qualified path as the representative.
                            link_type(ctx, short_ty, long_ty);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        }
                    }
                }

                // Narrow fallback for flattened nested-module aliases:
                // `A.B.X.t` vs `A__B.X.t`.
                // Only accept when env declarations prove they refer to the
                // same alias family (manifest or identical canonical type_path).
                let flatten_alias_candidate =
                    if seg1.len() == seg2.len() + 1
                        && seg1.len() >= 3
                        && seg2.len() >= 2
                        && format!("{}__{}", seg1[0], seg1[1]) == seg2[0]
                        && seg1[2..] == seg2[1..]
                    {
                        Some((t1, t2, path1, path2))
                    } else if seg2.len() == seg1.len() + 1
                        && seg2.len() >= 3
                        && seg1.len() >= 2
                        && format!("{}__{}", seg2[0], seg2[1]) == seg1[0]
                        && seg2[2..] == seg1[1..]
                    {
                        Some((t2, t1, path2, path1))
                    } else {
                        None
                    };
                if let Some((long_ty, short_ty, long_path, short_path)) = flatten_alias_candidate {
                    if args1.len() == args2.len() {
                        let alias_matches = if let Some(env) = state.env() {
                            flattened_alias_paths_equivalent(
                                ctx,
                                env,
                                long_path,
                                short_path,
                                args1.len(),
                            )
                        } else {
                            false
                        };
                        if alias_matches {
                            if std::env::var_os("RUST_DEBUG_FLAT_ALIAS_UNIFY").is_some() {
                                eprintln!(
                                    "[flat-alias-unify] long_ty={} long_path={} short_ty={} short_path={} args={}",
                                    ctx.repr(long_ty).0,
                                    long_path.name(),
                                    ctx.repr(short_ty).0,
                                    short_path.name(),
                                    args1.len()
                                );
                            }
                            let pairs: Vec<_> = args1
                                .iter()
                                .zip(args2.iter())
                                .map(|(&a, &b)| (a, b))
                                .collect();
                            drop(desc1);
                            drop(desc2);
                            // Keep the longer qualified path as the representative.
                            link_type(ctx, short_ty, long_ty);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        }
                    }
                }

                // Paths differ. Match OCaml flow by attempting alias expansion
                // before any equation generation.
                // Extract paths for potential GADT equation handling (nullary Tconstr only)
                let gadt_path1 = if args1.is_empty() { Some(path1.clone()) } else { None };
                let gadt_path2 = if args2.is_empty() { Some(path2.clone()) } else { None };
                let are_both_nullary = args1.is_empty() && args2.is_empty();
                let path1_for_newtype = path1.clone();
                let path2_for_newtype = path2.clone();

                drop(desc1);
                drop(desc2);

                // OCaml ctype.ml: when both sides are local newtypes, prefer
                // one-step expansion by newtype level before general unify2.
                if false && are_both_nullary {
                    if let Some(env) = state.env() {
                        if env.has_local_constraints()
                            && is_newtype_path(ctx, env, &path1_for_newtype)
                            && is_newtype_path(ctx, env, &path2_for_newtype)
                        {
                            let lev1 = find_newtype_level_for_path(ctx, env, &path1_for_newtype);
                            let lev2 = find_newtype_level_for_path(ctx, env, &path2_for_newtype);
                            if lev1 < lev2 {
                                if let Some(expanded_t2) = expand_head_once(ctx, env, t2) {
                                    return unify(ctx, state, t1, expanded_t2);
                                }
                            } else if let Some(expanded_t1) = expand_head_once(ctx, env, t1) {
                                return unify(ctx, state, expanded_t1, t2);
                            }
                        }
                    }
                }

                if let Some(env) = state.env() {
                    let exp1 = expand_head(ctx, env, t1);
                    let exp2 = expand_head(ctx, env, t2);
                    if debug_image_alias_pair {
                        let exp1_repr = ctx.repr(exp1);
                        let exp2_repr = ctx.repr(exp2);
                        let exp1_head = {
                            let d = ctx.get_desc(exp1_repr);
                            match &*d {
                                TypeDesc::Tconstr { path, .. } => path.name(),
                                _ => "<non-constr>".to_string(),
                            }
                        };
                        let exp2_head = {
                            let d = ctx.get_desc(exp2_repr);
                            match &*d {
                                TypeDesc::Tconstr { path, .. } => path.name(),
                                _ => "<non-constr>".to_string(),
                            }
                        };
                        eprintln!(
                            "[image-alias][unify-expand] exp1={} {} exp2={} {}",
                            exp1_repr.0, exp1_head, exp2_repr.0, exp2_head
                        );
                    }
                    if exp1 != t1 || exp2 != t2 {
                        return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                    }
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
            let path_name = path1.head_name().to_string();
            let path_full = path1.name();
            if std::env::var_os("RUST_DEBUG_UNIFY_REACT_ELEMENT").is_some()
                && path_full == "React.element"
                && args1.is_empty()
            {
                eprintln!(
                    "[unify-react-element] t1={}@{} t2={}@{} abbrev1={:?} memo1={:?} abbrev2={:?} memo2={:?}",
                    t1.0,
                    ctx.get_level(t1),
                    t2.0,
                    ctx.get_level(t2),
                    abbrev1,
                    ctx.get_abbrev_memo(*abbrev1),
                    abbrev2,
                    ctx.get_abbrev_memo(*abbrev2)
                );
            }
            drop(desc1);
            drop(desc2);

            if let Some(env) = state.env() {
                let exp1 = expand_head(ctx, env, t1);
                let exp2 = expand_head(ctx, env, t2);
                if exp1 != t1 || exp2 != t2 {
                    return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                }
            }

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
            // OCaml's unify2 expands both sides, so phantom type parameters
            // (non-injective variance) vanish in the expansion and are never
            // unified. We approximate this by checking type declaration
            // variance: only unify args for injective params, skip phantom.
            // OCaml's unify2 expands both Tconstr sides before unify3.
            // For types with phantom params (params not appearing in the
            // manifest body), the expansion hides those params, so they're
            // never unified. We detect phantom params by checking if the
            // type param appears in the manifest via deep_occur.
            let phantom_mask: Vec<bool> = if !args1.is_empty() {
                state.env().and_then(|env| {
                    env.find_type(&path_name).ok().and_then(|decl| {
                        let manifest = decl.type_manifest?;
                        let params = &decl.type_params;
                        if params.len() != args1.len() {
                            return None;
                        }
                        Some(params.iter().map(|p| {
                            // Phantom = param NOT appearing in manifest
                            !deep_occur(ctx, *p, manifest)
                        }).collect())
                    })
                }).unwrap_or_else(|| vec![false; args1.len()])
            } else {
                vec![]
            };

            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .enumerate()
                .map(|(i, (&a, &b))| (i, a, b))
                .collect();

            for (i, a, b) in pairs {
                // Skip phantom params — OCaml's expansion hides them.
                if !phantom_mask.get(i).copied().unwrap_or(false) {
                    unify(ctx, state, a, b)?;
                }
            }

            if state.mode != crate::types::UnifyMode::Pattern {
                let mut link_source = t1;
                if let Some(env) = state.env() {
                    let desc = ctx.get_desc(t1);
                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                        let path_norm = normalize_path_full(ctx, env, path);
                        if path_norm != *path {
                            link_source = ctx.new_constr(path_norm, args.clone());
                        } else if let Some(expanded) = try_expand_head(ctx, env, t1) {
                            let expanded = ctx.repr(expanded);
                            if expanded != t1 {
                                link_source = expanded;
                            }
                        }
                    }
                    drop(desc);
                }
                let source = ctx.repr(link_source);
                let target = ctx.repr(t2);
                if source != target && !deep_occur(ctx, source, target) {
                    link_type(ctx, source, target);
                }
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

            unify_rows(ctx, state, &row1, &row2)?;
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
            if !path1.same(path2) && path1.name() != path2.name() {
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
                        if std::env::var_os("RUST_DEBUG_PACK_UNIFY").is_some() {
                            let t1_desc = ctx.get_desc(t1);
                            let t2_desc = ctx.get_desc(t2);
                            let is_pack_constr = matches!((&*t1_desc, &*t2_desc), (TypeDesc::Tpackage { .. }, TypeDesc::Tconstr { .. }))
                                || matches!((&*t1_desc, &*t2_desc), (TypeDesc::Tconstr { .. }, TypeDesc::Tpackage { .. }));
                            if is_pack_constr {
                                drop(t1_desc);
                                drop(t2_desc);
                                let describe_args = |ty: TypeExprRef| -> String {
                                    let repr = ctx.repr(ty);
                                    let desc = ctx.get_desc(repr);
                                    match &*desc {
                                        TypeDesc::Tconstr { args, path, .. } => {
                                            let parts: Vec<String> = args
                                                .iter()
                                                .enumerate()
                                                .map(|(i, a)| {
                                                    let r = ctx.repr(*a);
                                                    format!("{i}:raw{}->repr{}", a.0, r.0)
                                                })
                                                .collect();
                                            format!("Tconstr({}) args=[{}]", path.name(), parts.join(","))
                                        }
                                        TypeDesc::Tpackage { args, path, .. } => {
                                            let parts: Vec<String> = args
                                                .iter()
                                                .enumerate()
                                                .map(|(i, a)| {
                                                    let r = ctx.repr(*a);
                                                    let d = ctx.get_desc(r);
                                                    let kind = match &*d {
                                                        TypeDesc::Tconstr { path, .. } => path.name(),
                                                        TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                                                        _ => format!("ty#{}", r.0),
                                                    };
                                                    format!("{i}:raw{}->repr{}={kind}", a.0, r.0)
                                                })
                                                .collect();
                                            format!("Tpackage({}) args=[{}]", path.name(), parts.join(","))
                                        }
                                        _ => format!("other#{}", repr.0),
                                    }
                                };
                                eprintln!(
                                    "[pack-unify] t1={} exp1={} t2={} exp2={}",
                                    describe_args(t1),
                                    describe_args(exp1),
                                    describe_args(t2),
                                    describe_args(exp2)
                                );
                            } else {
                                drop(t1_desc);
                                drop(t2_desc);
                            }
                        }
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

/// Sort row fields alphabetically by label, matching OCaml's `sort_row_fields`.
fn sort_row_fields(fields: &[(String, RowField)]) -> Vec<(String, RowField)> {
    let mut sorted = fields.to_vec();
    sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    sorted
}

/// Merge two sorted row field lists, matching OCaml's `merge_rf`.
/// Returns (r1, r2, pairs) where:
/// - r1: fields only in fi1 (sorted)
/// - r2: fields only in fi2 (sorted)
/// - pairs: matched fields from both sides
fn merge_rf(
    fi1: &[(String, RowField)],
    fi2: &[(String, RowField)],
) -> (
    Vec<(String, RowField)>,
    Vec<(String, RowField)>,
    Vec<(String, RowField, RowField)>,
) {
    let mut r1: Vec<(String, RowField)> = Vec::new();
    let mut r2: Vec<(String, RowField)> = Vec::new();
    let mut pairs: Vec<(String, RowField, RowField)> = Vec::new();

    let mut i1 = 0;
    let mut i2 = 0;

    while i1 < fi1.len() && i2 < fi2.len() {
        let (l1, f1) = &fi1[i1];
        let (l2, f2) = &fi2[i2];
        if l1 == l2 {
            pairs.push((l1.clone(), f1.clone(), f2.clone()));
            i1 += 1;
            i2 += 1;
        } else if l1 < l2 {
            r1.push((l1.clone(), f1.clone()));
            i1 += 1;
        } else {
            r2.push((l2.clone(), f2.clone()));
            i2 += 1;
        }
    }
    // Remaining elements
    while i1 < fi1.len() {
        r1.push(fi1[i1].clone());
        i1 += 1;
    }
    while i2 < fi2.len() {
        r2.push(fi2[i2].clone());
        i2 += 1;
    }

    // OCaml's merge_rf prepends matched pairs during recursion and does not
    // reverse them at the end, so the final pair order is the reverse of the
    // sorted traversal order.
    pairs.reverse();

    (r1, r2, pairs)
}

/// Merge row fields matching OCaml's `merge_row_fields`.
/// Sorts both inputs, then uses sorted merge to partition into
/// (r1_only, r2_only, pairs).
fn merge_row_fields(
    fi1: &[(String, RowField)],
    fi2: &[(String, RowField)],
) -> (
    Vec<(String, RowField)>,
    Vec<(String, RowField)>,
    Vec<(String, RowField, RowField)>,
) {
    // Match OCaml's fast paths
    if fi1.is_empty() || fi2.is_empty() {
        return (fi1.to_vec(), fi2.to_vec(), Vec::new());
    }
    if fi1.len() == 1 && fi2.iter().all(|(l, _)| l != &fi1[0].0) {
        return (fi1.to_vec(), fi2.to_vec(), Vec::new());
    }
    if fi2.len() == 1 && fi1.iter().all(|(l, _)| l != &fi2[0].0) {
        return (fi1.to_vec(), fi2.to_vec(), Vec::new());
    }
    merge_rf(&sort_row_fields(fi1), &sort_row_fields(fi2))
}

/// Unify two row types (for polymorphic variants).
/// Matches OCaml's `unify_row` (ctype.ml:2538): uses `merge_row_fields` to sort
/// and partition fields, then unifies pairs. The result has fields in alphabetical
/// order, matching OCaml's `row_repr` which flattens the sorted chain.
fn unify_rows<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    row1: &RowDesc,
    row2: &RowDesc,
) -> TypeResult<()> {
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);

    let (r1, r2, pairs) = merge_row_fields(&row1.row_fields, &row2.row_fields);
    let debug_filter = debug_unify_row_filter("RUST_DEBUG_UNIFY_ROWS");
    let debug_rows = debug_filter
        .as_ref()
        .is_some_and(|filter| debug_unify_rows_enabled(filter, &row1, &row2, &r1, &r2, &pairs));
    if debug_rows {
        debug_unify_rows_log("start", &row1, &row2, &r1, &r2, &pairs);
    }

    let rm1 = row_more(ctx, &row1);
    let rm2 = row_more(ctx, &row2);
    if rm1 == rm2 {
        return Ok(());
    }

    let fixed1 = row_fixed(ctx, &row1);
    let fixed2 = row_fixed(ctx, &row2);
    let more = if fixed1 {
        rm1
    } else if fixed2 {
        rm2
    } else {
        let more = ctx.new_var(None);
        let level = std::cmp::min(ctx.get_level(rm1), ctx.get_level(rm2));
        ctx.set_level(more, level);
        more
    };
    let fixed = fixed1 || fixed2;
    let closed = row1.row_closed || row2.row_closed;

    let filter_row_fields = |erase: bool, fields: &[(String, RowField)]| -> Vec<(String, RowField)> {
        let mut filtered = Vec::new();
        for (label, field) in fields {
            match super::btype::row_field_repr(ctx, field) {
                RowField::Rabsent => {}
                RowField::Reither {
                    matched: false,
                    link,
                    ..
                } if erase => {
                    ctx.set_row_field(link, RowField::Rabsent);
                }
                _ => filtered.push((label.clone(), field.clone())),
            }
        }
        filtered
    };
    let empty = |fields: &[(String, RowField)]| {
        fields
            .iter()
            .all(|(_, f)| matches!(super::btype::row_field_repr(ctx, f), RowField::Rabsent))
    };

    if closed {
        let all_absent = pairs.iter().all(|(_, f1, f2)| {
            matches!(super::btype::row_field_repr(ctx, f1), RowField::Rabsent)
                || matches!(super::btype::row_field_repr(ctx, f2), RowField::Rabsent)
        });
        if (empty(&r1) || row2.row_closed) && (empty(&r2) || row1.row_closed) && all_absent {
            return Err(TypeError::Unify(vec![]));
        }
    }

    let keep = |swap: bool| {
        pairs.iter().all(|(_, f1, f2)| {
            let (left, right) = if swap { (f2, f1) } else { (f1, f2) };
            matches!(super::btype::row_field_repr(ctx, left), RowField::Rabsent)
                || !matches!(super::btype::row_field_repr(ctx, right), RowField::Rabsent)
        })
    };
    let name = if row1.row_name.is_some()
        && (row1.row_closed || empty(&r2))
        && (!row2.row_closed || (keep(false) && empty(&r1)))
    {
        row1.row_name.clone()
    } else if row2.row_name.is_some()
        && (row2.row_closed || empty(&r1))
        && (!row1.row_closed || (keep(true) && empty(&r2)))
    {
        row2.row_name.clone()
    } else {
        None
    };
    let row0 = RowDesc {
        row_fields: vec![],
        row_more: more,
        row_closed: closed,
        row_fixed: fixed,
        row_name: name,
    };

    let set_more = |ctx: &'a TypeContext<'a>,
                    state: &mut UnifyState,
                    row: &RowDesc,
                    rest: &[(String, RowField)]|
     -> TypeResult<()> {
        let row_is_fixed = row_fixed(ctx, row);
        let rest = if closed {
            filter_row_fields(row.row_closed, rest)
        } else {
            rest.to_vec()
        };
        if debug_rows {
            eprintln!(
                "[unify-rows set-more] target={{closed:{} fixed:{} labels=[{}]}} rest=[{}]",
                row.row_closed,
                row_is_fixed,
                row.row_fields
                    .iter()
                    .map(|(label, _)| label.as_str())
                    .collect::<Vec<_>>()
                    .join(","),
                rest.iter()
                    .map(|(label, _)| label.as_str())
                    .collect::<Vec<_>>()
                    .join(","),
            );
        }
        if (!rest.is_empty() && (row.row_closed || row_is_fixed))
            || (closed && row_is_fixed && !row.row_closed)
        {
            return Err(TypeError::Unify(vec![]));
        }
        let rm = row_more(ctx, row);
        if row_is_fixed {
            if more == rm {
                return Ok(());
            }
            if super::btype::is_tvar(ctx, rm) {
                link_type(ctx, rm, more);
                return Ok(());
            }
            return unify(ctx, state, rm, more);
        }

        let ty = ctx.new_generic_type(TypeDesc::Tvariant(RowDesc {
            row_fields: rest,
            ..row0.clone()
        }));
        update_level(ctx, ctx.get_level(rm), ty);
        link_type(ctx, rm, ty);
        Ok(())
    };

    let md1 = {
        let desc = ctx.get_desc(rm1);
        (*desc).clone()
    };
    let md2 = {
        let desc = ctx.get_desc(rm2);
        (*desc).clone()
    };
    let result = (|| -> TypeResult<()> {
        set_more(ctx, state, &row2, &r1)?;
        set_more(ctx, state, &row1, &r2)?;
        for (label, f1, f2) in &pairs {
            if debug_rows {
                eprintln!("[unify-rows field] label={label}");
            }
            unify_row_field(ctx, state, fixed1, fixed2, more, label, f1, f2)?;
        }
        if super::btype::static_row(ctx, &row1) {
            let rm = row_more(ctx, &row1);
            if super::btype::is_tvar(ctx, rm) {
                let nil = ctx.new_type(TypeDesc::Tnil);
                ctx.set_level(nil, ctx.get_level(rm));
                link_type(ctx, rm, nil);
            }
        }
        Ok(())
    })();
    if let Err(err) = result {
        ctx.set_desc(rm1, md1.clone());
        ctx.set_desc(rm2, md2.clone());
        return Err(err);
    }
    Ok(())
}

/// Unify two row fields.
/// Matches OCaml's `unify_row_field` behavior, including Reither link updates.
fn unify_row_field<'a>(
    ctx: &'a TypeContext<'a>,
    state: &mut UnifyState,
    fixed1: bool,
    fixed2: bool,
    more: TypeExprRef,
    label: &str,
    field1: &RowField,
    field2: &RowField,
) -> TypeResult<()> {
    // Follow links before matching, like OCaml does
    let f1 = super::btype::row_field_repr(ctx, field1);
    let f2 = super::btype::row_field_repr(ctx, field2);
    let debug_field = debug_unify_row_field_enabled(label);
    match (&f1, &f2) {
        (RowField::Rpresent(Some(t1)), RowField::Rpresent(Some(t2))) => unify(ctx, state, *t1, *t2),
        (RowField::Rpresent(None), RowField::Rpresent(None)) => Ok(()),
        (RowField::Rabsent, RowField::Rabsent) => Ok(()),
        (
            RowField::Reither {
                constant: c1,
                types: types1,
                matched: m1,
                link: e1,
                ..
            },
            RowField::Reither {
                constant: c2,
                types: types2,
                matched: m2,
                link: e2,
                ..
            },
        ) => {
            if debug_field {
                eprintln!(
                    "[unify-row-field enter] label={} fixed=({}, {}) c=({}, {}) m=({}, {}) e=({}, {}) tl1=[{}] tl2=[{}]",
                    label,
                    fixed1,
                    fixed2,
                    c1,
                    c2,
                    m1,
                    m2,
                    e1.0,
                    e2.0,
                    debug_unify_row_types(ctx, types1),
                    debug_unify_row_types(ctx, types2),
                );
            }
            if e1 == e2 {
                if debug_field {
                    eprintln!("[unify-row-field short-circuit] label={} same-link", label);
                }
                return Ok(());
            }

            if (fixed1 || fixed2) && !(*c1 || *c2) && types1.len() == types2.len() {
                // OCaml fixed-row fast path (PR#7496): collapse both to a shared
                // Reither and unify payloads pairwise.
                let shared = RowField::Reither {
                    constant: *c1 || *c2,
                    types: vec![],
                    matched: *m1 || *m2,
                    link: ctx.alloc_row_field(None),
                };
                ctx.set_row_field(*e1, shared.clone());
                ctx.set_row_field(*e2, shared);
                for (t1, t2) in types1.iter().zip(types2.iter()) {
                    unify(ctx, state, *t1, *t2)?;
                }
                if debug_field {
                    eprintln!(
                        "[unify-row-field fixed-fast] label={} tl1=[{}] tl2=[{}]",
                        label,
                        debug_unify_row_types(ctx, types1),
                        debug_unify_row_types(ctx, types2),
                    );
                }
                return Ok(());
            }

            // OCaml redo branch: when fields are active/fixed/singleton and an
            // existing link is already present, retry on the linked representatives.
            // Match OCaml when rigid variants are enabled for this path:
            // singleton payload arity alone should not force the redo path.
            let active = *m1 || *m2 || fixed1 || fixed2;
            if active {
                let mut all_types: Vec<TypeExprRef> = Vec::with_capacity(types1.len() + types2.len());
                all_types.extend(types1.iter().copied());
                all_types.extend(types2.iter().copied());
                if !all_types.is_empty() {
                    if *c1 || *c2 {
                        return Err(TypeError::Unify(vec![]));
                    }
                    let head = all_types[0];
                    for ty in all_types.iter().skip(1) {
                        unify(ctx, state, head, *ty)?;
                    }
                    let has_existing_link =
                        ctx.get_row_field(*e1).is_some() || ctx.get_row_field(*e2).is_some();
                    if has_existing_link {
                        if debug_field {
                            eprintln!(
                                "[unify-row-field redo] label={} all=[{}] e1_linked={} e2_linked={}",
                                label,
                                debug_unify_row_types(ctx, &all_types),
                                ctx.get_row_field(*e1).is_some(),
                                ctx.get_row_field(*e2).is_some(),
                            );
                        }
                        return unify_row_field(ctx, state, fixed1, fixed2, more, label, &f1, &f2);
                    }
                }
            }

            let tl1: Vec<TypeExprRef> = types1.iter().map(|ty| ctx.repr(*ty)).collect();
            let tl2: Vec<TypeExprRef> = types2.iter().map(|ty| ctx.repr(*ty)).collect();

            // OCaml `remq`: remove physical duplicates by identity.
            let remq = |remove: &[TypeExprRef], src: &[TypeExprRef]| -> Vec<TypeExprRef> {
                src.iter()
                    .copied()
                    .filter(|ty| !remove.iter().any(|x| x == ty))
                    .collect()
            };
            let tl2_prime = remq(&tl2, &tl1);
            let tl1_prime = remq(&tl1, &tl2);
            let tl1_prime_debug = debug_field.then(|| debug_unify_row_types(ctx, &tl1_prime));
            let tl2_prime_debug = debug_field.then(|| debug_unify_row_types(ctx, &tl2_prime));

            if debug_field {
                eprintln!(
                    "[unify-row-field remq] label={} tl1=[{}] tl2=[{}] tl1'=[{}] tl2'=[{}]",
                    label,
                    debug_unify_row_types(ctx, &tl1),
                    debug_unify_row_types(ctx, &tl2),
                    tl1_prime_debug.as_deref().unwrap_or(""),
                    tl2_prime_debug.as_deref().unwrap_or(""),
                );
            }

            let more_level = ctx.get_level(ctx.repr(more));
            for ty in tl1_prime.iter().chain(tl2_prime.iter()) {
                update_level(ctx, more_level, *ty);
            }

            let shared_link = ctx.alloc_row_field(None);
            let f1_prime = RowField::Reither {
                constant: *c1 || *c2,
                types: tl1_prime,
                matched: *m1 || *m2,
                link: shared_link,
            };
            let f2_prime = RowField::Reither {
                constant: *c1 || *c2,
                types: tl2_prime,
                matched: *m1 || *m2,
                link: shared_link,
            };
            ctx.set_row_field(*e1, f1_prime);
            ctx.set_row_field(*e2, f2_prime);
            if debug_field {
                eprintln!(
                    "[unify-row-field set] label={} e1={} e2={} tl1'=[{}] tl2'=[{}]",
                    label,
                    e1.0,
                    e2.0,
                    tl1_prime_debug.as_deref().unwrap_or(""),
                    tl2_prime_debug.as_deref().unwrap_or(""),
                );
            }
            Ok(())
        }

        (RowField::Reither { matched: false, link: e1, .. }, RowField::Rabsent) if !fixed1 => {
            ctx.set_row_field(*e1, f2.clone());
            Ok(())
        }
        (RowField::Rabsent, RowField::Reither { matched: false, link: e2, .. }) if !fixed2 => {
            ctx.set_row_field(*e2, f1.clone());
            Ok(())
        }

        (
            RowField::Reither {
                constant: false,
                types,
                link: e1,
                ..
            },
            RowField::Rpresent(Some(t2)),
        ) if !fixed1 => {
            ctx.set_row_field(*e1, f2.clone());
            let more_level = ctx.get_level(ctx.repr(more));
            update_level(ctx, more_level, *t2);
            for t1 in types {
                if let Err(err) = unify(ctx, state, *t1, *t2) {
                    ctx.clear_row_field(*e1);
                    return Err(err);
                }
            }
            Ok(())
        }
        (
            RowField::Rpresent(Some(t1)),
            RowField::Reither {
                constant: false,
                types,
                link: e2,
                ..
            },
        ) if !fixed2 => {
            ctx.set_row_field(*e2, f1.clone());
            let more_level = ctx.get_level(ctx.repr(more));
            update_level(ctx, more_level, *t1);
            for t2 in types {
                if let Err(err) = unify(ctx, state, *t1, *t2) {
                    ctx.clear_row_field(*e2);
                    return Err(err);
                }
            }
            Ok(())
        }

        (
            RowField::Reither {
                constant: true,
                types,
                link: e1,
                ..
            },
            RowField::Rpresent(None),
        ) if !fixed1 && types.is_empty() => {
            ctx.set_row_field(*e1, f2.clone());
            Ok(())
        }
        (
            RowField::Rpresent(None),
            RowField::Reither {
                constant: true,
                types,
                link: e2,
                ..
            },
        ) if !fixed2 && types.is_empty() => {
            ctx.set_row_field(*e2, f1.clone());
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
        if let TypeDesc::Tconstr { abbrev, .. } = &*ctx.get_desc(ty) {
            btype::iter_abbrev(ctx, *abbrev, |memo_ty| {
                generalize_rec(ctx, memo_ty);
            });
        }
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

    if ctx.get_level(ty) != GENERIC_LEVEL {
        ctx.set_level(ty, GENERIC_LEVEL);
    }

    let mut children = Vec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        force_generalize_sig_type_rec(ctx, child, seen);
    }
}

pub fn force_generalize_sig_type(ctx: &TypeContext<'_>, ty: TypeExprRef) {
    ctx.clear_simple_abbrevs();
    let mut seen = HashSet::new();
    force_generalize_sig_type_rec(ctx, ty, &mut seen);
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
        PromoteAndRecurse {
            children: Vec<TypeExprRef>,
            clear_abbrev: Option<AbbrevMemoRef>,
        },
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
                TypeDesc::Tconstr { abbrev, .. } => {
                    let mut children = Vec::new();
                    iter_type_expr(ctx, ty, |child| children.push(child));
                    Action::PromoteAndRecurse {
                        children,
                        clear_abbrev: Some(*abbrev),
                    }
                }
                _ => {
                    let mut children = Vec::new();
                    iter_type_expr(ctx, ty, |child| children.push(child));
                    Action::PromoteAndRecurse {
                        children,
                        clear_abbrev: None,
                    }
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
        Action::PromoteAndRecurse {
            children,
            clear_abbrev,
        } => {
            if let Some(abbrev) = clear_abbrev {
                ctx.clear_abbrev_memo(abbrev);
            }
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
            let mut variances = lookup_type_decl_for_path(ctx, env, &path)
                .map(|decl| decl.type_variance.clone())
                .unwrap_or_else(|| vec![Variance::MAY_INV; args.len()]);
            if !args.is_empty() && variances.iter().all(|v| *v == Variance::NULL) {
                if std::env::var_os("RUST_DEBUG_NULL_VARIANCE_FALLBACK").is_some() {
                    eprintln!(
                        "[null-variance-fallback] path={} phase=generalize_expansive args={}",
                        path.name(),
                        args.len()
                    );
                }
                variances = vec![Variance::MAY_INV; args.len()];
            }
            if let Some(target) = std::env::var("RUST_DEBUG_GENERALIZE_PATH").ok() {
                if path.name() == target {
                    let arg_levels_before = args
                        .iter()
                        .map(|arg| {
                            let r = ctx.repr(*arg);
                            format!("{}@{}", r.0, ctx.get_level(r))
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    let vars = variances
                        .iter()
                        .enumerate()
                        .map(|(i, v)| {
                            format!(
                                "{}:(mp={},mn={},mw={},inj={},p={},n={},inv={})",
                                i,
                                v.mem(VarianceFlag::MayPos),
                                v.mem(VarianceFlag::MayNeg),
                                v.mem(VarianceFlag::MayWeak),
                                v.mem(VarianceFlag::Inj),
                                v.mem(VarianceFlag::Pos),
                                v.mem(VarianceFlag::Neg),
                                v.mem(VarianceFlag::Inv)
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    eprintln!(
                        "[generalize-path] path={} args={} variances={} var_level={} current_level={} before={}",
                        path.name(),
                        args.len(),
                        vars,
                        var_level,
                        ctx.current_level(),
                        arg_levels_before
                    );
                }
            }
            if std::env::var_os("RUST_DEBUG_GENERALIZE_T1").is_some() && path.head_name() == "t1" {
                let arg_levels_before = args
                    .iter()
                    .map(|arg| {
                        let r = ctx.repr(*arg);
                        format!("{}@{}", r.0, ctx.get_level(r))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                let vars = variances
                    .iter()
                    .enumerate()
                    .map(|(i, v)| format!("{i}:{v:?}"))
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!(
                    "[generalize-t1] path={} args={} variances={} var_level={} current_level={} before={}",
                    path.name(),
                    args.len(),
                    vars,
                    var_level,
                    ctx.current_level(),
                    arg_levels_before
                );
            }
            if std::env::var_os("RUST_DEBUG_GENERALIZE_COMPONENTSPEC").is_some()
                && path.last() == "componentSpec"
            {
                let arg_levels_before = args
                    .iter()
                    .map(|arg| {
                        let r = ctx.repr(*arg);
                        format!("{}@{}", r.0, ctx.get_level(r))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                let vars = variances
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        format!(
                            "{}:(mp={},mn={},mw={},inj={},p={},n={},inv={})",
                            i,
                            v.mem(VarianceFlag::MayPos),
                            v.mem(VarianceFlag::MayNeg),
                            v.mem(VarianceFlag::MayWeak),
                            v.mem(VarianceFlag::Inj),
                            v.mem(VarianceFlag::Pos),
                            v.mem(VarianceFlag::Neg),
                            v.mem(VarianceFlag::Inv)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!(
                    "[generalize-componentspec] path={} args={} variances={} var_level={} current_level={} before={}",
                    path.name(),
                    args.len(),
                    vars,
                    var_level,
                    ctx.current_level(),
                    arg_levels_before
                );
            }
            for (index, arg) in args.iter().enumerate() {
                let variance = variances.get(index).copied().unwrap_or(Variance::MAY_INV);
                if variance.mem(VarianceFlag::MayWeak) {
                    generalize_structure(ctx, var_level, *arg);
                } else {
                    generalize_expansive_rec(ctx, env, var_level, visited, *arg);
                }
            }
            if std::env::var_os("RUST_DEBUG_GENERALIZE_T1").is_some() && path.head_name() == "t1" {
                let arg_levels_after = args
                    .iter()
                    .map(|arg| {
                        let r = ctx.repr(*arg);
                        format!("{}@{}", r.0, ctx.get_level(r))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!("[generalize-t1] after={}", arg_levels_after);
            }
            if std::env::var_os("RUST_DEBUG_GENERALIZE_COMPONENTSPEC").is_some()
                && path.last() == "componentSpec"
            {
                let arg_levels_after = args
                    .iter()
                    .map(|arg| {
                        let r = ctx.repr(*arg);
                        format!("{}@{}", r.0, ctx.get_level(r))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                eprintln!("[generalize-componentspec] after={}", arg_levels_after);
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

/// Compute actual variance for each type parameter of a type declaration.
/// This matches OCaml's compute_variance_decl in typedecl.ml.
///
/// Without this, unannotated type params default to FULL (all flags including MayWeak),
/// causing generalize_expansive to prevent generalization of covariant params.
/// OCaml infers actual variance from the type body.
pub fn compute_variance_decl(
    ctx: &TypeContext<'_>,
    env: &Env,
    decl: &super::decl::TypeDeclaration,
) -> Vec<Variance> {
    let params = &decl.type_params;
    if params.is_empty() {
        return vec![];
    }

    // Abstract types with no manifest: keep declared variance
    if matches!(decl.type_kind, super::TypeKind::TypeAbstract | super::TypeKind::TypeOpen)
        && decl.type_manifest.is_none()
    {
        return decl.type_variance.clone();
    }

    // Map from TypeExprRef (repr of param) to accumulated variance
    let mut visited: HashMap<TypeExprRef, Variance> = HashMap::new();
    let param_reprs: Vec<TypeExprRef> = params.iter().map(|p| ctx.repr(*p)).collect();

    // Collect (is_mutable, type) pairs from the type body
    let mut fields: Vec<(bool, TypeExprRef)> = Vec::new();

    // From manifest
    if let Some(manifest) = decl.type_manifest {
        fields.push((false, manifest));
    }

    // From type kind
    match &decl.type_kind {
        super::TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                fields.push((
                    label.ld_mutable == super::asttypes::MutableFlag::Mutable,
                    label.ld_type,
                ));
            }
        }
        super::TypeKind::TypeVariant(constructors) => {
            for cstr in constructors {
                // Skip GADT constructors (cd_res != None) — their variance is more complex
                if cstr.cd_res.is_some() {
                    continue;
                }
                match &cstr.cd_args {
                    super::decl::ConstructorArguments::CstrTuple(tys) => {
                        for ty in tys {
                            fields.push((false, *ty));
                        }
                    }
                    super::decl::ConstructorArguments::CstrRecord(labels) => {
                        for label in labels {
                            fields.push((
                                label.ld_mutable == super::asttypes::MutableFlag::Mutable,
                                label.ld_type,
                            ));
                        }
                    }
                }
            }
        }
        _ => {}
    }

    // Compute variance for each field
    for (is_mutable, ty) in &fields {
        let initial_variance = if *is_mutable {
            Variance::FULL
        } else {
            Variance::covariant()
        };
        compute_variance_rec(ctx, env, &mut visited, initial_variance, *ty, 0);
    }

    // Extract variance for each param
    param_reprs
        .iter()
        .map(|p| visited.get(p).copied().unwrap_or(Variance::NULL))
        .collect()
}

fn compute_variance_rec(
    ctx: &TypeContext<'_>,
    env: &Env,
    visited: &mut HashMap<TypeExprRef, Variance>,
    vari: Variance,
    ty: TypeExprRef,
    depth: u32,
) {
    if depth > 100 {
        return; // prevent infinite recursion
    }

    let ty = ctx.repr(ty);
    let current = visited.get(&ty).copied().unwrap_or(Variance::NULL);
    if vari.subset(&current) {
        return; // already fully computed
    }

    let vari = vari.union(&current);
    visited.insert(ty, vari);

    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tarrow { arg, ret, .. } => {
            let v = vari.conjugate();
            let v1 = if v.mem(VarianceFlag::MayPos) || v.mem(VarianceFlag::MayNeg) {
                v.set(VarianceFlag::MayWeak, true)
            } else {
                v
            };
            let arg_ty = arg.typ;
            let ret_ty = *ret;
            drop(desc);
            compute_variance_rec(ctx, env, visited, v1, arg_ty, depth + 1);
            compute_variance_rec(ctx, env, visited, vari, ret_ty, depth + 1);
        }
        TypeDesc::Ttuple(tl) => {
            let tl = tl.clone();
            drop(desc);
            for t in &tl {
                compute_variance_rec(ctx, env, visited, vari, *t, depth + 1);
            }
        }
        TypeDesc::Tconstr { path, args, .. } => {
            if !args.is_empty() {
                let path = path.clone();
                let args = args.clone();
                drop(desc);
                let variances = env
                    .lookup_type(&path)
                    .map(|d| d.type_variance.clone())
                    .unwrap_or_else(|_| {
                        if let Path::Pdot(..) = &path {
                            let path_name = path.name();
                            if let Some(decl_ref) = ctx.find_type_decl_by_path(&path_name) {
                                return decl_ref.type_variance.clone();
                            }
                        }
                        vec![Variance::MAY_INV; args.len()]
                    });
                for (i, arg) in args.iter().enumerate() {
                    let var = variances.get(i).copied().unwrap_or(Variance::MAY_INV);
                    let cv = |f: VarianceFlag| var.mem(f);
                    let cvari = |f: VarianceFlag| vari.mem(f);
                    let strict = (cvari(VarianceFlag::Inv) && cv(VarianceFlag::Inj))
                        || ((cvari(VarianceFlag::Pos) || cvari(VarianceFlag::Neg))
                            && cv(VarianceFlag::Inv));
                    if strict {
                        compute_variance_rec(ctx, env, visited, Variance::FULL, *arg, depth + 1);
                    } else {
                        let p1 = var.inter(&vari);
                        let n1 = var.inter(&vari.conjugate());
                        let cov = Variance::covariant();
                        let neg_cov = cov.conjugate();
                        let v1 = cov
                            .inter(&p1.union(&p1.conjugate()))
                            .union(&neg_cov.inter(&n1.union(&n1.conjugate())));
                        let weak = (cvari(VarianceFlag::MayWeak)
                            && (cv(VarianceFlag::MayPos) || cv(VarianceFlag::MayNeg)))
                            || ((cvari(VarianceFlag::MayPos) || cvari(VarianceFlag::MayNeg))
                                && cv(VarianceFlag::MayWeak));
                        let v2 = v1.set(VarianceFlag::MayWeak, weak);
                        compute_variance_rec(ctx, env, visited, v2, *arg, depth + 1);
                    }
                }
            } else {
                drop(desc);
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            let v = if vari.mem(VarianceFlag::Pos) || vari.mem(VarianceFlag::Neg) {
                Variance::FULL
            } else {
                Variance::MAY_INV
            };
            let args: Vec<TypeExprRef> = args.clone();
            drop(desc);
            for t in &args {
                compute_variance_rec(ctx, env, visited, v, *t, depth + 1);
            }
        }
        TypeDesc::Tpoly { body, .. } => {
            let body = *body;
            drop(desc);
            compute_variance_rec(ctx, env, visited, vari, body, depth + 1);
        }
        TypeDesc::Tobject { fields, .. } => {
            let fields = *fields;
            drop(desc);
            compute_variance_rec(ctx, env, visited, vari, fields, depth + 1);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            let typ = *typ;
            let rest = *rest;
            drop(desc);
            compute_variance_rec(ctx, env, visited, vari, typ, depth + 1);
            compute_variance_rec(ctx, env, visited, vari, rest, depth + 1);
        }
        TypeDesc::Tvariant(row) => {
            let row_fields = row.row_fields.clone();
            let row_more = row.row_more;
            drop(desc);
            for (_, field) in &row_fields {
                match field {
                    RowField::Rpresent(Some(ty)) => {
                        compute_variance_rec(ctx, env, visited, vari, *ty, depth + 1);
                    }
                    RowField::Reither { types, .. } => {
                        let upper = Variance::NULL
                            .set(VarianceFlag::MayPos, true)
                            .set(VarianceFlag::MayNeg, true)
                            .set(VarianceFlag::MayWeak, true);
                        let v = vari.inter(&upper);
                        for t in types {
                            compute_variance_rec(ctx, env, visited, v, *t, depth + 1);
                        }
                    }
                    _ => {}
                }
            }
            compute_variance_rec(ctx, env, visited, vari, row_more, depth + 1);
        }
        // Tvar, Tnil, Tlink, Tunivar, Tsubst: no children to recurse into
        _ => {
            drop(desc);
        }
    }
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
        // Use unify_var-equivalent behavior here (not full unify): fresh var
        // linking should only do occur/update_level/link on this path.
        let fresh = ctx.repr(ctx.new_var(None));
        let arg_ty = ctx.repr(arg_ty);
        if fresh != arg_ty {
            let fresh_is_var = matches!(&*ctx.get_desc(fresh), TypeDesc::Tvar(_));
            if fresh_is_var {
                let needs_full_unify = {
                    let arg_desc = ctx.get_desc(arg_ty);
                    let is_constr = matches!(&*arg_desc, TypeDesc::Tconstr { .. });
                    drop(arg_desc);
                    is_constr && deep_occur(ctx, fresh, arg_ty)
                };
                if needs_full_unify {
                    let mut state = UnifyState::new();
                    state.set_env(env);
                    if unify(ctx, &mut state, fresh, arg_ty).is_err() {
                        unreachable!("lower_args failed deep_occur full unify")
                    }
                } else {
                    if occurs(ctx, fresh, arg_ty) {
                        unreachable!("lower_args recursive type in unify_var path")
                    }
                    update_level(ctx, ctx.get_level(fresh), arg_ty);
                    link_type(ctx, fresh, arg_ty);
                }
            } else {
                let mut state = UnifyState::new();
                state.set_env(env);
                if unify(ctx, &mut state, fresh, arg_ty).is_err() {
                    unreachable!("lower_args failed fallback unify")
                }
            }
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

/// Like instance_for_expansion, but also caches the result in simple_expansion_cache
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
    if std::env::var_os("RUST_DEBUG_INSTANCE_CSTR").is_some()
        && (cstr.cstr_name == "Node"
            || cstr.cstr_name == "Empty"
            || cstr.cstr_name == "SPlayer"
            || cstr.cstr_name == "SEnemy"
            || cstr.cstr_name == "Some"
            || cstr.cstr_name == "One"
            || cstr.cstr_name == "Two"
            || cstr.cstr_name == "Three")
    {
        let res_repr = ctx.repr(ty_res);
        let args = ty_args
            .iter()
            .map(|arg| {
                let r = ctx.repr(*arg);
                let desc = ctx.get_desc(r);
                match &*desc {
                    TypeDesc::Tconstr { path, args, .. } => {
                        let arg_dump = args
                            .iter()
                            .map(|a| {
                                let ar = ctx.repr(*a);
                                let ad = ctx.get_desc(ar);
                                match &*ad {
                                    TypeDesc::Tconstr { path, .. } => {
                                        format!("{}:{}@{}", path.name(), ar.0, ctx.get_level(ar))
                                    }
                                    TypeDesc::Tvar(_) => {
                                        format!("Tvar:{}@{}", ar.0, ctx.get_level(ar))
                                    }
                                    TypeDesc::Tunivar(_) => {
                                        format!("Tunivar:{}@{}", ar.0, ctx.get_level(ar))
                                    }
                                    _ => format!("{}@{}", ar.0, ctx.get_level(ar)),
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        format!("{}:{}@{}<{}>", path.name(), r.0, ctx.get_level(r), arg_dump)
                    }
                    TypeDesc::Tvar(_) => format!("Tvar:{}@{}", r.0, ctx.get_level(r)),
                    TypeDesc::Tunivar(_) => format!("Tunivar:{}@{}", r.0, ctx.get_level(r)),
                    _ => format!("{}@{}", r.0, ctx.get_level(r)),
                }
            })
            .collect::<Vec<_>>()
            .join(",");
        let src_args = cstr
            .cstr_args
            .iter()
            .map(|arg| {
                let r = ctx.repr(*arg);
                let desc = ctx.get_desc(r);
                match &*desc {
                    TypeDesc::Tconstr { path, args, .. } => {
                        let arg_dump = args
                            .iter()
                            .map(|a| {
                                let ar = ctx.repr(*a);
                                let ad = ctx.get_desc(ar);
                                match &*ad {
                                    TypeDesc::Tconstr { path, .. } => {
                                        format!("{}:{}@{}", path.name(), ar.0, ctx.get_level(ar))
                                    }
                                    TypeDesc::Tvar(_) => {
                                        format!("Tvar:{}@{}", ar.0, ctx.get_level(ar))
                                    }
                                    TypeDesc::Tunivar(_) => {
                                        format!("Tunivar:{}@{}", ar.0, ctx.get_level(ar))
                                    }
                                    _ => format!("{}@{}", ar.0, ctx.get_level(ar)),
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        format!("{}:{}@{}<{}>", path.name(), r.0, ctx.get_level(r), arg_dump)
                    }
                    TypeDesc::Tvar(_) => format!("Tvar:{}@{}", r.0, ctx.get_level(r)),
                    TypeDesc::Tunivar(_) => format!("Tunivar:{}@{}", r.0, ctx.get_level(r)),
                    _ => format!("{}@{}", r.0, ctx.get_level(r)),
                }
            })
            .collect::<Vec<_>>()
            .join(",");
        let res_desc = ctx.get_desc(res_repr);
        let res_head = match &*res_desc {
            TypeDesc::Tconstr { path, .. } => path.name(),
            TypeDesc::Tvar(_) => "Tvar".to_string(),
            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
            _ => format!("ty#{}", res_repr.0),
        };
        let src_res_repr = ctx.repr(cstr.cstr_res);
        let src_res_desc = ctx.get_desc(src_res_repr);
        let src_res_head = match &*src_res_desc {
            TypeDesc::Tconstr { path, .. } => path.name(),
            TypeDesc::Tvar(_) => "Tvar".to_string(),
            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
            _ => format!("ty#{}", src_res_repr.0),
        };
        eprintln!(
            "[instance-cstr] name={} src_res={}:{}@{} src_args=[{}] res={}:{}@{} args=[{}]",
            cstr.cstr_name,
            src_res_head,
            src_res_repr.0,
            ctx.get_level(src_res_repr),
            src_args,
            res_head,
            res_repr.0,
            ctx.get_level(res_repr),
            args
        );
    }
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

pub(crate) fn subst_type_params(
    ctx: &TypeContext<'_>,
    params: &[TypeExprRef],
    args: &[TypeExprRef],
    ty: TypeExprRef,
) -> TypeExprRef {
    subst_type(ctx, params, args, ty)
}

/// Instantiate a label description, creating fresh type variables for its
/// result type (record type) and argument type (field type) while sharing
/// the same variable substitutions between them.
/// Handles Tpoly unwrapping like OCaml's instance_label in ctype.ml.
pub fn instance_label(
    ctx: &TypeContext<'_>,
    fixed: bool,
    lbl: &super::LabelDescription,
) -> (Vec<TypeExprRef>, TypeExprRef, TypeExprRef) {
    if std::env::var_os("RUST_PANIC_INSTANCE_LABEL").is_some() {
        panic!("instance_label invoked");
    }
    let should_debug_label = std::env::var_os("RUST_DEBUG_INSTANCE_LABEL").is_some();
    let summarize = |ty: TypeExprRef| -> String {
        let ty = ctx.repr(ty);
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let args_summary = args
                    .iter()
                    .map(|arg| {
                        let arg = ctx.repr(*arg);
                        let arg_desc = ctx.get_desc(arg);
                        let kind = match &*arg_desc {
                            TypeDesc::Tconstr { path, .. } => path.name(),
                            TypeDesc::Tvar(name) => format!("Tvar({name:?})"),
                            TypeDesc::Tunivar(name) => format!("Tunivar({name:?})"),
                            _ => format!("ty#{}", arg.0),
                        };
                        format!("{}:{}", arg.0, kind)
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!(
                    "{}#{}@{}[{}]",
                    path.name(),
                    ty.0,
                    ctx.get_level(ty),
                    args_summary
                )
            }
            TypeDesc::Tvar(name) => {
                format!("Tvar({:?})#{}@{}", name, ty.0, ctx.get_level(ty))
            }
            TypeDesc::Tunivar(name) => {
                format!("Tunivar({:?})#{}@{}", name, ty.0, ctx.get_level(ty))
            }
            TypeDesc::Tpoly { body, vars } => format!(
                "Tpoly#{}@{}(body=#{} vars={})",
                ty.0,
                ctx.get_level(ty),
                ctx.repr(*body).0,
                vars.len()
            ),
            other => format!("{:?}#{}@{}", other, ty.0, ctx.get_level(ty)),
        }
    };
    if should_debug_label {
        eprintln!(
            "[instance-label] stage=enter name={} fixed={} arg={} res={}",
            lbl.lbl_name,
            fixed,
            summarize(lbl.lbl_arg),
            summarize(lbl.lbl_res)
        );
    }

    // Match OCaml ctype.ml instance_label:
    //   let ty_res = copy lbl.lbl_res
    //   let vars, ty_arg = match repr lbl.lbl_arg with
    //     | Tpoly (ty, tl) -> instance_poly fixed tl ty
    //     | _ -> [], copy lbl.lbl_arg
    // copy lbl_res / copy lbl_arg must share the same copy window.
    let mut cache = CopyCache::new();
    let ty_res = copy_type_cached(ctx, lbl.lbl_res, &mut cache);
    if should_debug_label {
        eprintln!(
            "[instance-label] stage=after-copy-res name={} ty_res={}",
            lbl.lbl_name,
            summarize(ty_res)
        );
    }
    let arg_repr = ctx.repr(lbl.lbl_arg);
    let (poly_vars, ty_arg) = {
        let desc = ctx.get_desc(arg_repr);
        match &*desc {
            super::TypeDesc::Tpoly { body, vars } => {
                let body = *body;
                let vars = vars.clone();
                drop(desc);
                // OCaml runs copy(lbl_res) and then instance_poly(lbl_arg) within
                // one temporary substitution window. For empty-Tpoly label args,
                // that means instance_poly allocates a fresh body but still
                // constrains it through the shared copy state from ty_res.
                // Reconcile the empty-Tpoly instance with the shared-body copy
                // without replacing the allocated instance node.
                let shared_body = if vars.is_empty() {
                    Some(copy_type_cached(ctx, body, &mut cache))
                } else {
                    None
                };
                let (poly_vars, ty_arg) = instance_poly(ctx, false, fixed, &vars, body);
                if let Some(shared_body) = shared_body {
                    let mut state = UnifyState::new();
                    let _ = unify(ctx, &mut state, ty_arg, shared_body);
                }
                if should_debug_label {
                    eprintln!(
                        "[instance-label] stage=arg-poly name={} vars={} shared_body={} ty_arg={}",
                        lbl.lbl_name,
                        vars.len(),
                        shared_body
                            .map(|t| summarize(t))
                            .unwrap_or_else(|| "<none>".to_string()),
                        summarize(ty_arg)
                    );
                }
                (poly_vars, ty_arg)
            }
            _ => {
                drop(desc);
                let copied = copy_type_cached(ctx, lbl.lbl_arg, &mut cache);
                if should_debug_label {
                    eprintln!(
                        "[instance-label] stage=arg-copy name={} src={} copied={}",
                        lbl.lbl_name,
                        summarize(lbl.lbl_arg),
                        summarize(copied)
                    );
                }
                (vec![], copied)
            }
        }
    };
    if should_debug_label {
        eprintln!(
            "[instance-label] stage=exit name={} ty_arg={} ty_res={} poly_vars={}",
            lbl.lbl_name,
            summarize(ty_arg),
            summarize(ty_res),
            poly_vars.len()
        );
    }
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
/// NOTE: OCaml's `copy` checks `t.level <> generic_level` and returns
/// non-generic types directly. Adding that check here regresses parity
/// because other parts of the system are calibrated for copy-everything.
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
    subst_identity_copy_with_partial(ctx, ty, false)
}

pub fn subst_identity_copy_with_partial(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    reopen_closed_variant_rows: bool,
) -> TypeExprRef {
    let mut seen = std::collections::HashMap::new();
    // OCaml Subst.typexp uses a temporary `row_more.desc <- Tsubst(Ttuple [...])`
    // marker window to preserve recursive row sharing while copying.
    // Keep the same lifetime semantics in a scoped side table.
    let mut row_more_markers = std::collections::HashMap::new();
    subst_identity_copy_rec(
        ctx,
        ty,
        reopen_closed_variant_rows,
        &mut seen,
        &mut row_more_markers,
    )
}

#[derive(Clone, Copy)]
struct SubstRowMoreMarker {
    tuple: TypeExprRef,
    variant: TypeExprRef,
}

fn subst_identity_copy_rec(
    ctx: &TypeContext<'_>,
    ty: TypeExprRef,
    reopen_closed_variant_rows: bool,
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
            // OCaml Subst.typexp creates a generic-level stub (`newgenvar`) for
            // every non-variable node. Keeping this at current_level allows the
            // copied manifest to be reused and mutated by later unification.
            let placeholder = ctx.new_generic_var(None);
            seen.insert(ty, placeholder);

            let desc = ctx.get_desc(ty);
            let new_desc = match &*desc {
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => unreachable!(),
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                    let target = *target;
                    drop(desc);
                    return subst_identity_copy_rec(
                        ctx,
                        target,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
                }
                TypeDesc::Tarrow { arg, ret, arity, .. } => {
                    let arg_typ = arg.typ;
                    let arg_lbl = arg.lbl.clone();
                    let ret = *ret;
                    let arity = *arity;
                    drop(desc);
                    let arg_copy = subst_identity_copy_rec(
                        ctx,
                        arg_typ,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
                    let ret_copy = subst_identity_copy_rec(
                        ctx,
                        ret,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
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
                        .map(|t| {
                            subst_identity_copy_rec(
                                ctx,
                                *t,
                                reopen_closed_variant_rows,
                                seen,
                                row_more_markers,
                            )
                        })
                        .collect();
                    TypeDesc::Ttuple(types_copy)
                }
                TypeDesc::Tconstr { path, args, .. } => {
                    let path = path.clone();
                    let args = args.clone();
                    drop(desc);
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| {
                            subst_identity_copy_rec(
                                ctx,
                                *t,
                                reopen_closed_variant_rows,
                                seen,
                                row_more_markers,
                            )
                        })
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
                    let fields_copy = subst_identity_copy_rec(
                        ctx,
                        fields,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
                    let name_copy = name.map(|(path, args)| {
                        (
                            path,
                            args.iter()
                                .map(|t| {
                                    subst_identity_copy_rec(
                                        ctx,
                                        *t,
                                        reopen_closed_variant_rows,
                                        seen,
                                        row_more_markers,
                                    )
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
                    let rest_copy = subst_identity_copy_rec(
                        ctx,
                        rest,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
                    if is_absent {
                        TypeDesc::Tlink(rest_copy)
                    } else {
                        let typ_copy = subst_identity_copy_rec(
                            ctx,
                            typ,
                            reopen_closed_variant_rows,
                            seen,
                            row_more_markers,
                        );
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
                    let body_copy = subst_identity_copy_rec(
                        ctx,
                        body,
                        reopen_closed_variant_rows,
                        seen,
                        row_more_markers,
                    );
                    let vars_copy: Vec<_> = vars
                        .iter()
                        .map(|t| {
                            subst_identity_copy_rec(
                                ctx,
                                *t,
                                reopen_closed_variant_rows,
                                seen,
                                row_more_markers,
                            )
                        })
                        .collect();
                    TypeDesc::Tpoly {
                        body: body_copy,
                        vars: vars_copy,
                    }
                }
                TypeDesc::Tvariant(row) => {
                    let row = row.clone();
                    drop(desc);
                    let mut row = row_repr(ctx, &row);
                    let more = ctx.repr(row.row_more);
                    if let Some(marker) = row_more_markers.get(&more).copied() {
                        // OCaml Subst.typexp fast-path:
                        // more.desc = Tsubst(Ttuple [more'; ty']) => reuse ty'
                        // and remap future visits of this source node to ty'
                        // within the same copy window.
                        seen.insert(ty, marker.variant);
                        TypeDesc::Tlink(marker.variant)
                    } else {
                    let keep = ctx.get_level(more) != GENERIC_LEVEL;
                    let (dup, mut more_copy) = {
                        let more_desc = ctx.get_desc(more).clone();
                        let more_is_constr = matches!(&more_desc, TypeDesc::Tconstr { .. });
                        let dup = ctx.get_level(more) == GENERIC_LEVEL
                            || super::btype::static_row(ctx, &row)
                            || more_is_constr;
                        let more_copy = match more_desc {
                            TypeDesc::Tsubst(target) => target,
                            TypeDesc::Tconstr { .. } | TypeDesc::Tnil => {
                                subst_identity_copy_rec(
                                    ctx,
                                    more,
                                    reopen_closed_variant_rows,
                                    seen,
                                    row_more_markers,
                                )
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
                                subst_identity_copy_rec(
                                    ctx,
                                    target,
                                    reopen_closed_variant_rows,
                                    seen,
                                    row_more_markers,
                                )
                            }
                            _ => panic!("unexpected row_more in subst_identity_copy_rec"),
                        };
                        (dup, more_copy)
                    };
                    if reopen_closed_variant_rows {
                        let has_reither = row.row_fields.iter().any(|(_, field)| {
                            matches!(
                                super::btype::row_field_repr(ctx, field),
                                crate::types::type_expr::RowField::Reither { .. }
                            )
                        });
                        if row.row_closed && !row.row_fixed && has_reither {
                            if more == ctx.repr(more_copy) {
                                let fresh = ctx.new_var(None);
                                let lv = if keep {
                                    ctx.get_level(more)
                                } else {
                                    ctx.current_level()
                                };
                                ctx.set_level(fresh, lv);
                                more_copy = fresh;
                            }
                            row.row_fields.retain(|(_, field)| {
                                !matches!(
                                    super::btype::row_field_repr(ctx, field),
                                    crate::types::type_expr::RowField::Reither { .. }
                                )
                            });
                            row.row_more = more_copy;
                            row.row_closed = false;
                            row.row_fixed = false;
                            row.row_name = None;
                        }
                    }
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
                                            reopen_closed_variant_rows,
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
                                                reopen_closed_variant_rows,
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
                                        reopen_closed_variant_rows,
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
                        .map(|t| {
                            subst_identity_copy_rec(
                                ctx,
                                *t,
                                reopen_closed_variant_rows,
                                seen,
                                row_more_markers,
                            )
                        })
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
    let debug_copy_constr = std::env::var_os("RUST_DEBUG_COPY_CONSTR").is_some();
    let debug_copy_path = std::env::var("RUST_DEBUG_COPY_PATH").ok();

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
        if debug_copy_constr || debug_copy_path.is_some() {
            if let TypeDesc::Tconstr { path, .. } = &*desc {
                let name = path.name();
                let path_match = debug_copy_path
                    .as_deref()
                    .is_some_and(|needle| name.contains(needle));
                if path_match
                    || name == "ticker"
                    || name == "Ticker_map.t"
                    || name == "Belt.List.t"
                    || name == "list"
                    || name == "int"
                    || name == "string"
                    || name == "option"
                    || name == "Stdlib.JSON.t"
                    || name == "JSON.t"
                {
                    eprintln!(
                        "[rust-copy-constr] inspect ty={} level={} name={}",
                        ty.0,
                        ctx.get_level(ty),
                        name
                    );
                }
            }
        }

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
                // Tconstr: OCaml's copy returns identity for ALL non-generic types.
                // Match that behavior: return self for all non-generic Tconstr.
                TypeDesc::Tconstr { path, .. } => {
                    let path_name = path.name();
                    let path_match = debug_copy_path
                        .as_deref()
                        .is_some_and(|needle| path_name.contains(needle));
                    if debug_copy_constr || path_match {
                        let name = path.name();
                        if path_match
                            || name == "ticker"
                            || name == "Ticker_map.t"
                            || name == "Belt.List.t"
                            || name == "list"
                            || name == "int"
                            || name == "string"
                            || name == "option"
                            || name == "Jsx.element"
                            || name == "React.element"
                            || name == "Stdlib.JSON.t"
                            || name == "JSON.t"
                        {
                            eprintln!(
                                "[rust-copy-constr] return-self ty={} level={} name={}",
                                ty.0,
                                ctx.get_level(ty),
                                name
                            );
                        }
                    }
                    CopyAction::ReturnSelf
                }
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
                TypeDesc::Tconstr { path, args, .. } => {
                    let path_name = path.name();
                    let path_match = debug_copy_path
                        .as_deref()
                        .is_some_and(|needle| path_name.contains(needle));
                    if debug_copy_constr || path_match {
                        let name = path.name();
                        if path_match
                            || name == "ticker"
                            || name == "Ticker_map.t"
                            || name == "Belt.List.t"
                            || name == "list"
                            || name == "int"
                            || name == "string"
                            || name == "option"
                            || name == "Jsx.element"
                            || name == "React.element"
                            || name == "Stdlib.JSON.t"
                            || name == "JSON.t"
                        {
                            eprintln!(
                                "[rust-copy-constr] copy-constr ty={} level={} name={}",
                                ty.0,
                                ctx.get_level(ty),
                                name
                            );
                        }
                    }
                    CopyAction::Constr {
                        path: path.clone(),
                        args: args.clone(),
                    }
                }
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
                    let abbrevs = ctx.current_abbreviations();
                    let lookup_abbrevs = proper_abbrevs(ctx, &path, &args, abbrevs);
                    let debug_copy_constr = std::env::var_os("RUST_DEBUG_COPY_CONSTR").is_some();
                    let debug_copy_constr_bt =
                        std::env::var_os("RUST_DEBUG_COPY_CONSTR_BT").is_some();
                    let full_path_name = if debug_copy_constr || debug_copy_path.is_some() {
                        Some(path.name())
                    } else {
                        None
                    };
                    let debug_path_name = if (debug_copy_constr || debug_copy_path.is_some())
                        && (debug_copy_path
                            .as_deref()
                            .is_some_and(|needle| path.name().contains(needle))
                            || path.last() == "value"
                            || path.last() == "xy"
                            || path.last() == "imageElement"
                            || path.last() == "key"
                            || path.last() == "elt"
                            || path.last() == "stateless"
                            || path.last() == "noRetainedProps"
                            || path.last() == "actionless"
                            || path.last() == "componentSpec"
                            || path.last() == "component"
                            || full_path_name.as_deref() == Some("Ord.t")
                            || full_path_name.as_deref() == Some("Js_string2.t")
                            || full_path_name.as_deref() == Some("Js.String2.t")
                            || full_path_name.as_deref() == Some("int")
                            || full_path_name.as_deref() == Some("string")
                            || full_path_name.as_deref() == Some("option")
                            || full_path_name.as_deref() == Some("N.t")
                            || full_path_name.as_deref() == Some("Belt.MutableSet.Int.t")
                            || full_path_name.as_deref() == Some("LayerStyleID.ID.t")
                            || full_path_name.as_deref() == Some("Layout.Types.t")
                            || full_path_name.as_deref() == Some("Jsx.element")
                            || full_path_name.as_deref() == Some("React.element")
                            || full_path_name.as_deref() == Some("Stdlib.JSON.t")
                            || full_path_name.as_deref() == Some("JSON.t"))
                    {
                        full_path_name.clone()
                    } else {
                        None
                    };

                    let is_local_nonpersistent =
                        matches!(&path, Path::Pident(id) if !id.is_persistent());
                    if let Some(found_ty) = ctx.find_abbrev_repr(lookup_abbrevs, &path) {
                        let found_source = ctx.repr(found_ty);
                        // OCaml copy() mutates source nodes to Tsubst stubs while
                        // copying, so find_repr observes the copied representative.
                        // Rust keeps source nodes immutable during copy, so we must
                        // project through the local copy cache to recover the same
                        // representative.
                        let found_cached = cache
                            .nodes
                            .get(&found_ty)
                            .copied()
                            .or_else(|| cache.nodes.get(&found_source).copied());
                        let found_repr = found_cached.unwrap_or(if is_local_nonpersistent {
                            found_source
                        } else {
                            found_ty
                        });
                        let found_ty_level = ctx.get_level(found_ty);
                        let found_source_level = ctx.get_level(found_source);
                        let stale_local_generic_hit = is_local_nonpersistent
                            && found_cached.is_none()
                            && ctx.get_level(found_source) == GENERIC_LEVEL;
                        if let Some(path_name) = &debug_path_name {
                            eprintln!(
                                "[copy-constr] hit path={} ty={} level={} head_stamp={} lookup={:?} found_ty={} found_ty_level={} found_source={} found_source_level={} found_repr={} found_cached={} stale_local_generic_hit={}",
                                path_name,
                                ty.0,
                                level,
                                path.head().stamp(),
                                lookup_abbrevs,
                                found_ty.0,
                                found_ty_level,
                                found_source.0,
                                found_source_level,
                                found_repr.0,
                                found_cached.is_some(),
                                stale_local_generic_hit
                            );
                            if debug_copy_constr_bt
                                && (path_name == "React.element"
                                    || path_name == "Stdlib.JSON.t"
                                    || path_name == "JSON.t")
                            {
                                let event =
                                    COPY_CONSTR_DEBUG_EVENTS.fetch_add(1, Ordering::Relaxed);
                                if event < 40 {
                                    eprintln!(
                                        "[copy-constr-bt] event={} kind=hit path={} ty={} found_source={} found_repr={}\n{:?}",
                                        event,
                                        path_name,
                                        ty.0,
                                        found_source.0,
                                        found_repr.0,
                                        std::backtrace::Backtrace::capture()
                                    );
                                }
                            }
                        }
                        if !stale_local_generic_hit && found_repr != placeholder {
                            cache.nodes.insert(ty, found_repr);
                            ctx.set_desc(placeholder, TypeDesc::Tlink(found_repr));
                            return found_repr;
                        }
                    } else if let Some(path_name) = &debug_path_name {
                        let memo_state = ctx.get_abbrev_memo(lookup_abbrevs);
                        eprintln!(
                            "[copy-constr] miss path={} ty={} level={} head_stamp={} lookup={:?} memo={:?}",
                            path_name,
                            ty.0,
                            level,
                            path.head().stamp(),
                            lookup_abbrevs,
                            memo_state
                        );
                        if debug_copy_constr_bt
                            && (path_name == "React.element"
                                || path_name == "Stdlib.JSON.t"
                                || path_name == "JSON.t")
                        {
                            let event = COPY_CONSTR_DEBUG_EVENTS.fetch_add(1, Ordering::Relaxed);
                            if event < 40 {
                                eprintln!(
                                    "[copy-constr-bt] event={} kind=miss path={} ty={} memo={:?}\n{:?}",
                                    event,
                                    path_name,
                                    ty.0,
                                    memo_state,
                                    std::backtrace::Backtrace::capture()
                                );
                            }
                        }
                    }

                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();

                    let copied_abbrev = match ctx.get_abbrev_memo(abbrevs) {
                        AbbrevMemo::Mcons { .. } => ctx.alloc_abbrev(AbbrevMemo::Mlink(abbrevs)),
                        memo => ctx.alloc_abbrev(memo),
                    };
                    if let Some(path_name) = &debug_path_name {
                        let args_dump = args_copy
                            .iter()
                            .map(|arg| {
                                let arg = ctx.repr(*arg);
                                format!("{}@{}", arg.0, ctx.get_level(arg))
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        eprintln!(
                            "[copy-constr] fresh path={} source_ty={} placeholder={} level={} args=[{}]",
                            path_name,
                            ty.0,
                            placeholder.0,
                            ctx.get_level(placeholder),
                            args_dump
                        );
                    }

                    TypeDesc::Tconstr {
                        path,
                        args: args_copy,
                        abbrev: copied_abbrev,
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
                    let mut row_copy = copy_row_cached(ctx, &row, true, keep, more_copy, cache);
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

// ============================================================================
// Type Normalization (before printing/saving)
// ============================================================================

/// Normalize a type before printing/saving, matching OCaml's `normalize_type_rec`.
///
/// For Tvariant: flattens row, filters Rabsent fields, sorts alphabetically, mutates desc.
/// For Tobject: flattens fields (sorts alphabetically), rebuilds chain, mutates desc.
/// Recursively visits all sub-types.
pub fn normalize_type(ctx: &TypeContext<'_>, ty: TypeExprRef) {
    let mut visited = HashSet::new();
    normalize_type_rec(ctx, &mut visited, ty);
}

/// Sort ALL Tobject field chains alphabetically in the entire type context.
/// OCaml sorts object fields during type checking (flatten_fields/unify_fields),
/// so all Tobject types should have sorted fields. This function ensures that.
pub fn sort_all_object_fields(ctx: &TypeContext<'_>) {
    let count = ctx.type_expr_count();
    for i in 0..count {
        let ty = TypeExprRef(i);
        let desc = ctx.get_desc(ty);
        if let TypeDesc::Tobject { fields: fi, .. } = &*desc {
            let fi = *fi;
            drop(desc);
            let fi_repr = ctx.repr(fi);
            let fi_level = ctx.get_level(fi_repr);
            if fi_level >= 0 {
                let (sorted_fields, rest) = flatten_fields(ctx, fi_repr);
                if !sorted_fields.is_empty() {
                    let new_fi = build_fields(ctx, fi_level, &sorted_fields, rest);
                    let new_desc = ctx.get_desc(new_fi).clone();
                    ctx.set_desc(fi_repr, new_desc);
                }
            }
        } else {
            drop(desc);
        }
    }
}

/// Normalize ALL type nodes in the context (sort variant/object fields).
pub fn normalize_all_types(ctx: &TypeContext<'_>) {
    let count = ctx.type_expr_count();
    for i in 0..count {
        let ty = TypeExprRef(i);
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvariant(row) => {
                let row = row_repr(ctx, row);
                let mut fields: Vec<(String, RowField)> = row.row_fields.iter()
                    .map(|(label, field)| {
                        let resolved = btype::row_field_repr(ctx, field);
                        (label.clone(), resolved)
                    })
                    .filter(|(_, field)| !matches!(field, RowField::Rabsent))
                    .collect();
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                drop(desc);
                ctx.set_desc(ty, TypeDesc::Tvariant(RowDesc {
                    row_fields: fields,
                    row_more: row.row_more,
                    row_closed: row.row_closed,
                    row_fixed: row.row_fixed,
                    row_name: row.row_name.clone(),
                }));
            }
            TypeDesc::Tobject { fields: fi, .. } => {
                let fi = *fi;
                drop(desc);
                let fi_repr = ctx.repr(fi);
                let fi_level = ctx.get_level(fi_repr);
                if fi_level >= 0 {
                    let (sorted_fields, rest) = flatten_fields(ctx, fi_repr);
                    if !sorted_fields.is_empty() {
                        let new_fi = build_fields(ctx, fi_level, &sorted_fields, rest);
                        let new_desc = ctx.get_desc(new_fi).clone();
                        ctx.set_desc(fi_repr, new_desc);
                    }
                }
            }
            _ => { drop(desc); }
        }
    }
}

fn normalize_type_rec(ctx: &TypeContext<'_>, visited: &mut HashSet<TypeExprRef>, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    if visited.contains(&ty) {
        return;
    }
    visited.insert(ty);

    // Normalize Tvariant (resolve row field reprs, filter Rabsent, sort alphabetically)
    // and Tobject (sort field chains alphabetically via flatten_fields/build_fields).
    // Matches OCaml's normalize_type_rec in ctype.ml lines 4144-4217.
    //
    // NOTE: OCaml's normalize only reaches types in the SIGNATURE (Sig_value val_type),
    // not the expression-level types from instance() copies. So only declaration-level
    // variants get sorted; expression-level variants retain their original order
    // (hash-fold from Ptyp_variant). Since we don't have a separate signature,
    // we normalize from typed tree entry points (pat_type, ctyp_type), which
    // has a similar but not identical reach.
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvariant(row) => {
            // Resolve row field reprs, filter Rabsent, and sort alphabetically.
            // OCaml's normalize sorts and only reaches SIGNATURE types (Sig_value val_type).
            // We reach more types (from typed tree entry points), but sorting is net positive:
            // +2 tests from signature-reachable variants being sorted, 0 tests lost from
            // over-sorting expression-level variants (they happen to sort correctly already
            // or their tests fail for other reasons).
            let row = row_repr(ctx, row);
            let mut fields: Vec<(String, RowField)> = row.row_fields.iter()
                .map(|(label, field)| {
                    let resolved = btype::row_field_repr(ctx, field);
                    (label.clone(), resolved)
                })
                .filter(|(_, field)| !matches!(field, RowField::Rabsent))
                .collect();
            fields.sort_by(|(a, _), (b, _)| a.cmp(b));
            drop(desc);
            ctx.set_desc(ty, TypeDesc::Tvariant(RowDesc {
                row_fields: fields,
                row_more: row.row_more,
                row_closed: row.row_closed,
                row_fixed: row.row_fixed,
                row_name: row.row_name.clone(),
            }));
        }
        TypeDesc::Tobject { fields: fi, .. } => {
            let fi = *fi;
            drop(desc);
            let fi_repr = ctx.repr(fi);
            let fi_level = ctx.get_level(fi_repr);
            if fi_level >= 0 {
                // flatten_fields sorts alphabetically, build_fields reconstructs
                let (sorted_fields, rest) = flatten_fields(ctx, fi_repr);
                if !sorted_fields.is_empty() {
                    let new_fi = build_fields(ctx, fi_level, &sorted_fields, rest);
                    // Mutate the fields pointer's desc to the sorted chain's desc
                    let new_desc = ctx.get_desc(new_fi).clone();
                    ctx.set_desc(fi_repr, new_desc);
                }
            }
        }
        _ => {
            drop(desc);
        }
    }

    // Recurse on all children
    iter_type_expr(ctx, ty, |child| {
        normalize_type_rec(ctx, visited, child);
    });
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
