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

use super::asttypes::{Label, MutableFlag, PrivateFlag};
use super::btype::{self, iter_type_expr, row_fixed, row_more, row_repr, row_repr_ref};
use super::context::TypeContext;
use super::decl::LabelDeclaration;
use super::env::Env;
use super::path::Path;
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, FieldMutability, GENERIC_LEVEL, MutabilityRef, RowDesc, RowField,
    TypeDesc, TypeExprRef, TypeExprRefSet,
};
use super::variance::{Variance, VarianceFlag};
use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use crate::ident::Ident;
use std::sync::Arc;

fn in_process_module_resolution_env(
    ctx: &TypeContext,
) -> Option<crate::cmi::persistent_env::PersistentEnv> {
    // OCaml compiler/ml/env.ml:1000-1007 resolves persistent units through
    // the current persistent environment before any CMI lookup. In Rust's
    // in-process build, TypeContext owns that environment and it is backed by
    // registry/source entries rather than disk artifacts.
    ctx.persistent_env_clone()
        .filter(|env| env.is_in_process_mode())
}
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

    /// Cannot expand a type abbreviation.
    CannotExpand,

    /// Cannot apply a type constructor.
    CannotApply,

    /// Type tags conflict in polymorphic variant.
    TagsConflict(String, String),

    /// Subtype constraint violated.
    Subtype {
        /// OCaml's first trace (`expand_trace env (List.rev trace)`), as
        /// unexpanded pairs.
        trace: Vec<TypePair>,
        /// The unification trace of the failed constraint, without its
        /// outermost pair.
        trace2: Vec<TypePair>,
        context: Option<SubtypeContext>,
    },
}

/// Context for subtype errors.
#[derive(Debug, Clone)]
pub enum SubtypeContext {
    /// Generic error with error code.
    Generic { error_code: String },

    /// Primitive-to-variant coercion target is not unboxed.
    CoercionTargetVariantNotUnboxed { variant_name: Path, primitive: Path },

    /// Primitive-to-variant coercion target does not cover the primitive type.
    CoercionTargetVariantDoesNotCoverType { variant_name: Path, primitive: Path },

    /// Variant constructors do not have the runtime representation required by the target.
    VariantConstructorRuntimeRepresentationMismatch {
        variant_name: Path,
        issues: Vec<VariantRuntimeRepresentationIssue>,
    },

    /// Variant type declarations have incompatible runtime configuration.
    VariantConfigurationsMismatch {
        left_variant_name: Path,
        right_variant_name: Path,
        issue: VariantConfigurationIssue,
    },

    /// Different type kinds.
    DifferentTypeKinds {
        left_typename: Path,
        right_typename: Path,
        left_type_kind: SubtypeTypeKind,
        right_type_kind: SubtypeTypeKind,
    },

    /// Records have fields that are not compatible.
    RecordFieldsMismatch {
        left_record_name: Path,
        right_record_name: Path,
        issues: Vec<RecordFieldSubtypeViolation>,
    },

    /// The target is a private record or variant, whose values only its own
    /// module can build.
    CoercionIntoPrivateType { typename: Path },
}

/// User-facing type kind for subtype diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubtypeTypeKind {
    /// Abstract type.
    Abstract,
    /// Record type.
    Record,
    /// Variant type.
    Variant,
    /// Open type.
    Open,
}

/// Runtime representation problem for variant-to-primitive coercions.
#[derive(Debug, Clone)]
pub enum VariantRuntimeRepresentationIssue {
    MismatchedUnboxedPayload {
        constructor_name: String,
        expected_typename: Path,
    },
    MismatchedAsPayload {
        constructor_name: String,
        expected_typename: Path,
        as_payload: Option<VariantConstructorAsPayload>,
    },
    AsPayloadNotEligibleForCoercion {
        constructor_name: String,
        expected_typename: Path,
        as_payload: VariantConstructorAsPayload,
    },
    InlineRecordCannotBeCoerced {
        constructor_name: String,
    },
    CannotCoerceNonUnboxedWithPayload {
        constructor_name: String,
        expected_typename: Path,
    },
}

/// Runtime type encoded by a variant constructor `@as` payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantConstructorAsPayload {
    String,
    Int,
    Float,
    BigInt,
    Bool,
    Null,
    Undefined,
}

/// Runtime configuration differences for variant-to-variant coercions.
#[derive(Debug, Clone)]
pub enum VariantConfigurationIssue {
    /// The variants differ in whether they are marked `@unboxed`.
    UnboxedConfigNotMatching {
        /// Whether the source variant is unboxed.
        left_unboxed: bool,
        /// Whether the target variant is unboxed.
        right_unboxed: bool,
    },
    /// The variants differ in their `@tag` attribute.
    TagNameNotMatching {
        /// The source variant tag field name.
        left_tag: Option<String>,
        /// The target variant tag field name.
        right_tag: Option<String>,
    },
    /// The source variant has constructors the target cannot represent.
    IncompatibleConstructorCount {
        /// Constructor names present only on the source variant.
        constructor_names: Vec<String>,
    },
}

/// A record field incompatibility found while checking subtype coercions.
#[derive(Debug, Clone)]
pub enum RecordFieldSubtypeViolation {
    /// One side marks a field optional and the other does not.
    OptionalMismatch {
        label: String,
        left_optional: bool,
        right_optional: bool,
    },
    /// The field runtime names differ, either by label or `@as` payload.
    FieldRuntimeNameMismatch {
        label: String,
        left_as: Option<String>,
        right_as: Option<String>,
    },
    /// A field present in the target record is missing from the source record.
    FieldMissing { label: String },
    /// A field immutable in the source record is mutable in the target
    /// record (record_coercion.ml:13, 44-49).
    MutableMismatch { label: String },
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
    unified_pairs: UnifiedPairSet,

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

    /// Dotted type paths whose OCaml `Env.find_type` lookup would force
    /// persistent module components while lowering levels.
    pending_type_lookup_paths: Vec<Path>,

    /// Type constructor paths whose level check proceeds to alias expansion
    /// after the `Env.find_type` lookup.
    pending_type_expansion_paths: Vec<Path>,

    /// Whether the current caller wants to collect those lookup side effects.
    capture_type_lookup_paths: bool,

    /// Current recursive call depth in `unify`.
    recursion_depth: usize,

    /// Current newtype level for GADT equation reification.
    pub newtype_level: Option<i32>,

    /// OCaml `univar_pairs` (newest entry last) and the shared slots its
    /// entries point to (OCaml's `type_expr option ref`).
    univar_pairs: Vec<UnivarPairEntry>,
    univar_slots: Vec<Option<TypeExprRef>>,
}

/// Multiplicative hash for the packed type-pair keys of `UnifiedPairSet`.
#[derive(Default, Clone, Copy)]
struct PairKeyHasher(u64);

impl std::hash::Hasher for PairKeyHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(b)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
    }

    #[inline]
    fn write_u64(&mut self, n: u64) {
        self.0 = (n ^ (n >> 29)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

/// Unordered type pairs already entered by `unify`, packed as
/// `(smaller id << 32) | larger id`.
type UnifiedPairSet = std::collections::HashSet<u64, std::hash::BuildHasherDefault<PairKeyHasher>>;

/// A unified-pair set moved out of a [`UnifyState`].
pub(crate) struct UnifiedPairSetOwned(UnifiedPairSet);

#[inline]
fn unified_pair_key(t1: TypeExprRef, t2: TypeExprRef) -> u64 {
    let (lo, hi) = if t1.0 < t2.0 {
        (t1.0, t2.0)
    } else {
        (t2.0, t1.0)
    };
    (u64::from(lo) << 32) | u64::from(hi)
}

/// Snapshot of mutable unifier state for OCaml-style speculative pattern
/// backtracking.
pub(crate) struct UnifyStateSnapshot {
    unified_pairs: UnifiedPairSet,
    mode: UnifyMode,
    generate_equations: bool,
    assume_injective: bool,
    env: Option<Env>,
    pending_type_lookup_paths: Vec<Path>,
    pending_type_expansion_paths: Vec<Path>,
    capture_type_lookup_paths: bool,
    recursion_depth: usize,
    newtype_level: Option<i32>,
}

impl UnifyState {
    /// Create a new unify state.
    pub fn new() -> Self {
        UnifyState {
            unified_pairs: UnifiedPairSet::default(),
            mode: UnifyMode::Expression,
            generate_equations: false,
            assume_injective: false,
            env: None,
            pending_type_lookup_paths: Vec::new(),
            pending_type_expansion_paths: Vec::new(),
            capture_type_lookup_paths: false,
            recursion_depth: 0,
            newtype_level: None,
            univar_pairs: Vec::new(),
            univar_slots: Vec::new(),
        }
    }

    /// Create a state for pattern matching.
    pub fn pattern_mode() -> Self {
        UnifyState {
            unified_pairs: UnifiedPairSet::default(),
            mode: UnifyMode::Pattern,
            generate_equations: true,
            assume_injective: false,
            env: None,
            pending_type_lookup_paths: Vec::new(),
            pending_type_expansion_paths: Vec::new(),
            capture_type_lookup_paths: false,
            recursion_depth: 0,
            newtype_level: None,
            univar_pairs: Vec::new(),
            univar_slots: Vec::new(),
        }
    }

    /// Set the environment snapshot for type alias expansion.
    pub fn set_env(&mut self, env: &Env) {
        if self
            .env
            .as_ref()
            .is_some_and(|current| current.id() == env.id())
        {
            return;
        }
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

    /// Save the complete mutable state that can be affected by speculative
    /// pattern typing.
    pub(crate) fn snapshot_backtrack_state(&self) -> UnifyStateSnapshot {
        UnifyStateSnapshot {
            unified_pairs: self.unified_pairs.clone(),
            mode: self.mode,
            generate_equations: self.generate_equations,
            assume_injective: self.assume_injective,
            env: self.env.as_ref().map(Env::clone_preserve_id),
            pending_type_lookup_paths: self.pending_type_lookup_paths.clone(),
            pending_type_expansion_paths: self.pending_type_expansion_paths.clone(),
            capture_type_lookup_paths: self.capture_type_lookup_paths,
            recursion_depth: self.recursion_depth,
            newtype_level: self.newtype_level,
        }
    }

    /// Restore a snapshot created by `snapshot_backtrack_state`.
    pub(crate) fn restore_backtrack_state(&mut self, snapshot: UnifyStateSnapshot) {
        self.unified_pairs = snapshot.unified_pairs;
        self.mode = snapshot.mode;
        self.generate_equations = snapshot.generate_equations;
        self.assume_injective = snapshot.assume_injective;
        self.env = snapshot.env;
        self.pending_type_lookup_paths = snapshot.pending_type_lookup_paths;
        self.pending_type_expansion_paths = snapshot.pending_type_expansion_paths;
        self.capture_type_lookup_paths = snapshot.capture_type_lookup_paths;
        self.recursion_depth = snapshot.recursion_depth;
        self.newtype_level = snapshot.newtype_level;
    }

    /// Temporarily move out the environment snapshot.
    ///
    /// Some typecore force helpers need `&mut TypeCheckContext` while reading
    /// the unify environment. Moving the owned snapshot out avoids cloning a
    /// large environment solely to satisfy the borrow checker.
    pub(crate) fn take_env(&mut self) -> Option<Env> {
        self.env.take()
    }

    /// Restore an environment snapshot previously removed with `take_env`.
    pub(crate) fn restore_env(&mut self, env: Env) {
        self.env = Some(env);
    }

    /// Start collecting type lookup paths reached through OCaml-equivalent
    /// `ctype.ml` level lowering.
    pub fn begin_type_lookup_capture(&mut self) -> bool {
        let previous = self.capture_type_lookup_paths;
        self.capture_type_lookup_paths = true;
        previous
    }

    /// Restore the previous capture state and return paths collected while it
    /// was active.
    pub fn finish_type_lookup_capture(&mut self, previous: bool) -> (Vec<Path>, Vec<Path>) {
        self.capture_type_lookup_paths = previous;
        (
            std::mem::take(&mut self.pending_type_lookup_paths),
            std::mem::take(&mut self.pending_type_expansion_paths),
        )
    }

    fn should_capture_type_lookup_paths(&self) -> bool {
        self.capture_type_lookup_paths
    }

    fn extend_type_lookup_paths(&mut self, paths: Vec<Path>) {
        self.pending_type_lookup_paths.extend(paths);
    }

    fn extend_type_expansion_paths(&mut self, paths: Vec<Path>) {
        self.pending_type_expansion_paths.extend(paths);
    }

    /// Check if two types have already been unified.
    pub fn already_unified(&self, t1: TypeExprRef, t2: TypeExprRef) -> bool {
        self.unified_pairs.contains(&unified_pair_key(t1, t2))
    }

    /// Mark two types as unified.
    pub fn mark_unified(&mut self, t1: TypeExprRef, t2: TypeExprRef) {
        self.unified_pairs.insert(unified_pair_key(t1, t2));
    }

    /// Move the unified-pair set out, leaving an empty one, for a
    /// speculative region that is always backtracked; hand it back with
    /// [`Self::put_back_unified_pairs`]. Avoids cloning a set that grows over
    /// the whole module.
    pub(crate) fn take_unified_pairs(&mut self) -> UnifiedPairSetOwned {
        UnifiedPairSetOwned(std::mem::take(&mut self.unified_pairs))
    }

    pub(crate) fn put_back_unified_pairs(&mut self, pairs: UnifiedPairSetOwned) {
        self.unified_pairs = pairs.0;
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

pub(crate) fn lookup_type_decl_for_path<'a>(
    ctx: &'a TypeContext,
    env: &'a Env,
    path: &Path,
) -> Option<super::decl::TypeDeclarationRef<'a>> {
    if let Some(decl) = env.find_local_constraint(path) {
        return Some(super::decl::TypeDeclarationRef::Borrowed(decl));
    }

    // Try direct env lookup. For qualified paths, only accept exact
    // identity matches (`Path.same`) to mirror OCaml's stamp-based lookup.
    // Name-only equality can pick declarations from different scopes.
    let exact_env_decl = match path {
        Path::Pident(id) => env.find_type_by_ident(id),
        _ => env.lookup_type(path),
    };
    if let Ok(decl) = exact_env_decl {
        let exact_lookup = match path {
            Path::Pident(_) => true,
            _ => decl
                .type_path
                .as_ref()
                .is_some_and(|decl_path| decl_path.same(path)),
        };
        if exact_lookup {
            return Some(super::decl::TypeDeclarationRef::Borrowed(decl));
        }
    }

    // OCaml compiler/ml/ctype.ml:759-762 asks `Env.find_type` for
    // constructor variances, and compiler/ml/env.ml:800-813 resolves dotted
    // types through the existing module component tables before falling back to
    // persistent structures. Prefer the env/component path here so lookups like
    // `Js.Types.tagged_t` do not eagerly read `Js.cmi`.
    if let Some(decl) = resolve_type_through_env(ctx, env, path, true) {
        return Some(decl);
    }

    if let Some(decl) = resolve_type_through_modules(ctx, path) {
        return Some(super::decl::TypeDeclarationRef::owned(decl));
    }

    None
}

pub(crate) fn lookup_type_decl_for_path_pub(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    lookup_type_decl_for_path(ctx, env, path).map(super::decl::TypeDeclarationRef::into_owned)
}

fn get_level_with_lookup_capture(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
    pending_type_lookup_paths: &mut Option<&mut Vec<Path>>,
) -> i32 {
    // OCaml compiler/ml/ctype.ml:666-673 `get_level env p` calls
    // `Env.find_type p env` before falling back to `Path.binding_time p`.
    // For dotted paths, compiler/ml/env.ml:800-813 builds parent component
    // tables as a lookup side effect; `lower_args` depends on that happening
    // before local binders are created.
    if matches!(path, Path::Pdot(_, _, _)) {
        if let Some(paths) = pending_type_lookup_paths.as_deref_mut() {
            paths.push(path.clone());
        }
    }
    // A declaration reached through a persistent unit comes out of
    // `Subst.type_declaration`, which clears `type_newtype_level`
    // (compiler/ml/subst.ml:292), so the lookup would fall back to the
    // binding time anyway.
    if path_root_is_persistent(path) {
        return path.binding_time();
    }
    // `Env.find_type` answers from bindings fixed within one module scope, so
    // repeated level checks of the same path reuse the first lookup.
    let scope_id = env.scope_id();
    if let Some(found_level) = ctx.find_type_newtype_level(scope_id, path) {
        return found_level.unwrap_or_else(|| path.binding_time());
    }
    let found_level = match path {
        Path::Pident(id) => env
            .find_type_by_ident(id)
            .ok()
            .and_then(|decl| decl.type_newtype_level.map(|(level, _)| level)),
        Path::Pdot(parent, type_name, _) => {
            // OCaml compiler/ml/ctype.ml:666-673 calls Env.find_type, whose
            // dotted path lookup reaches compiler/ml/env.ml:800-813 through
            // find_module_descr at env.ml:781-793. That path reads component
            // tables; it does not perform the env.ml:865-887 find_module alias
            // scrape used by normalize_path/module lookup. In Rust's
            // in-process mode the active persistent table lives on TypeContext,
            // so use it here with type-lookup component laziness preserved.
            let mut persistent_env = in_process_module_resolution_env(ctx);
            crate::types::typecore::lookup_type_in_resolved_path(
                parent,
                type_name.as_str(),
                env,
                &mut persistent_env,
                ctx,
            )
            .and_then(|(_, _, decl)| decl.type_newtype_level.map(|(level, _)| level))
        }
        Path::Papply(_, _) => None,
    };
    ctx.register_type_newtype_level(scope_id, path, found_level);
    found_level.unwrap_or_else(|| path.binding_time())
}

pub(crate) fn path_root_is_persistent(path: &Path) -> bool {
    match path {
        Path::Pident(id) => id.is_persistent(),
        Path::Pdot(parent, _, _) => path_root_is_persistent(parent),
        Path::Papply(_, _) => false,
    }
}

fn is_contractive(ctx: &TypeContext, env: &Env, path: &Path) -> bool {
    lookup_type_decl_for_path(ctx, env, path).is_some_and(|decl| {
        matches!(
            decl.type_kind,
            super::decl::TypeKind::TypeRecord(..) | super::decl::TypeKind::TypeVariant(..)
        ) || (is_predef_type_name(path.head_name()) && decl.type_manifest.is_none())
    })
}

fn local_non_recursive_abbrev(
    ctx: &TypeContext,
    env: &Env,
    source: &Path,
    ty: TypeExprRef,
) -> bool {
    fn go(
        ctx: &TypeContext,
        env: &Env,
        source: &Path,
        strict: bool,
        visited: &mut TypeExprRefSet,
        ty: TypeExprRef,
    ) -> bool {
        let ty = ctx.repr(ty);
        let desc = ctx.borrow_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                if path.same(source) {
                    return false;
                }
                if !strict && is_contractive(ctx, env, path) {
                    return true;
                }
                let path = path.clone();
                let args = args.clone();
                drop(desc);

                if !visited.insert(ty) {
                    return true;
                }

                if let Some(expanded) = try_expand_head(ctx, env, ty) {
                    let expanded = ctx.repr(expanded);
                    if expanded != ty {
                        return go(ctx, env, source, strict, visited, expanded);
                    }
                }

                let params = lookup_type_decl_for_path(ctx, env, &path)
                    .map(|decl| decl.type_params.clone())
                    .unwrap_or_else(|| args.to_vec());
                for (param, arg) in params.iter().zip(args.iter()) {
                    let strict = strict || !btype::is_tvar(ctx, ctx.repr(*param));
                    if !go(ctx, env, source, strict, visited, *arg) {
                        return false;
                    }
                }
                true
            }
            _ => {
                drop(desc);
                if !strict {
                    return true;
                }
                if !visited.insert(ty) {
                    return true;
                }
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                children
                    .into_iter()
                    .all(|child| go(ctx, env, source, true, visited, child))
            }
        }
    }

    let mut visited = TypeExprRefSet::new();
    go(ctx, env, source, false, &mut visited, ty)
}

// ============================================================================
// Pattern compatibility (OCaml `mcomp`, compiler/ml/ctype.ml:1729-1964)
// ============================================================================

/// OCaml `in_current_module` (compiler/ml/ctype.ml:243-245).
fn in_current_module(path: &Path) -> bool {
    matches!(path, Path::Pident(_))
}

/// OCaml `non_aliasable` (compiler/ml/ctype.ml:1729-1731).
fn non_aliasable(path: &Path, decl: &super::TypeDeclaration) -> bool {
    in_current_module(path) && decl.type_newtype_level.is_none()
}

/// OCaml `Btype.is_datatype`.
fn is_datatype(decl: &super::TypeDeclaration) -> bool {
    matches!(
        decl.type_kind,
        super::TypeKind::TypeRecord(..)
            | super::TypeKind::TypeVariant(..)
            | super::TypeKind::TypeOpen
    )
}

/// OCaml `expands_to_datatype` (compiler/ml/ctype.ml:1745-1754).
fn expands_to_datatype(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    let ty = ctx.repr(ty);
    let path = match &*ctx.borrow_desc(ty) {
        TypeDesc::Tconstr { path, .. } => path.clone(),
        _ => return false,
    };
    let Some(decl) = lookup_type_decl_for_path(ctx, env, &path) else {
        return false;
    };
    if is_datatype(&decl) {
        return true;
    }
    drop(decl);
    match try_expand_head_with_mode(ctx, env, ty, ExpandHeadMode::General) {
        Some(expanded) => expands_to_datatype(ctx, env, expanded),
        None => false,
    }
}

/// OCaml `Types.same_record_representation` (compiler/ml/types.ml:303-315).
fn same_record_representation(
    left: &super::decl::RecordRepresentation,
    right: &super::decl::RecordRepresentation,
) -> bool {
    use super::decl::RecordRepresentation as R;
    match (left, right) {
        (R::RecordRegular, R::RecordRegular) | (R::RecordExtension, R::RecordExtension) => true,
        (R::RecordInlined { name: left, .. }, R::RecordInlined { name: right, .. }) => {
            left == right
        }
        (R::RecordUnboxed(left), R::RecordUnboxed(right)) => left == right,
        _ => false,
    }
}

/// `univar_pairs` entry: each univar is paired with a shared slot (OCaml's
/// `type_expr option ref`).
type UnivarPairEntry = (Vec<(TypeExprRef, usize)>, Vec<(TypeExprRef, usize)>);

struct McompState {
    type_pairs: HashSet<(TypeExprRef, TypeExprRef)>,
    /// OCaml `univar_pairs`, newest entry last.
    univar_pairs: Vec<UnivarPairEntry>,
    univar_slots: Vec<Option<TypeExprRef>>,
}

fn mcomp_fail() -> TypeResult<()> {
    Err(TypeError::Unify(Vec::new()))
}

/// OCaml `mcomp env t1 t2` (compiler/ml/ctype.ml:1964): succeeds when `t1`
/// and `t2` might be equal under some instantiation of abstract types.
fn mcomp(ctx: &TypeContext, env: &Env, t1: TypeExprRef, t2: TypeExprRef) -> TypeResult<()> {
    let mut state = McompState {
        type_pairs: HashSet::new(),
        univar_pairs: Vec::new(),
        univar_slots: Vec::new(),
    };
    mcomp_rec(ctx, env, &mut state, t1, t2)
}

fn mcomp_rec(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    if t1 == t2 {
        return Ok(());
    }
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }
    {
        let d1 = ctx.borrow_desc(t1);
        let d2 = ctx.borrow_desc(t2);
        match (&*d1, &*d2) {
            (TypeDesc::Tvar(..), _) | (_, TypeDesc::Tvar(..)) => return Ok(()),
            (
                TypeDesc::Tconstr {
                    path: p1, args: a1, ..
                },
                TypeDesc::Tconstr {
                    path: p2, args: a2, ..
                },
            ) if a1.is_empty() && a2.is_empty() && p1.same(p2) => return Ok(()),
            _ => {}
        }
    }
    let t1p = ctx.repr(expand_head_opt(ctx, env, t1));
    let t2p = ctx.repr(expand_head_opt(ctx, env, t2));
    if t1p == t2p {
        return Ok(());
    }
    if !state.type_pairs.insert((t1p, t2p)) {
        return Ok(());
    }
    let d1 = ctx.get_desc(t1p).into_desc();
    let d2 = ctx.get_desc(t2p).into_desc();
    match (&d1, &d2) {
        (TypeDesc::Tvar(..), TypeDesc::Tvar(..)) => {
            panic!("Ctype.mcomp: unexpected pair of type variables")
        }
        (
            TypeDesc::Tarrow {
                args: params1,
                ret: ret1,
            },
            TypeDesc::Tarrow {
                args: params2,
                ret: ret2,
            },
        ) if params1.len() == params2.len()
            && params1.iter().zip(params2.iter()).all(|(a1, a2)| {
                a1.label().same_label(a2.label())
                    || !(a1.label().is_optional() || a2.label().is_optional())
            }) =>
        {
            for (a1, a2) in params1.iter().zip(params2.iter()) {
                mcomp_rec(ctx, env, state, a1.typ, a2.typ)?;
            }
            mcomp_rec(ctx, env, state, *ret1, *ret2)
        }
        (TypeDesc::Ttuple(tl1), TypeDesc::Ttuple(tl2)) => mcomp_list(ctx, env, state, tl1, tl2),
        (
            TypeDesc::Tconstr {
                path: p1,
                args: tl1,
                ..
            },
            TypeDesc::Tconstr {
                path: p2,
                args: tl2,
                ..
            },
        ) => mcomp_type_decl(ctx, env, state, p1, p2, tl1, tl2),
        (TypeDesc::Tconstr { path, .. }, _) | (_, TypeDesc::Tconstr { path, .. }) => {
            match lookup_type_decl_for_path(ctx, env, path) {
                Some(decl) if non_aliasable(path, &decl) || is_datatype(&decl) => mcomp_fail(),
                _ => Ok(()),
            }
        }
        (TypeDesc::Tpackage { .. }, TypeDesc::Tpackage { .. }) => Ok(()),
        (TypeDesc::Tvariant(row1), TypeDesc::Tvariant(row2)) => {
            mcomp_row(ctx, env, state, row1, row2)
        }
        (TypeDesc::Tobject { fields: fi1 }, TypeDesc::Tobject { fields: fi2 }) => {
            mcomp_fields(ctx, env, state, *fi1, *fi2)
        }
        (TypeDesc::Tfield { .. }, TypeDesc::Tfield { .. }) => {
            mcomp_fields(ctx, env, state, t1p, t2p)
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => Ok(()),
        (TypeDesc::Tpoly { body: b1, vars: v1 }, TypeDesc::Tpoly { body: b2, vars: v2 })
            if v1.is_empty() && v2.is_empty() =>
        {
            mcomp_rec(ctx, env, state, *b1, *b2)
        }
        (TypeDesc::Tpoly { body: b1, vars: v1 }, TypeDesc::Tpoly { body: b2, vars: v2 }) => {
            mcomp_enter_poly(ctx, env, state, *b1, v1, *b2, v2)
        }
        (TypeDesc::Tunivar(..), TypeDesc::Tunivar(..)) => mcomp_unify_univar(ctx, state, t1p, t2p),
        _ => mcomp_fail(),
    }
}

/// OCaml `get_univar_family` (compiler/ml/ctype.ml:1517-1528).
fn mcomp_univar_family(
    ctx: &TypeContext,
    pairs: &[UnivarPairEntry],
    univars: &[TypeExprRef],
) -> HashSet<TypeExprRef> {
    let mut family = HashSet::new();
    if univars.is_empty() {
        return family;
    }
    family.extend(univars.iter().copied());
    for (cl1, cl2) in pairs.iter().rev() {
        if !cl2.is_empty() && cl1.iter().any(|(t1, _)| family.contains(&ctx.repr(*t1))) {
            family.extend(cl2.iter().map(|(t, _)| ctx.repr(*t)));
        }
    }
    family
}

/// OCaml `univars_escape` (compiler/ml/ctype.ml:1531-1558).
fn mcomp_univars_escape(
    ctx: &TypeContext,
    env: &Env,
    pairs: &[UnivarPairEntry],
    vl: &[TypeExprRef],
    body: TypeExprRef,
    vars: &[TypeExprRef],
) -> bool {
    fn occur(
        ctx: &TypeContext,
        env: &Env,
        family: &HashSet<TypeExprRef>,
        visited: &mut HashSet<TypeExprRef>,
        t: TypeExprRef,
    ) -> bool {
        let t = ctx.repr(t);
        if !visited.insert(t) {
            return false;
        }
        let desc = ctx.get_desc(t).into_desc();
        match desc {
            TypeDesc::Tpoly { body, vars } => {
                if vars.iter().any(|v| family.contains(&ctx.repr(*v))) {
                    false
                } else {
                    occur(ctx, env, family, visited, body)
                }
            }
            TypeDesc::Tunivar(..) => family.contains(&t),
            TypeDesc::Tconstr { args, .. } if args.is_empty() => false,
            TypeDesc::Tconstr { path, args, .. } => {
                match lookup_type_decl_for_path(ctx, env, &path).map(|d| d.into_owned()) {
                    Some(td) => {
                        if td.type_variance.len() != args.len() {
                            panic!("Ctype.univars_escape: arity mismatch in List.iter2");
                        }
                        args.iter().zip(td.type_variance.iter()).any(|(&arg, v)| {
                            (v.mem(VarianceFlag::MayPos) || v.mem(VarianceFlag::MayNeg))
                                && occur(ctx, env, family, visited, arg)
                        })
                    }
                    None => args
                        .iter()
                        .any(|&arg| occur(ctx, env, family, visited, arg)),
                }
            }
            _ => {
                let mut children = Vec::new();
                iter_type_expr(ctx, t, |c| children.push(c));
                children
                    .into_iter()
                    .any(|c| occur(ctx, env, family, visited, c))
            }
        }
    }
    let family = mcomp_univar_family(ctx, pairs, vl);
    let mut visited = HashSet::new();
    // `newty (Tpoly (t, tl))`: the fresh wrapper is visited first.
    if vars.iter().any(|v| family.contains(&ctx.repr(*v))) {
        return false;
    }
    occur(ctx, env, &family, &mut visited, body)
}

/// OCaml `enter_poly` (compiler/ml/ctype.ml:1561-1584) specialised to `mcomp`.
fn mcomp_enter_poly(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    body1: TypeExprRef,
    vars1: &[TypeExprRef],
    body2: TypeExprRef,
    vars2: &[TypeExprRef],
) -> TypeResult<()> {
    let Some((tl1, tl2)) =
        enter_poly_univars(ctx, env, &state.univar_pairs, body1, vars1, body2, vars2)
    else {
        return mcomp_fail();
    };
    let new_slot = |state: &mut McompState| {
        state.univar_slots.push(None);
        state.univar_slots.len() - 1
    };
    let cl1: Vec<_> = tl1.iter().map(|&t| (t, new_slot(state))).collect();
    let cl2: Vec<_> = tl2.iter().map(|&t| (t, new_slot(state))).collect();
    let saved = state.univar_pairs.len();
    // OCaml: `(cl1, cl2) :: (cl2, cl1) :: old_univars` (newest last here).
    state.univar_pairs.push((cl2.clone(), cl1.clone()));
    state.univar_pairs.push((cl1, cl2));
    let result = mcomp_rec(ctx, env, state, body1, body2);
    state.univar_pairs.truncate(saved);
    result
}

/// OCaml `enter_poly` (compiler/ml/ctype.ml:1561-1584) escape check, shared
/// by `mcomp` and `unify`. Returns the represented `(tl1, tl2)`, or `None`
/// when a univar would escape.
fn enter_poly_univars(
    ctx: &TypeContext,
    env: &Env,
    univar_pairs: &[UnivarPairEntry],
    body1: TypeExprRef,
    vars1: &[TypeExprRef],
    body2: TypeExprRef,
    vars2: &[TypeExprRef],
) -> Option<(Vec<TypeExprRef>, Vec<TypeExprRef>)> {
    let known: HashSet<TypeExprRef> = univar_pairs
        .iter()
        .flat_map(|(cl, _)| cl.iter().map(|(t, _)| ctx.repr(*t)))
        .collect();
    let tl1: Vec<_> = vars1.iter().map(|&t| ctx.repr(t)).collect();
    let tl2: Vec<_> = vars2.iter().map(|&t| ctx.repr(t)).collect();
    let escapes = (tl1.iter().any(|t| known.contains(t))
        && mcomp_univars_escape(ctx, env, univar_pairs, &tl1, body2, &tl2))
        || (tl2.iter().any(|t| known.contains(t))
            && mcomp_univars_escape(ctx, env, univar_pairs, &tl2, body1, &tl1));
    (!escapes).then_some((tl1, tl2))
}

/// OCaml `unify_univar` (compiler/ml/ctype.ml:1449-1464), shared by `mcomp`
/// and `unify`. Returns whether `t1` and `t2` are bound to each other.
fn univars_unify(
    ctx: &TypeContext,
    univar_pairs: &[UnivarPairEntry],
    univar_slots: &mut [Option<TypeExprRef>],
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> bool {
    for (cl1, cl2) in univar_pairs.iter().rev() {
        let r1 = cl1
            .iter()
            .find(|(t, _)| ctx.repr(*t) == t1)
            .map(|(_, r)| *r);
        let r2 = cl2
            .iter()
            .find(|(t, _)| ctx.repr(*t) == t2)
            .map(|(_, r)| *r);
        match (r1, r2) {
            (Some(r1), Some(_)) if univar_slots[r1].is_some_and(|t| ctx.repr(t) == t2) => {
                return true;
            }
            (Some(r1), Some(r2)) if univar_slots[r1].is_none() && univar_slots[r2].is_none() => {
                univar_slots[r1] = Some(t2);
                univar_slots[r2] = Some(t1);
                return true;
            }
            (None, None) => continue,
            _ => return false,
        }
    }
    false
}

/// OCaml `unify_univar` (compiler/ml/ctype.ml:1449-1464) for `mcomp`.
fn mcomp_unify_univar(
    ctx: &TypeContext,
    state: &mut McompState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    if univars_unify(ctx, &state.univar_pairs, &mut state.univar_slots, t1, t2) {
        Ok(())
    } else {
        mcomp_fail()
    }
}

/// OCaml `unify_univar` (ctype.ml) over the unifier's `univar_pairs`.
fn unify_univar(
    ctx: &TypeContext,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    if univars_unify(ctx, &state.univar_pairs, &mut state.univar_slots, t1, t2) {
        Ok(())
    } else {
        Err(TypeError::Unify(Vec::new()))
    }
}

/// OCaml `enter_poly env univar_pairs t1 tl1 t2 tl2 (unify env)`.
fn unify_enter_poly(
    ctx: &TypeContext,
    state: &mut UnifyState,
    body1: TypeExprRef,
    vars1: &[TypeExprRef],
    body2: TypeExprRef,
    vars2: &[TypeExprRef],
) -> TypeResult<()> {
    let empty_env;
    let env = match state.env() {
        Some(env) => env,
        None => {
            empty_env = Env::empty();
            &empty_env
        }
    };
    let Some((tl1, tl2)) =
        enter_poly_univars(ctx, env, &state.univar_pairs, body1, vars1, body2, vars2)
    else {
        return Err(TypeError::Unify(Vec::new()));
    };
    let saved_slots = state.univar_slots.len();
    let new_slot = |state: &mut UnifyState| {
        state.univar_slots.push(None);
        state.univar_slots.len() - 1
    };
    let cl1: Vec<_> = tl1.iter().map(|&t| (t, new_slot(state))).collect();
    let cl2: Vec<_> = tl2.iter().map(|&t| (t, new_slot(state))).collect();
    let saved = state.univar_pairs.len();
    // OCaml: `(cl1, cl2) :: (cl2, cl1) :: old_univars` (newest last here).
    state.univar_pairs.push((cl2.clone(), cl1.clone()));
    state.univar_pairs.push((cl1, cl2));
    let result = unify(ctx, state, body1, body2);
    state.univar_pairs.truncate(saved);
    state.univar_slots.truncate(saved_slots);
    result
}

fn mcomp_list(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    tl1: &[TypeExprRef],
    tl2: &[TypeExprRef],
) -> TypeResult<()> {
    if tl1.len() != tl2.len() {
        return mcomp_fail();
    }
    for (&t1, &t2) in tl1.iter().zip(tl2.iter()) {
        mcomp_rec(ctx, env, state, t1, t2)?;
    }
    Ok(())
}

fn object_row_of_fields(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let mut current = ctx.repr(ty);
    loop {
        let next = match &*ctx.borrow_desc(current) {
            TypeDesc::Tfield { rest, .. } => *rest,
            _ => return current,
        };
        current = ctx.repr(next);
    }
}

fn mcomp_fields(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeResult<()> {
    let concrete = |ty| {
        !matches!(
            &*ctx.borrow_desc(object_row_of_fields(ctx, ty)),
            TypeDesc::Tvar(..)
        )
    };
    if !(concrete(ty1) && concrete(ty2)) {
        panic!("Ctype.mcomp_fields: non-concrete object");
    }
    let (fields2, rest2) = flatten_fields(ctx, ty2);
    let (fields1, rest1) = flatten_fields(ctx, ty1);
    let (pairs, miss1, miss2) = associate_fields(fields1, fields2);
    mcomp_rec(ctx, env, state, rest1, rest2)?;
    let row_is_nil = |ty| {
        matches!(
            &*ctx.borrow_desc(object_row_of_fields(ctx, ty)),
            TypeDesc::Tnil
        )
    };
    if (!miss1.is_empty() && row_is_nil(ty2)) || (!miss2.is_empty() && row_is_nil(ty1)) {
        return mcomp_fail();
    }
    for (f1, f2) in pairs {
        mcomp_rec(ctx, env, state, f1.typ, f2.typ)?;
    }
    Ok(())
}

fn mcomp_row(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    row1: &RowDesc,
    row2: &RowDesc,
) -> TypeResult<()> {
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);
    let (r1, r2, pairs) = merge_row_fields(&row1.row_fields, &row2.row_fields);
    let cannot_erase =
        |f: &RowField| matches!(btype::row_field_repr(ctx, f), RowField::Rpresent(_));
    if (row1.row_closed && r2.iter().any(|(_, f)| cannot_erase(f)))
        || (row2.row_closed && r1.iter().any(|(_, f)| cannot_erase(f)))
    {
        return mcomp_fail();
    }
    let pairs: Vec<(RowField, RowField)> = pairs
        .into_iter()
        .map(|(_, f1, f2)| {
            (
                btype::row_field_repr(ctx, f1),
                btype::row_field_repr(ctx, f2),
            )
        })
        .collect();
    for (f1, f2) in pairs {
        match (&f1, &f2) {
            (RowField::Rpresent(None), RowField::Rpresent(Some(_)) | RowField::Rabsent)
            | (RowField::Rpresent(Some(_)), RowField::Rpresent(None) | RowField::Rabsent)
            | (RowField::Rabsent, RowField::Rpresent(_)) => return mcomp_fail(),
            (RowField::Rpresent(None), RowField::Reither { types, .. })
            | (RowField::Reither { types, .. }, RowField::Rpresent(None))
                if !types.is_empty() =>
            {
                return mcomp_fail();
            }
            (RowField::Rpresent(Some(_)), RowField::Reither { constant: true, .. })
            | (RowField::Reither { constant: true, .. }, RowField::Rpresent(Some(_))) => {
                return mcomp_fail();
            }
            (RowField::Rpresent(Some(t1)), RowField::Rpresent(Some(t2))) => {
                mcomp_rec(ctx, env, state, *t1, *t2)?;
            }
            (
                RowField::Rpresent(Some(t1)),
                RowField::Reither {
                    constant: false,
                    types,
                    ..
                },
            ) => {
                for &t2 in types {
                    mcomp_rec(ctx, env, state, *t1, t2)?;
                }
            }
            (
                RowField::Reither {
                    constant: false,
                    types,
                    ..
                },
                RowField::Rpresent(Some(t2)),
            ) => {
                for &t1 in types {
                    mcomp_rec(ctx, env, state, *t2, t1)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn mcomp_type_decl(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    p1: &Path,
    p2: &Path,
    tl1: &[TypeExprRef],
    tl2: &[TypeExprRef],
) -> TypeResult<()> {
    let Some(decl) = lookup_type_decl_for_path(ctx, env, p1).map(|d| d.into_owned()) else {
        return Ok(());
    };
    let Some(decl2) = lookup_type_decl_for_path(ctx, env, p2).map(|d| d.into_owned()) else {
        return Ok(());
    };
    // compatible_paths (compiler/ml/ctype.ml:1743) is `Path.same`.
    if p1.same(p2) {
        let inj: Vec<bool> = if decl.type_variance.len() == tl1.len() {
            decl.type_variance
                .iter()
                .map(|v| v.mem(VarianceFlag::Inj))
                .collect()
        } else {
            vec![false; tl1.len()]
        };
        for (i, (&t1, &t2)) in inj.into_iter().zip(tl1.iter().zip(tl2.iter())) {
            if i {
                mcomp_rec(ctx, env, state, t1, t2)?;
            }
        }
        return Ok(());
    }
    if non_aliasable(p1, &decl) && non_aliasable(p2, &decl2) {
        return mcomp_fail();
    }
    use super::TypeKind as K;
    match (&decl.type_kind, &decl2.type_kind) {
        (K::TypeRecord(lst, r), K::TypeRecord(lst2, r2)) if same_record_representation(r, r2) => {
            mcomp_list(ctx, env, state, tl1, tl2)?;
            mcomp_record_description(ctx, env, state, lst, lst2)
        }
        (K::TypeVariant(v1, _), K::TypeVariant(v2, _)) => {
            mcomp_list(ctx, env, state, tl1, tl2)?;
            mcomp_variant_description(ctx, env, state, v1, v2)
        }
        (K::TypeOpen, K::TypeOpen) => mcomp_list(ctx, env, state, tl1, tl2),
        (K::TypeAbstract, K::TypeAbstract) => Ok(()),
        (K::TypeAbstract, _) if !non_aliasable(p1, &decl) => Ok(()),
        (_, K::TypeAbstract) if !non_aliasable(p2, &decl2) => Ok(()),
        _ => mcomp_fail(),
    }
}

fn mcomp_variant_description(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    xs: &[super::decl::ConstructorDeclaration],
    ys: &[super::decl::ConstructorDeclaration],
) -> TypeResult<()> {
    use super::decl::ConstructorArguments as A;
    for (c1, c2) in xs.iter().zip(ys.iter()) {
        match (c1.cd_res, c2.cd_res) {
            (None, None) => {}
            (Some(t), Some(t2)) => mcomp_rec(ctx, env, state, t, t2)?,
            _ => return mcomp_fail(),
        }
        match (&c1.cd_args, &c2.cd_args) {
            (A::CstrTuple(l1), A::CstrTuple(l2)) => mcomp_list(ctx, env, state, l1, l2)?,
            (A::CstrRecord(l1), A::CstrRecord(l2)) => {
                mcomp_record_description(ctx, env, state, l1, l2)?
            }
            _ => return mcomp_fail(),
        }
        if c1.cd_id.name() != c2.cd_id.name() {
            return mcomp_fail();
        }
    }
    if xs.len() != ys.len() {
        return mcomp_fail();
    }
    Ok(())
}

fn mcomp_record_description(
    ctx: &TypeContext,
    env: &Env,
    state: &mut McompState,
    xs: &[LabelDeclaration],
    ys: &[LabelDeclaration],
) -> TypeResult<()> {
    for (l1, l2) in xs.iter().zip(ys.iter()) {
        mcomp_rec(ctx, env, state, l1.ld_type, l2.ld_type)?;
        if !(l1.ld_id.name() == l2.ld_id.name()
            && l1.ld_mutable == l2.ld_mutable
            && l1.ld_optional == l2.ld_optional)
        {
            return mcomp_fail();
        }
    }
    if xs.len() != ys.len() {
        return mcomp_fail();
    }
    Ok(())
}

/// OCaml `unify3`'s same-path constructor case (compiler/ml/ctype.ml:2218-2245):
/// argument unification depends on the unification mode, equation
/// generation, and injectivity.
fn unify_same_path_constructor_args(
    ctx: &TypeContext,
    state: &mut UnifyState,
    t1_expanded: TypeExprRef,
    t1: TypeExprRef,
    t2: TypeExprRef,
    path: &Path,
    pairs: Vec<(TypeExprRef, TypeExprRef)>,
) -> TypeResult<()> {
    if state.mode == UnifyMode::Expression || !state.generate_equations {
        for (a, b) in pairs {
            unify(ctx, state, a, b)?;
        }
        return Ok(());
    }
    if state.assume_injective {
        let saved = (state.mode, state.generate_equations, state.assume_injective);
        state.mode = UnifyMode::Pattern;
        state.generate_equations = true;
        state.assume_injective = false;
        let result = pairs
            .into_iter()
            .try_for_each(|(a, b)| unify(ctx, state, a, b));
        (state.mode, state.generate_equations, state.assume_injective) = saved;
        return result;
    }
    let datatype = match state.env() {
        Some(env) => [t1_expanded, t1, t2]
            .into_iter()
            .any(|ty| expands_to_datatype(ctx, env, ty)),
        None => false,
    };
    if in_current_module(path) || datatype {
        for (a, b) in pairs {
            unify(ctx, state, a, b)?;
        }
        return Ok(());
    }
    let inj: Vec<bool> = match state
        .env()
        .and_then(|env| lookup_type_decl_for_path(ctx, env, path).map(|d| d.into_owned()))
    {
        Some(decl) => {
            if decl.type_variance.len() != pairs.len() {
                panic!("Ctype.unify3: variance arity mismatch in List.iter2");
            }
            decl.type_variance
                .iter()
                .map(|v| v.mem(VarianceFlag::Inj))
                .collect()
        }
        None => vec![false; pairs.len()],
    };
    for (injective, (a, b)) in inj.into_iter().zip(pairs) {
        if injective {
            unify(ctx, state, a, b)?;
            continue;
        }
        let saved = (state.mode, state.generate_equations, state.assume_injective);
        state.mode = UnifyMode::Pattern;
        state.generate_equations = false;
        state.assume_injective = false;
        let snap = ctx.snapshot_type_state();
        let result = unify(ctx, state, a, b);
        let result = match result {
            Err(TypeError::Unify(_)) => {
                ctx.restore_type_state(snap);
                reify_in_unify_state(ctx, state, a)
                    .and_then(|()| reify_in_unify_state(ctx, state, b))
            }
            other => {
                drop(snap);
                other
            }
        };
        (state.mode, state.generate_equations, state.assume_injective) = saved;
        result?;
    }
    Ok(())
}

/// OCaml `reify env t` using the unifier's environment and newtype level.
fn reify_in_unify_state(
    ctx: &TypeContext,
    state: &mut UnifyState,
    ty: TypeExprRef,
) -> TypeResult<()> {
    let Some(newtype_level) = state.newtype_level else {
        panic!("Ctype.reify: get_newtype_level called outside pattern unification");
    };
    match state.env_mut() {
        Some(env) => reify(ctx, env, newtype_level, ty),
        None => Ok(()),
    }
}

/// OCaml `unify3` pattern-mode constructor mismatch
/// (compiler/ml/ctype.ml:2266-2269): reify both sides and, when generating
/// equations, accept the pair if `mcomp` finds it compatible.
fn unify_pattern_constructor_mismatch(
    ctx: &TypeContext,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    reify_in_unify_state(ctx, state, t1)?;
    reify_in_unify_state(ctx, state, t2)?;
    if state.generate_equations {
        // ctype.ml:2266-2269: `mcomp` raises `Unify []`; the enclosing
        // `unify` adds the pair.
        let Some(env) = state.env() else {
            return Err(TypeError::Unify(vec![]));
        };
        if mcomp(ctx, env, t1, t2).is_err() {
            return Err(TypeError::Unify(vec![]));
        }
    }
    Ok(())
}

fn add_gadt_equation(
    ctx: &TypeContext,
    env: &mut Env,
    newtype_level: Option<i32>,
    source_path: &Path,
    destination: TypeExprRef,
) -> TypeResult<()> {
    if !local_non_recursive_abbrev(ctx, env, source_path, destination) {
        return Ok(());
    }

    if let Some(newtype_level) = newtype_level {
        reify(ctx, env, newtype_level, destination)?;
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
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_representation: super::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    };

    // Add as a local constraint
    env.add_local_constraint(source_path.clone(), decl);
    // OCaml add_gadt_equation calls cleanup_abbrev after installing the new
    // local constraint so future expansions observe the updated equation.
    ctx.clear_abbrev_memos();
    Ok(())
}

fn reified_type_decl(newtype_level: i32) -> super::TypeDeclaration {
    super::TypeDeclaration {
        type_params: vec![],
        type_arity: 0,
        type_kind: super::TypeKind::TypeAbstract,
        type_private: super::PrivateFlag::Public,
        type_manifest: None,
        type_variance: vec![],
        type_newtype_level: Some((newtype_level, newtype_level)),
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: false,
        type_representation: super::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    }
}

fn create_reified_constr(
    ctx: &TypeContext,
    env: &mut Env,
    newtype_level: i32,
    level: i32,
    name: Option<String>,
) -> TypeExprRef {
    let prefix = name.map_or_else(|| "$".to_string(), |name| format!("$'{name}"));
    let name = ctx.next_reified_abstract_name(&prefix);
    let ident = ctx.create_ident(&name);
    let decl = reified_type_decl(newtype_level);
    env.add_type(ident, decl);
    let path = Path::Pident(ident);
    let abbrev = ctx.alloc_abbrev(AbbrevMemo::Mnil);
    ctx.alloc_type_at_level(
        TypeDesc::Tconstr {
            path,
            args: vec![].into(),
            abbrev,
            path_block: crate::types::type_expr::PathBlock::OWN,
        },
        level,
    )
}

/// Match OCaml `Ctype.reify`: replace free RHS variables in a local GADT
/// equation with fresh local abstract types before installing the constraint.
fn reify(ctx: &TypeContext, env: &mut Env, newtype_level: i32, ty: TypeExprRef) -> TypeResult<()> {
    fn iterator(
        ctx: &TypeContext,
        env: &mut Env,
        newtype_level: i32,
        visited: &mut TypeExprRefSet,
        ty: TypeExprRef,
    ) -> TypeResult<()> {
        let ty = ctx.repr(ty);
        if !visited.insert(ty) {
            return Ok(());
        }

        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvar(name, ..) => {
                let name = name.clone();
                let level = ctx.get_level(ty);
                drop(desc);
                let reified = create_reified_constr(ctx, env, newtype_level, level, name);
                link_type(ctx, ty, reified);
                if level < newtype_level {
                    let rhs = ctx.alloc_type_at_level(
                        TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                        level,
                    );
                    return Err(TypeError::Unify(vec![(reified, rhs)]));
                }
                Ok(())
            }
            // compiler/ml/ctype.ml:1698-1714: non-static rows get a fresh
            // abstract row variable (or recurse into the fixed row_more), then
            // only the row's field types are visited through `iter_row`.
            TypeDesc::Tvariant(row) => {
                let row = super::btype::row_repr(ctx, row);
                drop(desc);
                if !super::btype::static_row(ctx, &row) {
                    if row.row_fixed {
                        iterator(
                            ctx,
                            env,
                            newtype_level,
                            visited,
                            super::btype::row_more(ctx, &row),
                        )?;
                    } else {
                        let m = ctx.repr(row.row_more);
                        let TypeDesc::Tvar(name, ..) = ctx.get_desc(m).into_desc() else {
                            panic!("Ctype.reify: non-variable row_more in a non-static row");
                        };
                        let m_level = ctx.get_level(m);
                        let t = create_reified_constr(ctx, env, newtype_level, m_level, name);
                        let fixed_row = RowDesc {
                            row_fields: Default::default(),
                            row_fixed: true,
                            row_more: t,
                            ..row.clone()
                        };
                        let fixed = ctx
                            .alloc_type_at_level(TypeDesc::Tvariant(Box::new(fixed_row)), m_level);
                        link_type(ctx, m, fixed);
                        if m_level < newtype_level {
                            let rhs = ctx.alloc_type_at_level(
                                TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                                m_level,
                            );
                            return Err(TypeError::Unify(vec![(t, rhs)]));
                        }
                    }
                }
                let mut children = Vec::new();
                super::btype::iter_row(ctx, &row, |child| children.push(child));
                for child in children {
                    iterator(ctx, env, newtype_level, visited, child)?;
                }
                Ok(())
            }
            // compiler/ml/ctype.ml:1715-1716.
            TypeDesc::Tconstr { path, .. } if path.head_name().starts_with('#') => {
                drop(desc);
                let expanded = full_expand(ctx, env, ty);
                let mut children = Vec::new();
                iter_type_expr(ctx, expanded, |child| children.push(child));
                for child in children {
                    iterator(ctx, env, newtype_level, visited, child)?;
                }
                Ok(())
            }
            _ => {
                drop(desc);
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                for child in children {
                    iterator(ctx, env, newtype_level, visited, child)?;
                }
                Ok(())
            }
        }
    }

    let mut visited = TypeExprRefSet::new();
    iterator(ctx, env, newtype_level, &mut visited, ty)
}

// ============================================================================
// Occurs Check
// ============================================================================

/// Check if a type variable occurs in another type.
///
/// This is the occurs check that prevents infinite types.
/// Returns `true` if `needle` occurs in `haystack`.
/// Whether `needle` is reachable from `haystack`, searched without a visited
/// set within `budget` nodes: `Some(found)` when the search finished, `None`
/// when the budget ran out (which also bounds cycles and repeatedly visited
/// shared nodes). With `shallow_rows`, object and variant nodes are not
/// entered (the `occurs` check); otherwise every child is.
fn reaches_quick(
    ctx: &TypeContext,
    needle: TypeExprRef,
    haystack: TypeExprRef,
    shallow_rows: bool,
    budget: &mut u32,
) -> Option<bool> {
    let haystack = ctx.repr(haystack);
    if needle == haystack {
        return Some(true);
    }
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let desc = ctx.borrow_desc(haystack);
    let mut search = |children: &mut dyn Iterator<Item = TypeExprRef>| {
        for child in children {
            if reaches_quick(ctx, needle, child, shallow_rows, budget)? {
                return Some(true);
            }
        }
        Some(false)
    };
    match &*desc {
        TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_) if shallow_rows => Some(false),
        TypeDesc::Tvar(..) | TypeDesc::Tnil | TypeDesc::Tunivar(..) => Some(false),
        TypeDesc::Tconstr { args, .. } | TypeDesc::Ttuple(args) => {
            search(&mut args.iter().copied())
        }
        TypeDesc::Tarrow { args, ret } => {
            search(&mut args.iter().map(|arg| arg.typ).chain(std::iter::once(*ret)))
        }
        _ => {
            drop(desc);
            let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
            iter_type_expr(ctx, haystack, |child| children.push(child));
            search(&mut children.into_iter())
        }
    }
}

pub fn occurs(ctx: &TypeContext, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    fn occurs_rec(
        ctx: &TypeContext,
        needle: TypeExprRef,
        haystack: TypeExprRef,
        visited: &mut TypeExprRefSet,
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
            let desc = ctx.borrow_desc(haystack);
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
    let mut budget = 256;
    if let Some(found) = reaches_quick(ctx, needle, haystack, true, &mut budget) {
        return found;
    }
    let mut visited = TypeExprRefSet::new();
    occurs_rec(ctx, needle, haystack, &mut visited)
}

/// Whether the `occur_univar` walk from `ty` certainly meets no `Tunivar`.
///
/// Visits a superset of that walk's nodes (every constructor argument, where
/// the walk skips invariant ones) without its visited set, variance lookups
/// or argument copies, and gives up (`false`) on reaching a `Tunivar` or
/// `Tpoly` or after `budget` nodes, which also bounds cycles and sharing.
fn surely_univar_free(ctx: &TypeContext, ty: TypeExprRef, budget: &mut u32) -> bool {
    let ty = ctx.repr(ty);
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Tvar(..) | TypeDesc::Tnil => true,
        TypeDesc::Tunivar(..) | TypeDesc::Tpoly { .. } => false,
        TypeDesc::Tconstr { args, .. } | TypeDesc::Ttuple(args) => {
            args.iter().all(|arg| surely_univar_free(ctx, *arg, budget))
        }
        TypeDesc::Tarrow { args, ret } => {
            args.iter()
                .all(|arg| surely_univar_free(ctx, arg.typ, budget))
                && surely_univar_free(ctx, *ret, budget)
        }
        _ => {
            drop(desc);
            let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
            iter_type_expr(ctx, ty, |child| children.push(child));
            children
                .into_iter()
                .all(|child| surely_univar_free(ctx, child, budget))
        }
    }
}

/// OCaml `occur` / `occur_rec` (compiler/ml/ctype.ml:1347-1395).
///
/// Fails when `ty0` occurs in `ty`. An occurrence found below a type
/// constructor is retried after expanding the constructor head, so
/// abbreviations such as `type t<'a> = int` do not count as recursion. In
/// pattern mode, recursion through contractive (datatype) constructors and
/// through structural nodes is allowed (`allow_recursive`).
#[derive(PartialEq, Eq)]
enum OccurMark {
    Unseen,
    OnPath,
    Done,
}

/// Visit marks of the occurs pre-pass: local nodes in an epoch-stamped
/// array indexed by node, store nodes in a set (`epoch * 2` = on the
/// current path, `epoch * 2 + 1` = fully visited).
#[derive(Default)]
struct OccurMarks {
    epoch: u32,
    local: Vec<u32>,
    store: crate::fast_hash::AHashMap<TypeExprRef, bool>,
}

impl OccurMarks {
    fn begin(&mut self) {
        self.epoch += 1;
        if self.epoch >= u32::MAX / 2 {
            self.epoch = 1;
            self.local.iter_mut().for_each(|m| *m = 0);
        }
        self.store.clear();
    }

    fn get(&self, ty: TypeExprRef) -> OccurMark {
        if ty.is_store() {
            return match self.store.get(&ty) {
                None => OccurMark::Unseen,
                Some(false) => OccurMark::OnPath,
                Some(true) => OccurMark::Done,
            };
        }
        match self.local.get(ty.index()).copied() {
            Some(m) if m == self.epoch * 2 => OccurMark::OnPath,
            Some(m) if m == self.epoch * 2 + 1 => OccurMark::Done,
            _ => OccurMark::Unseen,
        }
    }

    fn set(&mut self, ty: TypeExprRef, mark: OccurMark) {
        if ty.is_store() {
            self.store.insert(ty, mark == OccurMark::Done);
            return;
        }
        let idx = ty.index();
        if idx >= self.local.len() {
            self.local.resize((idx + 1).next_power_of_two(), 0);
        }
        self.local[idx] = self.epoch * 2 + u32::from(mark == OccurMark::Done);
    }
}

thread_local! {
    static OCCUR_MARKS: std::cell::RefCell<OccurMarks> = std::cell::RefCell::new(OccurMarks::default());
}

pub(crate) fn occur_check(
    ctx: &TypeContext,
    env: Option<&Env>,
    mode: UnifyMode,
    ty0: TypeExprRef,
    ty: TypeExprRef,
) -> TypeResult<()> {
    fn occur_rec(
        ctx: &TypeContext,
        env: Option<&Env>,
        allow_recursive: bool,
        visited: &mut Vec<TypeExprRef>,
        ty0: TypeExprRef,
        ty: TypeExprRef,
    ) -> Result<(), ()> {
        let ty = ctx.repr(ty);
        if ty == ty0 {
            return Err(());
        }
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, .. } => {
                let path = path.clone();
                drop(desc);
                if allow_recursive && env.is_some_and(|env| is_contractive(ctx, env, &path)) {
                    return Ok(());
                }
                let direct = if visited.contains(&ty) {
                    Err(())
                } else {
                    visited.push(ty);
                    let mut children = Vec::new();
                    iter_type_expr(ctx, ty, |child| children.push(child));
                    let result = children.into_iter().try_for_each(|child| {
                        occur_rec(ctx, env, allow_recursive, visited, ty0, child)
                    });
                    visited.pop();
                    result
                };
                match direct {
                    Ok(()) => Ok(()),
                    Err(()) => {
                        // `try_expand_head try_expand_once env ty`, then retry.
                        let expanded = env.and_then(|env| try_expand_head(ctx, env, ty));
                        match expanded {
                            Some(expanded) => {
                                occur_rec(ctx, env, allow_recursive, visited, ty0, expanded)
                            }
                            None => Err(()),
                        }
                    }
                }
            }
            TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_) => Ok(()),
            _ => {
                drop(desc);
                if allow_recursive || visited.contains(&ty) {
                    return Ok(());
                }
                visited.push(ty);
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                let result = children.into_iter().try_for_each(|child| {
                    occur_rec(ctx, env, allow_recursive, visited, ty0, child)
                });
                visited.pop();
                result
            }
        }
    }

    /// `occur_rec` can only fail by reaching `ty0` or by revisiting a node on
    /// its current path; when one walk over the graph (each node once,
    /// stopping where `occur_rec` stops at objects and variants) sees
    /// neither, every branch of `occur_rec` succeeds.
    fn surely_occur_free(
        ctx: &TypeContext,
        ty0: TypeExprRef,
        ty: TypeExprRef,
        marks: &mut OccurMarks,
    ) -> bool {
        let ty = ctx.repr(ty);
        if ty == ty0 {
            return false;
        }
        // Shared-store nodes never point at a compilation's own nodes, so a
        // local `ty0` cannot occur below one.
        if ty.is_store() && !ty0.is_store() {
            return true;
        }
        // Children in `iter_type_expr` order, read under one borrow; leaves
        // and the nodes `occur_rec` stops at need no bookkeeping.
        let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
        {
            let desc = ctx.borrow_desc(ty);
            match &*desc {
                TypeDesc::Tvar(..)
                | TypeDesc::Tnil
                | TypeDesc::Tunivar(..)
                | TypeDesc::Tobject { .. }
                | TypeDesc::Tvariant(_) => return true,
                TypeDesc::Tconstr { args, .. } | TypeDesc::Tpackage { args, .. }
                    if args.is_empty() =>
                {
                    return true;
                }
                TypeDesc::Tconstr { args, .. } | TypeDesc::Tpackage { args, .. } => {
                    children.extend(args.iter().copied())
                }
                TypeDesc::Ttuple(types) => children.extend(types.iter().copied()),
                TypeDesc::Tarrow { args, ret } => {
                    children.extend(args.iter().map(|arg| arg.typ));
                    children.push(*ret);
                }
                TypeDesc::Tfield { typ, rest, .. } => children.extend([*typ, *rest]),
                TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => children.push(*t),
                TypeDesc::Tpoly { body, vars } => {
                    children.push(*body);
                    children.extend(vars.iter().copied());
                }
            }
        }
        match marks.get(ty) {
            OccurMark::Done => return true,
            OccurMark::OnPath => return false,
            OccurMark::Unseen => {}
        }
        marks.set(ty, OccurMark::OnPath);
        for child in children {
            if !surely_occur_free(ctx, ty0, child, marks) {
                return false;
            }
        }
        marks.set(ty, OccurMark::Done);
        true
    }

    let allow_recursive = mode == UnifyMode::Pattern;
    let ty0 = ctx.repr(ty0);
    let free = OCCUR_MARKS.with(|marks| {
        let mut marks = marks.borrow_mut();
        marks.begin();
        surely_occur_free(ctx, ty0, ty, &mut marks)
    });
    if free {
        return Ok(());
    }
    let mut visited = Vec::new();
    occur_rec(ctx, env, allow_recursive, &mut visited, ty0, ty)
        .map_err(|()| TypeError::Unify(vec![]))
}

/// Match OCaml's `occur_univar` pass before linking a type variable.
///
/// OCaml compiler/ml/ctype.ml:1688-1724 walks the candidate type after the
/// regular occurs check. For parameterized constructors it calls
/// `Env.find_type` to read variance before deciding which arguments to visit;
/// that lookup is observable because env.ml:800-813 reaches lazy component
/// tables. Keep this as part of variable unification instead of forcing module
/// signatures from typecore call sites.
fn occur_univar(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeResult<()> {
    // The walk below can only fail on a reachable `Tunivar`, which is rare;
    // rule it out cheaply first.
    let mut budget = 256;
    if surely_univar_free(ctx, ty, &mut budget) {
        return Ok(());
    }
    fn occur_rec(
        ctx: &TypeContext,
        env: &Env,
        bound: &mut Vec<TypeExprRef>,
        visited: &mut TypeExprRefSet,
        ty: TypeExprRef,
    ) -> TypeResult<()> {
        let ty = ctx.repr(ty);
        if !visited.insert(ty) {
            return Ok(());
        }

        let desc = ctx.borrow_desc(ty);
        match &*desc {
            TypeDesc::Tunivar(..) => {
                if !bound.contains(&ty) {
                    return Err(TypeError::Unify(vec![(ty, ctx.new_var(None))]));
                }
                Ok(())
            }
            TypeDesc::Tpoly { body, vars } => {
                let body = *body;
                let vars = vars.clone();
                drop(desc);
                let old_bound_len = bound.len();
                for var in vars {
                    bound.push(ctx.repr(var));
                }
                let result = occur_rec(ctx, env, bound, visited, body);
                bound.truncate(old_bound_len);
                result
            }
            TypeDesc::Tconstr { args, .. } if args.is_empty() => Ok(()),
            TypeDesc::Tconstr { path, args, .. } => {
                let path = path.clone();
                let args: smallvec::SmallVec<[TypeExprRef; 8]> = args.iter().copied().collect();
                drop(desc);
                // OCaml compiler/ml/ctype.ml occur_univar reads only the
                // declaration's variances through `Env.find_type`, which is
                // fixed within one module scope; memoize the visit mask.
                let scope_id = env.scope_id();
                let mask = match ctx.find_occur_variance_mask(scope_id, &path) {
                    Some(mask) => mask,
                    None => {
                        let mask = lookup_type_decl_for_path(ctx, env, &path).map(|decl| {
                            // A declaration with more than 64 parameters would
                            // not fit the mask; visit every argument instead.
                            if decl.type_variance.len() > 64 {
                                return u64::MAX;
                            }
                            let mut mask = 0u64;
                            for (index, variance) in decl.type_variance.iter().enumerate() {
                                if variance.mem(VarianceFlag::MayPos)
                                    || variance.mem(VarianceFlag::MayNeg)
                                {
                                    mask |= 1 << index;
                                }
                            }
                            mask
                        });
                        ctx.register_occur_variance_mask(scope_id, &path, mask);
                        mask
                    }
                };
                if let Some(mask) = mask.filter(|mask| *mask != u64::MAX) {
                    for (index, arg) in args.iter().enumerate().take(64) {
                        if mask & (1 << index) != 0 {
                            occur_rec(ctx, env, bound, visited, *arg)?;
                        }
                    }
                    Ok(())
                } else {
                    for arg in args {
                        occur_rec(ctx, env, bound, visited, arg)?;
                    }
                    Ok(())
                }
            }
            _ => {
                drop(desc);
                let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                for child in children {
                    occur_rec(ctx, env, bound, visited, child)?;
                }
                Ok(())
            }
        }
    }

    // Univars bound by enclosing `Tpoly`s; a short stack, restored on exit.
    let mut bound = Vec::new();
    let mut visited = TypeExprRefSet::new();
    occur_rec(ctx, env, &mut bound, &mut visited, ty)
}

/// Deep occur check - follows type constructors.
pub fn deep_occur(ctx: &TypeContext, needle: TypeExprRef, haystack: TypeExprRef) -> bool {
    fn deep_occur_rec(
        ctx: &TypeContext,
        needle: TypeExprRef,
        haystack: TypeExprRef,
        visited: &mut TypeExprRefSet,
    ) -> bool {
        let haystack = ctx.repr(haystack);
        if needle == haystack {
            return true;
        }
        if !visited.insert(haystack) {
            return false;
        }

        let desc = ctx.borrow_desc(haystack);
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
    let mut budget = 256;
    if let Some(found) = reaches_quick(ctx, needle, haystack, false, &mut budget) {
        return found;
    }
    let mut visited = TypeExprRefSet::new();
    deep_occur_rec(ctx, needle, haystack, &mut visited)
}

/// Check if a type contains any Tvariant node (shallow check of Tconstr args).
/// Used to prevent identity sharing of types whose variant args would be
/// contaminated across branches (e.g. result<string, [#InvalidString]>).
pub fn type_contains_variant(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Tvariant(_) => true,
        TypeDesc::Tconstr { args, .. } => args
            .iter()
            .copied()
            .any(|arg| matches!(&*ctx.borrow_desc(ctx.repr(arg)), TypeDesc::Tvariant(_))),
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
pub fn link_type(ctx: &TypeContext, t1: TypeExprRef, t2: TypeExprRef) {
    // OCaml btype.ml:633-651 performs this mutation even for dependency
    // declaration nodes (e.g. ctype.ml:2118-2127 and record coercion). The
    // context overlays stored-node writes for this compilation; do not skip
    // the link, since later repr/instance calls must observe it.
    let t1_repr = ctx.repr(t1);
    let t2_repr = ctx.repr(t2);
    let source_name = {
        let desc = ctx.borrow_desc(t1_repr);
        match &*desc {
            TypeDesc::Tvar(name, ..) => Some(name.clone()),
            _ => None,
        }
    };
    let target_name = {
        let desc = ctx.borrow_desc(t2_repr);
        match &*desc {
            TypeDesc::Tvar(name, ..) => Some(name.clone()),
            _ => None,
        }
    };

    // Match OCaml Btype.link_type naming behavior:
    // - propagate source name to an anonymous target variable
    // - when both are named, keep source name if source level is lower
    match (source_name, target_name) {
        (Some(Some(name)), Some(None)) => {
            ctx.set_desc(
                t2_repr,
                TypeDesc::Tvar(Some(name), crate::types::type_expr::VarDescBlock::OWN),
            );
        }
        (Some(Some(name)), Some(Some(_existing))) => {
            if ctx.get_level(t1_repr) < ctx.get_level(t2_repr) {
                ctx.set_desc(
                    t2_repr,
                    TypeDesc::Tvar(Some(name), crate::types::type_expr::VarDescBlock::OWN),
                );
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
pub fn update_level(ctx: &TypeContext, level: i32, ty: TypeExprRef) {
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
pub fn update_level_expand(ctx: &TypeContext, env: &Env, level: i32, ty: TypeExprRef) {
    // Callers of this form ignore an escaping constructor, like the memoized
    // expansion in OCaml `expand_abbrev` (ctype.ml:1153-1160).
    let _ = update_level_checked(ctx, env, level, ty, &mut None, &mut None);
}

/// The tail of OCaml `unify1_var` (ctype.ml:2086-2095): link the variable,
/// then lower levels; if a constructor would escape, undo the link.
fn unify1_var_link(
    ctx: &TypeContext,
    state: &mut UnifyState,
    var: TypeExprRef,
    ty: TypeExprRef,
) -> Result<(), TypeError> {
    let level = ctx.get_level(var);
    let Some(env) = state.env() else {
        update_level(ctx, level, ty);
        link_type(ctx, var, ty);
        return Ok(());
    };
    let var_desc = ctx.get_desc(var).into_desc();
    link_type(ctx, var, ty);
    if let Err(err) = update_level_checked(ctx, env, level, ty, &mut None, &mut None) {
        ctx.set_desc(var, var_desc);
        return Err(err);
    }
    Ok(())
}

/// OCaml `update_level` (ctype.ml:615-622): first lower levels without
/// expanding parameterized constructors; if a constructor would escape its
/// scope, backtrack and retry expanding them. The error is OCaml's
/// `Unify [(ty, newvar2 level)]`.
pub(crate) fn update_level_checked(
    ctx: &TypeContext,
    env: &Env,
    level: i32,
    ty: TypeExprRef,
    pending_type_lookup_paths: &mut Option<&mut Vec<Path>>,
    pending_type_expansion_paths: &mut Option<&mut Vec<Path>>,
) -> Result<(), TypeError> {
    let ty = ctx.repr(ty);
    if ctx.get_level(ty) <= level {
        return Ok(());
    }
    let snapshot = ctx.snapshot_type_state();
    if update_level_expand_with_lookup_capture(
        ctx,
        env,
        level,
        false,
        ty,
        pending_type_lookup_paths,
        pending_type_expansion_paths,
    )
    .is_ok()
    {
        return Ok(());
    }
    ctx.restore_type_state(snapshot);
    update_level_expand_with_lookup_capture(
        ctx,
        env,
        level,
        true,
        ty,
        pending_type_lookup_paths,
        pending_type_expansion_paths,
    )
    .map_err(|escaping| TypeError::Unify(vec![(escaping, new_var_at_level(ctx, level))]))
}

/// OCaml `newvar2 level`.
fn new_var_at_level(ctx: &TypeContext, level: i32) -> TypeExprRef {
    let var = ctx.new_var(None);
    ctx.set_level(var, level);
    var
}

/// OCaml `update_level env level expand` (ctype.ml:561-613). Returns the type
/// whose constructor would escape its scope.
fn update_level_expand_with_lookup_capture(
    ctx: &TypeContext,
    env: &Env,
    level: i32,
    expand: bool,
    ty: TypeExprRef,
    pending_type_lookup_paths: &mut Option<&mut Vec<Path>>,
    pending_type_expansion_paths: &mut Option<&mut Vec<Path>>,
) -> Result<(), TypeExprRef> {
    let ty = ctx.repr(ty);
    let current = ctx.get_level(ty);

    if level < current {
        let desc = ctx.borrow_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let has_args = !args.is_empty();
                // OCaml compiler/ml/ctype.ml:695 calls `get_level env p`
                // here. Keep the same lookup side effects even when the
                // numeric result falls back to `Path.binding_time`. A path
                // rooted at a persistent unit answers with its binding time
                // without a lookup (see `get_level_with_lookup_capture`), so
                // it needs no copy unless it is recorded or expanded.
                let persistent_level = (path_root_is_persistent(path)
                    && (pending_type_lookup_paths.is_none() || !matches!(path, Path::Pdot(..))))
                .then(|| path.binding_time());
                let path_level = match persistent_level {
                    Some(path_level) => path_level,
                    None => {
                        let path = path.clone();
                        get_level_with_lookup_capture(ctx, env, &path, pending_type_lookup_paths)
                    }
                };
                // OCaml compiler/ml/ctype.ml:742-768 only requires
                // `level < get_level env p` after the outer `ty.level > level`
                // check. Generic-level constructor nodes are still eligible
                // for abbreviation expansion during `moregeneral`.
                let should_try_expand = level < path_level;
                let expansion_path = (should_try_expand && pending_type_expansion_paths.is_some())
                    .then(|| path.clone());
                drop(desc);
                // OCaml compiler/ml/ctype.ml:568-578: try to replace the
                // constructor by its expansion; a constructor that cannot be
                // expanded would escape its scope.
                if should_try_expand {
                    if let (Some(paths), Some(path)) =
                        (pending_type_expansion_paths.as_deref_mut(), expansion_path)
                    {
                        paths.push(path);
                    }
                    if let Some(expanded) = try_expand_head(ctx, env, ty) {
                        let expanded = ctx.repr(expanded);
                        if expanded != ty && !deep_occur(ctx, ty, expanded) {
                            link_type(ctx, ty, expanded);
                            // Recursively update the expansion
                            return update_level_expand_with_lookup_capture(
                                ctx,
                                env,
                                level,
                                expand,
                                expanded,
                                pending_type_lookup_paths,
                                pending_type_expansion_paths,
                            );
                        }
                    }
                }
                // OCaml ctype.ml:574-578: a constructor that cannot be
                // expanded would escape its scope.
                if should_try_expand {
                    return Err(ty);
                }
                // ctype.ml:579-585: the second pass also expands parameterized
                // constructors.
                if expand && has_args {
                    if let Some(expanded) = try_expand_head(ctx, env, ty) {
                        let expanded = ctx.repr(expanded);
                        if expanded != ty && !deep_occur(ctx, ty, expanded) {
                            link_type(ctx, ty, expanded);
                            return update_level_expand_with_lookup_capture(
                                ctx,
                                env,
                                level,
                                expand,
                                expanded,
                                pending_type_lookup_paths,
                                pending_type_expansion_paths,
                            );
                        }
                    }
                }
                ctx.set_level(ty, level);
                return update_level_children(
                    ctx,
                    env,
                    level,
                    expand,
                    ty,
                    pending_type_lookup_paths,
                    pending_type_expansion_paths,
                );
            }
            TypeDesc::Tvariant(row) => {
                let name_path = row_repr_ref(ctx, row)
                    .row_name
                    .as_ref()
                    .map(|(path, _)| path.clone());
                drop(desc);
                // OCaml compiler/ml/ctype.ml:723-730 checks the polymorphic
                // variant `row_name` path with `get_level env p` before
                // lowering the row. That call reaches Env.find_type
                // (compiler/ml/ctype.ml:666-673), so persistent alias
                // signatures force at the same point as OCaml.
                if let Some(path) = name_path
                    && level
                        < get_level_with_lookup_capture(ctx, env, &path, pending_type_lookup_paths)
                {
                    let mut row = match &*ctx.borrow_desc(ty) {
                        TypeDesc::Tvariant(row) => row_repr(ctx, row),
                        _ => unreachable!("update_level: variant descriptor changed"),
                    };
                    row.row_name = None;
                    ctx.set_desc(ty, TypeDesc::Tvariant(Box::new(row)));
                }
                ctx.set_level(ty, level);
                return update_level_children(
                    ctx,
                    env,
                    level,
                    expand,
                    ty,
                    pending_type_lookup_paths,
                    pending_type_expansion_paths,
                );
            }
            _ => {
                drop(desc);
                ctx.set_level(ty, level);
                return update_level_children(
                    ctx,
                    env,
                    level,
                    expand,
                    ty,
                    pending_type_lookup_paths,
                    pending_type_expansion_paths,
                );
            }
        }
    }
    Ok(())
}

/// `iter_type_expr (update_level env level expand) ty`.
fn update_level_children(
    ctx: &TypeContext,
    env: &Env,
    level: i32,
    expand: bool,
    ty: TypeExprRef,
    pending_type_lookup_paths: &mut Option<&mut Vec<Path>>,
    pending_type_expansion_paths: &mut Option<&mut Vec<Path>>,
) -> Result<(), TypeExprRef> {
    let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        update_level_expand_with_lookup_capture(
            ctx,
            env,
            level,
            expand,
            child,
            pending_type_lookup_paths,
            pending_type_expansion_paths,
        )?;
    }
    Ok(())
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

// ============================================================================
// Type Alias Expansion
// ============================================================================

/// Find `<module_name>.cmi` (or its uncapitalized spelling) in the load paths.
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

pub(crate) fn resolve_module_signature_through_cmi_shared(
    ctx: &TypeContext,
    load_paths: &[std::path::PathBuf],
    module_path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<Arc<super::decl::Signature>> {
    use crate::cmi::{cmi_format, sig_reader::SigReadContext};
    use crate::types::decl::{ModuleType, SignatureItem};

    if ctx.persistent_env_is_in_process() {
        return resolve_module_signature_through_persistent_env_shared(ctx, module_path, visiting);
    }

    let cache_key = module_path.name();
    if let Some((cached_path, cached_sig)) = ctx.find_resolved_module_sig(&cache_key) {
        if cached_path.same(module_path) {
            return Some(cached_sig);
        }
    }

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
            let mut sig = sig_ctx.read_signature(&cmi.cmi_sign);
            // Apply path substitution to qualify internal types with the
            // module path, matching persistent_env::load_module behavior.
            // Without this, types have bare Pident paths that cause
            // incorrect path qualification through resolve_module_lid_impl.
            crate::cmi::persistent_env::substitute_type_paths_in_sig(&sig, module_path, ctx);
            crate::cmi::persistent_env::qualify_unit_sig_decl_paths_in_place(
                &mut sig,
                module_path,
                ctx,
            );
            // Also recursively substitute submodule paths.
            crate::cmi::persistent_env::substitute_submodule_paths(&sig, module_path, ctx);
            Some(Arc::new(sig))
        }
        Path::Pdot(parent, module_name, _) => {
            let parent_sig =
                resolve_module_signature_through_cmi_shared(ctx, load_paths, parent, visiting)?;
            let mut resolved = None;
            for item in parent_sig.iter() {
                if let SignatureItem::SigModule(id, md, _) = item {
                    if id.name() == module_name {
                        resolved = match &md.md_type {
                            ModuleType::MtySignature(sig) => {
                                // Mirror OCaml Subst behavior when descending into
                                // submodules: keep parent substitutions visible.
                                crate::cmi::persistent_env::substitute_type_paths_in_child_sig(
                                    sig,
                                    parent_sig.as_ref(),
                                    parent,
                                    ctx,
                                );
                                Some(sig.clone())
                            }
                            ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                                let alias_path = md.md_type.ident_or_alias_path().unwrap();
                                resolve_module_signature_through_cmi_shared(
                                    ctx, load_paths, alias_path, visiting,
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

    if let Some(sig) = result.as_ref() {
        ctx.register_resolved_module_sig(&cache_key, module_path.clone(), sig.clone());
    }

    result
}

fn resolve_module_signature_through_persistent_env_shared(
    ctx: &TypeContext,
    module_path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<Arc<super::decl::Signature>> {
    use crate::types::decl::{ModuleType, SignatureItem};

    let cache_key = module_path.name();
    if let Some((cached_path, cached_sig)) = ctx.find_resolved_module_sig(&cache_key) {
        if cached_path.same(module_path) {
            return Some(cached_sig);
        }
    }

    if !visiting.insert(module_path.clone()) {
        return None;
    }

    let result = match module_path {
        Path::Pident(id) => {
            if !id.is_persistent() {
                return None;
            }

            // OCaml compiler/ml/env.ml:865-873 resolves persistent module
            // identifiers through find_pers_struct and then forces ps_sig.
            // In --in-process, PersistentEnv is the equivalent source of truth:
            // it can read already-published registry entries or source fallbacks,
            // but it must not fall through to disk .cmi files.
            let mut pers_env = ctx.persistent_env_clone()?;
            let ps = pers_env.find_pers_struct(id.name(), ctx)?;
            ctx.set_persistent_env(pers_env);
            Some(ps.ps_sig.clone())
        }
        Path::Pdot(parent, module_name, _) => {
            let parent_sig =
                resolve_module_signature_through_persistent_env_shared(ctx, parent, visiting)?;
            let mut resolved = None;
            for item in parent_sig.iter() {
                if let SignatureItem::SigModule(id, md, _) = item {
                    if id.name() == module_name {
                        resolved = match &md.md_type {
                            ModuleType::MtySignature(sig) => Some(sig.clone()),
                            ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                                let alias_path = md.md_type.ident_or_alias_path().unwrap();
                                resolve_module_signature_through_persistent_env_shared(
                                    ctx, alias_path, visiting,
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

    if let Some(sig) = result.as_ref() {
        ctx.register_resolved_module_sig(&cache_key, module_path.clone(), sig.clone());
    }

    result
}

fn normalize_module_path_through_components(
    ctx: &TypeContext,
    load_paths: &[std::path::PathBuf],
    module_path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<Path> {
    use crate::types::decl::{ModuleType, SignatureItem};

    if !visiting.insert(module_path.clone()) {
        return Some(module_path.clone());
    }

    let normalized_path = match module_path {
        Path::Pdot(parent, name, pos) => {
            let parent =
                normalize_module_path_through_components(ctx, load_paths, parent, visiting)
                    .unwrap_or_else(|| (**parent).clone());
            // env.ml:868-870 rebuilds the dot but keeps its suffix string.
            let _ = (name, pos);
            ctx.copy_dotted_with_prefix(module_path, std::sync::Arc::new(parent))
        }
        Path::Papply(functor, arg) => {
            let functor =
                normalize_module_path_through_components(ctx, load_paths, functor, visiting)
                    .unwrap_or_else(|| (**functor).clone());
            let arg = normalize_module_path_through_components(ctx, load_paths, arg, visiting)
                .unwrap_or_else(|| (**arg).clone());
            Path::Papply(std::sync::Arc::new(functor), std::sync::Arc::new(arg))
        }
        Path::Pident(_) => module_path.clone(),
    };

    let alias_target = match &normalized_path {
        Path::Pdot(parent, module_name, _) => {
            let mut lookup_visiting = HashSet::new();
            let parent_sig = resolve_module_signature_through_cmi_shared(
                ctx,
                load_paths,
                parent,
                &mut lookup_visiting,
            )?;
            parent_sig.iter().find_map(|item| match item {
                SignatureItem::SigModule(id, md, _) if id.name() == module_name => {
                    match &md.md_type {
                        ModuleType::MtyAlias(_, alias_path) => Some(alias_path.clone()),
                        _ => None,
                    }
                }
                _ => None,
            })
        }
        _ => None,
    };

    if let Some(alias_path) = alias_target {
        // OCaml `normalize_path` rewrites module aliases before component
        // lookup (compiler/ml/env.ml:903-913). Use the normalized module path
        // only as declaration metadata; the caller still caches the lookup
        // under the original access path.
        normalize_module_path_through_components(ctx, load_paths, &alias_path, visiting)
            .or(Some(crate::types::Path::clone(&alias_path)))
    } else {
        Some(normalized_path)
    }
}

/// Resolve a type declaration by walking through module signatures.
///
/// For a path like `Pdot(Pdot(Pident(Js), "Promise"), "t")`:
/// 1. Load the root module's CMI (`Js.cmi`)
/// 2. Find the sub-module `Promise` in its signature
/// 3. If it's an alias, load the aliased module
/// 4. Find type `t` in the resolved module's signature
///
/// Returns the type declaration.
pub(crate) fn resolve_type_item_through_modules(
    ctx: &TypeContext,
    path: &Path,
) -> Option<(crate::ident::Ident, super::decl::TypeDeclaration)> {
    use crate::types::decl::SignatureItem;

    let (module_path, type_name) = match path {
        Path::Pdot(parent, name, _) => (parent.as_ref(), name.as_str()),
        _ => return None,
    };
    let counters_enabled = ctx.compiler_counters_enabled();

    let load_paths = ctx.load_paths();
    if load_paths.is_empty() && !ctx.persistent_env_is_in_process() {
        return None;
    }

    let mut visiting = HashSet::new();
    // OCaml compiler/ml/env.ml:800-823 resolves dotted type paths through
    // persistent module components; compiler/ml/ctype.ml:1395-1439 then uses
    // those declarations for abbreviation expansion. In --in-process, the
    // persistent registry is the component source instead of disk `.cmi` files.
    let current_sig =
        resolve_module_signature_through_cmi_shared(ctx, &load_paths, module_path, &mut visiting)?;
    let type_module_path = normalize_module_path_through_components(
        ctx,
        &load_paths,
        module_path,
        &mut HashSet::new(),
    )
    .unwrap_or_else(|| module_path.clone());

    let type_module_path = std::sync::Arc::new(type_module_path);

    let mut result = None;
    let mut scanned_items = 0usize;
    let mut type_items = 0usize;
    for item in current_sig.iter() {
        if counters_enabled {
            scanned_items += 1;
        }
        if let SignatureItem::SigType(id, decl, _) = item {
            if counters_enabled {
                type_items += 1;
            }
            if id.name() == type_name {
                let qualified_decl =
                    qualify_type_decl_for_module_access_path(ctx, &type_module_path, id, decl);
                result = Some((*id, qualified_decl));
            }
        }
    }
    if counters_enabled {
        crate::perf_counters::record_type_item_resolve_scan(
            scanned_items,
            type_items,
            result.is_some(),
        );
    }
    result
}

pub fn resolve_type_through_modules(
    ctx: &TypeContext,
    path: &Path,
) -> Option<super::decl::TypeDeclaration> {
    resolve_type_item_through_modules(ctx, path).map(|(_, decl)| decl)
}

fn resolve_module_type_through_env_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    path: &Path,
    visiting: &mut HashSet<Path>,
) -> Option<super::decl::ModuleType> {
    // Keep visited paths for the entire alias-resolution chain; this mirrors
    // OCaml's cycle-safe alias scraping and prevents re-entering `Mty_ident`
    // loops through `resolve_signature_through_env_module_type`.
    if !visiting.insert(path.clone()) {
        return None;
    }

    match path {
        Path::Pident(id) => {
            let name = id.name();
            if id.is_persistent() {
                // OCaml env.ml:865-875 checks the local module table first,
                // then loads persistent Pident signatures with find_pers_struct.
                // The component resolver below is intentionally stricter for
                // flattened namespace heads, so keep the direct persistent path.
                let mut direct_persistent_env = ctx.persistent_env_clone();
                if let Some(sig) = direct_persistent_env
                    .as_mut()
                    .and_then(|pers| pers.find_pers_struct(name, ctx))
                    .map(|ps| ps.ps_sig.clone())
                {
                    Some(super::decl::ModuleType::MtySignature(sig))
                } else {
                    let mut persistent_env = in_process_module_resolution_env(ctx);
                    crate::types::typecore::resolve_module_signature_for_path(
                        path,
                        env,
                        &mut persistent_env,
                        ctx,
                    )
                    .map(|(_, sig)| super::decl::ModuleType::MtySignature(std::sync::Arc::new(sig)))
                    .or_else(|| {
                        let load_paths = ctx.load_paths();
                        if load_paths.is_empty() {
                            None
                        } else {
                            // Mirror OCaml Env.find_module: if not found in local env,
                            // consult .cmi signatures. Prefer the env_lazy-backed path
                            // above so persistent module lookups share the same
                            // qualified-view source of truth as other hot callers.
                            let mut cmi_visiting = HashSet::new();
                            resolve_module_signature_through_cmi_shared(
                                ctx,
                                &load_paths,
                                path,
                                &mut cmi_visiting,
                            )
                            .map(super::decl::ModuleType::MtySignature)
                        }
                    })
                }
            } else if let Ok(md) = env.lookup_module(path) {
                Some(md.md_type.clone())
            } else if let Ok(md) = env.find_module(name) {
                Some(md.md_type.clone())
            } else if let Ok(mtd) = env.find_modtype(name) {
                mtd.mtd_type.clone()
            } else {
                None
            }
        }
        Path::Pdot(parent, name, _) => {
            let mut persistent_env = in_process_module_resolution_env(ctx);
            let parent_is_opened_component = env.path_starts_with_opened_component(parent);
            if parent_is_opened_component {
                let selected_child_path = Path::pdot(parent.as_ref().clone(), name.to_string());
                if let Some((_, sig)) = crate::types::typecore::resolve_module_signature_for_path(
                    &selected_child_path,
                    env,
                    &mut persistent_env,
                    ctx,
                ) {
                    // OCaml compiler/ml/env.ml:1094-1100 value lookup uses
                    // `lookup_module_descr`, which descends through
                    // env.ml:781-793's `comp_components`; that does not force
                    // env.ml:1568's child `comp_modules` thunk. For any path
                    // whose first dotted component came from an open, reuse
                    // the selected component signature and leave the
                    // module-declaration force to env.ml:865-882-equivalent
                    // callers that actually ask for `find_module`.
                    return Some(super::decl::ModuleType::MtySignature(std::sync::Arc::new(
                        sig,
                    )));
                }
            }
            let mut persistent_env = in_process_module_resolution_env(ctx);
            let parent_alias_target = crate::types::typecore::module_alias_target_for_path(
                parent,
                env,
                &mut persistent_env,
                ctx,
            );
            if let Some((_, access_path, md)) =
                crate::types::typecore::lookup_module_in_resolved_path(
                    parent,
                    name,
                    env,
                    &mut persistent_env,
                    ctx,
                )
            {
                match &md.md_type {
                    super::decl::ModuleType::MtySignature(_) => {
                        let parent_is_opened_component =
                            env.path_starts_with_opened_component(parent);
                        let preferred_child_path = (!parent_is_opened_component)
                            .then_some(parent_alias_target.as_ref())
                            .flatten()
                            .map(|target_parent_path| {
                                Path::pdot(target_parent_path.clone(), name.to_string())
                            });
                        // OCaml compiler/ml/env.ml:1094-1100 resolves value
                        // prefixes through `lookup_module_descr`; for dotted
                        // opened components that path reads env.ml:781-793's
                        // selected `comp_components` table. Do not
                        // immediately rebuild the flattened alias target after
                        // selecting an opened component path; OCaml only
                        // forces the selected component module declaration at
                        // env.ml:865-882 when normalization explicitly asks
                        // for it.
                        crate::types::typecore::resolve_module_signature_for_path(
                            preferred_child_path.as_ref().unwrap_or(&access_path),
                            env,
                            &mut persistent_env,
                            ctx,
                        )
                        .or_else(|| {
                            preferred_child_path.as_ref().and_then(|_| {
                                crate::types::typecore::resolve_module_signature_for_path(
                                    &access_path,
                                    env,
                                    &mut persistent_env,
                                    ctx,
                                )
                            })
                        })
                        .map(|(_, sig)| {
                            super::decl::ModuleType::MtySignature(std::sync::Arc::new(sig))
                        })
                    }
                    other => {
                        let child_mty = other.clone();
                        if let Some(target_parent_path) = parent_alias_target.as_ref() {
                            let child_target_path =
                                Path::pdot(target_parent_path.clone(), name.to_string());
                            Some(strengthen_module_type_for_module_access_path(
                                ctx,
                                env,
                                true,
                                &child_target_path,
                                &child_mty,
                            ))
                        } else {
                            Some(child_mty)
                        }
                    }
                }
            } else if let Some((_, mtd)) = crate::types::typecore::lookup_modtype_in_resolved_path(
                parent,
                name,
                env,
                &mut persistent_env,
                ctx,
            ) {
                mtd.mtd_type.clone()
            } else {
                None
            }
        }
        Path::Papply(_, _) => None,
    }
}

pub fn resolve_module_type_through_env(
    ctx: &TypeContext,
    env: &super::env::Env,
    path: &Path,
) -> Option<super::decl::ModuleType> {
    let mut visiting = HashSet::new();
    resolve_module_type_through_env_path(ctx, env, path, &mut visiting)
}

fn resolve_signature_through_env_module_type(
    ctx: &TypeContext,
    env: &super::env::Env,
    mty: &super::decl::ModuleType,
    visiting: &mut HashSet<Path>,
) -> Option<super::decl::Signature> {
    use super::decl::ModuleType;

    match mty {
        // The env_lazy-backed signature view is already the qualified source of
        // truth for this access path. Reusing it preserves the same sharing
        // shape OCaml keeps in components_of_module_maker.
        ModuleType::MtySignature(sig) => Some((**sig).clone()),
        ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
            let path = mty.ident_or_alias_path().unwrap();
            let mut no_persistent_env = None;
            if let Some((_, sig)) = crate::types::typecore::resolve_module_signature_for_path(
                path,
                env,
                &mut no_persistent_env,
                ctx,
            ) {
                return Some(sig);
            }
            let resolved = resolve_module_type_through_env_path(ctx, env, path, visiting)?;
            resolve_signature_through_env_module_type(ctx, env, &resolved, visiting)
        }
        _ => None,
    }
}

fn strengthen_type_decl_for_module_access_path(
    ctx: &TypeContext,
    module_access_path: &Arc<Path>,
    id: &crate::ident::Ident,
    decl: &super::decl::TypeDeclaration,
) -> super::decl::TypeDeclaration {
    // Match OCaml compiler/ml/mtype.ml:55-70 `strengthen_sig`:
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
    // `Pdot (p, Ident.name id, nopos)` around the one `p` of the signature.
    let qualified_type_path =
        ctx.dotted_from_ident(module_access_path.clone(), *id, crate::types::path::NOPOS);

    if keep_manifest {
        let mut strengthened = decl.clone();
        strengthened.type_path = Some(qualified_type_path);
        return strengthened;
    }

    let mut strengthened = decl.clone();
    let manifest = ctx.new_generic_constr(qualified_type_path.clone(), decl.type_params.clone());
    strengthened.type_manifest = Some(manifest);
    strengthened.type_path = Some(qualified_type_path);
    if matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract) {
        strengthened.type_private = PrivateFlag::Public;
    }
    strengthened
}

fn qualify_type_decl_for_module_access_path(
    ctx: &TypeContext,
    module_access_path: &std::sync::Arc<Path>,
    id: &crate::ident::Ident,
    decl: &super::decl::TypeDeclaration,
) -> super::decl::TypeDeclaration {
    let qualified_type_path =
        ctx.dotted_from_ident(module_access_path.clone(), *id, crate::types::path::NOPOS);

    // OCaml `Env.find_type` resolves dotted paths through module components
    // (compiler/ml/env.ml:800-823), and component construction substitutes
    // signature type declarations under that component path
    // (compiler/ml/env.ml:1530-1544). Rust keeps the selected path as
    // out-of-band metadata on TypeDeclaration, so rewrite imported flattened
    // cmi paths to the component lookup path without allocating a strengthened
    // self-manifest at this point.
    let mut qualified = decl.clone();
    qualified.type_path = Some(qualified_type_path);
    qualified
}

fn strengthen_module_type_for_module_access_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    aliasable: bool,
    module_access_path: &Path,
    mty: &super::decl::ModuleType,
) -> super::decl::ModuleType {
    use super::decl::ModuleType;

    fn scrape_modtype_ident_for_strengthen(
        env: &super::env::Env,
        mty: &super::decl::ModuleType,
        visiting: &mut HashSet<Path>,
    ) -> super::decl::ModuleType {
        match mty {
            super::decl::ModuleType::MtyIdent(path) => {
                if !visiting.insert(path.clone()) {
                    return mty.clone();
                }
                let expanded = env
                    .lookup_modtype(path)
                    .ok()
                    .and_then(|mtd| mtd.mtd_type.as_ref())
                    .map(|expanded| scrape_modtype_ident_for_strengthen(env, expanded, visiting));
                visiting.remove(path);
                expanded.unwrap_or_else(|| mty.clone())
            }
            _ => mty.clone(),
        }
    }

    // Match OCaml compiler/ml/mtype.ml:22-32: `strengthen` calls `scrape`
    // first, and `scrape` expands `Mty_ident` with Env.find_modtype_expansion
    // before signature strengthening. This matters for strict typedtree parity
    // because each expansion walks/freshens the module type at OCaml's exact
    // inclusion points.
    let mut visiting = HashSet::new();
    let scraped = scrape_modtype_ident_for_strengthen(env, mty, &mut visiting);

    match &scraped {
        ModuleType::MtySignature(sig) => ModuleType::MtySignature(std::sync::Arc::new(
            strengthen_signature_for_module_access_path(
                ctx,
                env,
                aliasable,
                module_access_path,
                sig,
                0,
            ),
        )),
        ModuleType::MtyAlias(..) | ModuleType::MtyIdent(..) => scraped,
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } if param.name() != "*" => ModuleType::MtyFunctor {
            param: *param,
            param_type: param_type.clone(),
            result: Box::new(strengthen_module_type_for_module_access_path(
                ctx,
                env,
                false,
                &Path::papply(module_access_path.clone(), Path::pident(*param)),
                result,
            )),
        },
        ModuleType::MtyFunctor { .. } => mty.clone(),
    }
}

pub fn strengthen_module_type_for_inclusion_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    module_access_path: &Path,
    mty: &super::decl::ModuleType,
) -> super::decl::ModuleType {
    strengthen_module_type_for_module_access_path(ctx, env, true, module_access_path, mty)
}

pub fn strengthen_module_type_for_non_aliasable_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    module_access_path: &Path,
    mty: &super::decl::ModuleType,
) -> super::decl::ModuleType {
    strengthen_module_type_for_module_access_path(ctx, env, false, module_access_path, mty)
}

fn strengthen_module_decl_for_module_access_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    aliasable: bool,
    module_access_path: &Path,
    md: &super::decl::ModuleDeclaration,
) -> super::decl::ModuleDeclaration {
    use super::decl::{AliasPresence, ModuleType};

    let mut strengthened = md.clone();
    strengthened.md_type = match &md.md_type {
        ModuleType::MtyAlias(..) => md.md_type.clone(),
        _ if aliasable => ModuleType::MtyAlias(
            AliasPresence::MtaPresent,
            std::sync::Arc::new(module_access_path.clone()),
        ),
        _ => strengthen_module_type_for_module_access_path(
            ctx,
            env,
            aliasable,
            module_access_path,
            &md.md_type,
        ),
    };
    strengthened
}

fn strengthen_signature_for_module_access_path(
    ctx: &TypeContext,
    env: &super::env::Env,
    aliasable: bool,
    module_access_path: &Path,
    sig: &[super::decl::SignatureItem],
    mut pos: i32,
) -> super::decl::Signature {
    use super::decl::{SignatureItem, ValueKind};

    // mtype.ml:40-91: every item is strengthened with the same `p`.
    let module_access_path = &Arc::new(module_access_path.clone());
    let mut strengthened = Vec::with_capacity(sig.len());
    let mut env = env.clone();
    let mut index = 0;
    while index < sig.len() {
        let item = &sig[index];
        if let SignatureItem::SigType(id, decl, _) = item
            && matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
            && let Some(SignatureItem::SigType(next_id, next_decl, _)) = sig.get(index + 1)
            && next_decl.type_private == PrivateFlag::Private
            && id.name().strip_suffix("#row") == Some(next_id.name())
        {
            index += 1;
            continue;
        }
        let new_item = match item {
            SignatureItem::SigValue(id, desc) => {
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    pos += 1;
                }
                SignatureItem::SigValue(*id, desc.clone())
            }
            SignatureItem::SigType(id, decl, rec_status) => SignatureItem::SigType(
                *id,
                std::sync::Arc::new(strengthen_type_decl_for_module_access_path(
                    ctx,
                    module_access_path,
                    id,
                    decl,
                )),
                *rec_status,
            ),
            SignatureItem::SigTypext(id, ext, ext_status) => {
                pos += 1;
                SignatureItem::SigTypext(*id, ext.clone(), *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                let child_path = ctx.dotted_from_ident(module_access_path.clone(), *id, pos);
                pos += 1;
                let strengthened_md = strengthen_module_decl_for_module_access_path(
                    ctx,
                    &env,
                    aliasable,
                    &child_path,
                    md,
                );
                let new_item = SignatureItem::SigModule(*id, strengthened_md, *rec_status);
                env.add_module(*id, md.clone());
                new_item
            }
            SignatureItem::SigModtype(id, mtd) => {
                let mut strengthened_mtd = mtd.clone();
                if mtd.mtd_type.is_none() {
                    let modtype_path = ctx.dotted_from_ident(
                        module_access_path.clone(),
                        *id,
                        crate::types::path::NOPOS,
                    );
                    strengthened_mtd.mtd_type =
                        Some(super::decl::ModuleType::MtyIdent(modtype_path));
                }
                let new_item = SignatureItem::SigModtype(*id, strengthened_mtd);
                env.add_modtype(*id, mtd.clone());
                new_item
            }
            SignatureItem::SigClass => SignatureItem::SigClass,
            SignatureItem::SigClassType => SignatureItem::SigClassType,
        };
        strengthened.push(new_item);
        index += 1;
    }
    strengthened
}

/// Resolve a type through local environment modules.
/// For paths like Pdot(Pident(Ord), "t"), look up module Ord in env,
/// follow aliases (MtyAlias/MtyIdent), and then find type t in its signature.
fn lookup_component_module_sig_type(
    ctx: &TypeContext,
    env: &super::env::Env,
    module_path: &Path,
    type_name: &str,
) -> Option<(crate::ident::Ident, Arc<super::decl::TypeDeclaration>)> {
    use super::decl::SignatureItem;

    if matches!(module_path, Path::Pdot(..) | Path::Papply(..)) {
        let mut persistent_env = in_process_module_resolution_env(ctx);
        // OCaml compiler/ml/env.ml:781-793 resolves dotted module descriptors
        // through `comp_components`, and env.ml:800-813 then reads `comp_types`.
        // That path may reach persistent `ps_comps` at env.ml:786-788, but it
        // still does not force env.ml:865-882's `comp_modules` declaration
        // thunk. Use the in-process persistent env so dotted persistent paths
        // such as `Layout__Types.Name.t` can be found through component tables
        // instead of falling back to module-declaration lookup.
        return crate::types::typecore::with_resolved_module_components_for_path_with_cache_mode(
            module_path,
            env,
            &mut persistent_env,
            ctx,
            crate::types::typecore::ComponentLookupApi::FindType,
            |components| {
                components
                    .lookup_type(type_name)
                    .map(|(id, decl)| (*id, decl.clone()))
            },
        )
        .flatten();
    }

    let raw_sig = match module_path {
        Path::Pident(id) => {
            // OCaml compiler/ml/env.ml:781-788 path lookup uses exact
            // `IdTbl.find_same` for persistent `Pident`s; only source
            // Longident lookup uses name fallback before persistent lookup
            // (compiler/ml/env.ml:1000-1007).
            let module_decl = if id.is_persistent() {
                env.lookup_module_ident_exact(id).ok()
            } else {
                env.lookup_module(module_path)
                    .or_else(|_| env.find_module(id.name()))
                    .ok()
            };
            module_decl.and_then(|md| match &md.md_type {
                super::decl::ModuleType::MtySignature(sig) => Some(sig.clone()),
                _ => None,
            })
        }
        Path::Pdot(..) | Path::Papply(..) => None,
    }?;
    raw_sig.iter().find_map(|item| match item {
        SignatureItem::SigType(id, decl, _) if id.name() == type_name => Some((*id, decl.clone())),
        _ => None,
    })
}

fn lookup_raw_module_sig_type(
    ctx: &TypeContext,
    env: &super::env::Env,
    module_path: &Path,
    type_name: &str,
) -> Option<(crate::ident::Ident, Arc<super::decl::TypeDeclaration>)> {
    use super::decl::SignatureItem;

    if let Some((id, decl)) = lookup_component_module_sig_type(ctx, env, module_path, type_name) {
        let queried_type_path = Path::pdot(module_path.clone(), type_name.to_string());
        let is_self_manifest = decl.type_manifest.is_some_and(|manifest| {
            matches!(
                &*ctx.get_desc(ctx.repr(manifest)),
                TypeDesc::Tconstr { path, .. } if path.same(&queried_type_path)
            )
        });
        if !is_self_manifest {
            return Some((id, decl));
        }
    }

    if let Path::Pident(id) = module_path
        && id.is_persistent()
    {
        // OCaml compiler/ml/env.ml:800-813 `find_type_full` reaches persistent
        // roots through env.ml:781-788 `find_module_descr`, then reads the
        // already-built `comp_types` table. It does not force env.ml:865-882
        // `find_module` just to check whether a raw persistent parent has a
        // direct type item. Mirror that by scanning the raw signature and
        // returning `None` when the type is absent.
        return ctx
            .with_raw_module_sig(id.name(), |raw_sig| {
                raw_sig.iter().find_map(|item| match item {
                    SignatureItem::SigType(raw_id, raw_decl, _) if raw_id.name() == type_name => {
                        Some((*raw_id, raw_decl.clone()))
                    }
                    _ => None,
                })
            })
            .flatten();
    }

    let mut visiting = HashSet::new();
    let raw_sig = resolve_module_type_through_env_path(ctx, env, module_path, &mut visiting)
        .and_then(|resolved| {
            resolve_signature_through_env_module_type(ctx, env, &resolved, &mut visiting)
        })?;
    raw_sig.iter().find_map(|item| match item {
        SignatureItem::SigType(id, decl, _) if id.name() == type_name => Some((*id, decl.clone())),
        _ => None,
    })
}

/// Resolve a dotted type path to its declaration, memoized per module scope.
///
/// OCaml `Env.find_type` (compiler/ml/env.ml:800-813) reads the declaration
/// from the module's lazily built component table
/// (compiler/ml/env.ml:1516-1552), so repeated lookups of one path under the
/// same module-level bindings return the same declaration. The result only
/// depends on those bindings (`Env::scope_id`), so later lookups reuse the
/// first result instead of re-walking the component tables.
fn resolve_type_item_through_env<'a>(
    ctx: &'a TypeContext,
    env: &super::env::Env,
    path: &Path,
    strengthen_alias_types: bool,
) -> Option<(crate::ident::Ident, super::decl::TypeDeclarationRef<'a>)> {
    let scope_id = env.scope_id();
    if let Some((id, decl)) = ctx.find_resolved_type_item(scope_id, path, strengthen_alias_types) {
        return Some((id, super::decl::TypeDeclarationRef::Shared(decl)));
    }
    let (id, decl) =
        resolve_type_item_through_env_uncached(ctx, env, path, strengthen_alias_types)?;
    let decl = match decl {
        super::decl::TypeDeclarationRef::Borrowed(decl) => Arc::new(decl.clone()),
        super::decl::TypeDeclarationRef::Shared(decl) => decl,
        super::decl::TypeDeclarationRef::Owned(decl) => Arc::new(*decl),
    };
    ctx.register_resolved_type_item(scope_id, path, strengthen_alias_types, id, decl.clone());
    Some((id, super::decl::TypeDeclarationRef::Shared(decl)))
}

fn resolve_type_item_through_env_uncached<'a>(
    ctx: &'a TypeContext,
    env: &super::env::Env,
    path: &Path,
    strengthen_alias_types: bool,
) -> Option<(crate::ident::Ident, super::decl::TypeDeclarationRef<'a>)> {
    let (module_path, type_name) = match path {
        Path::Pdot(parent, name, _) => (parent.as_ref(), name.as_str()),
        _ => return None,
    };

    let mut persistent_env = in_process_module_resolution_env(ctx);
    if let Some((qualified_module_path, id, decl)) =
        crate::types::typecore::lookup_type_in_resolved_path(
            module_path,
            type_name,
            env,
            &mut persistent_env,
            ctx,
        )
    {
        // `lookup_type_in_resolved_path` already reads from the cached
        // env_lazy-qualified module view. Keep that declaration graph shared
        // instead of re-copying it on every lookup.
        let resolved_decl = super::decl::TypeDeclarationRef::Shared(decl);
        // OCaml compiler/ml/env.ml:1438-1444 scrapes `Mty_alias` by looking
        // up the target module with `path`, compiler/ml/mtype.ml:55-70 then
        // strengthens abstract types to that alias target, and
        // compiler/ml/env.ml:1513-1552 prefixes the component lookup path
        // separately. Keep the expansion body rooted at the alias target for
        // local aliases too (e.g. `module ZoomT = Zoom`: `ZoomT.t` expands to
        // `Zoom.t`), while the queried access path remains `ZoomT.t`.
        let alias_target_for_strengthening = if strengthen_alias_types {
            let mut persistent_env = in_process_module_resolution_env(ctx);
            crate::types::typecore::module_alias_target_for_path(
                module_path,
                env,
                &mut persistent_env,
                ctx,
            )
        } else {
            None
        };

        let queried_type_path = Path::pdot(qualified_module_path.clone(), type_name.to_string());
        let self_manifest = resolved_decl.type_manifest.is_some_and(|manifest| {
            let manifest = ctx.repr(manifest);
            let manifest_desc = ctx.get_desc(manifest);
            matches!(
                &*manifest_desc,
                TypeDesc::Tconstr {
                    path: manifest_path, ..
                } if manifest_path.same(&queried_type_path)
            )
        });
        if self_manifest {
            if let Some(target_path) = alias_target_for_strengthening.as_ref() {
                // OCaml compiler/ml/env.ml:1438-1444 scrapes `Mty_alias`
                // with the alias target path before compiler/ml/mtype.ml:55-70
                // strengthens abstract type manifests; compiler/ml/env.ml:1513-1552
                // then prefixes the visible component lookup path separately.
                // Rust may already be holding that visible, self-manifested
                // component decl, so rewrite this alias-scrape case to the
                // target manifest without changing general strengthening.
                let mut target_decl = resolved_decl.clone();
                target_decl.type_manifest = Some(ctx.new_generic_constr(
                    Path::pdot(target_path.clone(), id.name()),
                    resolved_decl.type_params.clone(),
                ));
                target_decl.type_path = Some(queried_type_path.clone());
                if matches!(
                    resolved_decl.type_kind,
                    crate::types::TypeKind::TypeAbstract
                ) {
                    target_decl.type_private = PrivateFlag::Public;
                }
                return Some((id, super::decl::TypeDeclarationRef::owned(target_decl)));
            }
            let raw_module_path = alias_target_for_strengthening
                .as_ref()
                .unwrap_or(module_path);
            if let Some((raw_id, raw_decl)) =
                lookup_raw_module_sig_type(ctx, env, raw_module_path, type_name)
            {
                return Some((raw_id, super::decl::TypeDeclarationRef::Shared(raw_decl)));
            }
        }
        if let Some(target_path) = alias_target_for_strengthening.as_ref() {
            return Some((
                id,
                super::decl::TypeDeclarationRef::owned(
                    strengthen_type_decl_for_module_access_path(
                        ctx,
                        &Arc::new(target_path.clone()),
                        &id,
                        &resolved_decl,
                    ),
                ),
            ));
        }
        return Some((id, resolved_decl));
    }

    // Fall back to CMI-based resolution if local env-based lookup didn't find
    // the type item (e.g. when only the persistent path is available).
    // OCaml compiler/ml/env.ml:800-813 returns the existing component-table
    // entry, which compiler/ml/env.ml:1542-1552 built from the `Sig_type`
    // item. Keep that item id here; allocating a fresh `t` would advance the
    // global stamp clock at a lookup point where OCaml only inspects.
    resolve_type_item_through_modules(ctx, path)
        .map(|(id, decl)| (id, super::decl::TypeDeclarationRef::owned(decl)))
}

fn resolve_type_through_env<'a>(
    ctx: &'a TypeContext,
    env: &super::env::Env,
    path: &Path,
    strengthen_alias_types: bool,
) -> Option<super::decl::TypeDeclarationRef<'a>> {
    resolve_type_item_through_env(ctx, env, path, strengthen_alias_types).map(|(_, decl)| decl)
}

/// Normalize a path by following module aliases, using both the local env
/// and persistent environment (CMI files) for module lookup.
///
/// This is equivalent to OCaml's `Env.normalize_path` but with access to
/// the full module resolution machinery. For `Pdot(p, s)`, it:
/// 1. Recursively normalizes the prefix `p`
/// 2. Looks up the module at the path (checking env + CMI)
/// 3. If the module is an alias (`MtyAlias`), follows it
pub(crate) fn normalize_path_full(ctx: &TypeContext, env: &Env, path: &Path) -> Path {
    // Normalization only reads module-level bindings (see `Env::scope_id`).
    let env_id = env.scope_id();
    let recipe = match ctx.find_normalized_path_full(env_id, path) {
        Some(recipe) => recipe,
        None => {
            let (_, recipe) =
                normalize_path_full_inner(ctx, env, path, 0, &mut HashSet::new(), true, false);
            let recipe = std::sync::Arc::new(recipe);
            ctx.register_normalized_path_full(env_id, path, recipe.clone());
            recipe
        }
    };
    recipe.materialize(ctx, path)
}

pub(crate) fn normalize_path_full_strict(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
) -> Result<Path, Path> {
    // OCaml `Env.normalize_path (Some loc)` raises `Missing_module` when
    // alias normalization lands on a persistent path with no compiled
    // interface. The lax `None` form only returns the dangling path.
    let normalized = normalize_path_full(ctx, env, path);
    if module_path_exists_for_strict_normalize(ctx, env, &normalized) {
        Ok(normalized)
    } else {
        Err(normalized)
    }
}

fn module_path_exists_for_strict_normalize(ctx: &TypeContext, env: &Env, path: &Path) -> bool {
    match path {
        Path::Pident(id) => {
            if env.find_module_same(id).is_ok() {
                return true;
            }
            if id.is_persistent() {
                let mut persistent_env = ctx.persistent_env_clone();
                if persistent_env
                    .as_mut()
                    .and_then(|pers| pers.find_pers_struct(id.name(), ctx))
                    .is_some()
                {
                    return true;
                }
            }
            if !id.is_persistent() && id.stamp() != 0 {
                return false;
            }
        }
        Path::Pdot(parent, module_name, _) => {
            let mut persistent_env = in_process_module_resolution_env(ctx);
            if crate::types::typecore::lookup_module_in_resolved_path(
                parent,
                module_name,
                env,
                &mut persistent_env,
                ctx,
            )
            .is_some()
            {
                return true;
            }
        }
        Path::Papply(_, _) => {}
    }

    let mut persistent_env = in_process_module_resolution_env(ctx);
    crate::types::typecore::resolve_module_signature_for_path(path, env, &mut persistent_env, ctx)
        .is_some()
}

pub(crate) fn force_normalize_path_full_side_effects(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
) -> Path {
    // OCaml compiler/ml/ctype.ml:1367-1372 calls
    // compiler/ml/env.ml:923-934 `Env.normalize_path` as an expansion fallback.
    // That path is intentionally side-effectful: env.ml:896-900 reads
    // `comp_modules` and forces the env.ml:1568 module-declaration thunk even
    // when the normalized path is discarded by the caller. Use a distinct cache
    // from normal structural normalization: the first lookup still performs
    // those side effects at the OCaml compare point, while repeated label
    // disambiguation compares observe the already-forced lazy state.
    let env_id = env.scope_id();
    let recipe = match ctx.find_forced_normalized_path_full(env_id, path) {
        Some(recipe) => recipe,
        None => {
            let (_, recipe) =
                normalize_path_full_inner(ctx, env, path, 0, &mut HashSet::new(), true, true);
            let recipe = std::sync::Arc::new(recipe);
            ctx.register_forced_normalized_path_full(env_id, path, recipe.clone());
            recipe
        }
    };
    recipe.materialize(ctx, path)
}

fn normalize_path_forward_only(ctx: &TypeContext, env: &Env, path: &Path) -> Path {
    // Like `normalize_path_full`, this only reads module-level bindings, so
    // memoize it per `Env::scope_id`; unification asks for the same abstract
    // type heads many times per scope.
    let env_id = env.scope_id();
    let recipe = match ctx.find_normalized_path_forward(env_id, path) {
        Some(recipe) => recipe,
        None => {
            let (_, recipe) =
                normalize_path_full_inner(ctx, env, path, 0, &mut HashSet::new(), false, false);
            let recipe = std::sync::Arc::new(recipe);
            ctx.register_normalized_path_forward(env_id, path, recipe.clone());
            recipe
        }
    };
    recipe.materialize(ctx, path)
}

fn normalize_path_full_inner(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
    depth: usize,
    visiting: &mut HashSet<Path>,
    allow_reverse_local_aliases: bool,
    force_module_lookup_side_effects: bool,
) -> (Path, NormRecipe) {
    if depth > 20 {
        return (path.clone(), NormRecipe::Same);
    }

    if let Path::Pdot(parent, module_name, _) = path {
        let path_starts_with_implicit_opened_component =
            env.path_starts_with_implicit_opened_component(path);
        if !force_module_lookup_side_effects
            && !path_starts_with_implicit_opened_component
            && let Some(alias_path) = ctx.find_module_alias_in_components(parent, module_name)
            && !alias_path.same(path)
        {
            // OCaml compiler/ml/env.ml:781-793 lets `find_module_descr`
            // navigate persistent components through `ps_comps`, and
            // env.ml:876-880 reads a dotted module from those components before
            // alias normalization continues. `open_signature` at
            // env.ml:1841-1877 installs opened child component tables too.
            // Initial-env opens from compiler/core/res_compmisc.ml:48-63 keep
            // their root force behavior; source-level opens follow the opened
            // component descriptor path instead of forcing the opened root
            // through env.ml:865-875. Side-effectful compare_type_path calls
            // skip this shortcut so compiler/ml/env.ml:903-914 can reach
            // find_module at env.ml:865-882 and force component module thunks.
            return normalize_alias_target(
                ctx,
                env,
                alias_path.clone(),
                depth,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
        }
    }

    // First, recursively normalize module-path structure. OCaml
    // compiler/ml/env.ml:903-910 handles both `Pdot` prefixes and both sides
    // of `Papply`; functor arguments use lax normalization but still force
    // local module-declaration thunks through env.ml:865-875.
    // env.ml:868-872 rebuilds every `Pdot`/`Papply` with a fresh block and
    // returns a `Pident` itself. `path` below is the logical value used for
    // lookups; `recipe` says how each call allocates its result.
    let (path, recipe) = match path {
        Path::Pdot(p, s, pos) => {
            let (p_norm, p_recipe) = normalize_path_full_inner(
                ctx,
                env,
                p,
                depth + 1,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
            (
                Path::Pdot(std::sync::Arc::new(p_norm), *s, *pos),
                NormRecipe::Dot(Box::new(p_recipe)),
            )
        }
        Path::Papply(p1, p2) => {
            let (p1_norm, p1_recipe) = normalize_path_full_inner(
                ctx,
                env,
                p1,
                depth + 1,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
            let (p2_norm, p2_recipe) = normalize_path_full_inner(
                ctx,
                env,
                p2,
                depth + 1,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
            (
                Path::Papply(std::sync::Arc::new(p1_norm), std::sync::Arc::new(p2_norm)),
                NormRecipe::Apply(Box::new(p1_recipe), Box::new(p2_recipe)),
            )
        }
        _ => (path.clone(), NormRecipe::Same),
    };

    // Match OCaml compiler/ml/ctype.ml:1367-1372 and
    // compiler/ml/env.ml:865-875/env.ml:903-914: `normalize_path` calls
    // `find_module ~alias:true`, which forces a persistent structure's
    // `ps_sig` unless the exact module id is already present in `env.modules`.
    // Implicit opens in compiler/core/res_compmisc.ml:61-62 go through
    // compiler/ml/env.ml:1874-1877 `open_signature`, which exposes opened
    // components but not root module bindings, so implicit `Pervasives` and
    // `Stdlib` roots naturally take the persistent force path here.
    if let Path::Pident(id) = &path {
        let has_local_module = env.find_module_same(id).is_ok();
        if id.is_persistent() && !has_local_module {
            ctx.trigger_module_sig_rename(id.name());
        }
    }

    if !force_module_lookup_side_effects
        && let Path::Pdot(parent, module_name, _) = &path
        && let Some(alias_path) = ctx.find_module_alias_in_components(parent, module_name)
        && !alias_path.same(&path)
    {
        // OCaml compiler/ml/ctype.ml:1367-1372 falls back to
        // `Env.normalize_path`, and compiler/ml/env.ml:865-882 implements that
        // by reading the component module declaration with alias preservation.
        // Use the same forward alias fact when Rust already has the qualified
        // component table, so `expand_head` observes aliases such as
        // `Js.File -> Js_file` without forcing the full persistent signature.
        return normalize_alias_target(
            ctx,
            env,
            alias_path,
            depth,
            visiting,
            allow_reverse_local_aliases,
            force_module_lookup_side_effects,
        );
    }

    // Then check if the path itself is a module alias. For dotted paths, use
    // the side-effectful module resolution path first: OCaml
    // compiler/ml/env.ml:876-882 reaches `comp_modules` and forces
    // `EnvLazy.force subst_modtype_maker data` before seeing whether the
    // module is an alias. A plain env lookup would inspect the declaration but
    // skip the freshening side effects that determine later identifier stamps.
    if matches!(path, Path::Pdot(..)) {
        if !visiting.insert(path.clone()) {
            return (path, recipe);
        }
        let mut resolve_visiting = HashSet::new();
        if let Some(super::decl::ModuleType::MtyAlias(_, alias_path)) =
            resolve_module_type_through_env_path(ctx, env, &path, &mut resolve_visiting)
        {
            return normalize_alias_target(
                ctx,
                env,
                alias_path.clone(),
                depth,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
        }
    } else {
        let md = match &path {
            Path::Pident(id) => env.find_module_same(id),
            _ => env.lookup_module(&path),
        };
        if let Ok(md) = md
            && let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type
        {
            // OCaml compiler/ml/env.ml:865-875 uses `IdTbl.find_same` for
            // exact `Path.Pident` module lookup, and env.ml:285-290 skips
            // opened component tables. Do not let an opened alias such as
            // `Webapi.Dom` satisfy normalization of the persistent runtime
            // root `Dom`; env.ml:872-874 would force `Dom.ps_sig` first.
            return normalize_alias_target(
                ctx,
                env,
                alias_path.clone(),
                depth,
                visiting,
                allow_reverse_local_aliases,
                force_module_lookup_side_effects,
            );
        }
    }

    (path, recipe)
}

/// Follow a module alias: env.ml:878 `normalize_path lax env path1`, where
/// `path1` is the declaration's stored alias path.
#[allow(clippy::too_many_arguments)]
fn normalize_alias_target(
    ctx: &TypeContext,
    env: &Env,
    alias_path: std::sync::Arc<Path>,
    depth: usize,
    visiting: &mut HashSet<Path>,
    allow_reverse_local_aliases: bool,
    force_module_lookup_side_effects: bool,
) -> (Path, NormRecipe) {
    let (normalized, recipe) = normalize_path_full_inner(
        ctx,
        env,
        &alias_path,
        depth + 1,
        visiting,
        allow_reverse_local_aliases,
        force_module_lookup_side_effects,
    );
    (normalized, NormRecipe::Alias(alias_path, Box::new(recipe)))
}

/// How `Env.normalize_path` (env.ml:868-888) allocates its result, relative
/// to the path it was called on. A resolution cache keeps the logical
/// decisions; every call still builds its own fresh `Pdot`/`Papply` blocks,
/// keeps an unchanged `Pident` (the caller's own prefix block) and the
/// alias declaration's path, and retains each rebuilt suffix string.
#[derive(Debug)]
pub(crate) enum NormRecipe {
    /// The path itself, unchanged.
    Same,
    /// A fresh `Pdot` around the normalized prefix of the dotted path.
    Dot(Box<NormRecipe>),
    /// A fresh `Papply` around both normalized module paths.
    Apply(Box<NormRecipe>, Box<NormRecipe>),
    /// Continue from a module alias's stored path.
    Alias(std::sync::Arc<Path>, Box<NormRecipe>),
}

impl NormRecipe {
    pub(crate) fn materialize(&self, ctx: &TypeContext, origin: &Path) -> Path {
        match (self, origin) {
            (NormRecipe::Same, _) => origin.clone(),
            (NormRecipe::Alias(target, recipe), _) => recipe.materialize(ctx, target),
            (NormRecipe::Dot(prefix), Path::Pdot(..)) => {
                ctx.rebuild_dotted(origin, |p| prefix.materialize_shared(ctx, p))
            }
            (NormRecipe::Apply(functor, argument), Path::Papply(f, a)) => Path::Papply(
                functor.materialize_shared(ctx, f),
                argument.materialize_shared(ctx, a),
            ),
            _ => unreachable!("normalization recipe does not match its path"),
        }
    }

    fn materialize_shared(
        &self,
        ctx: &TypeContext,
        origin: &std::sync::Arc<Path>,
    ) -> std::sync::Arc<Path> {
        match self {
            NormRecipe::Same => origin.clone(),
            NormRecipe::Alias(target, recipe) => recipe.materialize_shared(ctx, target),
            _ => std::sync::Arc::new(self.materialize(ctx, origin)),
        }
    }
}

/// has a manifest (i.e., `type t = <body>`), expand it by substituting
/// the type parameters with the given arguments.
///
/// Returns `Some(expanded)` if expansion was possible, `None` otherwise.
#[inline]
fn proper_abbrevs(
    ctx: &TypeContext,
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

/// How a `Pdot`-headed constructor expands in one module scope.
#[derive(Clone)]
pub(crate) enum PdotExpansion {
    /// Substitute the arguments into the declaration's manifest.
    Expand {
        params: Vec<TypeExprRef>,
        manifest: TypeExprRef,
    },
    /// Rebuild the head at another path: an alias target (strengthened
    /// self-manifest) or the normalized path (OCaml ctype.ml:1370).
    Rewrite(Path),
    /// No expansion.
    None,
}

/// The `Pdot` route of `try_expand_head_with_mode`: OCaml
/// `expand_abbrev_gen` (compiler/ml/ctype.ml:1346-1372) through
/// `Env.find_type_expansion` and then `Env.normalize_path`.
fn pdot_expansion(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
    arity: usize,
    mode: ExpandHeadMode,
    can_expand_decl_manifest: &dyn Fn(&super::decl::TypeDeclaration, TypeExprRef) -> bool,
) -> PdotExpansion {
    if let Some(decl) = resolve_type_through_env(ctx, env, path, true)
        && let Some(manifest) = decl.type_manifest
    {
        let synthetic_self_manifest = {
            let manifest_repr = ctx.repr(manifest);
            let manifest_desc = ctx.borrow_desc(manifest_repr);
            matches!(
                &*manifest_desc,
                TypeDesc::Tconstr {
                    path: manifest_path,
                    args: manifest_args,
                    ..
                } if manifest_path.same(path)
                    && manifest_args.len() == arity
                    && matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
            )
        };
        // See the general route: parameterized strengthened self-manifests
        // rewrite to the alias target instead of substituting.
        if matches!(mode, ExpandHeadMode::General) && synthetic_self_manifest && arity != 0 {
            if let Path::Pdot(parent, type_name, pos) = path {
                let mut persistent_env = in_process_module_resolution_env(ctx);
                let target = crate::types::typecore::module_alias_target_for_path(
                    parent,
                    env,
                    &mut persistent_env,
                    ctx,
                )
                .filter(|target_module_path| !target_module_path.same(parent))
                .map(|target_module_path| {
                    Path::Pdot(std::sync::Arc::new(target_module_path), *type_name, *pos)
                });
                if let Some(target) = target {
                    return PdotExpansion::Rewrite(target);
                }
            }
        }
        if can_expand_decl_manifest(&decl, manifest) && decl.type_params.len() == arity {
            return PdotExpansion::Expand {
                params: decl.type_params.clone(),
                manifest,
            };
        }
    }
    let path_norm = match mode {
        ExpandHeadMode::General | ExpandHeadMode::Optimize => normalize_path_full(ctx, env, path),
        ExpandHeadMode::Unify => normalize_path_forward_only(ctx, env, path),
    };
    if path_norm != *path {
        PdotExpansion::Rewrite(path_norm)
    } else {
        PdotExpansion::None
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpandHeadMode {
    General,
    Unify,
    Optimize,
}

fn try_expand_head_with_mode(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    mode: ExpandHeadMode,
) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Tconstr {
            path, args, abbrev, ..
        } => {
            // OCaml runs check_abbrev_env from expand_abbrev_gen, which is only
            // reached for Tconstr heads (try_expand_once pattern-matches first).
            // Matching that behavior avoids clearing simple_abbrevs on non-constr
            // expand_head calls.
            ctx.check_abbrev_env(env);

            let args = args.clone();
            let path = path.clone();
            let orig_abbrev = *abbrev;
            let lookup_abbrev = proper_abbrevs(ctx, &path, &args, *abbrev);

            drop(desc);

            let private_flag = match mode {
                ExpandHeadMode::Optimize => PrivateFlag::Private,
                ExpandHeadMode::General | ExpandHeadMode::Unify => PrivateFlag::Public,
            };

            // OCaml ctype.ml expand_abbrev_gen: check memoized expansions first.
            if let Some(cached) = ctx.find_abbrev_expansion(lookup_abbrev, private_flag, &path) {
                let level = ctx.get_level(ty);
                if level != GENERIC_LEVEL {
                    // OCaml compiler/ml/ctype.ml:1353-1359 lowers a
                    // memoized abbreviation expansion with
                    // `update_level env level ty'`. That is observable:
                    // ctype.ml:666-673 `get_level` calls
                    // Env.find_type, which can force component signatures
                    // while expanding the head. Keep the env-aware path
                    // here rather than the cheaper structural lowering.
                    update_level_expand(ctx, env, level, cached);
                }
                // The cached expansion is returned even when it is `ty`
                // itself (ctype.ml:1360-1362, PR#7324).
                return Some(ctx.repr(cached));
            }

            let expand_with_subst =
                |params: &[TypeExprRef], manifest: TypeExprRef| -> TypeExprRef {
                    subst_with_memo(
                        ctx,
                        env,
                        ty,
                        lookup_abbrev,
                        private_flag,
                        params,
                        &args,
                        manifest,
                    )
                };

            let can_expand_decl_manifest =
                |decl: &super::decl::TypeDeclaration, manifest: TypeExprRef| {
                    // OCaml `expand_head_opt` exposes private abstract
                    // manifests for type-based optimizations
                    // (compiler/ml/ctype.ml:1464-1478). The regular
                    // `expand_head` path still follows `Env.find_type_expansion`
                    // privacy (compiler/ml/env.ml:944-957).
                    matches!(mode, ExpandHeadMode::Optimize)
                        || matches!(decl.type_private, PrivateFlag::Public)
                        || !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
                        || btype::has_constr_row(ctx, manifest)
                };

            // 0. Check local constraints first (GADT equations)
            if let Some(constraint_decl) = env.find_local_constraint(&path) {
                if let Some(manifest) = constraint_decl.type_manifest {
                    let params = &constraint_decl.type_params;
                    if params.len() == args.len() {
                        let expanded = expand_with_subst(params, manifest);
                        return Some(expanded);
                    }
                }
            }

            // Predefined types have no manifest (compiler/ml/predef.ml:239-424):
            // the general route below finds the abstract declaration with
            // `IdTbl.find_same` and stops without expanding.
            if let Path::Pident(id) = &path
                && super::predef::is_predef_type_ident(id)
                && env
                    .find_type_by_ident(id)
                    .is_ok_and(|decl| decl.type_manifest.is_none())
            {
                return None;
            }

            // Qualified heads: the outcome depends only on the module scope,
            // the path, the mode and the arity (each lookup on this route is
            // memoized per `Env::scope_id`), so it is computed once per key.
            if matches!(&path, Path::Pdot(..)) {
                let scope_id = env.scope_id();
                let mode_tag = mode as u8;
                let expansion = match ctx.find_pdot_expansion(scope_id, mode_tag, args.len(), &path)
                {
                    Some(expansion) => expansion,
                    None => {
                        let expansion = pdot_expansion(
                            ctx,
                            env,
                            &path,
                            args.len(),
                            mode,
                            &can_expand_decl_manifest,
                        );
                        ctx.register_pdot_expansion(
                            scope_id,
                            mode_tag,
                            args.len(),
                            &path,
                            expansion.clone(),
                        );
                        expansion
                    }
                };
                return match expansion {
                    PdotExpansion::Expand { params, manifest } => {
                        Some(expand_with_subst(&params, manifest))
                    }
                    PdotExpansion::Rewrite(target) => {
                        let level = ctx.get_level(ty);
                        let rewritten = ctx.new_type(TypeDesc::Tconstr {
                            path: target,
                            args: args.clone(),
                            abbrev: orig_abbrev,
                            path_block: crate::types::type_expr::PathBlock::OWN,
                        });
                        ctx.set_level(rewritten, level);
                        Some(rewritten)
                    }
                    PdotExpansion::None => None,
                };
            }

            // 1. Prefer environment lookup when the declaration matches the
            // queried path exactly. For qualified paths, reject leaf-fallback
            // hits to unrelated declarations.
            let mut forbid_fallback_manifest_expansion = false;
            let mut local_env_type_is_authoritative = false;
            let exact_env_decl = match &path {
                Path::Pident(id) => {
                    // OCaml compiler/ml/env.ml:800-813 uses
                    // `IdTbl.find_same` for Pident paths, and ctype.ml:1367-1372
                    // falls through to normalization only after that exact
                    // expansion lookup fails. Do not let a same-name local type
                    // suppress stamp-based expansion for imported aliases.
                    env.find_type_by_ident(id)
                }
                _ => env.lookup_type(&path),
            };
            if let Ok(env_decl) = exact_env_decl {
                let exact_lookup = match &path {
                    Path::Pident(_) => {
                        // OCaml abbreviation expansion calls `Env.find_type`,
                        // whose `Pident` case is exact `IdTbl.find_same`;
                        // do not use Rust's broader recovery fallback here
                        // (compiler/ml/env.ml:800-813,862,
                        // compiler/ml/ctype.ml:1395-1439).
                        true
                    }
                    Path::Pdot(_, _, _) => {
                        // OCaml `Env.find_type` resolves every qualified path
                        // through `find_module_descr` and the parent component
                        // table (compiler/ml/env.ml:781-813). Even an exact
                        // declaration cached in Rust's flat Env must take that
                        // route: a `Papply` parent forces the functor component
                        // and result substitutions in env.ml:1595-1602 and
                        // env.ml:1699-1710 before exposing the type.
                        false
                    }
                    Path::Papply(_, _) => false,
                };
                local_env_type_is_authoritative = matches!(&path, Path::Pident(id) if !id.is_persistent() && id.stamp() != 0)
                    && exact_lookup;
                if exact_lookup {
                    let self_manifest = env_decl.type_manifest.is_some_and(|manifest| {
                        let manifest = ctx.repr(manifest);
                        let manifest_desc = ctx.borrow_desc(manifest);
                        matches!(
                            &*manifest_desc,
                            TypeDesc::Tconstr {
                                path: manifest_path, ..
                            } if manifest_path.same(&path)
                        )
                    });
                    let alias_backed_parent = match &path {
                        Path::Pdot(parent, _, _) => {
                            let mut persistent_env = in_process_module_resolution_env(ctx);
                            // OCaml compiler/ml/env.ml:800-813 resolves type
                            // expansions through `find_type_full`, whose
                            // dotted case descends via env.ml:781-793
                            // `find_module_descr` and `comp_components`.
                            // Probe the alias from that component table instead
                            // of forcing env.ml:865-882 `find_module`.
                            crate::types::typecore::module_alias_target_for_path(
                                parent,
                                env,
                                &mut persistent_env,
                                ctx,
                            )
                            .is_some()
                        }
                        _ => false,
                    };
                    if self_manifest && alias_backed_parent {
                    } else if let Some(manifest) = env_decl.type_manifest {
                        if can_expand_decl_manifest(env_decl, manifest) {
                            let params = &env_decl.type_params;
                            if params.len() == args.len() {
                                let expanded = expand_with_subst(params, manifest);
                                return Some(expanded);
                            } else {
                                forbid_fallback_manifest_expansion = true;
                            }
                        } else {
                            forbid_fallback_manifest_expansion = true;
                        }
                    } else {
                        // Abstract type with no manifest found in env.
                        // Don't fall through to stamp-based lookup — the env is
                        // authoritative and this type should NOT be expanded.
                        forbid_fallback_manifest_expansion = true;
                    }
                }
            }

            // 1b. For qualified paths, mirror OCaml `find_type` resolution by
            // descending through the current environment's module signatures
            // before consulting global fallbacks. OCaml
            // compiler/ml/ctype.ml:1346-1372 uses the same
            // `Env.find_type_expansion` path for both `expand_head` and
            // `expand_head_unif`, so alias-module strengthening from
            // compiler/ml/env.ml:1438-1444 and compiler/ml/mtype.ml:55-70
            // applies in both Rust expansion modes.
            let strengthen_alias_types = true;
            let resolved_env_decl = if matches!(&path, Path::Pdot(..)) {
                resolve_type_through_env(ctx, env, &path, strengthen_alias_types)
            } else {
                None
            };
            if let Some(decl) = resolved_env_decl {
                if let Some(manifest) = decl.type_manifest {
                    let synthetic_self_manifest = {
                        let manifest_repr = ctx.repr(manifest);
                        let manifest_desc = ctx.borrow_desc(manifest_repr);
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
                    if matches!(mode, ExpandHeadMode::General)
                        && synthetic_self_manifest
                        && !args.is_empty()
                    {
                        let immediate_alias_target_path = match &path {
                            Path::Pdot(parent, type_name, pos) => {
                                let mut persistent_env = in_process_module_resolution_env(ctx);
                                // OCaml compiler/ml/env.ml:800-813 reaches
                                // aliases for type expansion through
                                // `find_module_descr`/`comp_components`
                                // (env.ml:781-793), leaving the module
                                // declaration thunk at env.ml:865-882 lazy.
                                crate::types::typecore::module_alias_target_for_path(
                                    parent,
                                    env,
                                    &mut persistent_env,
                                    ctx,
                                )
                                .filter(|target_module_path| !target_module_path.same(parent))
                                .map(|target_module_path| {
                                    Path::Pdot(
                                        std::sync::Arc::new(target_module_path),
                                        *type_name,
                                        *pos,
                                    )
                                })
                            }
                            _ => None,
                        };
                        if let Some(target_path) = immediate_alias_target_path {
                            let level = ctx.get_level(ty);
                            let rewritten = ctx.new_type(TypeDesc::Tconstr {
                                path: target_path,
                                args: args.clone(),
                                abbrev: orig_abbrev,
                                path_block: crate::types::type_expr::PathBlock::OWN,
                            });
                            ctx.set_level(rewritten, level);
                            return Some(rewritten);
                        }
                    }
                    if can_expand_decl_manifest(&decl, manifest) {
                        let params = &decl.type_params;
                        if params.len() == args.len() {
                            let expanded = expand_with_subst(params, manifest);
                            return Some(expanded);
                        } else {
                            forbid_fallback_manifest_expansion = true;
                        }
                    } else {
                        forbid_fallback_manifest_expansion = true;
                    }
                }
            }

            // 4. Path normalization fallback (OCaml ctype.ml:1370).
            // `expand_abbrev_gen` does this for both `expand_head` and
            // `expand_head_unif`, so keep unification on the same path instead
            // of recovering later with Rust-only alias fallback work.
            if local_env_type_is_authoritative && forbid_fallback_manifest_expansion {
                return None;
            }
            {
                let path_norm = match mode {
                    ExpandHeadMode::General | ExpandHeadMode::Optimize => {
                        normalize_path_full(ctx, env, &path)
                    }
                    ExpandHeadMode::Unify => normalize_path_forward_only(ctx, env, &path),
                };
                if path_norm != path {
                    let level = ctx.get_level(ty);
                    let normalized = ctx.new_type(TypeDesc::Tconstr {
                        path: path_norm,
                        args: args.clone(),
                        abbrev: orig_abbrev,
                        path_block: crate::types::type_expr::PathBlock::OWN,
                    });
                    ctx.set_level(normalized, level);
                    Some(normalized)
                } else {
                    None
                }
            }
        }
        _ => None,
    }
}

fn try_expand_head(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> Option<TypeExprRef> {
    try_expand_head_with_mode(ctx, env, ty, ExpandHeadMode::General)
}

/// Fully expand a type through all aliases until it can't be expanded further.
/// Like OCaml's expand_head_opt: repeatedly calls try_expand_head until stable.
pub fn expand_head_once(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    try_expand_head(ctx, env, ty).map(|expanded| ctx.repr(expanded))
}

pub(crate) fn expand_abbrev_opt_once(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    // OCaml compiler/ml/ctype.ml:4165 calls `expand_abbrev_opt` from
    // `cyclic_abbrev`; ctype.ml:1464-1478 defines that as the Private
    // expansion path through `Env.find_type_expansion_opt`.
    try_expand_head_with_mode(ctx, env, ty, ExpandHeadMode::Optimize)
        .map(|expanded| ctx.repr(expanded))
}

/// Ctype.instance_declaration (compiler/ml/ctype.ml:962-972): copy the
/// declaration's params, manifest and kind within one shared copy window.
pub(crate) fn instance_declaration(
    ctx: &crate::types::context::TypeContext,
    decl: &crate::types::decl::TypeDeclaration,
) -> crate::types::decl::TypeDeclaration {
    let mut cache = CopyCache::new(ctx);
    let mut copy = |ty: TypeExprRef| copy_type_cached(ctx, ty, &mut cache);
    let type_kind = match &decl.type_kind {
        crate::types::TypeKind::TypeAbstract => crate::types::TypeKind::TypeAbstract,
        crate::types::TypeKind::TypeRecord(labels, repr) => crate::types::TypeKind::TypeRecord(
            labels
                .iter()
                .map(|label| crate::types::decl::LabelDeclaration {
                    ld_id: label.ld_id,
                    ld_runtime_name: label.ld_runtime_name.clone(),
                    ld_mutable: label.ld_mutable,
                    ld_optional: label.ld_optional,
                    ld_type: copy(label.ld_type),
                    ld_loc: label.ld_loc,
                    ld_attributes: label.ld_attributes.clone(),
                })
                .collect(),
            repr.clone(),
        ),
        crate::types::TypeKind::TypeVariant(constrs, layout) => {
            crate::types::TypeKind::TypeVariant(
                constrs
                    .iter()
                    .map(|cstr| {
                        let mut cstr = cstr.clone();
                        match &cstr.cd_args {
                            crate::types::ConstructorArguments::CstrTuple(args) => {
                                cstr.cd_args = crate::types::ConstructorArguments::CstrTuple(
                                    args.iter().map(|arg| copy(*arg)).collect(),
                                );
                            }
                            crate::types::ConstructorArguments::CstrRecord(labels) => {
                                cstr.cd_args = crate::types::ConstructorArguments::CstrRecord(
                                    labels
                                        .iter()
                                        .map(|label| {
                                            let mut label = label.clone();
                                            label.ld_type = copy(label.ld_type);
                                            label
                                        })
                                        .collect(),
                                );
                            }
                        }
                        if let Some(res) = cstr.cd_res {
                            cstr.cd_res = Some(copy(res));
                        }
                        cstr
                    })
                    .collect(),
                *layout,
            )
        }
        crate::types::TypeKind::TypeOpen => crate::types::TypeKind::TypeOpen,
    };
    crate::types::decl::TypeDeclaration {
        type_params: decl.type_params.iter().map(|p| copy(*p)).collect(),
        type_manifest: decl.type_manifest.map(copy),
        type_kind,
        ..decl.clone()
    }
}

/// OCaml `Ctype.cyclic_abbrev env id ty` (ctype.ml:3953-3968): whether the
/// manifest `ty` of the declaration `id` expands back to `id` or loops.
pub(crate) fn cyclic_abbrev(ctx: &TypeContext, env: &Env, id: &Ident, ty: TypeExprRef) -> bool {
    let mut seen: Vec<TypeExprRef> = Vec::new();
    let mut current = ty;
    loop {
        let ty = ctx.repr(current);
        let path = match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, .. } => path.clone(),
            _ => return false,
        };
        if matches!(&path, Path::Pident(p) if p.same(id)) || seen.contains(&ty) {
            return true;
        }
        match expand_abbrev_opt_once(ctx, env, ty) {
            Some(expanded) => {
                seen.push(ty);
                current = expanded;
            }
            None => {
                // `expand_abbrev_opt` still normalizes the path when
                // `Env.find_type_expansion` fails (ctype.ml:1367-1372).
                force_normalize_path_full_side_effects(ctx, env, &path);
                return false;
            }
        }
    }
}

/// OCaml `Ctype.same_constr` (ctype.ml:4259-4264): whether two types expand
/// to constructors with the same path.
pub fn same_constr(ctx: &TypeContext, env: &Env, t1: TypeExprRef, t2: TypeExprRef) -> bool {
    let t1 = ctx.repr(expand_head(ctx, env, t1));
    let t2 = ctx.repr(expand_head(ctx, env, t2));
    match (&*ctx.get_desc(t1), &*ctx.get_desc(t2)) {
        (TypeDesc::Tconstr { path: p1, .. }, TypeDesc::Tconstr { path: p2, .. }) => p1.same(p2),
        _ => false,
    }
}

/// Fully expand a type through all aliases until it can't be expanded further.
/// Like OCaml's expand_head_opt: repeatedly calls try_expand_head until stable.
pub fn expand_head(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    expand_head_with_mode(ctx, env, ty, ExpandHeadMode::General)
}

pub(crate) fn expand_head_unif(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    expand_head_with_mode(ctx, env, ty, ExpandHeadMode::Unify)
}

pub(crate) fn expand_head_opt(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    expand_head_with_mode(ctx, env, ty, ExpandHeadMode::Optimize)
}

// ============================================================================
// Subtyping
// ============================================================================

/// Check whether `ty1` is a subtype of `ty2`.
///
/// This mirrors the shape of OCaml `Ctype.subtype`: walk the two type
/// descriptors structurally, expanding safe abbreviations at the head and
/// accumulating the source/target pair for diagnostics. The Rust port does not
/// yet model OCaml's delayed constraint closure, so variable constraints are
/// forced immediately through ordinary unification.
fn primitive_coercion_path(path: &Path) -> bool {
    path.same(&crate::types::predef::path_string())
        || path.same(&crate::types::predef::path_int())
        || path.same(&crate::types::predef::path_float())
        || path.same(&crate::types::predef::path_bigint())
}

fn variant_runtime_configuration(
    ctx: &TypeContext,
    decl: &crate::types::TypeDeclaration,
) -> crate::types::VariantConfiguration {
    let mut configuration = decl
        .variant_layout_ref()
        .map(|layout_ref| ctx.variant_layout(layout_ref).configuration())
        .unwrap_or(crate::types::VariantConfiguration {
            unboxed: false,
            tag_name: None,
        });
    configuration.unboxed |= decl.type_representation == crate::types::TypeRepresentation::Unboxed;
    configuration
}

fn variant_configuration_issue(
    ctx: &TypeContext,
    decl1: &crate::types::TypeDeclaration,
    decl2: &crate::types::TypeDeclaration,
) -> Option<VariantConfigurationIssue> {
    let left = variant_runtime_configuration(ctx, decl1);
    let right = variant_runtime_configuration(ctx, decl2);
    let left_unboxed = left.unboxed;
    let right_unboxed = right.unboxed;
    if left_unboxed != right_unboxed {
        return Some(VariantConfigurationIssue::UnboxedConfigNotMatching {
            left_unboxed,
            right_unboxed,
        });
    }

    let left_tag = left.tag_name;
    let right_tag = right.tag_name;
    if left_tag != right_tag {
        return Some(VariantConfigurationIssue::TagNameNotMatching {
            left_tag,
            right_tag,
        });
    }

    None
}

fn subtype_type_kind(kind: &crate::types::TypeKind) -> SubtypeTypeKind {
    match kind {
        crate::types::TypeKind::TypeAbstract => SubtypeTypeKind::Abstract,
        crate::types::TypeKind::TypeRecord(_, _) => SubtypeTypeKind::Record,
        crate::types::TypeKind::TypeVariant(_, _) => SubtypeTypeKind::Variant,
        crate::types::TypeKind::TypeOpen => SubtypeTypeKind::Open,
    }
}

fn generic_private_abbrev(ctx: &TypeContext, env: &Env, path: &Path) -> bool {
    lookup_type_decl_for_path(ctx, env, path).is_some_and(|decl| {
        matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
            && decl.type_private == PrivateFlag::Private
            && decl
                .type_manifest
                .is_some_and(|manifest| ctx.get_level(ctx.repr(manifest)) == GENERIC_LEVEL)
    })
}

fn type_expr_path_same(ctx: &TypeContext, ty: TypeExprRef, target_path: &Path) -> bool {
    matches!(
        &*ctx.get_desc(ctx.repr(ty)),
        TypeDesc::Tconstr { path, args, .. } if args.is_empty() && path.same(target_path)
    )
}

fn variant_constructor_as_payload(
    tag: &Option<crate::types::VariantLiteralTag>,
) -> Option<VariantConstructorAsPayload> {
    tag.as_ref().map(|tag| match tag {
        crate::types::VariantLiteralTag::String(_) => VariantConstructorAsPayload::String,
        crate::types::VariantLiteralTag::Int(_) => VariantConstructorAsPayload::Int,
        crate::types::VariantLiteralTag::Float(_) => VariantConstructorAsPayload::Float,
        crate::types::VariantLiteralTag::BigInt(_) => VariantConstructorAsPayload::BigInt,
        crate::types::VariantLiteralTag::Bool(_) => VariantConstructorAsPayload::Bool,
        crate::types::VariantLiteralTag::Null => VariantConstructorAsPayload::Null,
        crate::types::VariantLiteralTag::Undefined => VariantConstructorAsPayload::Undefined,
    })
}

/// variant_coercion.ml `variant_representation_matches`: the runtime
/// literals of `Variant_runtime.constructor_tag layout position`, compared
/// by value.
fn variant_representation_matches(
    layout1: &crate::types::VariantLayout,
    position1: usize,
    layout2: &crate::types::VariantLayout,
    position2: usize,
) -> bool {
    crate::types::variant_runtime::same_literal_value(
        layout1.constructor_tag(position1),
        layout2.constructor_tag(position2),
    )
}

fn variant_constructor_covers_primitive(
    ctx: &TypeContext,
    constructor: &crate::types::decl::ConstructorDeclaration,
    primitive_path: &Path,
) -> bool {
    match &constructor.cd_args {
        crate::types::decl::ConstructorArguments::CstrTuple(args) if args.len() == 1 => {
            type_expr_path_same(ctx, args[0], primitive_path)
        }
        _ => false,
    }
}

fn variant_constructor_matches_polyvariant_label(
    ctx: &TypeContext,
    constructor: &crate::types::decl::ConstructorDeclaration,
    tag: &Option<crate::types::VariantLiteralTag>,
    label: &str,
    unboxed: bool,
) -> bool {
    if let Some(crate::types::VariantLiteralTag::String(as_string)) = tag {
        return as_string == label;
    }
    if tag.is_some() {
        return false;
    }
    if unboxed
        && let crate::types::decl::ConstructorArguments::CstrTuple(args) = &constructor.cd_args
        && args.len() == 1
        && type_expr_path_same(ctx, args[0], &crate::types::predef::path_string())
    {
        return true;
    }
    constructor.cd_id.name() == label
}

fn can_coerce_polyvariant_to_variant(
    ctx: &TypeContext,
    row: &RowDesc,
    constructors: &[crate::types::decl::ConstructorDeclaration],
    unboxed: bool,
) -> bool {
    // OCaml compiler/ml/variant_coercion.ml:246-286 accepts only closed
    // payload-free polymorphic variant rows, then compares each row label with
    // the target variant constructor runtime representation.
    row.row_fields.iter().all(|(label, field)| {
        matches!(btype::row_field_repr(ctx, field), RowField::Rpresent(None))
            && constructors.iter().any(|constructor| {
                variant_constructor_matches_polyvariant_label(
                    ctx,
                    constructor,
                    &constructor.cd_runtime_tag,
                    label,
                    unboxed,
                )
            })
    })
}

fn is_valid_hash_number_label(value: &str) -> bool {
    let bytes = value.as_bytes();
    match bytes {
        [] => false,
        [b'0'..=b'9'] => true,
        [b'1'..=b'9', rest @ ..] => rest.iter().all(u8::is_ascii_digit),
        _ => false,
    }
}

fn variant_row_is_subtype_of_primitive(
    ctx: &TypeContext,
    row: &RowDesc,
    target: TypeExprRef,
) -> bool {
    // OCaml compiler/core/matching_polyfill.ml:51-70 plugs
    // Ctype.variant_is_subtype at compiler/core/bs_conditional_initial.ml:33:
    // closed payload-free numeric rows coerce to int, and closed payload-free
    // nonnumeric rows coerce to string.
    let row = row_repr(ctx, row);
    if !row.row_closed {
        return false;
    }
    let mut numeric_row = None;
    for (label, field) in &row.row_fields {
        if !matches!(
            btype::row_field_repr(ctx, field),
            RowField::Rabsent | RowField::Rpresent(None)
        ) {
            return false;
        }
        let numeric = is_valid_hash_number_label(label);
        match numeric_row {
            Some(expected) if expected != numeric => return false,
            Some(_) => {}
            None => numeric_row = Some(numeric),
        }
    }
    match numeric_row {
        Some(true) => type_expr_path_same(ctx, target, &crate::types::predef::path_int()),
        Some(false) => type_expr_path_same(ctx, target, &crate::types::predef::path_string()),
        None => false,
    }
}

fn variant_runtime_representation_issues(
    ctx: &TypeContext,
    constructors: &[crate::types::decl::ConstructorDeclaration],
    target_path: &Path,
    unboxed: bool,
) -> Vec<VariantRuntimeRepresentationIssue> {
    constructors
        .iter()
        .filter_map(|constructor| {
            let constructor_name = constructor.cd_id.name().to_string();
            match &constructor.cd_args {
                crate::types::decl::ConstructorArguments::CstrTuple(args)
                    if args.len() == 1 && unboxed =>
                {
                    let matches_unboxed_payload = (target_path
                        .same(&crate::types::predef::path_string())
                        || target_path.same(&crate::types::predef::path_float())
                        || target_path.same(&crate::types::predef::path_bigint()))
                        && type_expr_path_same(ctx, args[0], target_path);
                    if matches_unboxed_payload {
                        None
                    } else {
                        Some(
                            VariantRuntimeRepresentationIssue::MismatchedUnboxedPayload {
                                constructor_name,
                                expected_typename: target_path.clone(),
                            },
                        )
                    }
                }
                crate::types::decl::ConstructorArguments::CstrTuple(args) if args.is_empty() => {
                    // variant_coercion.ml: the messages name the declared `@as`.
                    let as_payload = variant_constructor_as_payload(&constructor.cd_runtime_tag);
                    let matches_as_payload = match as_payload {
                        None | Some(VariantConstructorAsPayload::String) => {
                            target_path.same(&crate::types::predef::path_string())
                        }
                        Some(VariantConstructorAsPayload::Int) => {
                            target_path.same(&crate::types::predef::path_int())
                        }
                        Some(VariantConstructorAsPayload::Float) => {
                            target_path.same(&crate::types::predef::path_float())
                        }
                        Some(VariantConstructorAsPayload::BigInt) => {
                            target_path.same(&crate::types::predef::path_bigint())
                        }
                        Some(
                            VariantConstructorAsPayload::Bool
                            | VariantConstructorAsPayload::Null
                            | VariantConstructorAsPayload::Undefined,
                        ) => {
                            return Some(
                                VariantRuntimeRepresentationIssue::AsPayloadNotEligibleForCoercion {
                                    constructor_name,
                                    expected_typename: target_path.clone(),
                                    as_payload: as_payload.expect("matched Some payload"),
                                },
                            );
                        }
                    };
                    if matches_as_payload {
                        None
                    } else {
                        Some(VariantRuntimeRepresentationIssue::MismatchedAsPayload {
                            constructor_name,
                            expected_typename: target_path.clone(),
                            as_payload,
                        })
                    }
                }
                crate::types::decl::ConstructorArguments::CstrTuple(_) => Some(
                    VariantRuntimeRepresentationIssue::CannotCoerceNonUnboxedWithPayload {
                        constructor_name,
                        expected_typename: target_path.clone(),
                    },
                ),
                crate::types::decl::ConstructorArguments::CstrRecord(_) => Some(
                    VariantRuntimeRepresentationIssue::InlineRecordCannotBeCoerced {
                        constructor_name,
                    },
                ),
            }
        })
        .collect()
}

/// A constraint collected by `subtype_rec`: OCaml's
/// `(trace, t1, t2, univar_pairs, ctx)` (ctype.ml:3435-3897). The trace is
/// kept outermost first, i.e. OCaml's `List.rev trace`.
#[derive(Debug, Clone)]
pub struct SubtypeConstraint {
    trace: Vec<TypePair>,
    t1: TypeExprRef,
    t2: TypeExprRef,
    univar_pairs: Vec<UnivarPairEntry>,
    context: Option<SubtypeContext>,
}

/// The constraint set built by [`subtype`]; [`force_subtype`] enforces it.
/// `univar_slots` are the slots the constraints' `univar_pairs` share
/// (OCaml's `type_expr option ref`s).
#[derive(Debug, Clone, Default)]
pub struct SubtypeConstraints {
    cstrs: Vec<SubtypeConstraint>,
    univar_slots: Vec<Option<TypeExprRef>>,
}

/// The constraint accumulator threaded through `subtype_rec`, with OCaml's
/// global `univar_pairs` at the current point.
#[derive(Debug, Clone, Default)]
struct SubtypeAcc {
    cstrs: Vec<SubtypeConstraint>,
    univar_pairs: Vec<UnivarPairEntry>,
    univar_slots: Vec<Option<TypeExprRef>>,
}

impl SubtypeAcc {
    /// An empty accumulator at the same `univar_pairs`.
    fn child(&self) -> SubtypeAcc {
        SubtypeAcc {
            cstrs: Vec::new(),
            univar_pairs: self.univar_pairs.clone(),
            univar_slots: self.univar_slots.clone(),
        }
    }
}

impl std::ops::Deref for SubtypeAcc {
    type Target = Vec<SubtypeConstraint>;
    fn deref(&self) -> &Self::Target {
        &self.cstrs
    }
}

impl std::ops::DerefMut for SubtypeAcc {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cstrs
    }
}

/// ctype.ml `change`: how `build_subtype` changed a type.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SubtypeChange {
    Unchanged,
    Changed,
}

/// The state threaded through ctype.ml `build_subtype`: the `warn` flag
/// (whether double coercion might do better).
struct BuildSubtype<'a, 'e> {
    ctx: &'a TypeContext,
    env: &'e Env,
    warn: bool,
}

/// ctype.ml `pred_expand`.
fn pred_expand(n: i32) -> i32 {
    if n % 2 == 0 && n > 0 { n - 1 } else { n }
}

/// ctype.ml `pred_enlarge`.
fn pred_enlarge(n: i32) -> i32 {
    if n % 2 == 1 { n - 1 } else { n }
}

impl BuildSubtype<'_, '_> {
    /// ctype.ml `filter_visited`.
    fn filter_visited(&self, visited: &[TypeExprRef]) -> Vec<TypeExprRef> {
        let start = visited
            .iter()
            .position(|t| {
                matches!(
                    &*self.ctx.get_desc(*t),
                    TypeDesc::Tobject { .. } | TypeDesc::Tvariant(_)
                )
            })
            .unwrap_or(visited.len());
        visited[start..].to_vec()
    }

    /// ctype.ml `memq_warn`.
    fn memq_warn(&mut self, t: TypeExprRef, visited: &[TypeExprRef]) -> bool {
        if visited.contains(&t) {
            self.warn = true;
            true
        } else {
            false
        }
    }

    /// ctype.ml `safe_abbrev`.
    fn safe_abbrev(&self, ty: TypeExprRef) -> bool {
        let snap = self.ctx.snapshot_type_state();
        if try_expand_head(self.ctx, self.env, ty).is_some() {
            true
        } else {
            self.ctx.restore_type_state(snap);
            false
        }
    }

    /// ctype.ml `has_constr_row'`.
    fn has_constr_row_expanded(&self, t: TypeExprRef) -> bool {
        try_expand_head(self.ctx, self.env, t).is_some_and(|t| btype::has_constr_row(self.ctx, t))
    }

    /// ctype.ml `build_subtype env visited loops posi level t`. Rust has no
    /// positive loops to reproduce (`loops` is always empty in
    /// `enlarge_type`).
    fn build(
        &mut self,
        visited: &[TypeExprRef],
        posi: bool,
        level: i32,
        t: TypeExprRef,
    ) -> (TypeExprRef, SubtypeChange) {
        let ctx = self.ctx;
        let t = ctx.repr(t);
        let desc = (*ctx.get_desc(t)).clone();
        match desc {
            TypeDesc::Tvar(..) => (t, SubtypeChange::Unchanged),
            TypeDesc::Tarrow { args, ret } => {
                if self.memq_warn(t, visited) {
                    return (t, SubtypeChange::Unchanged);
                }
                let mut visited = visited.to_vec();
                visited.insert(0, t);
                let params: Vec<_> = args
                    .iter()
                    .map(|arg| {
                        let (t1, c1) = self.build(&visited, !posi, level, arg.typ);
                        let mut arg = arg.clone();
                        arg.typ = t1;
                        (arg, c1)
                    })
                    .collect();
                let (t2, c2) = self.build(&visited, posi, level, ret);
                let c = params.iter().fold(c2, |acc, (_, c1)| acc.max(*c1));
                if c > SubtypeChange::Unchanged {
                    let args = params.into_iter().map(|(arg, _)| arg).collect();
                    (ctx.new_type(TypeDesc::Tarrow { args, ret: t2 }), c)
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Ttuple(tlist) => {
                if self.memq_warn(t, visited) {
                    return (t, SubtypeChange::Unchanged);
                }
                let mut visited = visited.to_vec();
                visited.insert(0, t);
                let tlist2: Vec<_> = tlist
                    .iter()
                    .map(|t| self.build(&visited, posi, level, *t))
                    .collect();
                let c = tlist2
                    .iter()
                    .fold(SubtypeChange::Unchanged, |acc, (_, c)| acc.max(*c));
                if c > SubtypeChange::Unchanged {
                    (
                        ctx.new_tuple(tlist2.into_iter().map(|(t, _)| t).collect()),
                        c,
                    )
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tconstr { ref path, .. }
                if level > 0
                    && generic_abbrev(ctx, self.env, path)
                    && self.safe_abbrev(t)
                    && !self.has_constr_row_expanded(t) =>
            {
                let expanded = try_expand_head(ctx, self.env, t).expect("safe_abbrev");
                let t1 = ctx.repr(expanded);
                let (t2, c) = self.build(visited, posi, pred_expand(level), t1);
                if c > SubtypeChange::Unchanged {
                    (t2, c)
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tconstr { path, args, .. } => {
                // Must check recursion on constructors, since we do not
                // always expand them.
                if self.memq_warn(t, visited) {
                    return (t, SubtypeChange::Unchanged);
                }
                let mut visited = visited.to_vec();
                visited.insert(0, t);
                let Some(decl) = lookup_type_decl_for_path(ctx, self.env, &path) else {
                    return (t, SubtypeChange::Unchanged);
                };
                let variance = decl.type_variance.clone();
                if level == 0
                    && generic_abbrev(ctx, self.env, &path)
                    && self.safe_abbrev(t)
                    && !self.has_constr_row_expanded(t)
                {
                    self.warn = true;
                }
                let tl2: Vec<_> = variance
                    .iter()
                    .zip(args.iter())
                    .map(|(v, t)| {
                        let (co, cn) = v.get_upper();
                        if cn {
                            if co {
                                (*t, SubtypeChange::Unchanged)
                            } else {
                                self.build(&visited, !posi, level, *t)
                            }
                        } else if co {
                            self.build(&visited, posi, level, *t)
                        } else {
                            (ctx.new_var(None), SubtypeChange::Changed)
                        }
                    })
                    .collect();
                let c = tl2
                    .iter()
                    .fold(SubtypeChange::Unchanged, |acc, (_, c)| acc.max(*c));
                if c > SubtypeChange::Unchanged {
                    (
                        ctx.new_constr(path, tl2.into_iter().map(|(t, _)| t).collect()),
                        c,
                    )
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tvariant(row) => {
                let row = btype::row_repr(ctx, &row);
                if self.memq_warn(t, visited) || !btype::static_row(ctx, &row) {
                    return (t, SubtypeChange::Unchanged);
                }
                let level2 = pred_enlarge(level);
                let mut visited = if level2 < level {
                    Vec::new()
                } else {
                    self.filter_visited(visited)
                };
                visited.insert(0, t);
                // `filter_row_fields false`: drop absent fields.
                let fields: Vec<_> = row
                    .row_fields
                    .iter()
                    .filter(|(_, f)| !btype::row_field_is_absent(ctx, f))
                    .cloned()
                    .collect();
                let fields: Vec<_> = fields
                    .into_iter()
                    .map(|(l, f)| match btype::row_field_repr(ctx, &f) {
                        RowField::Rpresent(None) => {
                            if posi {
                                (
                                    (
                                        l,
                                        RowField::Reither {
                                            constant: true,
                                            types: Vec::new(),
                                            matched: false,
                                            link: ctx.alloc_row_field(None),
                                        },
                                    ),
                                    SubtypeChange::Unchanged,
                                )
                            } else {
                                ((l, f), SubtypeChange::Unchanged)
                            }
                        }
                        RowField::Rpresent(Some(t)) => {
                            let (t2, c) = self.build(&visited, posi, level2, t);
                            let f = if posi && level > 0 {
                                RowField::Reither {
                                    constant: false,
                                    types: vec![t2],
                                    matched: false,
                                    link: ctx.alloc_row_field(None),
                                }
                            } else {
                                RowField::Rpresent(Some(t2))
                            };
                            ((l, f), c)
                        }
                        _ => unreachable!("build_subtype: non-static row field"),
                    })
                    .collect();
                let c = fields
                    .iter()
                    .fold(SubtypeChange::Unchanged, |acc, (_, c)| acc.max(*c));
                let row = RowDesc {
                    row_fields: fields
                        .into_iter()
                        .map(|(f, _)| f)
                        .collect::<Vec<_>>()
                        .into(),
                    row_more: ctx.new_var(None),
                    row_closed: posi,
                    row_fixed: false,
                    row_name: if c > SubtypeChange::Unchanged {
                        None
                    } else {
                        row.row_name.clone()
                    },
                };
                (ctx.new_variant(row), SubtypeChange::Changed)
            }
            TypeDesc::Tobject { fields: t1 } => {
                if self.memq_warn(t, visited) || object_row_is_structurally_open(ctx, t1) {
                    return (t, SubtypeChange::Unchanged);
                }
                let level2 = pred_enlarge(level);
                let mut visited = if level2 < level {
                    Vec::new()
                } else {
                    self.filter_visited(visited)
                };
                visited.insert(0, t);
                let (t2, c) = self.build(&visited, posi, level2, t1);
                if c > SubtypeChange::Unchanged {
                    (ctx.new_type(TypeDesc::Tobject { fields: t2 }), c)
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tfield {
                name,
                mutability,
                typ: t1,
                rest: t2,
            } => {
                let flag = ctx.mutability_repr(mutability);
                let (t1b, c1) = match flag {
                    // Do not enlarge a mutable field's type. The unification
                    // performed after enlargement will then require the
                    // source and target field types to be equivalent.
                    crate::types::asttypes::MutableFlag::Mutable => (t1, SubtypeChange::Unchanged),
                    crate::types::asttypes::MutableFlag::Immutable => {
                        self.build(visited, posi, level, t1)
                    }
                };
                let (t2b, c2) = self.build(visited, posi, level, t2);
                let c = c1.max(c2);
                if c > SubtypeChange::Unchanged {
                    // The enlarged type is an approximation, not a view of the
                    // declared type: it gets its own unlinked cell.
                    (
                        ctx.new_type(TypeDesc::Tfield {
                            name,
                            mutability: ctx.alloc_mutability(
                                crate::types::type_expr::FieldMutability::Value(flag),
                            ),
                            typ: t1b,
                            rest: t2b,
                        }),
                        c,
                    )
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tnil => {
                if posi {
                    (ctx.new_var(None), SubtypeChange::Changed)
                } else {
                    self.warn = true;
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tsubst(_) | TypeDesc::Tlink(_) => unreachable!("build_subtype"),
            TypeDesc::Tpoly { body, vars } => {
                let (t1, c) = self.build(visited, posi, level, body);
                if c > SubtypeChange::Unchanged {
                    (ctx.new_type(TypeDesc::Tpoly { body: t1, vars }), c)
                } else {
                    (t, SubtypeChange::Unchanged)
                }
            }
            TypeDesc::Tunivar(..) | TypeDesc::Tpackage { .. } => (t, SubtypeChange::Unchanged),
        }
    }
}

/// ctype.ml `enlarge_type env ty`: a supertype approximation of `ty` and
/// whether double coercion might do better.
pub fn enlarge_type(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> (TypeExprRef, bool) {
    let mut builder = BuildSubtype {
        ctx,
        env,
        warn: false,
    };
    // `level = 4` allows 2 expansions involving objects/variants.
    let (ty, _) = builder.build(&[], true, 4, ty);
    (ty, builder.warn)
}

/// OCaml `Ctype.subtype env ty1 ty2` (ctype.ml:3905-3923): build the
/// constraint set, raising only the structural errors `subtype_rec` raises
/// directly. The returned constraints are enforced by [`force_subtype`], the
/// closure OCaml returns.
pub fn subtype(
    ctx: &TypeContext,
    env: &Env,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeResult<SubtypeConstraints> {
    let mut subtypes = HashSet::new();
    let mut cstrs = SubtypeAcc::default();
    subtype_rec(ctx, env, &mut subtypes, &[(ty1, ty2)], ty1, ty2, &mut cstrs)?;
    Ok(SubtypeConstraints {
        cstrs: cstrs.cstrs,
        univar_slots: cstrs.univar_slots,
    })
}

/// The closure returned by OCaml `Ctype.subtype`: unify each constraint in
/// registration order (`List.rev cstrs`); a failure raises
/// `Subtype (expand_trace env (List.rev trace0), List.tl (List.tl trace), ctx)`.
pub fn force_subtype(ctx: &TypeContext, env: &Env, cstrs: SubtypeConstraints) -> TypeResult<()> {
    let mut univar_slots = cstrs.univar_slots;
    for cstr in cstrs.cstrs {
        // ctype.ml `unify_pairs (ref env) t1 t2 pairs`.
        let mut unify_state = UnifyState::new();
        unify_state.set_env(env);
        unify_state.univar_pairs = cstr.univar_pairs;
        unify_state.univar_slots = std::mem::take(&mut univar_slots);
        let result = unify(ctx, &mut unify_state, cstr.t1, cstr.t2);
        univar_slots = std::mem::take(&mut unify_state.univar_slots);
        if let Err(err) = result {
            let trace = match err {
                TypeError::Unify(trace) => trace,
                _ => Vec::new(),
            };
            record_trace_expansions(ctx, env, &cstr.trace);
            // Rust traces hold one pair per level; OCaml's expanded trace has
            // two entries per level, so `List.tl (List.tl trace)` drops one.
            let trace2 = trace.get(1..).map(<[TypePair]>::to_vec).unwrap_or_default();
            return Err(TypeError::Subtype {
                trace: cstr.trace,
                trace2,
                context: cstr.context,
            });
        }
    }
    Ok(())
}

/// `subtype env ty1 ty2 ()`: build and enforce the constraints at once.
pub fn subtype_now(
    ctx: &TypeContext,
    env: &Env,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeResult<()> {
    let cstrs = subtype(ctx, env, ty1, ty2)?;
    force_subtype(ctx, env, cstrs)
}

/// OCaml `subtype_error env trace` (ctype.ml:3427-3428).
fn subtype_error(ctx: &TypeContext, env: &Env, trace: &[TypePair]) -> TypeError {
    record_trace_expansions(ctx, env, trace);
    TypeError::Subtype {
        trace: trace.to_vec(),
        trace2: Vec::new(),
        context: None,
    }
}

fn push_subtype_cstr(
    cstrs: &mut SubtypeAcc,
    trace: &[TypePair],
    t1: TypeExprRef,
    t2: TypeExprRef,
    context: Option<SubtypeContext>,
) {
    let univar_pairs = cstrs.univar_pairs.clone();
    cstrs.push(SubtypeConstraint {
        trace: trace.to_vec(),
        t1,
        t2,
        univar_pairs,
        context,
    });
}

fn with_trace(trace: &[TypePair], t1: TypeExprRef, t2: TypeExprRef) -> Vec<TypePair> {
    let mut trace = trace.to_vec();
    trace.push((t1, t2));
    trace
}

/// OCaml `generic_abbrev env path` (ctype.ml:1317-1321), through
/// `Env.find_type_expansion` (env.ml:830-838).
fn generic_abbrev(ctx: &TypeContext, env: &Env, path: &Path) -> bool {
    lookup_type_decl_for_path(ctx, env, path).is_some_and(|decl| {
        decl.type_manifest.is_some_and(|body| {
            (decl.type_private == PrivateFlag::Public
                || !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract)
                || btype::has_constr_row(ctx, body))
                && ctx.get_level(ctx.repr(body)) == GENERIC_LEVEL
        })
    })
}

/// OCaml `extract_concrete_typedecl env ty` (ctype.ml:1249-1261):
/// `(p, p', decl)` for the path of `ty` and the first non-abstract
/// declaration its expansion reaches.
pub(crate) fn extract_concrete_typedecl(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<(Path, Path, crate::types::TypeDeclaration)> {
    let ty = ctx.repr(ty);
    let path = match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, .. } => path.clone(),
        _ => return None,
    };
    let decl = lookup_type_decl_for_path(ctx, env, &path)?;
    if !matches!(decl.type_kind, crate::types::TypeKind::TypeAbstract) {
        return Some((path.clone(), path, decl.into_owned()));
    }
    let expanded = try_expand_head(ctx, env, ty)?;
    let (_, concrete, decl) = extract_concrete_typedecl(ctx, env, expanded)?;
    Some((path, concrete, decl))
}

/// `Variant_coercion.can_try_coerce_variant_to_primitive`
/// (variant_coercion.ml:139-157): the concrete variant path, constructors,
/// layout and unboxed flag of a parameterless variant other than `bool`.
fn can_try_coerce_variant_to_primitive_opt(
    ctx: &TypeContext,
    concrete: Option<(Path, Path, crate::types::TypeDeclaration)>,
) -> Option<(Path, Vec<crate::types::decl::ConstructorDeclaration>, bool)> {
    let (_, path, decl) = concrete?;
    match &decl.type_kind {
        crate::types::TypeKind::TypeVariant(constructors, _)
            if decl.type_params.is_empty() && !path.same(&crate::types::predef::path_bool()) =>
        {
            let unboxed = variant_runtime_configuration(ctx, &decl).unboxed;
            Some((path, constructors.to_vec(), unboxed))
        }
        _ => None,
    }
}

/// OCaml `coerces_into_private_type env t1 t2` (ctype.ml:3504-3516):
/// whether `t2` is a private record or variant that `t1`, another type,
/// would be coerced into.
fn coerces_into_private_type(
    ctx: &TypeContext,
    env: &Env,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> bool {
    match extract_concrete_typedecl(ctx, env, t2) {
        Some((p2, _, decl))
            if decl.type_private == PrivateFlag::Private
                && matches!(
                    decl.type_kind,
                    crate::types::TypeKind::TypeRecord(..)
                        | crate::types::TypeKind::TypeVariant(..)
                ) =>
        {
            match extract_concrete_typedecl(ctx, env, t1) {
                Some((p1, _, _)) => !p1.same(&p2),
                None => true,
            }
        }
        Some(_) | None => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn subtype_rec(
    ctx: &TypeContext,
    env: &Env,
    subtypes: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    trace: &[TypePair],
    t1: TypeExprRef,
    t2: TypeExprRef,
    cstrs: &mut SubtypeAcc,
) -> TypeResult<()> {
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 || !subtypes.insert((t1, t2)) {
        return Ok(());
    }
    let desc1 = (*ctx.get_desc(t1)).clone();
    let desc2 = (*ctx.get_desc(t2)).clone();
    match (&desc1, &desc2) {
        (TypeDesc::Tvar(..), _) | (_, TypeDesc::Tvar(..)) => {
            push_subtype_cstr(cstrs, trace, t1, t2, None);
            Ok(())
        }
        (
            TypeDesc::Tarrow {
                args: args1,
                ret: ret1,
            },
            TypeDesc::Tarrow {
                args: args2,
                ret: ret2,
            },
        ) if args1.len() == args2.len()
            && args1
                .iter()
                .zip(args2)
                .all(|(a1, a2)| a1.label().same_label(a2.label())) =>
        {
            for (a1, a2) in args1.iter().zip(args2) {
                subtype_rec(
                    ctx,
                    env,
                    subtypes,
                    &with_trace(trace, a2.typ, a1.typ),
                    a2.typ,
                    a1.typ,
                    cstrs,
                )?;
            }
            subtype_rec(
                ctx,
                env,
                subtypes,
                &with_trace(trace, *ret1, *ret2),
                *ret1,
                *ret2,
                cstrs,
            )
        }
        (TypeDesc::Ttuple(tl1), TypeDesc::Ttuple(tl2)) => {
            subtype_list(ctx, env, subtypes, trace, tl1, tl2, cstrs)
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) if a1.is_empty() && a2.is_empty() && p1.same(p2) => Ok(()),
        (TypeDesc::Tconstr { path: p1, .. }, _)
            if generic_abbrev(ctx, env, p1) && try_expand_head(ctx, env, t1).is_some() =>
        {
            let expanded = try_expand_head(ctx, env, t1).expect("checked by safe_abbrev");
            subtype_rec(ctx, env, subtypes, trace, expanded, t2, cstrs)
        }
        (_, TypeDesc::Tconstr { path: p2, .. })
            if generic_abbrev(ctx, env, p2) && try_expand_head(ctx, env, t2).is_some() =>
        {
            let expanded = try_expand_head(ctx, env, t2).expect("checked by safe_abbrev");
            subtype_rec(ctx, env, subtypes, trace, t1, expanded, cstrs)
        }
        (
            TypeDesc::Tconstr {
                path: p1,
                args: tl1,
                ..
            },
            TypeDesc::Tconstr {
                path: p2,
                args: tl2,
                ..
            },
        ) if p1.same(p2) => {
            let Some(decl) = lookup_type_decl_for_path(ctx, env, p1) else {
                push_subtype_cstr(cstrs, trace, t1, t2, None);
                return Ok(());
            };
            for (variance, (&a1, &a2)) in decl.type_variance.iter().zip(tl1.iter().zip(tl2.iter()))
            {
                let (co, cn) = variance.get_upper();
                if co && cn {
                    // Invariant argument: check both ways.
                    let mut forward = cstrs.child();
                    subtype_rec(
                        ctx,
                        env,
                        subtypes,
                        &with_trace(trace, a1, a2),
                        a1,
                        a2,
                        &mut forward,
                    )?;
                    let mut backward = cstrs.child();
                    let both_empty = forward.is_empty() && {
                        subtype_rec(
                            ctx,
                            env,
                            subtypes,
                            &with_trace(trace, a2, a1),
                            a2,
                            a1,
                            &mut backward,
                        )?;
                        backward.is_empty()
                    };
                    if !both_empty {
                        let tuple1 = ctx.alloc_type_at_level(
                            TypeDesc::Ttuple(vec![a1].into()),
                            ctx.get_level(a1),
                        );
                        let tuple2 = ctx.alloc_type_at_level(
                            TypeDesc::Ttuple(vec![a2].into()),
                            ctx.get_level(a2),
                        );
                        push_subtype_cstr(cstrs, trace, tuple1, tuple2, None);
                    }
                } else if co {
                    subtype_rec(
                        ctx,
                        env,
                        subtypes,
                        &with_trace(trace, a1, a2),
                        a1,
                        a2,
                        cstrs,
                    )?;
                } else if cn {
                    subtype_rec(
                        ctx,
                        env,
                        subtypes,
                        &with_trace(trace, a2, a1),
                        a2,
                        a1,
                        cstrs,
                    )?;
                }
            }
            Ok(())
        }
        (TypeDesc::Tconstr { path: p1, .. }, _) if generic_private_abbrev(ctx, env, p1) => {
            match try_expand_head_with_mode(ctx, env, t1, ExpandHeadMode::Optimize) {
                Some(expanded) => subtype_rec(ctx, env, subtypes, trace, expanded, t2, cstrs),
                None => {
                    push_subtype_cstr(cstrs, trace, t1, t2, None);
                    Ok(())
                }
            }
        }
        (_, TypeDesc::Tconstr { .. }) if coerces_into_private_type(ctx, env, t1, t2) => {
            // Only the module defining a private record or variant builds its
            // values; a coercion from another type would build one anywhere
            // (ctype.ml:3582-3595).
            let (typename, _, _) =
                extract_concrete_typedecl(ctx, env, t2).expect("checked by the guard");
            push_subtype_cstr(
                cstrs,
                trace,
                t1,
                t2,
                Some(SubtypeContext::CoercionIntoPrivateType { typename }),
            );
            Ok(())
        }
        (
            TypeDesc::Tconstr {
                path: p1, args: a1, ..
            },
            TypeDesc::Tconstr {
                path: p2, args: a2, ..
            },
        ) if a1.is_empty()
            && a2.is_empty()
            && p1.same(&crate::types::predef::path_int())
            && p2.same(&crate::types::predef::path_float()) =>
        {
            // Int can always be coerced to float.
            Ok(())
        }
        (TypeDesc::Tconstr { path, args: a1, .. }, TypeDesc::Tconstr { args: a2, .. })
            if a1.is_empty()
                && a2.is_empty()
                && primitive_coercion_path(path)
                && can_try_coerce_variant_to_primitive_opt(
                    ctx,
                    extract_concrete_typedecl(ctx, env, t2),
                )
                .is_some() =>
        {
            // Primitive to an eligible unboxed variant.
            let (p, constructors, unboxed) = can_try_coerce_variant_to_primitive_opt(
                ctx,
                extract_concrete_typedecl(ctx, env, t2),
            )
            .expect("checked above");
            if !unboxed {
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(SubtypeContext::CoercionTargetVariantNotUnboxed {
                        variant_name: p,
                        primitive: path.clone(),
                    }),
                );
            } else if !constructors
                .iter()
                .any(|constructor| variant_constructor_covers_primitive(ctx, constructor, path))
            {
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(SubtypeContext::CoercionTargetVariantDoesNotCoverType {
                        variant_name: p,
                        primitive: path.clone(),
                    }),
                );
            }
            Ok(())
        }
        (TypeDesc::Tconstr { args: a1, .. }, TypeDesc::Tconstr { path, args: a2, .. })
            if a1.is_empty()
                && a2.is_empty()
                && primitive_coercion_path(path)
                && can_try_coerce_variant_to_primitive_opt(
                    ctx,
                    extract_concrete_typedecl(ctx, env, t1),
                )
                .is_some() =>
        {
            // Variant to a primitive.
            let (p, constructors, unboxed) = can_try_coerce_variant_to_primitive_opt(
                ctx,
                extract_concrete_typedecl(ctx, env, t1),
            )
            .expect("checked above");
            let issues = variant_runtime_representation_issues(ctx, &constructors, path, unboxed);
            if !issues.is_empty() {
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(
                        SubtypeContext::VariantConstructorRuntimeRepresentationMismatch {
                            variant_name: p,
                            issues,
                        },
                    ),
                );
            }
            Ok(())
        }
        (TypeDesc::Tconstr { args: a1, .. }, TypeDesc::Tconstr { args: a2, .. })
            if a1.is_empty() && a2.is_empty() =>
        {
            subtype_concrete_typedecls(ctx, env, subtypes, trace, t1, t2, cstrs)
        }
        (TypeDesc::Tobject { fields: f1, .. }, TypeDesc::Tobject { fields: f2, .. })
            if matches!(
                &*ctx.borrow_desc(object_row_of_fields(ctx, *f1)),
                TypeDesc::Tvar(..)
            ) && matches!(
                &*ctx.borrow_desc(object_row_of_fields(ctx, *f2)),
                TypeDesc::Tvar(..)
            ) =>
        {
            // Same row variable implies same object.
            push_subtype_cstr(cstrs, trace, t1, t2, None);
            Ok(())
        }
        (TypeDesc::Tobject { fields: f1, .. }, TypeDesc::Tobject { fields: f2, .. }) => {
            subtype_fields(ctx, env, subtypes, trace, *f1, *f2, cstrs)
        }
        (TypeDesc::Tvariant(row1), TypeDesc::Tvariant(row2)) => {
            let mut row_cstrs = cstrs.clone();
            match subtype_row(ctx, env, subtypes, trace, row1, row2, &mut row_cstrs)? {
                true => *cstrs = row_cstrs,
                false => push_subtype_cstr(cstrs, trace, t1, t2, None),
            }
            Ok(())
        }
        (TypeDesc::Tvariant(row), TypeDesc::Tconstr { args, .. })
            if row_repr(ctx, row).row_closed
                && args.is_empty()
                && matches!(
                    extract_concrete_typedecl(ctx, env, t2).map(|(_, _, decl)| decl.type_kind),
                    Some(crate::types::TypeKind::TypeVariant(..))
                ) =>
        {
            // Polymorphic variant to variant.
            let row = row_repr(ctx, row);
            if let Some((_, _, decl)) = extract_concrete_typedecl(ctx, env, t2)
                && let crate::types::TypeKind::TypeVariant(constructors, _) = &decl.type_kind
                && can_coerce_polyvariant_to_variant(
                    ctx,
                    &row,
                    constructors,
                    variant_runtime_configuration(ctx, &decl).unboxed,
                )
            {
                return Ok(());
            }
            push_subtype_cstr(cstrs, trace, t1, t2, None);
            Ok(())
        }
        (TypeDesc::Tvariant(row), _) if variant_row_is_subtype_of_primitive(ctx, row, t2) => Ok(()),
        (
            TypeDesc::Tpoly {
                body: u1,
                vars: tl1,
            },
            TypeDesc::Tpoly {
                body: u2,
                vars: tl2,
            },
        ) if tl1.is_empty() && tl2.is_empty() => {
            subtype_rec(ctx, env, subtypes, trace, *u1, *u2, cstrs)
        }
        (
            TypeDesc::Tpoly {
                body: u1,
                vars: tl1,
            },
            TypeDesc::Tpoly {
                body: u2,
                vars: tl2,
            },
        ) if tl2.is_empty() => {
            let (_, u1) = instance_poly(ctx, false, false, tl1, *u1);
            subtype_rec(ctx, env, subtypes, trace, u1, *u2, cstrs)
        }
        (
            TypeDesc::Tpoly {
                body: u1,
                vars: tl1,
            },
            TypeDesc::Tpoly {
                body: u2,
                vars: tl2,
            },
        ) => {
            // ctype.ml: `try enter_poly env univar_pairs u1 tl1 u2 tl2 (fun t1
            // t2 -> subtype_rec env trace t1 t2 cstrs) with Unify _ -> (trace,
            // t1, t2, !univar_pairs, None) :: cstrs`.
            let (u1, u2) = (*u1, *u2);
            let tl1: Vec<_> = tl1.iter().map(|&t| ctx.repr(t)).collect();
            let tl2: Vec<_> = tl2.iter().map(|&t| ctx.repr(t)).collect();
            let known: HashSet<TypeExprRef> = cstrs
                .univar_pairs
                .iter()
                .flat_map(|(cl, _)| cl.iter().map(|(t, _)| ctx.repr(*t)))
                .collect();
            if (tl1.iter().any(|t| known.contains(t))
                && mcomp_univars_escape(ctx, env, &cstrs.univar_pairs, &tl1, u2, &tl2))
                || (tl2.iter().any(|t| known.contains(t))
                    && mcomp_univars_escape(ctx, env, &cstrs.univar_pairs, &tl2, u1, &tl1))
            {
                push_subtype_cstr(cstrs, trace, t1, t2, None);
                return Ok(());
            }
            let new_slot = |cstrs: &mut SubtypeAcc| {
                cstrs.univar_slots.push(None);
                cstrs.univar_slots.len() - 1
            };
            let cl1: Vec<_> = tl1.iter().map(|&t| (t, new_slot(cstrs))).collect();
            let cl2: Vec<_> = tl2.iter().map(|&t| (t, new_slot(cstrs))).collect();
            let saved = cstrs.univar_pairs.len();
            cstrs.univar_pairs.push((cl2.clone(), cl1.clone()));
            cstrs.univar_pairs.push((cl1, cl2));
            let result = subtype_rec(ctx, env, subtypes, trace, u1, u2, cstrs);
            cstrs.univar_pairs.truncate(saved);
            result
        }
        _ => {
            push_subtype_cstr(cstrs, trace, t1, t2, None);
            Ok(())
        }
    }
}

/// OCaml `subtype_list` (ctype.ml:3796-3800).
fn subtype_list(
    ctx: &TypeContext,
    env: &Env,
    subtypes: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    trace: &[TypePair],
    tl1: &[TypeExprRef],
    tl2: &[TypeExprRef],
    cstrs: &mut SubtypeAcc,
) -> TypeResult<()> {
    if tl1.len() != tl2.len() {
        return Err(subtype_error(ctx, env, trace));
    }
    for (&t1, &t2) in tl1.iter().zip(tl2) {
        subtype_rec(
            ctx,
            env,
            subtypes,
            &with_trace(trace, t1, t2),
            t1,
            t2,
            cstrs,
        )?;
    }
    Ok(())
}

/// OCaml `subtype_fields` (ctype.ml:3802-3831).
fn subtype_fields(
    ctx: &TypeContext,
    env: &Env,
    subtypes: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    trace: &[TypePair],
    ty1: TypeExprRef,
    ty2: TypeExprRef,
    cstrs: &mut SubtypeAcc,
) -> TypeResult<()> {
    let (fields1, rest1) = flatten_fields(ctx, ty1);
    let (fields2, rest2) = flatten_fields(ctx, ty2);
    let (pairs, miss1, miss2) = associate_fields(fields1, fields2);
    let rest2_is_nil = matches!(&*ctx.borrow_desc(ctx.repr(rest2)), TypeDesc::Tnil);
    if !rest2_is_nil {
        if miss1.is_empty() {
            subtype_rec(
                ctx,
                env,
                subtypes,
                &with_trace(trace, rest1, rest2),
                rest1,
                rest2,
                cstrs,
            )?;
        } else {
            let level = ctx.get_level(ctx.repr(ty1));
            let built = build_fields(ctx, level, &miss1, rest1);
            push_subtype_cstr(cstrs, trace, built, rest2, None);
        }
    }
    if !miss2.is_empty() {
        let level = ctx.get_level(ctx.repr(ty2));
        let built = build_fields(ctx, level, &miss2, ctx.new_var(None));
        push_subtype_cstr(cstrs, trace, rest1, built, None);
    }
    for (f1, f2) in pairs {
        match ctx.mutability_repr(f2.mutability) {
            // Read-only target: covariant; a mutable source just forgets its
            // write permission.
            MutableFlag::Immutable => {
                let (t1, t2) = (f1.typ, f2.typ);
                subtype_rec(
                    ctx,
                    env,
                    subtypes,
                    &with_trace(trace, t1, t2),
                    t1,
                    t2,
                    cstrs,
                )?;
            }
            // A writable target requires equivalent field types: a deferred
            // unification constraint over transient one-field fragments. The
            // source fragment retains `rest1`, so `unify_fields` can observe
            // whether the source row was open and promote the field.
            MutableFlag::Mutable => {
                let src = ctx.new_type(TypeDesc::Tfield {
                    name: f1.name,
                    mutability: f1.mutability,
                    typ: f1.typ,
                    rest: rest1,
                });
                let rest = ctx.new_var(None);
                let tgt = ctx.new_type(TypeDesc::Tfield {
                    name: f2.name,
                    mutability: f2.mutability,
                    typ: f2.typ,
                    rest,
                });
                push_subtype_cstr(cstrs, trace, src, tgt, None);
            }
        }
    }
    Ok(())
}

/// OCaml `subtype_row` (ctype.ml:3833-3869); `Ok(false)` is its `Exit`.
fn subtype_row(
    ctx: &TypeContext,
    env: &Env,
    subtypes: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    trace: &[TypePair],
    row1: &RowDesc,
    row2: &RowDesc,
    cstrs: &mut SubtypeAcc,
) -> TypeResult<bool> {
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);
    let (r1, r2, pairs) = merge_row_fields(&row1.row_fields, &row2.row_fields);
    let more1 = ctx.repr(row_more(ctx, &row1));
    let more2 = ctx.repr(row_more(ctx, &row2));
    let more1_desc = (*ctx.get_desc(more1)).clone();
    let more2_desc = (*ctx.get_desc(more2)).clone();
    match (&more1_desc, &more2_desc) {
        (TypeDesc::Tconstr { path: p1, .. }, TypeDesc::Tconstr { path: p2, .. }) if p1.same(p2) => {
            subtype_rec(
                ctx,
                env,
                subtypes,
                &with_trace(trace, more1, more2),
                more1,
                more2,
                cstrs,
            )?;
            Ok(true)
        }
        (
            TypeDesc::Tvar(..) | TypeDesc::Tconstr { .. } | TypeDesc::Tnil,
            TypeDesc::Tvar(..) | TypeDesc::Tconstr { .. } | TypeDesc::Tnil,
        ) if row1.row_closed && r1.is_empty() => {
            for (_, f1, f2) in pairs {
                match (
                    btype::row_field_repr(ctx, f1),
                    btype::row_field_repr(ctx, f2),
                ) {
                    (
                        RowField::Rpresent(None) | RowField::Reither { constant: true, .. },
                        RowField::Rpresent(None),
                    )
                    | (RowField::Rabsent, _) => {}
                    (RowField::Rpresent(Some(t1)), RowField::Rpresent(Some(t2))) => {
                        subtype_rec(
                            ctx,
                            env,
                            subtypes,
                            &with_trace(trace, t1, t2),
                            t1,
                            t2,
                            cstrs,
                        )?;
                    }
                    (
                        RowField::Reither {
                            constant: false,
                            types,
                            ..
                        },
                        RowField::Rpresent(Some(t2)),
                    ) if !types.is_empty() => {
                        let t1 = types[0];
                        subtype_rec(
                            ctx,
                            env,
                            subtypes,
                            &with_trace(trace, t1, t2),
                            t1,
                            t2,
                            cstrs,
                        )?;
                    }
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }
        (TypeDesc::Tunivar(..), TypeDesc::Tunivar(..))
            if row1.row_closed == row2.row_closed && r1.is_empty() && r2.is_empty() =>
        {
            subtype_rec(
                ctx,
                env,
                subtypes,
                &with_trace(trace, more1, more2),
                more1,
                more2,
                cstrs,
            )?;
            for (_, f1, f2) in pairs {
                match (
                    btype::row_field_repr(ctx, f1),
                    btype::row_field_repr(ctx, f2),
                ) {
                    (RowField::Rpresent(None), RowField::Rpresent(None))
                    | (RowField::Rabsent, RowField::Rabsent) => {}
                    (
                        RowField::Reither {
                            constant: true,
                            types: types1,
                            ..
                        },
                        RowField::Reither {
                            constant: true,
                            types: types2,
                            ..
                        },
                    ) if types1.is_empty() && types2.is_empty() => {}
                    (RowField::Rpresent(Some(t1)), RowField::Rpresent(Some(t2))) => {
                        subtype_rec(
                            ctx,
                            env,
                            subtypes,
                            &with_trace(trace, t1, t2),
                            t1,
                            t2,
                            cstrs,
                        )?;
                    }
                    (
                        RowField::Reither {
                            constant: false,
                            types: types1,
                            ..
                        },
                        RowField::Reither {
                            constant: false,
                            types: types2,
                            ..
                        },
                    ) if types1.len() == 1 && types2.len() == 1 => {
                        let (t1, t2) = (types1[0], types2[0]);
                        subtype_rec(
                            ctx,
                            env,
                            subtypes,
                            &with_trace(trace, t1, t2),
                            t1,
                            t2,
                            cstrs,
                        )?;
                    }
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// The `Tconstr (_, [], _), Tconstr (_, [], _)` case of `subtype_rec`
/// (ctype.ml:3760-3950): coercion between variants and between records.
#[allow(clippy::too_many_arguments)]
fn subtype_concrete_typedecls(
    ctx: &TypeContext,
    env: &Env,
    subtypes: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    trace: &[TypePair],
    t1: TypeExprRef,
    t2: TypeExprRef,
    cstrs: &mut SubtypeAcc,
) -> TypeResult<()> {
    let (Some((p1, _, decl1)), Some((p2, _, decl2))) = (
        extract_concrete_typedecl(ctx, env, t1),
        extract_concrete_typedecl(ctx, env, t2),
    ) else {
        push_subtype_cstr(cstrs, trace, t1, t2, None);
        return Ok(());
    };
    match (&decl1.type_kind, &decl2.type_kind) {
        (
            crate::types::TypeKind::TypeVariant(c1, layout_ref1),
            crate::types::TypeKind::TypeVariant(c2, layout_ref2),
        ) => {
            if let Some(issue) = variant_configuration_issue(ctx, &decl1, &decl2) {
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(SubtypeContext::VariantConfigurationsMismatch {
                        left_variant_name: p1,
                        right_variant_name: p2,
                        issue,
                    }),
                );
                return Ok(());
            }
            if c1.len() > c2.len() {
                let c2_names: HashSet<&str> = c2.iter().map(|c| c.cd_id.name()).collect();
                let constructor_names = c1
                    .iter()
                    .map(|c| c.cd_id.name())
                    .filter(|name| !c2_names.contains(name))
                    .map(str::to_string)
                    .collect();
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(SubtypeContext::VariantConfigurationsMismatch {
                        left_variant_name: p1,
                        right_variant_name: p2,
                        issue: VariantConfigurationIssue::IncompatibleConstructorCount {
                            constructor_names,
                        },
                    }),
                );
                return Ok(());
            }
            let layout1 = ctx.variant_layout(*layout_ref1);
            let layout2 = ctx.variant_layout(*layout_ref2);
            let c2_by_name: HashMap<&str, (usize, &crate::types::decl::ConstructorDeclaration)> =
                c2.iter()
                    .enumerate()
                    .map(|(position, c)| (c.cd_id.name(), (position, c)))
                    .collect();
            let mut has_violation = false;
            for (position1, c) in c1.iter().enumerate() {
                let violation = match (&c.cd_args, c2_by_name.get(c.cd_id.name())) {
                    (
                        crate::types::decl::ConstructorArguments::CstrRecord(fields1),
                        Some((
                            position2,
                            crate::types::decl::ConstructorDeclaration {
                                cd_args:
                                    crate::types::decl::ConstructorArguments::CstrRecord(fields2),
                                ..
                            },
                        )),
                    ) => {
                        if variant_representation_matches(&layout1, position1, &layout2, *position2)
                        {
                            let (violations, mut tl1, mut tl2) =
                                check_record_fields(fields1, fields2);
                            if violations.is_empty() {
                                tl1.reverse();
                                tl2.reverse();
                                let mut probe = cstrs.clone();
                                match subtype_list(
                                    ctx, env, subtypes, trace, &tl1, &tl2, &mut probe,
                                ) {
                                    Ok(()) => probe.len() != cstrs.len(),
                                    Err(_) => true,
                                }
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    }
                    (
                        crate::types::decl::ConstructorArguments::CstrTuple(tl1),
                        Some((
                            position2,
                            crate::types::decl::ConstructorDeclaration {
                                cd_args: crate::types::decl::ConstructorArguments::CstrTuple(tl2),
                                ..
                            },
                        )),
                    ) => {
                        if variant_representation_matches(&layout1, position1, &layout2, *position2)
                        {
                            let mut probe = cstrs.clone();
                            match subtype_list(ctx, env, subtypes, trace, tl1, tl2, &mut probe) {
                                Ok(()) => probe.len() != cstrs.len(),
                                Err(_) => true,
                            }
                        } else {
                            true
                        }
                    }
                    _ => true,
                };
                has_violation |= violation;
            }
            if has_violation {
                push_subtype_cstr(cstrs, trace, t1, t2, None);
            }
            Ok(())
        }
        (
            crate::types::TypeKind::TypeRecord(fields1, repr1),
            crate::types::TypeKind::TypeRecord(fields2, repr2),
        ) => {
            if repr1 != repr2 {
                push_subtype_cstr(cstrs, trace, t1, t2, None);
                return Ok(());
            }
            let (violations, mut tl1, mut tl2) = check_record_fields(fields1, fields2);
            if !violations.is_empty() {
                push_subtype_cstr(
                    cstrs,
                    trace,
                    t1,
                    t2,
                    Some(SubtypeContext::RecordFieldsMismatch {
                        left_record_name: p1,
                        right_record_name: p2,
                        issues: violations,
                    }),
                );
                return Ok(());
            }
            // Record_coercion.check_record_fields builds its type lists with
            // cons during a left fold.
            tl1.reverse();
            tl2.reverse();
            subtype_list(ctx, env, subtypes, trace, &tl1, &tl2, cstrs)
        }
        (kind1, kind2) => {
            push_subtype_cstr(
                cstrs,
                trace,
                t1,
                t2,
                Some(SubtypeContext::DifferentTypeKinds {
                    left_typename: p1,
                    right_typename: p2,
                    left_type_kind: subtype_type_kind(kind1),
                    right_type_kind: subtype_type_kind(kind2),
                }),
            );
            Ok(())
        }
    }
}

fn check_record_fields(
    fields1: &[LabelDeclaration],
    fields2: &[LabelDeclaration],
) -> (
    Vec<RecordFieldSubtypeViolation>,
    Vec<TypeExprRef>,
    Vec<TypeExprRef>,
) {
    let mut issues = Vec::new();
    let mut field_types1 = Vec::new();
    let mut field_types2 = Vec::new();

    for field2 in fields2 {
        let Some(field1) = fields1
            .iter()
            .find(|field1| field1.ld_id.name() == field2.ld_id.name())
        else {
            issues.push(RecordFieldSubtypeViolation::FieldMissing {
                label: field2.ld_id.name().to_string(),
            });
            continue;
        };

        if field1.ld_optional != field2.ld_optional {
            issues.push(RecordFieldSubtypeViolation::OptionalMismatch {
                label: field1.ld_id.name().to_string(),
                left_optional: field1.ld_optional,
                right_optional: field2.ld_optional,
            });
        }

        if label_declaration_runtime_name(field1) != label_declaration_runtime_name(field2) {
            issues.push(RecordFieldSubtypeViolation::FieldRuntimeNameMismatch {
                label: field1.ld_id.name().to_string(),
                left_as: field1.ld_runtime_name.clone(),
                right_as: field2.ld_runtime_name.clone(),
            });
        }

        // record_coercion.ml:44-49: writing through the target would change
        // a field that the source treats as immutable.
        if field1.ld_mutable == MutableFlag::Immutable && field2.ld_mutable == MutableFlag::Mutable
        {
            issues.push(RecordFieldSubtypeViolation::MutableMismatch {
                label: field1.ld_id.name().to_string(),
            });
        }

        // record_coercion.ml:50-53: a field mutable in both records is read
        // and written through both types, so it is a subtype both ways:
        // `ld1 :: ld2 :: acc1` and `ld2 :: ld1 :: acc2`. The lists are built
        // forward here and reversed by the callers, so each pair is pushed
        // in reverse.
        if field1.ld_mutable == MutableFlag::Mutable && field2.ld_mutable == MutableFlag::Mutable {
            field_types1.push(field2.ld_type);
            field_types1.push(field1.ld_type);
            field_types2.push(field1.ld_type);
            field_types2.push(field2.ld_type);
        } else {
            field_types1.push(field1.ld_type);
            field_types2.push(field2.ld_type);
        }
    }

    // Issues are accumulated by prepending (OCaml list cons order).
    issues.reverse();
    (issues, field_types1, field_types2)
}

/// `Record_runtime.declaration_name`, without allocating.
fn label_declaration_runtime_name(label: &LabelDeclaration) -> &str {
    label
        .ld_runtime_name
        .as_deref()
        .unwrap_or_else(|| label.ld_id.name())
}

fn expand_head_with_mode(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    mode: ExpandHeadMode,
) -> TypeExprRef {
    let mut current = ctx.repr(ty);
    // Stack-allocated cycle detection for up to 20 iterations.
    // Linear scan is faster than HashSet for this small size.
    let mut seen = [TypeExprRef(0); 20];
    let mut seen_len: usize = 0;
    for _ in 0..20 {
        if seen[..seen_len].contains(&current) {
            break;
        }
        seen[seen_len] = current;
        seen_len += 1;
        match try_expand_head_with_mode(ctx, env, current, mode) {
            Some(expanded) => {
                let expanded = ctx.repr(expanded);
                if expanded == current {
                    break;
                }
                if seen[..seen_len].contains(&expanded) {
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

/// ctype.ml `object_row`: the terminator of an object's row.
pub(crate) fn object_row(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let mut current = ctx.repr(ty);
    loop {
        let next = match &*ctx.borrow_desc(current) {
            TypeDesc::Tobject { fields } => *fields,
            TypeDesc::Tfield { rest, .. } => *rest,
            _ => return current,
        };
        current = ctx.repr(next);
    }
}

/// ctype.ml `object_row_is_structurally_open`.
pub(crate) fn object_row_is_structurally_open(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    matches!(
        &*ctx.borrow_desc(object_row(ctx, ty)),
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tconstr { .. }
    )
}

/// ctype.ml `filter_method_field`.
fn filter_method_field(
    ctx: &TypeContext,
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
            matches: bool,
            typ: TypeExprRef,
            rest: TypeExprRef,
        },
        Error,
    }
    let action = match &*ctx.get_desc(ty) {
        TypeDesc::Tvar(..) => FieldAction::FreshField {
            level: ctx.get_level(ty),
        },
        TypeDesc::Tfield {
            name, typ, rest, ..
        } => FieldAction::ExistingField {
            matches: name == method_name,
            typ: *typ,
            rest: *rest,
        },
        _ => FieldAction::Error,
    };
    match action {
        FieldAction::FreshField { level } => {
            let field_ty = ctx.new_var(None);
            let rest_ty = ctx.new_var(None);
            ctx.set_level(field_ty, level);
            ctx.set_level(rest_ty, level);
            let mutability = ctx.alloc_mutability(FieldMutability::Value(MutableFlag::Immutable));
            let linked = ctx.new_type(TypeDesc::Tfield {
                name: method_name.to_string(),
                mutability,
                typ: field_ty,
                rest: rest_ty,
            });
            ctx.set_level(linked, level);
            link_type(ctx, ty, linked);
            Ok(field_ty)
        }
        FieldAction::ExistingField {
            matches: true, typ, ..
        } => Ok(typ),
        FieldAction::ExistingField { rest, .. } => filter_method_field(ctx, env, method_name, rest),
        FieldAction::Error => Err(TypeError::Unify(vec![])),
    }
}

/// ctype.ml `filter_method`: require a readable `name` field and return its
/// type. If lookup reaches a `Tvar` row terminator, it can acquire the
/// missing field; rigid and closed rows cannot. This does not require or
/// introduce write capability.
pub fn filter_method(
    ctx: &TypeContext,
    env: &Env,
    method_name: &str,
    ty: TypeExprRef,
) -> TypeResult<TypeExprRef> {
    let ty = expand_head(ctx, env, ty);
    let action = match &*ctx.get_desc(ty) {
        TypeDesc::Tvar(..) => Some(Err(ctx.get_level(ty))),
        TypeDesc::Tobject { fields } => Some(Ok(*fields)),
        _ => None,
    };
    match action {
        Some(Err(level)) => {
            let fields_ty = ctx.new_var(None);
            ctx.set_level(fields_ty, level);
            let object_ty = ctx.new_type(TypeDesc::Tobject { fields: fields_ty });
            update_level(ctx, level, object_ty);
            link_type(ctx, ty, object_ty);
            filter_method_field(ctx, env, method_name, fields_ty)
        }
        Some(Ok(fields)) => filter_method_field(ctx, env, method_name, fields),
        None => Err(TypeError::Unify(vec![])),
    }
}

/// ctype.ml `object_field_write_error`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectFieldWriteError {
    OwriteMissing,
    OwriteNotMutable,
}

/// ctype.ml `filter_object_field_for_write`: look up `name` for assignment
/// in the object type `ty`.
/// - A `Mutable` field yields its type.
/// - An `Immutable` field is promoted iff the row ends in a `Tvar`, the same
///   predicate `unify_mutability` uses.
/// - An absent field is added as `Mutable` through a `Tvar` rest; on a closed
///   or private row the write is rejected as missing.
pub fn filter_object_field_for_write(
    ctx: &TypeContext,
    env: &Env,
    name: &str,
    ty: TypeExprRef,
) -> TypeResult<Result<TypeExprRef, ObjectFieldWriteError>> {
    fn write_field(
        ctx: &TypeContext,
        env: &Env,
        name: &str,
        can_promote: bool,
        ty: TypeExprRef,
    ) -> Result<TypeExprRef, ObjectFieldWriteError> {
        let ty = expand_head(ctx, env, ty);
        enum Action {
            Fresh(i32),
            Field {
                matches: bool,
                mutability: MutabilityRef,
                typ: TypeExprRef,
                rest: TypeExprRef,
            },
            Missing,
        }
        let action = match &*ctx.get_desc(ty) {
            TypeDesc::Tvar(..) => Action::Fresh(ctx.get_level(ty)),
            TypeDesc::Tfield {
                name: n,
                mutability,
                typ,
                rest,
            } => Action::Field {
                matches: n == name,
                mutability: *mutability,
                typ: *typ,
                rest: *rest,
            },
            _ => Action::Missing,
        };
        match action {
            Action::Fresh(level) => {
                let ty1 = ctx.new_var(None);
                let ty2 = ctx.new_var(None);
                ctx.set_level(ty1, level);
                ctx.set_level(ty2, level);
                let mutability = ctx.alloc_mutability(FieldMutability::Value(MutableFlag::Mutable));
                let field = ctx.new_type(TypeDesc::Tfield {
                    name: name.to_string(),
                    mutability,
                    typ: ty1,
                    rest: ty2,
                });
                ctx.set_level(field, level);
                link_type(ctx, ty, field);
                Ok(ty1)
            }
            Action::Field {
                matches: true,
                mutability,
                typ,
                ..
            } => match ctx.mutability_repr(mutability) {
                MutableFlag::Mutable => Ok(typ),
                MutableFlag::Immutable if can_promote => {
                    ctx.set_mutability(
                        ctx.mutability_ref_repr(mutability),
                        FieldMutability::Value(MutableFlag::Mutable),
                    );
                    Ok(typ)
                }
                MutableFlag::Immutable => Err(ObjectFieldWriteError::OwriteNotMutable),
            },
            Action::Field { rest, .. } => write_field(ctx, env, name, can_promote, rest),
            Action::Missing => Err(ObjectFieldWriteError::OwriteMissing),
        }
    }

    let ty = expand_head(ctx, env, ty);
    let action = match &*ctx.get_desc(ty) {
        TypeDesc::Tvar(..) => Some(Err(ctx.get_level(ty))),
        TypeDesc::Tobject { fields } => Some(Ok(*fields)),
        _ => None,
    };
    match action {
        Some(Err(level)) => {
            let fields_ty = ctx.new_var(None);
            let object_ty = ctx.new_type(TypeDesc::Tobject { fields: fields_ty });
            update_level(ctx, level, object_ty);
            link_type(ctx, ty, object_ty);
            Ok(write_field(ctx, env, name, true, fields_ty))
        }
        Some(Ok(fields)) => {
            let can_promote = matches!(&*ctx.borrow_desc(object_row(ctx, ty)), TypeDesc::Tvar(..));
            Ok(write_field(ctx, env, name, can_promote, fields))
        }
        None => Ok(Err(ObjectFieldWriteError::OwriteMissing)),
    }
}

/// Substitute type parameters in a type expression.
///
/// Given a mapping from parameter type refs to argument type refs,
/// create a copy of `ty` with all occurrences of parameters replaced by arguments.
fn subst_type(
    ctx: &TypeContext,
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
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => {
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
            args: arrow_args,
            ret,
        } => {
            // Map types in the original order, but only copy owned labels when
            // rebuilding the arrow. A no-op substitution returns its original id.
            let new_types = arrow_args
                .iter()
                .map(|arg| subst_type(ctx, params, args, arg.typ))
                .collect::<Vec<_>>();
            let new_ret = subst_type(ctx, params, args, *ret);
            if new_types.iter().zip(arrow_args).all(|(a, b)| *a == b.typ) && new_ret == *ret {
                ty
            } else {
                let new_args = arrow_args
                    .iter()
                    .zip(new_types)
                    .map(|(arg, typ)| arg.with_type(typ))
                    .collect();
                drop(desc);
                ctx.new_type(TypeDesc::Tarrow {
                    args: new_args,
                    ret: new_ret,
                })
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
                    args: new_args.into(),
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
    ctx: &TypeContext,
    _env: &Env,
    ty: TypeExprRef,              // original Tconstr being expanded
    lookup_abbrev: AbbrevMemoRef, // proper_abbrevs target memo
    private_flag: PrivateFlag,    // OCaml subst `priv` argument
    params: &[TypeExprRef],       // type declaration params
    args: &[TypeExprRef],         // actual type arguments
    body: TypeExprRef,            // manifest
) -> TypeExprRef {
    // Match OCaml subst: run the whole substitution/unification at the
    // Tconstr's level, then restore.
    let tconstr_level = ctx.get_level(ctx.repr(ty));
    let old_level = ctx.current_level();
    ctx.set_current_level(tconstr_level);

    // 1. Create stub variable (OCaml: body0 = newvar())
    let body0 = ctx.new_var(None);

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
            private_flag,
            path,
            ty,    // abbrev: original type (returned by find_repr)
            body0, // expansion: stub (returned by find_expans)
        );
    }

    // 3. Set global abbreviations context so copy_type_cached can use find_repr
    ctx.set_current_abbreviations(memo_ref);

    // 4. `instance_parameterized_type` (ctype.ml:1087). `copy` leaves
    // non-generic nodes shared (ctype.ml `copy`: level <> generic_level), so
    // a recursive stub's manifest variable is the body that unification binds.
    let (fresh_params, fresh_body) = instance_parameterized_type(ctx, params, body);

    // 5. Clear instantiation abbreviations before the unifications below.
    // OCaml sets the global `abbreviations` ref back to `ref Mnil` here rather
    // than restoring any previous outer context.
    ctx.set_current_abbreviations(AbbrevMemoRef::nil());

    // 6. Unify stub with body (OCaml: !unify' env body0 body'). `unify'` is
    // `unify_var` (ctype.ml:2609-2628), which links a variable without the
    // top-level `unify` snapshot (ctype.ml:2589-2594); a snapshot here would
    // trail links of the fresh instance that an outer backtrack must keep.
    let mut unify_state = UnifyState::new();
    unify_state.set_env(_env);
    if unify_var(ctx, &mut unify_state, body0, fresh_body).is_err() {
        // Preserve previous behavior if full unification fails.
        link_type(ctx, body0, fresh_body);
    }

    // 7. Bind params to args (OCaml: List.iter2 (!unify' env) params' args)
    for (p, a) in fresh_params.iter().zip(args.iter()) {
        if unify_var(ctx, &mut unify_state, *p, *a).is_err() {
            link_type(ctx, *p, *a);
        }
    }

    // 8. Restore typing level after all substitutions/unifications.
    ctx.set_current_level(old_level);

    fresh_body
}

/// ctype.ml `apply env params body args` = `subst env generic_level Public
/// (ref Mnil) None params args body`; `None` for OCaml's `Cannot_apply`.
pub(crate) fn apply(
    ctx: &TypeContext,
    env: &Env,
    params: &[TypeExprRef],
    body: TypeExprRef,
    args: &[TypeExprRef],
) -> Option<TypeExprRef> {
    if params.len() != args.len() {
        return None;
    }
    let old_level = ctx.current_level();
    ctx.set_current_level(GENERIC_LEVEL);
    let body0 = ctx.new_var(None);
    ctx.set_current_abbreviations(ctx.alloc_abbrev(AbbrevMemo::Mnil));
    let (fresh_params, fresh_body) = instance_parameterized_type(ctx, params, body);
    ctx.set_current_abbreviations(AbbrevMemoRef::nil());
    let mut unify_state = UnifyState::new();
    unify_state.set_env(env);
    let mut ok = unify_var(ctx, &mut unify_state, body0, fresh_body).is_ok();
    for (p, a) in fresh_params.iter().zip(args.iter()) {
        ok = ok && unify_var(ctx, &mut unify_state, *p, *a).is_ok();
    }
    ctx.set_current_level(old_level);
    ok.then_some(fresh_body)
}

// ============================================================================
// Core Unification
// ============================================================================

pub(crate) fn package_type_lists_have_ocaml_same_label_completion_side_effect(
    ctx: &TypeContext,
    env: Option<&Env>,
    mty: super::decl::ModuleType,
    required_lids: &[crate::parser::longident::Longident],
    existing_lids: &[crate::parser::longident::Longident],
) -> bool {
    // Matches the same-label path through compiler/ml/ctype.ml:2199-2206:
    // `complete_type_list` first allocates `Pkg` and calls `Env.add_module`
    // (compiler/ml/ctype.ml:2200-2201), then returns existing entries when
    // `Longident.cmp n n2 = 0` (compiler/ml/ctype.ml:2205-2206). CMI package
    // labels are reconstructed with synthetic StrIdx values, so compare their
    // resolved component names like OCaml's structural Longident comparison
    // instead of raw arena ids.
    let pkg_id = ctx.create_ident("Pkg");
    if let Some(env) = env {
        let mut env_prime = env.clone_preserve_id();
        env_prime.add_module(
            pkg_id,
            super::decl::ModuleDeclaration {
                md_type: mty,
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );
    }
    required_lids.len() == existing_lids.len()
        && required_lids
            .iter()
            .zip(existing_lids.iter())
            .all(|(required, existing)| package_longident_same_label(ctx, required, existing))
}

fn package_longident_same_label(
    ctx: &TypeContext,
    left: &crate::parser::longident::Longident,
    right: &crate::parser::longident::Longident,
) -> bool {
    use crate::parser::longident::Longident;

    fn component_same(
        ctx: &TypeContext,
        left: crate::intern::StrIdx,
        right: crate::intern::StrIdx,
    ) -> bool {
        left == right
            || match (
                ctx.resolve_any_longident_component(left),
                ctx.resolve_any_longident_component(right),
            ) {
                (Some(left), Some(right)) => left == right,
                _ => false,
            }
    }

    match (left, right) {
        (Longident::Lident(left), Longident::Lident(right)) => component_same(ctx, *left, *right),
        (Longident::Ldot(left_prefix, left), Longident::Ldot(right_prefix, right)) => {
            package_longident_same_label(ctx, left_prefix, right_prefix)
                && component_same(ctx, *left, *right)
        }
        (
            Longident::Lapply(left_functor, left_arg),
            Longident::Lapply(right_functor, right_arg),
        ) => {
            package_longident_same_label(ctx, left_functor, right_functor)
                && package_longident_same_label(ctx, left_arg, right_arg)
        }
        _ => false,
    }
}

/// Unify two types.
///
/// This is the main entry point for unification. It attempts to make
/// `t1` and `t2` equal by finding substitutions for type variables.
///
/// # Errors
///
/// Returns `TypeError::Unify` if the types cannot be unified.
pub fn unify(
    ctx: &TypeContext,
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
    // OCaml's outer `unify` (ctype.ml:2589-2594) takes a snapshot so a
    // failure can `undo_compress` before expanding the trace.
    let top_snapshot =
        (state.recursion_depth == 1).then(|| ctx.snapshot_type_state_for_undo_compress());

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

    let reset_tracing =
        ctx.check_trace_gadt_instances(state.env().is_some_and(|env| env.has_local_constraints()));

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
    // OCaml's outer `unify` (ctype.ml:2589-2594) expands the whole trace with
    // `full_expand` in the unification environment.
    if state.recursion_depth == 0
        && let Err(TypeError::Unify(trace)) = &result
    {
        if let Some(snapshot) = &top_snapshot {
            ctx.undo_compress(snapshot);
        }
        if let Some(env) = state.env() {
            record_trace_expansions(ctx, env, trace);
        }
    }
    drop(top_snapshot);
    result
}

/// OCaml `Ctype.enforce_constraints` (ctype.ml:1292-1301) for a constructor
/// whose declaration `decl` was found: `subst` the declaration against the
/// constructor's arguments, unifying them with the constrained parameters.
/// Callers where OCaml treats a failure as impossible (typedecl.ml:769).
pub(crate) fn enforce_constraints(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    decl: &crate::types::TypeDeclaration,
) {
    let unified = try_enforce_constraints(ctx, env, ty, decl);
    debug_assert!(unified.is_ok(), "enforce_constraints failed to unify");
}

/// OCaml `Ctype.enforce_constraints` (ctype.ml:1292-1301), raising `Unify`
/// as typetexp.ml:369-371 expects.
pub(crate) fn try_enforce_constraints(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    decl: &crate::types::TypeDeclaration,
) -> TypeResult<()> {
    let ty = ctx.repr(ty);
    let args = match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { args, .. } => args.clone(),
        _ => unreachable!("enforce_constraints expects a type constructor"),
    };
    let level = ctx.get_level(ty);
    // `subst env level Public (ref Mnil) None decl.type_params args
    // (newvar2 level)` (ctype.ml:1127-1149).
    if decl.type_params.len() != args.len() {
        return Err(TypeError::Unify(vec![]));
    }
    let body = new_var_at_level(ctx, level);
    let old_level = ctx.current_level();
    ctx.set_current_level(level);
    let body0 = ctx.new_var(None);
    let (params, body) = instance_parameterized_type(ctx, &decl.type_params, body);
    let mut state = UnifyState::new();
    state.set_env(env);
    let unified = unify(ctx, &mut state, body0, body).and_then(|()| {
        params
            .iter()
            .zip(args.iter())
            .try_for_each(|(param, arg)| unify(ctx, &mut state, *param, *arg))
    });
    ctx.set_current_level(old_level);
    unified
}

/// OCaml `Ctype.rigidify` (ctype.ml:2926-2950): the variables of `ty`, with
/// open polymorphic-variant rows fixed.
fn rigidify(ctx: &TypeContext, ty: TypeExprRef) -> Vec<TypeExprRef> {
    fn walk(
        ctx: &TypeContext,
        ty: TypeExprRef,
        seen: &mut TypeExprRefSet,
        vars: &mut Vec<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return;
        }
        let desc = ctx.get_desc(ty).into_desc();
        match desc {
            TypeDesc::Tvar(..) => {
                if !vars.contains(&ty) {
                    vars.push(ty);
                }
            }
            TypeDesc::Tvariant(row) => {
                let row = crate::types::btype::row_repr(ctx, &row);
                let more = ctx.repr(row.row_more);
                if matches!(&*ctx.borrow_desc(more), TypeDesc::Tvar(..))
                    && !crate::types::btype::row_fixed(ctx, &row)
                {
                    let more_prime = ctx.new_type(ctx.get_desc(more).into_desc().shared_from(more));
                    ctx.set_level(more_prime, ctx.get_level(more));
                    let fixed_row = crate::types::type_expr::RowDesc {
                        row_fields: Default::default(),
                        row_more: more_prime,
                        row_fixed: true,
                        ..row.clone()
                    };
                    let variant = ctx.new_type(TypeDesc::Tvariant(Box::new(fixed_row)));
                    ctx.set_level(variant, ctx.get_level(ty));
                    link_type(ctx, more, variant);
                }
                let mut children = Vec::new();
                crate::types::btype::iter_row(ctx, &row, |child| children.push(child));
                for child in children {
                    walk(ctx, child, seen, vars);
                }
                if !crate::types::btype::static_row(ctx, &row) {
                    let more = crate::types::btype::row_repr(ctx, &row).row_more;
                    walk(ctx, more, seen, vars);
                }
            }
            _ => {
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                for child in children {
                    walk(ctx, child, seen, vars);
                }
            }
        }
    }
    let mut vars = Vec::new();
    walk(ctx, ty, &mut TypeExprRefSet::new(), &mut vars);
    vars
}

/// OCaml `Ctype.matches` (ctype.ml:2952-2974): `ty'` is an instance of `ty`
/// without instantiating `ty`'s variables. All effects are undone except
/// `cleanup_abbrev`, which OCaml does not log.
pub(crate) fn matches(ctx: &TypeContext, env: &Env, ty: TypeExprRef, ty2: TypeExprRef) -> bool {
    ctx.clear_abbrev_memos();
    let snapshot = ctx.snapshot_type_state();
    let vars = rigidify(ctx, ty);
    let mut state = UnifyState::new();
    state.set_env(env);
    let ok = unify(ctx, &mut state, ty, ty2).is_ok() && {
        let mut seen = Vec::new();
        vars.iter().all(|&var| {
            let expanded = expand_head(ctx, env, var);
            if seen.contains(&expanded) {
                false
            } else {
                seen.push(expanded);
                matches!(&*ctx.borrow_desc(expanded), TypeDesc::Tvar(..))
            }
        })
    };
    ctx.restore_type_state(snapshot);
    ok
}

/// OCaml `full_expand` (ctype.ml:1283).
fn full_expand(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    ctx.repr(expand_head(ctx, env, ty))
}

/// OCaml `expand_trace` (ctype.ml:1601-1605), kept beside the raw trace.
pub(crate) fn record_trace_expansions(
    ctx: &TypeContext,
    env: &Env,
    trace: &[(TypeExprRef, TypeExprRef)],
) {
    for &(t1, t2) in trace {
        for ty in [t1, t2] {
            let ty = ctx.repr(ty);
            let expansion = full_expand(ctx, env, ty);
            ctx.record_trace_expansion(ty, expansion);
        }
    }
}

/// Unify with OCaml's `unify_var` fast path.
///
/// OCaml compiler/ml/ctype.ml:2820-2837 links a left-hand `Tvar` directly
/// after the occurs check and level update, falling back to full `unify` for
/// constructor self-occurrences and non-variable left sides.
pub fn unify_var(
    ctx: &TypeContext,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }

    // Only the variants are needed; read them without cloning descriptors.
    let var1 = matches!(&*ctx.borrow_desc(t1), TypeDesc::Tvar(..));
    let constr2 = matches!(&*ctx.borrow_desc(t2), TypeDesc::Tconstr { .. });
    match (var1, constr2) {
        (true, true) if deep_occur(ctx, t1, t2) => unify(ctx, state, t1, t2),
        (true, _) => {
            // OCaml compiler/ml/ctype.ml:2820-2837 `unify_var`
            // performs `occur`, lowers levels, and links directly. It does
            // not call `occur_univar`; that check belongs to the full
            // `unify1_var` path at ctype.ml:2278-2286.
            // OCaml compiler/ml/ctype.ml:2618 `occur env t1 t2`.
            if occur_check(ctx, state.env(), state.mode, t1, t2).is_err() {
                return Err(TypeError::Unify(vec![(t1, t2)]));
            }
            let level = ctx.get_level(t1);
            let capture_type_lookup_paths = state.should_capture_type_lookup_paths();
            let mut pending_type_lookup_paths = Vec::new();
            let mut pending_type_expansion_paths = Vec::new();
            let lowered = if let Some(env) = state.env() {
                if capture_type_lookup_paths {
                    let mut capture = Some(&mut pending_type_lookup_paths);
                    let mut expansion_capture = Some(&mut pending_type_expansion_paths);
                    update_level_checked(ctx, env, level, t2, &mut capture, &mut expansion_capture)
                } else {
                    update_level_checked(ctx, env, level, t2, &mut None, &mut None)
                }
            } else {
                update_level(ctx, level, t2);
                Ok(())
            };
            state.extend_type_lookup_paths(pending_type_lookup_paths);
            state.extend_type_expansion_paths(pending_type_expansion_paths);
            // OCaml ctype.ml:2617-2625: `update_level` raising aborts before
            // `link_type`, and the trace starts with the variable pair.
            if let Err(TypeError::Unify(trace)) = lowered {
                let mut full = vec![(t1, t2)];
                full.extend(trace);
                // ctype.ml:2622-2625: `unify_var` expands its trace.
                if let Some(env) = state.env() {
                    record_trace_expansions(ctx, env, &full);
                }
                return Err(TypeError::Unify(full));
            }
            link_type(ctx, t1, t2);
            Ok(())
        }
        _ => unify(ctx, state, t1, t2),
    }
}

// Match OCaml ctype.ml unify2/unify3 alias-expansion linking direction.
// OCaml still picks a relinking direction when both sides expanded:
//   if t1 == t1' || t2 != t2' then unify3 t1 t1' t2 t2'
//   else unify3 t2 t2' t1 t1'
// and unify3 links t1' -> t2 for expression-mode unification.
// We mirror that branch choice so alias identity is preserved for both
// one-sided and two-sided expansion cases.
fn unify_after_expansion(
    ctx: &TypeContext,
    state: &mut UnifyState,
    t1: TypeExprRef,
    t1_expanded: TypeExprRef,
    t2: TypeExprRef,
    t2_expanded: TypeExprRef,
) -> TypeResult<()> {
    let t1_changed = t1_expanded != t1;
    let t2_changed = t2_expanded != t2;

    // Match OCaml unify2 branching:
    //   if t1 == t1' || t2 != t2' then unify3(t1,t1',t2,t2')
    //   else unify3(t2,t2',t1,t1')
    // Swap only when left changed and right did not.
    let swap = t1_changed && !t2_changed;
    let lhs = if swap { t2_expanded } else { t1_expanded };
    let rhs = if swap { t1_expanded } else { t2_expanded };
    let relink_target = if swap { t1 } else { t2 };
    let swap_trace = |result: TypeResult<()>| -> TypeResult<()> {
        match result {
            Err(TypeError::Unify(trace)) if swap => Err(TypeError::Unify(
                trace
                    .into_iter()
                    .map(|(left, right)| (right, left))
                    .collect(),
            )),
            other => other,
        }
    };

    let lhs = ctx.repr(lhs);
    let rhs = ctx.repr(rhs);
    if lhs == rhs {
        // OCaml ctype.ml:2348 returns immediately when the expanded heads are
        // physically equal; the unify3 relink at lines 2393-2397 is not run.
        return Ok(());
    }
    {
        // OCaml `unify3` (compiler/ml/ctype.ml:2181-2192) handles type
        // variables before anything else: `occur`, `occur_univar`, then link
        // the expanded variable to the ORIGINAL opposite side. unify2 always
        // reaches unify3, including when neither head was expanded.
        let swap = t1_changed && !t2_changed;
        let (left, left_exp, right, right_exp) = if swap {
            (t2, ctx.repr(t2_expanded), t1, ctx.repr(t1_expanded))
        } else {
            (t1, ctx.repr(t1_expanded), t2, ctx.repr(t2_expanded))
        };
        let left_is_var = matches!(&*ctx.borrow_desc(left_exp), TypeDesc::Tvar(..));
        let right_is_var = matches!(&*ctx.borrow_desc(right_exp), TypeDesc::Tvar(..));
        let left_is_univar = matches!(&*ctx.borrow_desc(left_exp), TypeDesc::Tunivar(..));
        let right_is_univar = matches!(&*ctx.borrow_desc(right_exp), TypeDesc::Tunivar(..));
        if !(left_is_univar && right_is_univar) {
            let var_link = if left_is_var {
                Some((left_exp, ctx.repr(right)))
            } else if right_is_var {
                Some((right_exp, ctx.repr(left)))
            } else {
                None
            };
            if let Some((var, target)) = var_link {
                if var == target {
                    return Ok(());
                }
                // `occur` raises `Unify []`; the caller's `unify` adds (t1, t2).
                occur_check(ctx, state.env(), state.mode, var, target)?;
                if let Some(env) = state.env() {
                    occur_univar(ctx, env, target)?;
                }
                link_type(ctx, var, target);
                return Ok(());
            }
        }
    }
    if !t1_changed && !t2_changed {
        // OCaml's unify2 calls unify3 directly here (ctype.ml:2169); the
        // pair the nested `unify` adds to a failure trace is not part of
        // OCaml's trace.
        let (e1, e2) = (ctx.repr(t1_expanded), ctx.repr(t2_expanded));
        return match unify(ctx, state, t1_expanded, t2_expanded) {
            Err(TypeError::Unify(mut trace)) if trace.first() == Some(&(e1, e2)) => {
                trace.remove(0);
                Err(TypeError::Unify(trace))
            }
            other => other,
        };
    }

    {
        let lhs_desc = ctx.get_desc(lhs);
        let rhs_desc = ctx.get_desc(rhs);
        if let (
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
        ) = (&*lhs_desc, &*rhs_desc)
            && path1.same(path2)
            && args1.len() == args2.len()
        {
            let same_path = path1.clone();
            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();
            drop(lhs_desc);
            drop(rhs_desc);

            // ctype.ml:2178: `d1` is restored if unification fails.
            let lhs_desc = ctx.get_desc(lhs).into_desc();
            if state.mode != crate::types::UnifyMode::Pattern {
                // OCaml unify3 Expression mode (compiler/ml/ctype.ml:2198-2201):
                // `occur !env t1' t2'` before `link_type t1' t2`.
                occur_check(ctx, state.env(), state.mode, lhs, rhs)?;
                // OCaml ctype.ml:2393-2414 links the selected expanded
                // side to the original opposite side before unifying
                // constructor arguments, so nested alias spelling follows
                // the original argument type.
                let to_ty = ctx.repr(relink_target);
                if lhs != to_ty && !deep_occur(ctx, lhs, rhs) {
                    ctx.set_desc(lhs, TypeDesc::Tlink(to_ty));
                }
            }

            let original_lhs = if swap { t2 } else { t1 };
            if let Err(err) = unify_same_path_constructor_args(
                ctx,
                state,
                lhs,
                original_lhs,
                relink_target,
                &same_path,
                pairs,
            ) {
                // ctype.ml:2321-2323 `with Unify trace -> t1'.desc <- d1`.
                ctx.set_desc(lhs, lhs_desc);
                return swap_trace(Err(err));
            }

            return Ok(());
        }
    }

    // OCaml runs unify3 on the expanded pair without a trace entry of its
    // own (ctype.ml:2169-2173); drop the pair the nested `unify` adds.
    let unify_result = swap_trace(match unify(ctx, state, lhs, rhs) {
        Err(TypeError::Unify(mut trace)) if trace.first() == Some(&(lhs, rhs)) => {
            trace.remove(0);
            Err(TypeError::Unify(trace))
        }
        other => other,
    });
    unify_result?;

    if state.mode != crate::types::UnifyMode::Pattern {
        // Match OCaml unify3 expression mode:
        //   link_type t1' t2
        // where t1' is the selected expanded side and t2 is the selected
        // ORIGINAL opposite side.
        let to_ty = ctx.repr(relink_target);
        if lhs != to_ty && !deep_occur(ctx, lhs, to_ty) {
            ctx.set_desc(lhs, TypeDesc::Tlink(to_ty));
        }
    }

    Ok(())
}

fn has_cached_expansion(ctx: &TypeContext, path: &Path, mut memo: AbbrevMemoRef) -> bool {
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
fn unify_types(
    ctx: &TypeContext,
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
        let desc1 = ctx.borrow_desc(t1);
        let desc2 = ctx.borrow_desc(t2);
        if let (
            TypeDesc::Tconstr {
                path: path1,
                args: args1,
                abbrev: abbrev1,
                ..
            },
            TypeDesc::Tconstr {
                path: path2,
                args: args2,
                abbrev: abbrev2,
                ..
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

    // Match OCaml update-level behavior before structural matching.
    if let Some(env) = state.env() {
        let lv1 = ctx.get_level(t1);
        let lv2 = ctx.get_level(t2);
        let lv = std::cmp::min(lv1, lv2);
        let capture_type_lookup_paths = state.should_capture_type_lookup_paths();
        let mut pending_type_lookup_paths = Vec::new();
        let mut pending_type_expansion_paths = Vec::new();
        // OCaml ctype.ml:2154-2155 `update_level !env lv t2; update_level !env lv t1`.
        let lowered = if capture_type_lookup_paths {
            let mut capture = Some(&mut pending_type_lookup_paths);
            let mut expansion_capture = Some(&mut pending_type_expansion_paths);
            update_level_checked(ctx, env, lv, t2, &mut capture, &mut expansion_capture).and_then(
                |()| update_level_checked(ctx, env, lv, t1, &mut capture, &mut expansion_capture),
            )
        } else {
            update_level_checked(ctx, env, lv, t2, &mut None, &mut None)
                .and_then(|()| update_level_checked(ctx, env, lv, t1, &mut None, &mut None))
        };
        state.extend_type_lookup_paths(pending_type_lookup_paths);
        state.extend_type_expansion_paths(pending_type_expansion_paths);
        lowered?;
    }

    // Re-repr after update_level_expand may have linked types.
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }

    // The type-variable cases below read only the two descriptors' variants;
    // take them without cloning the descriptors (arms in the same order and
    // with the same guards as the full match).
    let (var1, constr1) = {
        let desc = ctx.borrow_desc(t1);
        (
            matches!(&*desc, TypeDesc::Tvar(..)),
            matches!(&*desc, TypeDesc::Tconstr { .. }),
        )
    };
    let (var2, constr2) = {
        let desc = ctx.borrow_desc(t2);
        (
            matches!(&*desc, TypeDesc::Tvar(..)),
            matches!(&*desc, TypeDesc::Tconstr { .. }),
        )
    };
    if var1 || var2 {
        if var1 && constr2 && state.env().is_some() && deep_occur(ctx, t1, t2) {
            // OCaml compiler/ml/ctype.ml:2302-2303: see the full match below.
            let env = state.env().expect("checked above");
            let exp1 = expand_head_unif(ctx, env, t1);
            let exp2 = expand_head_unif(ctx, env, t2);
            return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
        }
        if constr1 && var2 && state.env().is_some() && deep_occur(ctx, t2, t1) {
            let env = state.env().expect("checked above");
            let exp1 = expand_head_unif(ctx, env, t1);
            let exp2 = expand_head_unif(ctx, env, t2);
            return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
        }
        if var1 {
            // OCaml compiler/ml/ctype.ml:2280-2286 `unify1_var`.
            if occur_check(ctx, state.env(), state.mode, t1, t2).is_err() {
                return Err(TypeError::Unify(vec![]));
            }
            if let Some(env) = state.env() {
                occur_univar(ctx, env, t2)?;
            }
            return unify1_var_link(ctx, state, t1, t2);
        }
        // Symmetric `unify1_var` case from compiler/ml/ctype.ml:2304.
        if occur_check(ctx, state.env(), state.mode, t2, t1).is_err() {
            return Err(TypeError::Unify(vec![]));
        }
        if let Some(env) = state.env() {
            occur_univar(ctx, env, t1)?;
        }
        return unify1_var_link(ctx, state, t2, t1);
    }

    let desc1 = ctx.get_desc(t1);
    let desc2 = ctx.get_desc(t2);

    // Match on both descriptors
    match (&*desc1, &*desc2) {
        // Type-variable cases were handled above.

        // Universal type variables
        // ctype.ml unify: `Tunivar _, Tunivar _ -> unify_univar t1 t2
        // !univar_pairs; update_level !env t1.level t2; link_type t1 t2`.
        (TypeDesc::Tunivar(..), TypeDesc::Tunivar(..)) => {
            drop(desc1);
            drop(desc2);
            unify_univar(ctx, state, t1, t2)?;
            update_level(ctx, ctx.get_level(t1), t2);
            link_type(ctx, t1, t2);
            Ok(())
        }

        // compiler/ml/ctype.ml:2204-2218: n-ary arrows unify only when
        // parameter counts agree and labels are pairwise compatible.
        (
            TypeDesc::Tarrow {
                args: args1,
                ret: ret1,
            },
            TypeDesc::Tarrow {
                args: args2,
                ret: ret2,
            },
        ) if args1.len() == args2.len()
            && args1.iter().zip(args2).all(|(a1, a2)| {
                a1.label().same_label(a2.label())
                    || (state.mode == UnifyMode::Pattern
                        && !(a1.label().is_optional() || a2.label().is_optional()))
            }) =>
        {
            let original_desc1 = (*desc1).clone();
            let args1 = args1.clone();
            let args2 = args2.clone();
            let ret1 = *ret1;
            let ret2 = *ret2;
            drop(desc1);
            drop(desc2);

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            // OCaml links t1'→t2 before recursively unifying children.
            link_type(ctx, t1, t2);
            let result = (|| {
                for (arg1, arg2) in args1.iter().zip(&args2) {
                    unify(ctx, state, arg1.typ, arg2.typ)?;
                }
                unify(ctx, state, ret1, ret2)
            })();
            if matches!(result, Err(TypeError::Unify(_))) {
                ctx.set_desc(t1, original_desc1);
            }
            result
        }

        // Tuple types
        (TypeDesc::Ttuple(tl1), TypeDesc::Ttuple(tl2)) => {
            if tl1.len() != tl2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![]));
            }

            let original_desc1 = (*desc1).clone();
            let pairs: Vec<_> = tl1.iter().zip(tl2.iter()).map(|(&a, &b)| (a, b)).collect();
            drop(desc1);
            drop(desc2);

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            let result = (|| {
                for (a, b) in pairs {
                    unify(ctx, state, a, b)?;
                }

                Ok(())
            })();

            if matches!(result, Err(TypeError::Unify(_))) {
                ctx.set_desc(t1, original_desc1);
            }

            result
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
                if let Some(env) = state.env() {
                    // OCaml compiler/ml/ctype.ml:2338-2344 (`unify2`) expands
                    // both constructor heads before the constructor-path cases
                    // at ctype.ml:2412-2414 are considered.
                    let exp1 = expand_head_unif(ctx, env, t1);
                    let exp2 = expand_head_unif(ctx, env, t2);
                    if exp1 != t1 || exp2 != t2 {
                        drop(desc1);
                        drop(desc2);
                        return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                    }
                }
                // OCaml compiler/ml/ctype.ml:2413-2433 only takes the
                // constructor argument-only path for `Path.same`; divergent
                // stamps with the same printed path fall through to normal
                // expansion, equation generation, or failure.
                if let Some(env) = state.env() {
                    let norm1 = normalize_path_full(ctx, env, path1);
                    let norm2 = normalize_path_full(ctx, env, path2);
                    if norm1.same(&norm2) && args1.len() == args2.len() {
                        let pairs: Vec<_> = args1
                            .iter()
                            .zip(args2.iter())
                            .map(|(&a, &b)| (a, b))
                            .collect();
                        let p1_changed = !norm1.same(path1);
                        let p2_changed = !norm2.same(path2);
                        let p1_persistent = path_root_is_persistent(path1);
                        let p2_persistent = path_root_is_persistent(path2);
                        if p1_changed && !p2_changed && p1_persistent && p2_persistent {
                            drop(desc1);
                            drop(desc2);
                            link_type(ctx, t2, t1);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        } else if p2_changed && !p1_changed && p1_persistent && p2_persistent {
                            drop(desc1);
                            drop(desc2);
                            link_type(ctx, t1, t2);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        }
                        // When a local target path normalizes through a current
                        // letmodule alias (e.g. Int32Array.t -> Array.t), keep
                        // the unchanged alias path as the representative so the
                        // typedtree matches OCaml's local-alias spelling.
                        if p1_changed
                            && !p2_changed
                            && !p1_persistent
                            && !p2_persistent
                            && norm1.same(path2)
                        {
                            drop(desc1);
                            drop(desc2);
                            link_type(ctx, t1, t2);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        } else if p2_changed
                            && !p1_changed
                            && !p1_persistent
                            && !p2_persistent
                            && norm2.same(path1)
                        {
                            drop(desc1);
                            drop(desc2);
                            link_type(ctx, t2, t1);
                            for (a, b) in pairs {
                                unify(ctx, state, a, b)?;
                            }
                            return Ok(());
                        }
                    }
                }

                // Paths differ after `expand_head_unif`; match OCaml
                // compiler/ml/ctype.ml:2413-2433 by leaving the constructor
                // argument path unless the expanded paths are `Path.same`.
                // Extract paths for potential GADT equation handling (nullary Tconstr only)
                let gadt_path1 = if args1.is_empty() {
                    Some(path1.clone())
                } else {
                    None
                };
                let gadt_path2 = if args2.is_empty() {
                    Some(path2.clone())
                } else {
                    None
                };

                drop(desc1);
                drop(desc2);

                // GADT equation handling for Tconstr with different paths
                if state.generate_equations {
                    let newtype_level = state.newtype_level;
                    if let Some(ref p1) = gadt_path1 {
                        if let Some(ref p2) = gadt_path2 {
                            if let Some(env) = state.env_mut() {
                                let inst1 = is_instantiable(env, p1);
                                let inst2 = is_instantiable(env, p2);
                                if inst1 && inst2 {
                                    let lev1 = env
                                        .find_local_constraint(p1)
                                        .or_else(|| env.find_type(p1.head_name()).ok())
                                        .and_then(|d| d.type_newtype_level);
                                    let lev2 = env
                                        .find_local_constraint(p2)
                                        .or_else(|| env.find_type(p2.head_name()).ok())
                                        .and_then(|d| d.type_newtype_level);
                                    let (source, dest) = if lev1 > lev2 {
                                        (p1.clone(), t2)
                                    } else {
                                        (p2.clone(), t1)
                                    };
                                    add_gadt_equation(ctx, env, newtype_level, &source, dest)?;
                                    return Ok(());
                                } else if inst1 {
                                    add_gadt_equation(ctx, env, newtype_level, p1, t2)?;
                                    return Ok(());
                                } else if inst2 {
                                    add_gadt_equation(ctx, env, newtype_level, p2, t1)?;
                                    return Ok(());
                                }
                            }
                        } else if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p1) {
                                add_gadt_equation(ctx, env, newtype_level, p1, t2)?;
                                return Ok(());
                            }
                        }
                    } else if let Some(ref p2) = gadt_path2 {
                        if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p2) {
                                add_gadt_equation(ctx, env, newtype_level, p2, t1)?;
                                return Ok(());
                            }
                        }
                    }
                }

                if state.mode == UnifyMode::Pattern {
                    return unify_pattern_constructor_mismatch(ctx, state, t1, t2);
                }
                return Err(TypeError::Unify(vec![]));
            }

            if args1.len() != args2.len() {
                drop(desc1);
                drop(desc2);
                return Err(TypeError::Unify(vec![]));
            }

            let same_path = path1.clone();
            let args1 = args1.clone();
            let args2 = args2.clone();
            drop(desc1);
            drop(desc2);

            // OCaml ctype.ml:2338-2414 runs same-constructor cases through
            // `unify2`, expanding abbreviations before structurally comparing
            // arguments. This keeps phantom parameters of manifest aliases
            // (for example `type t<'k, 'id> = N.t<'k>`) out of result unification.
            if let Some(env) = state.env() {
                // OCaml compiler/ml/ctype.ml:2341-2344 expands constructor
                // heads during unification with `expand_head_unif`, not the
                // general safe `expand_head`. Keep the same mode here so
                // persistent aliases such as `Stdlib.Lazy.t` do not repeatedly
                // allocate normalized-but-still-abstract heads before argument
                // unification.
                let exp1 = expand_head_unif(ctx, env, t1);
                let exp2 = expand_head_unif(ctx, env, t2);
                if exp1 != t1 || exp2 != t2 {
                    return unify_after_expansion(ctx, state, t1, exp1, t2, exp2);
                }
            }

            // OCaml ctype.ml:2412-2414: after abbreviation expansion, equal
            // concrete constructor paths unify their full argument lists.
            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            unify_same_path_constructor_args(ctx, state, t1, t1, t2, &same_path, pairs)?;

            if state.mode != crate::types::UnifyMode::Pattern {
                let mut link_source = t1;
                if let Some(env) = state.env() {
                    let desc = ctx.get_desc(t1);
                    if let TypeDesc::Tconstr { path, args, .. } = &*desc {
                        let path_norm = normalize_path_full(ctx, env, path);
                        if path_norm != *path {
                            link_source = ctx.new_constr(path_norm, args.to_vec());
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
            let original_desc1 = (*desc1).clone();
            let body1 = *body1;
            let body2 = *body2;
            let vars1 = vars1.to_vec();
            let vars2 = vars2.to_vec();
            drop(desc1);
            drop(desc2);

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            // ctype.ml unify3: `Tpoly (t1, []), Tpoly (t2, []) -> unify env
            // t1 t2 | Tpoly (t1, tl1), Tpoly (t2, tl2) -> enter_poly !env
            // univar_pairs t1 tl1 t2 tl2 (unify env)`.
            let result = if vars1.is_empty() && vars2.is_empty() {
                unify(ctx, state, body1, body2)
            } else {
                unify_enter_poly(ctx, state, body1, &vars1, body2, &vars2)
            };

            if matches!(result, Err(TypeError::Unify(_))) {
                ctx.set_desc(t1, original_desc1);
            }

            result
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
            let original_desc1 = (*desc1).clone();
            let row1 = row1.clone();
            let row2 = row2.clone();
            drop(desc1);
            drop(desc2);

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            let result = unify_rows(ctx, state, &row1, &row2);
            if matches!(result, Err(TypeError::Unify(_))) {
                ctx.set_desc(t1, original_desc1);
            }
            result
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
            let original_desc1 = (*desc1).clone();
            let fields1 = *fields1;
            let fields2 = *fields2;
            drop(desc1);
            drop(desc2);

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
            // OCaml links t1'→t2 BEFORE recursing into children
            link_type(ctx, t1, t2);

            let result = unify_object_fields(ctx, state, fields1, fields2);
            if matches!(result, Err(TypeError::Unify(_))) {
                ctx.set_desc(t1, original_desc1);
            }
            result
        }

        // ctype.ml unify3 `Tfield _, Tfield _` (special case for GADTs):
        // `unify_fields env t1' t2'`, without linking.
        (TypeDesc::Tfield { .. }, TypeDesc::Tfield { .. }) => {
            drop(desc1);
            drop(desc2);
            unify_object_fields(ctx, state, t1, t2)
        }

        // Package types
        (
            TypeDesc::Tpackage {
                path: path1,
                lids: lids1,
                args: args1,
            },
            TypeDesc::Tpackage {
                path: path2,
                lids: lids2,
                args: args2,
            },
        ) => {
            let path1 = path1.clone();
            let path2 = path2.clone();
            let lids1 = lids1.clone();
            let lids2 = lids2.clone();
            let args1 = args1.clone();
            let args2 = args2.clone();
            drop(desc1);
            drop(desc2);

            let unify_env = state.env().map(Env::clone_preserve_id);
            let labels_2_complete = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                unify_env.as_ref(),
                super::decl::ModuleType::MtyIdent(path2.clone()),
                &lids1,
                &lids2,
            );
            let labels_1_complete = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                unify_env.as_ref(),
                super::decl::ModuleType::MtyIdent(path1.clone()),
                &lids2,
                &lids1,
            );
            if !labels_1_complete || !labels_2_complete {
                return Err(TypeError::Unify(vec![]));
            }

            let package_paths_equivalent = path1.same(&path2)
                || unify_env.as_ref().is_some_and(|env| {
                    // OCaml compiler/ml/ctype.ml:2173-2175 `eq_package_path`
                    // compares the original paths or their normalized paths
                    // with `Path.same`; it does not compare printed names.
                    let norm1 = normalize_path_full(ctx, env, &path1);
                    let norm2 = normalize_path_full(ctx, env, &path2);
                    norm1.same(&norm2)
                });
            if !package_paths_equivalent {
                return Err(TypeError::Unify(vec![]));
            }

            if args1.len() != args2.len() {
                return Err(TypeError::Unify(vec![]));
            }

            if lids1.len() != args1.len() || lids2.len() != args2.len() {
                return Err(TypeError::Unify(vec![]));
            }

            let pairs: Vec<_> = args1
                .iter()
                .zip(args2.iter())
                .map(|(&a, &b)| (a, b))
                .collect();

            // ctype.ml:2197-2201: in Expression mode unify3 runs
            // `occur !env t1' t2'` before linking and unifying children.
            if state.mode == UnifyMode::Expression {
                occur_check(ctx, state.env(), state.mode, t1, t2)?;
            }
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
                let newtype_level = state.newtype_level;
                if let Some(ref p1) = path1_for_gadt {
                    if let Some(ref p2) = path2_for_gadt {
                        // Both are nullary Tconstr
                        if let Some(env) = state.env_mut() {
                            let inst1 = is_instantiable(env, p1);
                            let inst2 = is_instantiable(env, p2);
                            if inst1 && inst2 {
                                // Both instantiable: equation from higher to lower newtype level
                                let lev1 = env
                                    .find_local_constraint(p1)
                                    .or_else(|| env.find_type(p1.head_name()).ok())
                                    .and_then(|d| d.type_newtype_level);
                                let lev2 = env
                                    .find_local_constraint(p2)
                                    .or_else(|| env.find_type(p2.head_name()).ok())
                                    .and_then(|d| d.type_newtype_level);
                                let (source, dest) = if lev1 > lev2 {
                                    (p1.clone(), t2)
                                } else {
                                    (p2.clone(), t1)
                                };
                                add_gadt_equation(ctx, env, newtype_level, &source, dest)?;
                                return Ok(());
                            } else if inst1 {
                                add_gadt_equation(ctx, env, newtype_level, p1, t2)?;
                                return Ok(());
                            } else if inst2 {
                                add_gadt_equation(ctx, env, newtype_level, p2, t1)?;
                                return Ok(());
                            }
                        }
                    } else {
                        // Only left is nullary Tconstr
                        if let Some(env) = state.env_mut() {
                            if is_instantiable(env, p1) {
                                add_gadt_equation(ctx, env, newtype_level, p1, t2)?;
                                return Ok(());
                            }
                        }
                    }
                } else if let Some(ref p2) = path2_for_gadt {
                    // Only right is nullary Tconstr
                    if let Some(env) = state.env_mut() {
                        if is_instantiable(env, p2) {
                            add_gadt_equation(ctx, env, newtype_level, p2, t1)?;
                            return Ok(());
                        }
                    }
                }
            }

            if (is_constr1 || is_constr2) && state.mode == UnifyMode::Pattern {
                return unify_pattern_constructor_mismatch(ctx, state, t1, t2);
            }
            Err(TypeError::Unify(vec![]))
        }
    }
}

// ============================================================================
// Row Unification
// ============================================================================

/// Sort row fields alphabetically by label, matching OCaml's `sort_row_fields`.
pub(crate) type RowFieldEntryRef<'a> = (&'a Label, &'a RowField);
pub(crate) type RowPairRef<'a, 'b> = (&'a str, &'a RowField, &'b RowField);

fn sort_row_fields<'a>(fields: &'a [(Label, RowField)]) -> Vec<RowFieldEntryRef<'a>> {
    let mut sorted: Vec<_> = fields.iter().map(|(label, field)| (label, field)).collect();
    sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    sorted
}

fn row_fields_are_strictly_sorted(fields: &[(Label, RowField)]) -> bool {
    fields.windows(2).all(|pair| pair[0].0 < pair[1].0)
}

/// Merge two sorted row field lists, matching OCaml's `merge_rf`.
/// Returns (r1, r2, pairs) where:
/// - r1: fields only in fi1 (sorted)
/// - r2: fields only in fi2 (sorted)
/// - pairs: matched fields from both sides
fn merge_rf<'a, 'b>(
    fi1: &[RowFieldEntryRef<'a>],
    fi2: &[RowFieldEntryRef<'b>],
) -> (
    Vec<RowFieldEntryRef<'a>>,
    Vec<RowFieldEntryRef<'b>>,
    Vec<RowPairRef<'a, 'b>>,
) {
    let mut r1 = Vec::new();
    let mut r2 = Vec::new();
    let mut pairs = Vec::new();

    let mut i1 = 0;
    let mut i2 = 0;

    while i1 < fi1.len() && i2 < fi2.len() {
        let (l1, f1) = &fi1[i1];
        let (l2, f2) = &fi2[i2];
        if l1 == l2 {
            pairs.push((l1.as_str(), *f1, *f2));
            i1 += 1;
            i2 += 1;
        } else if l1 < l2 {
            r1.push((*l1, *f1));
            i1 += 1;
        } else {
            r2.push((*l2, *f2));
            i2 += 1;
        }
    }
    // Remaining elements
    while i1 < fi1.len() {
        r1.push(fi1[i1]);
        i1 += 1;
    }
    while i2 < fi2.len() {
        r2.push(fi2[i2]);
        i2 += 1;
    }

    // OCaml's merge_rf prepends matched pairs during recursion and does not
    // reverse them at the end, so the final pair order is the reverse of the
    // sorted traversal order.
    pairs.reverse();

    (r1, r2, pairs)
}

fn merge_strictly_sorted_row_fields<'a, 'b>(
    fi1: &'a [(Label, RowField)],
    fi2: &'b [(Label, RowField)],
) -> (
    Vec<RowFieldEntryRef<'a>>,
    Vec<RowFieldEntryRef<'b>>,
    Vec<RowPairRef<'a, 'b>>,
) {
    let mut r1 = Vec::new();
    let mut r2 = Vec::new();
    let mut pairs = Vec::new();

    let mut i1 = 0;
    let mut i2 = 0;

    while i1 < fi1.len() && i2 < fi2.len() {
        let (l1, f1) = (&fi1[i1].0, &fi1[i1].1);
        let (l2, f2) = (&fi2[i2].0, &fi2[i2].1);
        if l1 == l2 {
            pairs.push((l1.as_str(), f1, f2));
            i1 += 1;
            i2 += 1;
        } else if l1 < l2 {
            r1.push((l1, f1));
            i1 += 1;
        } else {
            r2.push((l2, f2));
            i2 += 1;
        }
    }
    while i1 < fi1.len() {
        let (label, field) = (&fi1[i1].0, &fi1[i1].1);
        r1.push((label, field));
        i1 += 1;
    }
    while i2 < fi2.len() {
        let (label, field) = (&fi2[i2].0, &fi2[i2].1);
        r2.push((label, field));
        i2 += 1;
    }

    pairs.reverse();

    (r1, r2, pairs)
}

/// Merge row fields matching OCaml's `merge_row_fields`.
/// Sorts both inputs, then uses sorted merge to partition into
/// (r1_only, r2_only, pairs).
pub(crate) fn merge_row_fields<'a, 'b>(
    fi1: &'a [(Label, RowField)],
    fi2: &'b [(Label, RowField)],
) -> (
    Vec<RowFieldEntryRef<'a>>,
    Vec<RowFieldEntryRef<'b>>,
    Vec<RowPairRef<'a, 'b>>,
) {
    // Match OCaml's fast paths
    if fi1.is_empty() || fi2.is_empty() {
        return (
            fi1.iter().map(|(label, field)| (label, field)).collect(),
            fi2.iter().map(|(label, field)| (label, field)).collect(),
            Vec::new(),
        );
    }
    if fi1.len() == 1 && fi2.iter().all(|(l, _)| l != &fi1[0].0) {
        return (
            fi1.iter().map(|(label, field)| (label, field)).collect(),
            fi2.iter().map(|(label, field)| (label, field)).collect(),
            Vec::new(),
        );
    }
    if fi2.len() == 1 && fi1.iter().all(|(l, _)| l != &fi2[0].0) {
        return (
            fi1.iter().map(|(label, field)| (label, field)).collect(),
            fi2.iter().map(|(label, field)| (label, field)).collect(),
            Vec::new(),
        );
    }
    if fi1.len() >= 8
        && fi2.len() >= 8
        && row_fields_are_strictly_sorted(fi1)
        && row_fields_are_strictly_sorted(fi2)
    {
        return merge_strictly_sorted_row_fields(fi1, fi2);
    }
    let sorted1 = sort_row_fields(fi1);
    let sorted2 = sort_row_fields(fi2);
    merge_rf(&sorted1, &sorted2)
}

/// Unify two row types (for polymorphic variants).
/// Matches OCaml's `unify_row` (ctype.ml:2538): uses `merge_row_fields` to sort
/// and partition fields, then unifies pairs. The result has fields in alphabetical
/// order, matching OCaml's `row_repr` which flattens the sorted chain.
fn unify_rows<'a>(
    ctx: &'a TypeContext,
    state: &mut UnifyState,
    row1: &RowDesc,
    row2: &RowDesc,
) -> TypeResult<()> {
    let row1 = row_repr_ref(ctx, row1);
    let row2 = row_repr_ref(ctx, row2);
    let row1 = row1.as_ref();
    let row2 = row2.as_ref();

    let rm1 = row_more(ctx, row1);
    let rm2 = row_more(ctx, row2);
    if rm1 == rm2 {
        return Ok(());
    }

    let (r1, r2, pairs) = merge_row_fields(&row1.row_fields, &row2.row_fields);

    let fixed1 = row_fixed(ctx, row1);
    let fixed2 = row_fixed(ctx, row2);
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

    let filter_row_fields =
        |erase: bool, fields: &[RowFieldEntryRef<'_>]| -> Vec<(Label, RowField)> {
            let mut filtered = Vec::new();
            for (label, field) in fields.iter().copied() {
                if super::btype::row_field_is_absent(ctx, field) {
                    continue;
                }
                if erase {
                    if let Some(link) = super::btype::row_field_unmatched_reither_link(ctx, field) {
                        ctx.set_row_field(link, RowField::Rabsent);
                        continue;
                    }
                }
                filtered.push((label.clone(), field.clone()));
            }
            filtered
        };
    let empty = |fields: &[RowFieldEntryRef<'_>]| {
        fields
            .iter()
            .copied()
            .all(|(_, f)| super::btype::row_field_is_absent(ctx, f))
    };

    if closed {
        let all_absent = pairs.iter().all(|(_, f1, f2)| {
            super::btype::row_field_is_absent(ctx, f1) || super::btype::row_field_is_absent(ctx, f2)
        });
        if (empty(&r1) || row2.row_closed) && (empty(&r2) || row1.row_closed) && all_absent {
            // ctype.ml:2432 `raise (Unify [(mkvariant [] true, mkvariant [] true)])`.
            return Err(TypeError::Unify(vec![(
                mkvariant(ctx, Vec::new(), true),
                mkvariant(ctx, Vec::new(), true),
            )]));
        }
    }

    let keep = |swap: bool| {
        pairs.iter().all(|(_, f1, f2)| {
            let (left, right) = if swap { (f2, f1) } else { (f1, f2) };
            super::btype::row_field_is_absent(ctx, left)
                || !super::btype::row_field_is_absent(ctx, right)
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
        row_fields: vec![].into(),
        row_more: more,
        row_closed: closed,
        row_fixed: fixed,
        row_name: name,
    };

    let set_more = |ctx: &'a TypeContext,
                    state: &mut UnifyState,
                    row: &RowDesc,
                    is_row1: bool,
                    rest: &[RowFieldEntryRef<'_>]|
     -> TypeResult<()> {
        let row_is_fixed = row_fixed(ctx, row);
        let rest = if closed {
            filter_row_fields(row.row_closed, rest)
        } else {
            rest.iter()
                .copied()
                .map(|(label, field)| (label.clone(), field.clone()))
                .collect()
        };
        if (!rest.is_empty() && (row.row_closed || row_is_fixed))
            || (closed && row_is_fixed && !row.row_closed)
        {
            // ctype.ml:2463-2464.
            let t1 = mkvariant(ctx, Vec::new(), true);
            let t2 = mkvariant(ctx, rest, false);
            return Err(TypeError::Unify(vec![if is_row1 {
                (t1, t2)
            } else {
                (t2, t1)
            }]));
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

        let ty = ctx.new_generic_type(TypeDesc::Tvariant(Box::new(RowDesc {
            row_fields: rest.into(),
            ..row0.clone()
        })));
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
        set_more(ctx, state, row2, false, &r1)?;
        set_more(ctx, state, row1, true, &r2)?;
        for (label, f1, f2) in &pairs {
            // ctype.ml:2485-2491 prefixes the single-field variants.
            if let Err(err) = unify_row_field(ctx, state, fixed1, fixed2, more, label, f1, f2) {
                return Err(match err {
                    TypeError::Unify(trace) => {
                        let mut new_trace = vec![(
                            mkvariant(ctx, vec![((*label).into(), (*f1).clone())], true),
                            mkvariant(ctx, vec![((*label).into(), (*f2).clone())], true),
                        )];
                        new_trace.extend(trace);
                        TypeError::Unify(new_trace)
                    }
                    err => err,
                });
            }
        }
        if super::btype::static_row(ctx, row1) {
            let rm = row_more(ctx, row1);
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

/// `mkvariant fields closed` (ctype.ml): a generic row with a fresh row
/// variable, used for unification traces.
fn mkvariant(ctx: &TypeContext, fields: Vec<(Label, RowField)>, closed: bool) -> TypeExprRef {
    let row_more = ctx.new_var(None);
    ctx.new_generic_type(TypeDesc::Tvariant(Box::new(RowDesc {
        row_fields: fields.into(),
        row_more,
        row_closed: closed,
        row_fixed: false,
        row_name: None,
    })))
}

/// Unify two row fields.
/// Matches OCaml's `unify_row_field` behavior, including Reither link updates.
fn unify_row_field(
    ctx: &TypeContext,
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
            if e1 == e2 {
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
                return Ok(());
            }

            // ctype.ml:2488-2492: `redo` when the fields are matched or
            // fixed, or, under `expand_head_rigid`, when either side has a
            // single conjunct.
            let active = !ctx.passive_variants()
                && (*m1
                    || *m2
                    || fixed1
                    || fixed2
                    || (ctx.rigid_variants() && (types1.len() == 1 || types2.len() == 1)));
            if active {
                let mut all_types: Vec<TypeExprRef> =
                    Vec::with_capacity(types1.len() + types2.len());
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
            Ok(())
        }

        (
            RowField::Reither {
                matched: false,
                link: e1,
                ..
            },
            RowField::Rabsent,
        ) if !fixed1 => {
            ctx.set_row_field(*e1, f2.clone());
            Ok(())
        }
        (
            RowField::Rabsent,
            RowField::Reither {
                matched: false,
                link: e2,
                ..
            },
        ) if !fixed2 => {
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
/// ctype.ml `field_info`: an object field as stored. `mutability` is the
/// field's cell; read its class value with `TypeContext::mutability_repr`.
#[derive(Debug, Clone)]
pub(crate) struct FieldInfo {
    pub(crate) name: String,
    pub(crate) mutability: MutabilityRef,
    pub(crate) typ: TypeExprRef,
}

/// ctype.ml `flatten_fields`: the fields of a row sorted by name, and the
/// row's terminator.
pub(crate) fn flatten_fields(ctx: &TypeContext, ty: TypeExprRef) -> (Vec<FieldInfo>, TypeExprRef) {
    let mut fields = Vec::new();
    let mut current = ctx.repr(ty);
    loop {
        let next = match &*ctx.get_desc(current) {
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                fields.push(FieldInfo {
                    name: name.clone(),
                    mutability: *mutability,
                    typ: *typ,
                });
                *rest
            }
            _ => break,
        };
        current = ctx.repr(next);
    }
    // OCaml accumulates the fields in reverse before its stable sort.
    fields.reverse();
    fields.sort_by(|a, b| a.name.cmp(&b.name));
    (fields, current)
}

/// ctype.ml `associate_fields`: pair two sorted field lists by name.
/// Returns (paired, surplus_from_1, surplus_from_2).
pub(crate) fn associate_fields(
    fields1: Vec<FieldInfo>,
    fields2: Vec<FieldInfo>,
) -> (Vec<(FieldInfo, FieldInfo)>, Vec<FieldInfo>, Vec<FieldInfo>) {
    let mut pairs = Vec::new();
    let mut miss1 = Vec::new();
    let mut miss2 = Vec::new();
    let mut it1 = fields1.into_iter().peekable();
    let mut it2 = fields2.into_iter().peekable();
    loop {
        match (it1.peek(), it2.peek()) {
            (Some(f1), Some(f2)) => match f1.name.cmp(&f2.name) {
                std::cmp::Ordering::Equal => {
                    pairs.push((it1.next().unwrap(), it2.next().unwrap()));
                }
                std::cmp::Ordering::Less => miss1.push(it1.next().unwrap()),
                std::cmp::Ordering::Greater => miss2.push(it2.next().unwrap()),
            },
            (Some(_), None) => miss1.push(it1.next().unwrap()),
            (None, Some(_)) => miss2.push(it2.next().unwrap()),
            (None, None) => break,
        }
    }
    (pairs, miss1, miss2)
}

/// Build a Tfield chain from a list of fields with a given rest.
/// Matches OCaml `build_fields` in ctype.ml.
fn build_fields(
    ctx: &TypeContext,
    level: i32,
    fields: &[FieldInfo],
    rest: TypeExprRef,
) -> TypeExprRef {
    let mut current = rest;
    for field in fields.iter().rev() {
        current = ctx.alloc_type_at_level(
            TypeDesc::Tfield {
                name: field.name.clone(),
                mutability: field.mutability,
                typ: field.typ,
                rest: current,
            },
            level,
        );
    }
    current
}

/// Unify two object field chains using OCaml's field-order-independent algorithm.
/// Matches OCaml `unify_fields` in ctype.ml.
fn unify_object_fields(
    ctx: &TypeContext,
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
    // ctype.ml:2298-2301: sample openness before unifying the row tails;
    // `unify_mutability` needs the pre-unification state because tail
    // unification can close an open row.
    let open1 = matches!(&*ctx.borrow_desc(ctx.repr(rest1)), TypeDesc::Tvar(..));
    let open2 = matches!(&*ctx.borrow_desc(ctx.repr(rest2)), TypeDesc::Tvar(..));

    // Create shared row variable (OCaml make_rowvar)
    let va = if miss2.is_empty() {
        rest1
    } else if miss1.is_empty() {
        rest2
    } else {
        // ctype.ml:2427: `newty2 (min ...) (Tvar None)`, the static constant.
        ctx.alloc_type_at_level(
            TypeDesc::Tvar(None, super::type_expr::VarDescBlock::Static),
            min_level,
        )
    };

    // ctype.ml:2356-2377: on failure, restore the rest descriptions.
    let d1 = (*ctx.get_desc(rest1)).clone();
    let d2 = (*ctx.get_desc(rest2)).clone();
    let result = unify_object_field_pairs(
        ctx,
        state,
        &pairs,
        &miss1,
        &miss2,
        (l1, l2),
        (open1, open2),
        va,
        rest1,
        rest2,
    );
    if result.is_err() {
        ctx.set_desc(rest1, d1);
        ctx.set_desc(rest2, d2);
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn unify_object_field_pairs(
    ctx: &TypeContext,
    state: &mut UnifyState,
    pairs: &[(FieldInfo, FieldInfo)],
    miss1: &[FieldInfo],
    miss2: &[FieldInfo],
    (l1, l2): (i32, i32),
    (open1, open2): (bool, bool),
    va: TypeExprRef,
    rest1: TypeExprRef,
    rest2: TypeExprRef,
) -> TypeResult<()> {
    // unify(build_fields miss1 va, rest2) — rest2 must absorb miss1 fields
    let extended1 = build_fields(ctx, l1, miss1, va);
    unify(ctx, state, extended1, rest2)?;

    // unify(rest1, build_fields miss2 va) — rest1 must absorb miss2 fields
    let extended2 = build_fields(ctx, l2, miss2, va);
    unify(ctx, state, rest1, extended2)?;

    // Unify paired fields (matching names from both sides)
    for (f1, f2) in pairs {
        unify_mutability(ctx, open1, open2, f1, f2)?;
        if let Err(err) = unify(ctx, state, f1.typ, f2.typ) {
            return Err(match err {
                TypeError::Unify(trace) => {
                    let field1 = ctx.new_type(TypeDesc::Tfield {
                        name: f1.name.clone(),
                        mutability: f1.mutability,
                        typ: f1.typ,
                        rest: ctx.new_type(TypeDesc::Tnil),
                    });
                    let field2 = ctx.new_type(TypeDesc::Tfield {
                        name: f2.name.clone(),
                        mutability: f2.mutability,
                        typ: f2.typ,
                        rest: ctx.new_type(TypeDesc::Tnil),
                    });
                    let mut wrapped_trace = vec![(field1, field2)];
                    wrapped_trace.extend(trace);
                    TypeError::Unify(wrapped_trace)
                }
                err => err,
            });
        }
    }

    Ok(())
}

/// ctype.ml `unify_mutability`: `open1`/`open2` describe the rows before
/// their tails were unified. Promotion and class merging operate on
/// representatives and are recorded on the trail.
fn unify_mutability(
    ctx: &TypeContext,
    open1: bool,
    open2: bool,
    f1: &FieldInfo,
    f2: &FieldInfo,
) -> TypeResult<()> {
    let r1 = ctx.mutability_ref_repr(f1.mutability);
    let r2 = ctx.mutability_ref_repr(f2.mutability);
    if r1 == r2 {
        return Ok(());
    }
    let value = |r| match ctx.get_mutability(r) {
        FieldMutability::Value(flag) => flag,
        FieldMutability::Link(_) => unreachable!("mutability_ref_repr returns a value cell"),
    };
    match (value(r1), value(r2)) {
        (MutableFlag::Immutable, MutableFlag::Immutable)
        | (MutableFlag::Mutable, MutableFlag::Mutable) => {}
        (MutableFlag::Immutable, MutableFlag::Mutable) => {
            if !open1 {
                return Err(TypeError::Unify(vec![]));
            }
            ctx.set_mutability(r1, FieldMutability::Value(MutableFlag::Mutable));
        }
        (MutableFlag::Mutable, MutableFlag::Immutable) => {
            if !open2 {
                return Err(TypeError::Unify(vec![]));
            }
            ctx.set_mutability(r2, FieldMutability::Value(MutableFlag::Mutable));
        }
    }
    // Merge the two equivalence classes.
    ctx.set_mutability(r2, FieldMutability::Link(r1));
    Ok(())
}

// ============================================================================
// More-general Inclusion Check
// ============================================================================

fn moregen_may_instantiate(ctx: &TypeContext, inst_nongen: bool, ty: TypeExprRef) -> bool {
    if inst_nongen {
        ctx.get_level(ty) != GENERIC_LEVEL - 1
    } else {
        ctx.get_level(ty) == GENERIC_LEVEL
    }
}

fn moregen_occur(ctx: &TypeContext, env: &Env, level: i32, ty: TypeExprRef) -> TypeResult<()> {
    fn occur(
        ctx: &TypeContext,
        level: i32,
        ty: TypeExprRef,
        seen: &mut TypeExprRefSet,
    ) -> TypeResult<()> {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return Ok(());
        }
        if ctx.get_level(ty) > level {
            let desc = ctx.get_desc(ty);
            if matches!(&*desc, TypeDesc::Tvar(..)) && ctx.get_level(ty) >= GENERIC_LEVEL - 1 {
                return Err(TypeError::Unify(vec![]));
            }
            let static_variant_row = match &*desc {
                TypeDesc::Tvariant(row) if btype::static_row(ctx, row) => Some(row.clone()),
                _ => None,
            };
            drop(desc);
            if let Some(row) = static_variant_row {
                let mut children = Vec::new();
                btype::iter_row(ctx, &row, |child| children.push(child));
                for child in children {
                    occur(ctx, level, child, seen)?;
                }
            } else {
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                for child in children {
                    occur(ctx, level, child, seen)?;
                }
            }
        }
        Ok(())
    }

    // OCaml compiler/ml/ctype.ml:2934-2952 checks that subject-side generic
    // variables are not captured before lowering the candidate with
    // `update_level`.
    let mut seen = TypeExprRefSet::new();
    occur(ctx, level, ty, &mut seen)?;
    update_level_expand(ctx, env, level, ty);
    Ok(())
}

fn moregen_list(
    ctx: &TypeContext,
    inst_nongen: bool,
    type_pairs: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    env: &Env,
    left: &[TypeExprRef],
    right: &[TypeExprRef],
) -> TypeResult<()> {
    // OCaml compiler/ml/ctype.ml:3018-3020 rejects different arities before
    // recursing pairwise.
    if left.len() != right.len() {
        return Err(TypeError::Unify(vec![]));
    }
    for (&left, &right) in left.iter().zip(right.iter()) {
        moregen(ctx, inst_nongen, type_pairs, env, left, right)?;
    }
    Ok(())
}

fn moregen_fields(
    ctx: &TypeContext,
    inst_nongen: bool,
    type_pairs: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    env: &Env,
    ty1: TypeExprRef,
    ty2: TypeExprRef,
) -> TypeResult<()> {
    // OCaml compiler/ml/ctype.ml:3022-3039 flattens both object field chains,
    // requires the implementation-side fields to cover the signature-side
    // fields, then compares paired field payloads.
    let (fields1, rest1) = flatten_fields(ctx, ty1);
    let (fields2, rest2) = flatten_fields(ctx, ty2);
    let (pairs, miss1, miss2) = associate_fields(fields1, fields2);
    if !miss1.is_empty() {
        return Err(TypeError::Unify(vec![]));
    }
    let rest2_with_missing = build_fields(ctx, ctx.get_level(ctx.repr(ty2)), &miss2, rest2);
    moregen(ctx, inst_nongen, type_pairs, env, rest1, rest2_with_missing)?;
    for (f1, f2) in pairs {
        // ctype.ml moregen_fields: the field capabilities must agree.
        if ctx.mutability_repr(f1.mutability) != ctx.mutability_repr(f2.mutability) {
            return Err(TypeError::Unify(vec![]));
        }
        moregen(ctx, inst_nongen, type_pairs, env, f1.typ, f2.typ)?;
    }
    Ok(())
}

fn moregen_filter_row_fields(
    ctx: &TypeContext,
    erase: bool,
    fields: Vec<RowFieldEntryRef<'_>>,
) -> Vec<(Label, RowField)> {
    // OCaml compiler/ml/ctype.ml:473-482 drops absent row fields and, when
    // requested, mutates unmatched Reither refs to Rabsent while filtering.
    let mut filtered = Vec::new();
    for (label, field) in fields {
        match btype::row_field_repr(ctx, field) {
            RowField::Rabsent => {}
            RowField::Reither {
                matched: false,
                link,
                ..
            } if erase => {
                ctx.set_row_field(link, RowField::Rabsent);
            }
            field => filtered.push((label.clone(), field)),
        }
    }
    filtered
}

fn moregen_row(
    ctx: &TypeContext,
    inst_nongen: bool,
    type_pairs: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    env: &Env,
    row1: &RowDesc,
    row2: &RowDesc,
) -> TypeResult<()> {
    // OCaml compiler/ml/ctype.ml:3051-3109 compares row descriptors after
    // `row_repr`, preserving the same row-field mutation order.
    let row1 = row_repr(ctx, row1);
    let row2 = row_repr(ctx, row2);
    let rm1 = ctx.repr(row_more(ctx, &row1));
    let rm2 = ctx.repr(row_more(ctx, &row2));
    if rm1 == rm2 {
        return Ok(());
    }

    let may_inst = {
        let rm1_desc = ctx.get_desc(rm1);
        let is_instantiable_var = matches!(&*rm1_desc, TypeDesc::Tvar(..))
            && moregen_may_instantiate(ctx, inst_nongen, rm1);
        let is_nil = matches!(&*rm1_desc, TypeDesc::Tnil);
        is_instantiable_var || is_nil
    };
    let (r1, r2, pairs) = merge_row_fields(&row1.row_fields, &row2.row_fields);
    let (r1, r2) = if row2.row_closed {
        (
            moregen_filter_row_fields(ctx, may_inst, r1),
            moregen_filter_row_fields(ctx, false, r2),
        )
    } else {
        (
            r1.into_iter()
                .map(|(label, field)| (label.clone(), field.clone()))
                .collect(),
            r2.into_iter()
                .map(|(label, field)| (label.clone(), field.clone()))
                .collect(),
        )
    };

    if !r1.is_empty() || (row1.row_closed && (!row2.row_closed || !r2.is_empty())) {
        return Err(TypeError::Unify(vec![]));
    }

    let rm1_desc = ctx.get_desc(rm1);
    let rm2_desc = ctx.get_desc(rm2);
    match (&*rm1_desc, &*rm2_desc) {
        (TypeDesc::Tunivar(name1, ..), TypeDesc::Tunivar(name2, ..)) if name1 == name2 => {}
        (TypeDesc::Tunivar(..), _) | (_, TypeDesc::Tunivar(..)) => {
            return Err(TypeError::Unify(vec![]));
        }
        _ if btype::static_row(ctx, &row1) => {}
        _ if may_inst => {
            drop(rm1_desc);
            drop(rm2_desc);
            let ext = ctx.new_generic_type(TypeDesc::Tvariant(Box::new(RowDesc {
                row_fields: r2.into(),
                row_name: None,
                ..row2.clone()
            })));
            moregen_occur(ctx, env, ctx.get_level(rm1), ext)?;
            link_type(ctx, rm1, ext);
        }
        (TypeDesc::Tconstr { .. }, TypeDesc::Tconstr { .. }) => {
            drop(rm1_desc);
            drop(rm2_desc);
            moregen(ctx, inst_nongen, type_pairs, env, rm1, rm2)?;
        }
        _ => return Err(TypeError::Unify(vec![])),
    }

    for (_label, field1, field2) in pairs {
        let field1 = btype::row_field_repr(ctx, field1);
        let field2 = btype::row_field_repr(ctx, field2);
        match (&field1, &field2) {
            (RowField::Rpresent(Some(ty1)), RowField::Rpresent(Some(ty2))) => {
                moregen(ctx, inst_nongen, type_pairs, env, *ty1, *ty2)?;
            }
            (RowField::Rpresent(None), RowField::Rpresent(None))
            | (RowField::Rabsent, RowField::Rabsent) => {}
            (
                RowField::Reither {
                    constant: false,
                    types,
                    link,
                    ..
                },
                RowField::Rpresent(Some(ty2)),
            ) if may_inst => {
                ctx.set_row_field(*link, field2.clone());
                for ty1 in types {
                    moregen(ctx, inst_nongen, type_pairs, env, *ty1, *ty2)?;
                }
            }
            (
                RowField::Reither {
                    constant: c1,
                    types: types1,
                    link: link1,
                    ..
                },
                RowField::Reither {
                    constant: c2,
                    types: types2,
                    matched: matched2,
                    link: link2,
                },
            ) => {
                if link1 != link2 {
                    if *c1 && !*c2 {
                        return Err(TypeError::Unify(vec![]));
                    }
                    ctx.set_row_field(
                        *link1,
                        RowField::Reither {
                            constant: *c2,
                            types: vec![],
                            matched: *matched2,
                            link: *link2,
                        },
                    );
                    if types1.len() == types2.len() {
                        for (&ty1, &ty2) in types1.iter().zip(types2.iter()) {
                            moregen(ctx, inst_nongen, type_pairs, env, ty1, ty2)?;
                        }
                    } else if let Some(&ty2) = types2.first() {
                        for &ty1 in types1 {
                            moregen(ctx, inst_nongen, type_pairs, env, ty1, ty2)?;
                        }
                    } else if !types1.is_empty() {
                        return Err(TypeError::Unify(vec![]));
                    }
                }
            }
            (
                RowField::Reither {
                    constant: true,
                    types,
                    link,
                    ..
                },
                RowField::Rpresent(None),
            ) if may_inst && types.is_empty() => {
                ctx.set_row_field(*link, field2.clone());
            }
            (RowField::Reither { link, .. }, RowField::Rabsent) if may_inst => {
                ctx.set_row_field(*link, field2.clone());
            }
            _ => return Err(TypeError::Unify(vec![])),
        }
    }
    Ok(())
}

fn moregen(
    ctx: &TypeContext,
    inst_nongen: bool,
    type_pairs: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    env: &Env,
    t1: TypeExprRef,
    t2: TypeExprRef,
) -> TypeResult<()> {
    let t1 = ctx.repr(t1);
    let t2 = ctx.repr(t2);
    if t1 == t2 {
        return Ok(());
    }

    // OCaml compiler/ml/ctype.ml:2958-3016 first handles instantiable pattern
    // variables, then expands both heads and records the expanded pair before
    // structural recursion. The pair table is what prevents recursive alias
    // expansion from becoming an eager unification loop.
    {
        let desc1 = ctx.get_desc(t1);
        if matches!(&*desc1, TypeDesc::Tvar(..)) && moregen_may_instantiate(ctx, inst_nongen, t1) {
            drop(desc1);
            moregen_occur(ctx, env, ctx.get_level(t1), t2)?;
            occur_check(ctx, Some(env), UnifyMode::Expression, t1, t2)?;
            link_type(ctx, t1, t2);
            return Ok(());
        }
    }

    {
        let desc1 = ctx.get_desc(t1);
        let desc2 = ctx.get_desc(t2);
        if let (
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
        ) = (&*desc1, &*desc2)
        {
            if args1.is_empty() && args2.is_empty() && path1.same(path2) {
                return Ok(());
            }
        }
    }

    let t1_expanded = ctx.repr(expand_head(ctx, env, t1));
    let t2_expanded = ctx.repr(expand_head(ctx, env, t2));
    if t1_expanded == t2_expanded {
        return Ok(());
    }
    if !type_pairs.insert((t1_expanded, t2_expanded)) {
        return Ok(());
    }

    let desc1 = ctx.get_desc(t1_expanded);
    let desc2 = ctx.get_desc(t2_expanded);
    match (&*desc1, &*desc2) {
        (TypeDesc::Tvar(..), _) if moregen_may_instantiate(ctx, inst_nongen, t1_expanded) => {
            drop(desc1);
            drop(desc2);
            moregen_occur(ctx, env, ctx.get_level(t1_expanded), t2)?;
            link_type(ctx, t1_expanded, t2);
            Ok(())
        }
        // OCaml compiler/ml/ctype.ml:2986-2989 uses
        // `Asttypes.same_arg_label`, so source locations on labels do not
        // participate in the inclusion check.
        (
            TypeDesc::Tarrow {
                args: args1,
                ret: ret1,
            },
            TypeDesc::Tarrow {
                args: args2,
                ret: ret2,
            },
        ) if args1.len() == args2.len()
            && args1
                .iter()
                .zip(args2)
                .all(|(a1, a2)| a1.label().same_label(a2.label())) =>
        {
            let args1 = args1.clone();
            let args2 = args2.clone();
            let ret1 = *ret1;
            let ret2 = *ret2;
            drop(desc1);
            drop(desc2);
            for (arg1, arg2) in args1.iter().zip(&args2) {
                moregen(ctx, inst_nongen, type_pairs, env, arg1.typ, arg2.typ)?;
            }
            moregen(ctx, inst_nongen, type_pairs, env, ret1, ret2)
        }
        (TypeDesc::Ttuple(left), TypeDesc::Ttuple(right)) => {
            let left = left.clone();
            let right = right.clone();
            drop(desc1);
            drop(desc2);
            moregen_list(ctx, inst_nongen, type_pairs, env, &left, &right)
        }
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
        ) if path1.same(path2) => {
            let args1 = args1.clone();
            let args2 = args2.clone();
            drop(desc1);
            drop(desc2);
            moregen_list(ctx, inst_nongen, type_pairs, env, &args1, &args2)
        }
        (
            TypeDesc::Tpackage {
                path: path1,
                lids: lids1,
                args: args1,
            },
            TypeDesc::Tpackage {
                path: path2,
                lids: lids2,
                args: args2,
            },
        ) => {
            let path1 = path1.clone();
            let path2 = path2.clone();
            let lids1 = lids1.clone();
            let lids2 = lids2.clone();
            let args1 = args1.clone();
            let args2 = args2.clone();
            drop(desc1);
            drop(desc2);
            // OCaml compiler/ml/ctype.ml:2996-3002 routes package
            // comparison through `unify_package`; ctype.ml:2237-2238 calls
            // `complete_type_list` twice, and ctype.ml:2199-2201 allocates a
            // hidden `Pkg` module for each completion even when the labels are
            // already identical.
            let complete_right = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                Some(env),
                crate::types::decl::ModuleType::MtyIdent(path2.clone()),
                &lids1,
                &lids2,
            );
            let complete_left = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                Some(env),
                crate::types::decl::ModuleType::MtyIdent(path1.clone()),
                &lids2,
                &lids1,
            );
            if !(complete_right && complete_left && path1.same(&path2)) {
                return Err(TypeError::Unify(vec![]));
            }
            moregen_list(ctx, inst_nongen, type_pairs, env, &args1, &args2)
        }
        (TypeDesc::Tvariant(row1), TypeDesc::Tvariant(row2)) => {
            let row1 = row1.clone();
            let row2 = row2.clone();
            drop(desc1);
            drop(desc2);
            moregen_row(ctx, inst_nongen, type_pairs, env, &row1, &row2)
        }
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
            moregen_fields(ctx, inst_nongen, type_pairs, env, fields1, fields2)
        }
        (TypeDesc::Tfield { .. }, TypeDesc::Tfield { .. }) => {
            drop(desc1);
            drop(desc2);
            moregen_fields(ctx, inst_nongen, type_pairs, env, t1_expanded, t2_expanded)
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => Ok(()),
        (
            TypeDesc::Tpoly { body: body1, vars },
            TypeDesc::Tpoly {
                body: body2,
                vars: vars2,
            },
        ) if vars.is_empty() && vars2.is_empty() => {
            let body1 = *body1;
            let body2 = *body2;
            drop(desc1);
            drop(desc2);
            moregen(ctx, inst_nongen, type_pairs, env, body1, body2)
        }
        (
            TypeDesc::Tpoly { body: body1, vars },
            TypeDesc::Tpoly {
                body: body2,
                vars: vars2,
            },
        ) if vars.len() == vars2.len() => {
            let body1 = *body1;
            let body2 = *body2;
            drop(desc1);
            drop(desc2);
            moregen(ctx, inst_nongen, type_pairs, env, body1, body2)
        }
        (TypeDesc::Tunivar(name1, ..), TypeDesc::Tunivar(name2, ..)) if name1 == name2 => Ok(()),
        _ => Err(TypeError::Unify(vec![])),
    }
}

pub fn moregeneral(
    ctx: &TypeContext,
    env: &Env,
    inst_nongen: bool,
    pat_sch: TypeExprRef,
    subj_sch: TypeExprRef,
) -> bool {
    // OCaml compiler/ml/ctype.ml:3124-3144 copies the subject with
    // `current_level = generic_level - 1`, then copies the pattern with
    // `current_level = generic_level`, and finally runs `moregen` with a fresh
    // TypePairs table.
    let old_level = ctx.current_level();
    ctx.set_current_level(GENERIC_LEVEL - 1);
    let subj = subst_identity_copy(ctx, instance(ctx, subj_sch));
    ctx.set_current_level(GENERIC_LEVEL);
    let patt = instance(ctx, pat_sch);
    let mut type_pairs = HashSet::new();
    let result = moregen(ctx, inst_nongen, &mut type_pairs, env, patt, subj).is_ok();
    ctx.set_current_level(old_level);
    result
}

fn closed_schema_rec(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    visited: &mut TypeExprRefSet,
) -> bool {
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return true;
    }

    enum Action {
        Tvar,
        Tconstr(Vec<TypeExprRef>),
        Tfield { typ: TypeExprRef, rest: TypeExprRef },
        Tvariant(RowDesc),
        Children(Vec<TypeExprRef>),
    }

    let action = {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvar(..) => Action::Tvar,
            TypeDesc::Tconstr { args, .. } => Action::Tconstr(args.to_vec()),
            TypeDesc::Tfield { typ, rest, .. } => Action::Tfield {
                typ: *typ,
                rest: *rest,
            },
            TypeDesc::Tvariant(row) => Action::Tvariant(*row.clone()),
            _ => {
                let mut children = Vec::new();
                iter_type_expr(ctx, ty, |child| children.push(child));
                Action::Children(children)
            }
        }
    };

    match action {
        Action::Tvar => ctx.get_level(ty) == GENERIC_LEVEL,
        Action::Tconstr(children) => {
            let old_visited = visited.clone();
            if children
                .iter()
                .all(|child| closed_schema_rec(ctx, env, *child, visited))
            {
                true
            } else if let Some(expanded) = expand_head_once(ctx, env, ty) {
                *visited = old_visited;
                closed_schema_rec(ctx, env, expanded, visited)
            } else {
                false
            }
        }
        // OCaml compiler/ml/ctype.ml closed_schema_rec handles variant rows
        // separately from generic `iter_type_expr`: static variant rows
        // deliberately do not visit `row_more`.
        Action::Tfield { typ, rest } => {
            closed_schema_rec(ctx, env, typ, visited) && closed_schema_rec(ctx, env, rest, visited)
        }
        Action::Tvariant(row) => {
            let row = crate::types::btype::row_repr(ctx, &row);
            let mut row_children = Vec::new();
            crate::types::btype::iter_row(ctx, &row, |child| row_children.push(child));
            row_children
                .into_iter()
                .all(|child| closed_schema_rec(ctx, env, child, visited))
                && (crate::types::btype::static_row(ctx, &row)
                    || closed_schema_rec(ctx, env, row.row_more, visited))
        }
        Action::Children(children) => children
            .iter()
            .all(|child| closed_schema_rec(ctx, env, *child, visited)),
    }
}

/// Return whether all variables of type `ty` are generic.
///
/// Mirrors OCaml `Ctype.closed_schema`: a non-generic `Tvar` means the inferred
/// signature contains a weak type variable and must be rejected.
pub fn closed_schema(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    let mut visited = TypeExprRefSet::new();
    closed_schema_rec(ctx, env, ty, &mut visited)
}

// ============================================================================
// Generalization
// ============================================================================

/// Generalize a type.
///
/// This marks all type variables at or above the current level as generic,
/// making the type polymorphic.
fn generalize_rec(ctx: &TypeContext, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    let current = ctx.current_level();

    if level > current && level != GENERIC_LEVEL {
        // Mark as generic
        ctx.set_level(ty, GENERIC_LEVEL);
        let abbrev = match &*ctx.borrow_desc(ty) {
            TypeDesc::Tconstr { abbrev, .. } => Some(*abbrev),
            _ => None,
        };
        if let Some(abbrev) = abbrev {
            btype::iter_abbrev(ctx, abbrev, |memo_ty| {
                generalize_rec(ctx, memo_ty);
            });
        }
        iter_type_expr(ctx, ty, |child| {
            generalize_rec(ctx, child);
        });
    }
}

pub fn generalize(ctx: &TypeContext, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    generalize_rec(ctx, ty);
}

fn lower_nongen_type_expr_rec(
    ctx: &TypeContext,
    nglev: i32,
    ty: TypeExprRef,
    seen: &mut TypeExprRefSet,
) {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }

    let level = ctx.get_level(ty);
    let is_tvar = matches!(&*ctx.borrow_desc(ty), TypeDesc::Tvar(..));
    if is_tvar && level < GENERIC_LEVEL && level > nglev {
        ctx.set_level(ty, nglev);
    }

    let mut children: smallvec::SmallVec<[TypeExprRef; 8]> = smallvec::SmallVec::new();
    iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        lower_nongen_type_expr_rec(ctx, nglev, child, seen);
    }
}

fn lower_nongen_type_decl_rec(
    ctx: &TypeContext,
    nglev: i32,
    decl: &crate::types::decl::TypeDeclaration,
    seen: &mut TypeExprRefSet,
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
        TypeKind::TypeVariant(constructors, _) => {
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
    ctx: &TypeContext,
    nglev: i32,
    ext: &crate::types::decl::ExtensionConstructor,
    seen: &mut TypeExprRefSet,
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
    ctx: &TypeContext,
    nglev: i32,
    mty: &crate::types::decl::ModuleType,
    seen: &mut TypeExprRefSet,
) {
    use crate::types::decl::ModuleType;
    use crate::types::decl::SignatureItem;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig_items) => {
            for item in sig_items.iter() {
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
    ctx: &TypeContext,
    nglev: i32,
    mty: &crate::types::decl::ModuleType,
) {
    let mut seen = TypeExprRefSet::new();
    lower_nongen_module_type_rec(ctx, nglev, mty, &mut seen);
}

fn force_generalize_sig_type_rec(ctx: &TypeContext, ty: TypeExprRef, seen: &mut TypeExprRefSet) {
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

pub fn force_generalize_sig_type(ctx: &TypeContext, ty: TypeExprRef) {
    ctx.clear_simple_abbrevs();
    let mut seen = TypeExprRefSet::new();
    force_generalize_sig_type_rec(ctx, ty, &mut seen);
}

fn force_generalize_module_type_rec(
    ctx: &TypeContext,
    mty: &crate::types::decl::ModuleType,
    seen: &mut TypeExprRefSet,
) {
    use crate::types::decl::ModuleType;
    use crate::types::decl::SignatureItem;

    match mty {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig_items) => {
            for item in sig_items.iter() {
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

pub fn force_generalize_module_sig_values(ctx: &TypeContext, mty: &crate::types::decl::ModuleType) {
    let mut seen = TypeExprRefSet::new();
    force_generalize_module_type_rec(ctx, mty, &mut seen);
}

pub fn force_generalize_signature_values(
    ctx: &TypeContext,
    sig_items: &[crate::types::decl::SignatureItem],
) {
    use crate::types::decl::SignatureItem;

    let mut seen = TypeExprRefSet::new();
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, vd) => {
                force_generalize_sig_type_rec(ctx, vd.val_type, &mut seen);
            }
            SignatureItem::SigModule(_, md, _) => {
                force_generalize_module_type_rec(ctx, &md.md_type, &mut seen);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(inner) = &mtd.mtd_type {
                    force_generalize_module_type_rec(ctx, inner, &mut seen);
                }
            }
            _ => {}
        }
    }
}

/// Generalize the structure of a type at a given level.
fn generalize_structure_rec(ctx: &TypeContext, var_level: i32, ty: TypeExprRef) {
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
        if matches!(&*desc, TypeDesc::Tvar(..)) && level > var_level {
            Action::LowerVar
        } else if level > ctx.current_level() {
            match &*desc {
                // Match OCaml ctype.ml is_object_type path guard in generalize_structure:
                // object types (names starting with '#') are not promoted here.
                TypeDesc::Tconstr { path, .. } if path.head_name().starts_with('#') => Action::Noop,
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

pub fn generalize_structure(ctx: &TypeContext, var_level: i32, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    generalize_structure_rec(ctx, var_level, ty);
}

fn generalize_expansive_rec(
    ctx: &TypeContext,
    env: &Env,
    var_level: i32,
    visited: &mut TypeExprRefSet,
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
        Constr {
            path: Path,
            args: Vec<TypeExprRef>,
        },
        Package {
            args: Vec<TypeExprRef>,
        },
        Arrow {
            args: Vec<TypeExprRef>,
            ret: TypeExprRef,
        },
        Recurse(Vec<TypeExprRef>),
    }

    let action = {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => Action::Constr {
                path: path.clone(),
                args: args.to_vec(),
            },
            TypeDesc::Tpackage { args, .. } => Action::Package {
                args: args.to_vec(),
            },
            TypeDesc::Tarrow { args, ret } => Action::Arrow {
                args: args.iter().map(|arg| arg.typ).collect(),
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
                variances = vec![Variance::MAY_INV; args.len()];
            }
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
        Action::Arrow { args, ret } => {
            for arg in args {
                generalize_structure(ctx, var_level, arg);
            }
            generalize_expansive_rec(ctx, env, var_level, visited, ret);
        }
        Action::Recurse(children) => {
            for child in children {
                generalize_expansive_rec(ctx, env, var_level, visited, child);
            }
        }
    }
}

pub fn generalize_expansive(ctx: &TypeContext, env: &Env, ty: TypeExprRef) {
    // OCaml: simple_abbrevs := Mnil
    ctx.clear_simple_abbrevs();
    let mut visited = TypeExprRefSet::new();
    generalize_expansive_rec(ctx, env, ctx.nongen_level(), &mut visited, ty);
}

/// Compute actual variance for each type parameter of a type declaration.
/// This matches OCaml's compute_variance_decl in typedecl.ml.
///
/// Without this, unannotated type params default to FULL (all flags including MayWeak),
/// causing generalize_expansive to prevent generalization of covariant params.
/// OCaml infers actual variance from the type body.
pub fn compute_variance_decl(
    ctx: &TypeContext,
    env: &Env,
    decl: &super::decl::TypeDeclaration,
    required: &[(bool, bool, bool)],
) -> Vec<Variance> {
    let params = &decl.type_params;
    let make = |p: bool, n: bool, i: bool| {
        Variance::null()
            .set(VarianceFlag::MayPos, p)
            .set(VarianceFlag::MayNeg, n)
            .set(VarianceFlag::MayWeak, n)
            .set(VarianceFlag::Inj, i)
    };

    // OCaml typedecl.ml:1277-1285 handles abstract/open types without
    // manifests before the general occurrence walk. This keeps abstract
    // covariant parameters non-injective, which is observable in constrained
    // parameter propagation diagnostics.
    if matches!(
        decl.type_kind,
        super::TypeKind::TypeAbstract | super::TypeKind::TypeOpen
    ) && decl.type_manifest.is_none()
    {
        return params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let (c, n, i) = required.get(idx).copied().unwrap_or((true, true, false));
                make(
                    !n,
                    !c,
                    !matches!(decl.type_kind, super::TypeKind::TypeAbstract) || i,
                )
            })
            .collect();
    }

    // OCaml typedecl.ml:1278-1312.
    let mut mn: Vec<(bool, TypeExprRef)> = Vec::new();
    if let Some(manifest) = decl.type_manifest {
        mn.push((false, manifest));
    }
    let for_constr = |args: &super::decl::ConstructorArguments| -> Vec<(bool, TypeExprRef)> {
        match args {
            super::decl::ConstructorArguments::CstrTuple(tys) => {
                tys.iter().map(|ty| (false, *ty)).collect()
            }
            super::decl::ConstructorArguments::CstrRecord(labels) => labels
                .iter()
                .map(|label| {
                    (
                        label.ld_mutable == super::asttypes::MutableFlag::Mutable,
                        label.ld_type,
                    )
                })
                .collect(),
        }
    };
    let is_abstract = matches!(decl.type_kind, super::TypeKind::TypeAbstract);
    match &decl.type_kind {
        super::TypeKind::TypeAbstract | super::TypeKind::TypeOpen => compute_variance_type(
            ctx,
            env,
            params,
            is_abstract,
            decl.type_private,
            required,
            &mn,
        ),
        super::TypeKind::TypeVariant(constructors, _)
            if constructors.iter().all(|cstr| cstr.cd_res.is_none()) =>
        {
            let mut tyl = mn;
            for cstr in constructors {
                tyl.extend(for_constr(&cstr.cd_args));
            }
            compute_variance_type(
                ctx,
                env,
                params,
                is_abstract,
                decl.type_private,
                required,
                &tyl,
            )
        }
        super::TypeKind::TypeVariant(constructors, _) => {
            // `compute_variance_gadt` on the manifest and on each
            // constructor, then the union of the results.
            let mut tll: Vec<(Vec<(bool, TypeExprRef)>, Option<TypeExprRef>)> =
                mn.into_iter().map(|field| (vec![field], None)).collect();
            for cstr in constructors {
                tll.push((for_constr(&cstr.cd_args), cstr.cd_res));
            }
            let mut varl: Option<Vec<Variance>> = None;
            for (tl, ret_type) in &tll {
                let vari =
                    compute_variance_gadt(ctx, env, params, is_abstract, required, tl, *ret_type);
                varl = Some(match varl {
                    None => vari,
                    Some(acc) => acc
                        .iter()
                        .zip(vari.iter())
                        .map(|(a, b)| a.union(b))
                        .collect(),
                });
            }
            varl.unwrap_or_default()
                .into_iter()
                .map(|v| {
                    if v.mem(VarianceFlag::Pos) && v.mem(VarianceFlag::Neg) {
                        Variance::full()
                    } else {
                        v
                    }
                })
                .collect()
        }
        super::TypeKind::TypeRecord(labels, _) => {
            let mut tyl = mn;
            for label in labels {
                tyl.push((
                    label.ld_mutable == super::asttypes::MutableFlag::Mutable,
                    label.ld_type,
                ));
            }
            compute_variance_type(
                ctx,
                env,
                params,
                is_abstract,
                decl.type_private,
                required,
                &tyl,
            )
        }
    }
}

/// OCaml `compute_variance_gadt` (typedecl.ml:1235-1263): a constructor
/// without a return type is computed as if the declaration were private; one
/// with a return type `t<tyl>` uses `tyl` as the parameters.
fn compute_variance_gadt(
    ctx: &TypeContext,
    env: &Env,
    params: &[TypeExprRef],
    is_abstract: bool,
    required: &[(bool, bool, bool)],
    tl: &[(bool, TypeExprRef)],
    ret_type: Option<TypeExprRef>,
) -> Vec<Variance> {
    match ret_type {
        None => compute_variance_type(
            ctx,
            env,
            params,
            is_abstract,
            PrivateFlag::Private,
            required,
            tl,
        ),
        Some(ret_type) => {
            let ret_type = ctx.repr(ret_type);
            let tyl: Vec<TypeExprRef> = match &*ctx.get_desc(ret_type) {
                TypeDesc::Tconstr { args, .. } => args.iter().map(|ty| ctx.repr(*ty)).collect(),
                _ => params.to_vec(),
            };
            compute_variance_type(
                ctx,
                env,
                &tyl,
                is_abstract,
                PrivateFlag::Private,
                required,
                tl,
            )
        }
    }
}

/// The occurrence walk and final per-parameter step of OCaml
/// `compute_variance_type` (typedecl.ml:1121-1224) with `check = false`.
fn compute_variance_type(
    ctx: &TypeContext,
    env: &Env,
    params: &[TypeExprRef],
    is_abstract: bool,
    private: PrivateFlag,
    required: &[(bool, bool, bool)],
    tyl: &[(bool, TypeExprRef)],
) -> Vec<Variance> {
    let make = |p: bool, n: bool, i: bool| {
        Variance::null()
            .set(VarianceFlag::MayPos, p)
            .set(VarianceFlag::MayNeg, n)
            .set(VarianceFlag::MayWeak, n)
            .set(VarianceFlag::Inj, i)
    };
    let mut visited: HashMap<TypeExprRef, Variance> = HashMap::new();
    // OCaml compiler/ml/typedecl.ml:1128-1143 still walks the body of a
    // zero-parameter declaration to compute occurrences. That traversal has
    // observable `Env.find_type` lazy-forcing effects for constructor payloads
    // such as `Pervasives.ref`, so do not return early when `params` is empty.
    let param_reprs: Vec<TypeExprRef> = params.iter().map(|p| ctx.repr(*p)).collect();
    for (is_mutable, ty) in tyl {
        let initial_variance = if *is_mutable {
            Variance::FULL
        } else {
            Variance::covariant()
        };
        compute_variance_rec(ctx, env, &mut visited, initial_variance, *ty, 0);
    }

    let is_type_var =
        |ty: TypeExprRef| matches!(&*ctx.borrow_desc(ctx.repr(ty)), TypeDesc::Tvar(..));
    let is_concrete = !is_abstract;

    // OCaml typedecl.ml:1200-1224: occurrence variance is unioned with the
    // required row only where the declaration kind/private flag makes that
    // row semantically relevant.
    param_reprs
        .iter()
        .enumerate()
        .map(|(idx, p)| {
            let mut variance = visited.get(p).copied().unwrap_or(Variance::NULL);
            let (required_pos, required_neg, required_inj) =
                required.get(idx).copied().unwrap_or((false, false, false));
            let (required_pos, required_neg) = if required_pos || required_neg {
                (required_pos, required_neg)
            } else {
                (true, true)
            };
            let is_tvar = is_type_var(*p);
            let (pos, neg) = if private == PrivateFlag::Private || !is_tvar {
                (required_pos, required_neg)
            } else {
                (false, false)
            };
            let inj = is_concrete || (required_inj && private == PrivateFlag::Private);
            variance = variance.union(&make(pos, neg, inj));
            if is_concrete {
                let (lower_pos, lower_neg, _, _) = variance.get_lower();
                if lower_pos && lower_neg {
                    variance = Variance::full();
                } else if !is_tvar {
                    let required_variance = if required_pos {
                        if required_neg {
                            Variance::full()
                        } else {
                            Variance::covariant()
                        }
                    } else {
                        Variance::covariant().conjugate()
                    };
                    variance = variance.union(&required_variance);
                }
            }
            // typedecl.ml:1222: `set May_weak (mem May_neg v) v`, the
            // upper (may) bound, not the lower `Neg`.
            if is_abstract && private == PrivateFlag::Public {
                variance
            } else {
                let may_neg = variance.mem(VarianceFlag::MayNeg);
                variance.set(VarianceFlag::MayWeak, may_neg)
            }
        })
        .collect()
}

pub(crate) fn compute_variance_map_for_fields(
    ctx: &TypeContext,
    env: &Env,
    fields: &[(bool, TypeExprRef)],
) -> crate::fast_hash::AHashMap<TypeExprRef, Variance> {
    let roots: Vec<_> = fields
        .iter()
        .map(|(is_mutable, ty)| {
            let initial_variance = if *is_mutable {
                Variance::FULL
            } else {
                Variance::covariant()
            };
            (initial_variance, *ty)
        })
        .collect();
    compute_variance_map_with_initial(ctx, env, &roots)
}

pub(crate) fn compute_variance_map_with_initial(
    ctx: &TypeContext,
    env: &Env,
    roots: &[(Variance, TypeExprRef)],
) -> crate::fast_hash::AHashMap<TypeExprRef, Variance> {
    let mut visited: HashMap<TypeExprRef, Variance> = HashMap::new();
    for (initial_variance, ty) in roots {
        compute_variance_rec(ctx, env, &mut visited, *initial_variance, *ty, 0);
    }
    visited
}

pub(crate) fn equal_type_exprs_without_renaming(
    ctx: &TypeContext,
    env: &Env,
    left: TypeExprRef,
    right: TypeExprRef,
) -> bool {
    let mut type_pairs = EqtypeState {
        pairs: HashSet::new(),
        subst: Vec::new(),
        rename: false,
    };
    equal_type_exprs_without_renaming_rec(ctx, env, &mut type_pairs, left, right).is_ok()
}

/// `type_pairs`, `subst` and `rename` of OCaml `eqtype`
/// (compiler/ml/ctype.ml:2996-3165).
pub(crate) struct EqtypeState {
    pairs: HashSet<(TypeExprRef, TypeExprRef)>,
    subst: Vec<(TypeExprRef, TypeExprRef)>,
    rename: bool,
}

/// `Ctype.equal env rename tyl1 tyl2` (ctype.ml:3161-3165).
pub(crate) fn equal(
    ctx: &TypeContext,
    env: &Env,
    rename: bool,
    left: &[TypeExprRef],
    right: &[TypeExprRef],
) -> bool {
    let mut state = EqtypeState {
        pairs: HashSet::new(),
        subst: Vec::new(),
        rename,
    };
    equal_type_expr_lists_without_renaming(ctx, env, &mut state, left, right).is_ok()
}

/// The `Tvar _, Tvar _ when rename` case of `eqtype`: the renaming must stay
/// a bijection.
fn eqtype_rename_vars(
    ctx: &TypeContext,
    state: &mut EqtypeState,
    left: TypeExprRef,
    right: TypeExprRef,
) -> TypeResult<()> {
    // normalize_subst
    if state
        .subst
        .iter()
        .any(|(a, b)| ctx.repr(*a) != *a || ctx.repr(*b) != *b)
    {
        for (a, b) in state.subst.iter_mut() {
            *a = ctx.repr(*a);
            *b = ctx.repr(*b);
        }
    }
    match state.subst.iter().find(|(a, _)| *a == left) {
        Some((_, mapped)) => {
            if *mapped != right {
                return Err(TypeError::Unify(vec![]));
            }
        }
        None => {
            if state.subst.iter().any(|(_, b)| *b == right) {
                return Err(TypeError::Unify(vec![]));
            }
            state.subst.insert(0, (left, right));
        }
    }
    Ok(())
}

fn equal_type_exprs_without_renaming_rec(
    ctx: &TypeContext,
    env: &Env,
    type_pairs: &mut EqtypeState,
    left: TypeExprRef,
    right: TypeExprRef,
) -> TypeResult<()> {
    if left == right {
        return Ok(());
    }

    let left = ctx.repr(left);
    let right = ctx.repr(right);
    if left == right {
        return Ok(());
    }

    if type_pairs.rename
        && matches!(*ctx.get_desc(left), TypeDesc::Tvar(..))
        && matches!(*ctx.get_desc(right), TypeDesc::Tvar(..))
    {
        return eqtype_rename_vars(ctx, type_pairs, left, right);
    }

    {
        let left_desc = ctx.get_desc(left);
        let right_desc = ctx.get_desc(right);
        if let (
            TypeDesc::Tconstr {
                path: left_path,
                args: left_args,
                ..
            },
            TypeDesc::Tconstr {
                path: right_path,
                args: right_args,
                ..
            },
        ) = (&*left_desc, &*right_desc)
        {
            if left_args.is_empty() && right_args.is_empty() && left_path.same(right_path) {
                return Ok(());
            }
        }
    }

    // ctype.ml:3041-3042.
    let left_expanded = ctx.repr(expand_head_rigid(ctx, env, left));
    let right_expanded = ctx.repr(expand_head_rigid(ctx, env, right));
    if left_expanded == right_expanded {
        return Ok(());
    }
    if !type_pairs.pairs.insert((left_expanded, right_expanded)) {
        return Ok(());
    }
    if type_pairs.rename
        && matches!(*ctx.get_desc(left_expanded), TypeDesc::Tvar(..))
        && matches!(*ctx.get_desc(right_expanded), TypeDesc::Tvar(..))
    {
        return eqtype_rename_vars(ctx, type_pairs, left_expanded, right_expanded);
    }

    let left_desc = ctx.get_desc(left_expanded);
    let right_desc = ctx.get_desc(right_expanded);
    match (&*left_desc, &*right_desc) {
        (
            TypeDesc::Tarrow {
                args: left_args,
                ret: left_ret,
            },
            TypeDesc::Tarrow {
                args: right_args,
                ret: right_ret,
            },
        ) if left_args.len() == right_args.len()
            && left_args
                .iter()
                .zip(right_args)
                .all(|(a, b)| a.label().same_label(b.label())) =>
        {
            let left_args = left_args.clone();
            let right_args = right_args.clone();
            let left_ret = *left_ret;
            let right_ret = *right_ret;
            drop(left_desc);
            drop(right_desc);
            for (left, right) in left_args.iter().zip(&right_args) {
                equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left.typ, right.typ)?;
            }
            equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left_ret, right_ret)
        }
        (TypeDesc::Ttuple(left_items), TypeDesc::Ttuple(right_items)) => {
            let left_items = left_items.clone();
            let right_items = right_items.clone();
            drop(left_desc);
            drop(right_desc);
            equal_type_expr_lists_without_renaming(ctx, env, type_pairs, &left_items, &right_items)
        }
        (
            TypeDesc::Tconstr {
                path: left_path,
                args: left_args,
                ..
            },
            TypeDesc::Tconstr {
                path: right_path,
                args: right_args,
                ..
            },
        ) if left_path.same(right_path) => {
            let left_args = left_args.clone();
            let right_args = right_args.clone();
            drop(left_desc);
            drop(right_desc);
            equal_type_expr_lists_without_renaming(ctx, env, type_pairs, &left_args, &right_args)
        }
        (
            TypeDesc::Tpackage {
                path: left_path,
                lids: left_lids,
                args: left_args,
            },
            TypeDesc::Tpackage {
                path: right_path,
                lids: right_lids,
                args: right_args,
            },
        ) => {
            let left_path = left_path.clone();
            let right_path = right_path.clone();
            let left_lids = left_lids.clone();
            let right_lids = right_lids.clone();
            let left_args = left_args.clone();
            let right_args = right_args.clone();
            drop(left_desc);
            drop(right_desc);
            let complete_right = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                Some(env),
                crate::types::decl::ModuleType::MtyIdent(right_path.clone()),
                &left_lids,
                &right_lids,
            );
            let complete_left = package_type_lists_have_ocaml_same_label_completion_side_effect(
                ctx,
                Some(env),
                crate::types::decl::ModuleType::MtyIdent(left_path.clone()),
                &right_lids,
                &left_lids,
            );
            if !(complete_right && complete_left && left_path.same(&right_path)) {
                return Err(TypeError::Unify(vec![]));
            }
            equal_type_expr_lists_without_renaming(ctx, env, type_pairs, &left_args, &right_args)
        }
        (TypeDesc::Tvariant(left_row), TypeDesc::Tvariant(right_row)) => {
            let left_row = left_row.clone();
            let right_row = right_row.clone();
            drop(left_desc);
            drop(right_desc);
            equal_rows_without_renaming(ctx, env, type_pairs, &left_row, &right_row)
        }
        (
            TypeDesc::Tobject {
                fields: left_fields,
                ..
            },
            TypeDesc::Tobject {
                fields: right_fields,
                ..
            },
        ) => {
            let left_fields = *left_fields;
            let right_fields = *right_fields;
            drop(left_desc);
            drop(right_desc);
            equal_object_fields_without_renaming(ctx, env, type_pairs, left_fields, right_fields)
        }
        (TypeDesc::Tfield { .. }, TypeDesc::Tfield { .. }) => {
            drop(left_desc);
            drop(right_desc);
            equal_object_fields_without_renaming(
                ctx,
                env,
                type_pairs,
                left_expanded,
                right_expanded,
            )
        }
        (TypeDesc::Tnil, TypeDesc::Tnil) => Ok(()),
        (
            TypeDesc::Tpoly {
                body: left_body,
                vars,
            },
            TypeDesc::Tpoly {
                body: right_body,
                vars: right_vars,
            },
        ) if vars.is_empty() && right_vars.is_empty() => {
            let left_body = *left_body;
            let right_body = *right_body;
            drop(left_desc);
            drop(right_desc);
            equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left_body, right_body)
        }
        (
            TypeDesc::Tpoly {
                body: left_body,
                vars,
            },
            TypeDesc::Tpoly {
                body: right_body,
                vars: right_vars,
            },
        ) if vars.len() == right_vars.len() => {
            let left_body = *left_body;
            let right_body = *right_body;
            drop(left_desc);
            drop(right_desc);
            equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left_body, right_body)
        }
        (TypeDesc::Tunivar(left_name, ..), TypeDesc::Tunivar(right_name, ..))
            if left_name == right_name =>
        {
            Ok(())
        }
        _ => Err(TypeError::Unify(vec![])),
    }
}

fn equal_type_expr_lists_without_renaming(
    ctx: &TypeContext,
    env: &Env,
    type_pairs: &mut EqtypeState,
    left: &[TypeExprRef],
    right: &[TypeExprRef],
) -> TypeResult<()> {
    if left.len() != right.len() {
        return Err(TypeError::Unify(vec![]));
    }
    for (left_item, right_item) in left.iter().zip(right.iter()) {
        equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, *left_item, *right_item)?;
    }
    Ok(())
}

/// `Ctype.expand_head_rigid` (ctype.ml:3007-3012).
fn expand_head_rigid(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    let old = ctx.set_rigid_variants(true);
    let expanded = expand_head(ctx, env, ty);
    ctx.set_rigid_variants(old);
    expanded
}

fn equal_rows_without_renaming(
    ctx: &TypeContext,
    env: &Env,
    type_pairs: &mut EqtypeState,
    left: &RowDesc,
    right: &RowDesc,
) -> TypeResult<()> {
    // ctype.ml:3147-3150 `eqtype_row`: try expanding the right row's
    // `row_more` first (needed when called from Includecore.type_manifest).
    let right_more = ctx.repr(expand_head_rigid(ctx, env, right.row_more));
    let expanded_right = match &*ctx.get_desc(right_more) {
        TypeDesc::Tvariant(row) => Some(row.clone()),
        _ => None,
    };
    if let Some(expanded_right) = expanded_right {
        return equal_rows_without_renaming(ctx, env, type_pairs, left, &expanded_right);
    }
    let left = row_repr_ref(ctx, left);
    let right = row_repr_ref(ctx, right);
    let left = left.as_ref();
    let right = right.as_ref();
    let (left_only, right_only, pairs) = merge_row_fields(&left.row_fields, &right.row_fields);
    if left.row_closed != right.row_closed
        || (!left.row_closed && (!left_only.is_empty() || !right_only.is_empty()))
        || left_only
            .iter()
            .chain(right_only.iter())
            .any(|(_, field)| !btype::row_field_is_absent(ctx, field))
    {
        return Err(TypeError::Unify(vec![]));
    }

    if !btype::static_row(ctx, left) {
        equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left.row_more, right.row_more)?;
    }
    for (_, left_field, right_field) in pairs {
        equal_row_fields_without_renaming(ctx, env, type_pairs, left_field, right_field)?;
    }
    Ok(())
}

fn equal_row_fields_without_renaming(
    ctx: &TypeContext,
    env: &Env,
    type_pairs: &mut EqtypeState,
    left: &RowField,
    right: &RowField,
) -> TypeResult<()> {
    let left = btype::row_field_repr(ctx, left);
    let right = btype::row_field_repr(ctx, right);
    match (&left, &right) {
        (RowField::Rpresent(None), RowField::Rpresent(None))
        | (RowField::Rabsent, RowField::Rabsent) => Ok(()),
        (RowField::Rpresent(Some(left_ty)), RowField::Rpresent(Some(right_ty))) => {
            equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, *left_ty, *right_ty)
        }
        (
            RowField::Reither {
                constant: left_constant,
                types: left_types,
                ..
            },
            RowField::Reither {
                constant: right_constant,
                types: right_types,
                ..
            },
        ) if left_constant == right_constant && left_types.is_empty() && right_types.is_empty() => {
            Ok(())
        }
        (
            RowField::Reither {
                constant: left_constant,
                types: left_types,
                ..
            },
            RowField::Reither {
                constant: right_constant,
                types: right_types,
                ..
            },
        ) if left_constant == right_constant
            && !left_types.is_empty()
            && !right_types.is_empty() =>
        {
            equal_type_exprs_without_renaming_rec(
                ctx,
                env,
                type_pairs,
                left_types[0],
                right_types[0],
            )?;
            if left_types.len() == right_types.len() {
                equal_type_expr_lists_without_renaming(
                    ctx,
                    env,
                    type_pairs,
                    &left_types[1..],
                    &right_types[1..],
                )
            } else {
                for right_ty in right_types.iter().skip(1) {
                    equal_type_exprs_without_renaming_rec(
                        ctx,
                        env,
                        type_pairs,
                        left_types[0],
                        *right_ty,
                    )?;
                }
                for left_ty in left_types.iter().skip(1) {
                    equal_type_exprs_without_renaming_rec(
                        ctx,
                        env,
                        type_pairs,
                        *left_ty,
                        right_types[0],
                    )?;
                }
                Ok(())
            }
        }
        _ => Err(TypeError::Unify(vec![])),
    }
}

fn equal_object_fields_without_renaming(
    ctx: &TypeContext,
    env: &Env,
    type_pairs: &mut EqtypeState,
    left: TypeExprRef,
    right: TypeExprRef,
) -> TypeResult<()> {
    let (left_fields, left_rest) = flatten_fields(ctx, left);
    let (right_fields, right_rest) = flatten_fields(ctx, right);
    let same_row = left_rest == right_rest
        || type_pairs.pairs.contains(&(left_rest, right_rest))
        || (type_pairs.rename && type_pairs.subst.contains(&(left_rest, right_rest)));
    if !same_row {
        // ctype.ml:3114.
        let right_rest_expanded = ctx.repr(expand_head_rigid(ctx, env, right_rest));
        if let TypeDesc::Tobject { fields, .. } = &*ctx.get_desc(right_rest_expanded) {
            return equal_object_fields_without_renaming(ctx, env, type_pairs, left, *fields);
        }
    }

    let (pairs, missing_left, missing_right) = associate_fields(left_fields, right_fields);
    equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, left_rest, right_rest)?;
    if !missing_left.is_empty() || !missing_right.is_empty() {
        return Err(TypeError::Unify(vec![]));
    }
    for (f1, f2) in pairs {
        // ctype.ml eqtype_fields: the field capabilities must agree.
        if ctx.mutability_repr(f1.mutability) != ctx.mutability_repr(f2.mutability) {
            return Err(TypeError::Unify(vec![]));
        }
        equal_type_exprs_without_renaming_rec(ctx, env, type_pairs, f1.typ, f2.typ)?;
    }
    Ok(())
}

fn compute_variance_rec(
    ctx: &TypeContext,
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
        TypeDesc::Tarrow { args, ret } => {
            let v = vari.conjugate();
            let v1 = if v.mem(VarianceFlag::MayPos) || v.mem(VarianceFlag::MayNeg) {
                v.set(VarianceFlag::MayWeak, true)
            } else {
                v
            };
            let args = args.clone();
            let ret = *ret;
            drop(desc);
            for arg in args {
                compute_variance_rec(ctx, env, visited, v1, arg.typ, depth + 1);
            }
            compute_variance_rec(ctx, env, visited, vari, ret, depth + 1);
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
                // OCaml compiler/ml/typedecl.ml:1064-1066 asks
                // `Env.find_type` for constructor variance, which goes through
                // compiler/ml/env.ml:800-813 path lookup and can force the
                // same lazy persistent signature components that later stamps
                // depend on. Use Rust's path-aware helper instead of the
                // name fallback-only env lookup.
                let variances = lookup_type_decl_for_path(ctx, env, &path)
                    .map(|d| d.type_variance.clone())
                    .unwrap_or_else(|| vec![Variance::MAY_INV; args.len()]);
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
            let args: Vec<TypeExprRef> = args.to_vec();
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
        TypeDesc::Tfield {
            mutability,
            typ,
            rest,
            ..
        } => {
            let mutability = *mutability;
            let typ = *typ;
            let rest = *rest;
            drop(desc);
            // typedecl.ml compute_variance: a settable field can be both read
            // and written, so its payload is an invariant occurrence, like a
            // mutable record label.
            let typ_vari = match ctx.mutability_repr(mutability) {
                MutableFlag::Mutable => Variance::FULL,
                MutableFlag::Immutable => vari,
            };
            compute_variance_rec(ctx, env, visited, typ_vari, typ, depth + 1);
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
pub fn lower_args(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> (Vec<Path>, Vec<Path>) {
    let mut seen = Vec::new();
    let mut current = ty;
    let mut pending_type_lookup_paths = Vec::new();
    let mut pending_type_expansion_paths = Vec::new();
    loop {
        let expanded = expand_head(ctx, env, current);
        if seen.contains(&expanded) {
            return (pending_type_lookup_paths, pending_type_expansion_paths);
        }
        let arrow = {
            let desc = ctx.get_desc(expanded);
            if let TypeDesc::Tarrow { args, ret } = &*desc {
                Some((args.iter().map(|arg| arg.typ).collect::<Vec<_>>(), *ret))
            } else {
                None
            }
        };
        let Some((arg_types, ret_ty)) = arrow else {
            return (pending_type_lookup_paths, pending_type_expansion_paths);
        };

        // OCaml compiler/ml/typecore.ml:2341 calls
        // `unify_var env (newvar ()) arg.typ`; keep the Rust structure on the
        // same ctype.ml:2820-2837 path instead of inlining a second copy here.
        // Its ctype.ml:666-673 `get_level` path reaches Env.find_type, so
        // return those dotted lookup points for typecore to force through the
        // persistent component environment.
        for arg_ty in arg_types {
            let mut state = UnifyState::new();
            state.set_env(env);
            let previous_capture = state.begin_type_lookup_capture();
            if unify_var(ctx, &mut state, ctx.new_var(None), arg_ty).is_err() {
                unreachable!("lower_args failed unify_var")
            }
            let (lookup_paths, expansion_paths) =
                state.finish_type_lookup_capture(previous_capture);
            pending_type_lookup_paths.extend(lookup_paths);
            pending_type_expansion_paths.extend(expansion_paths);
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
pub fn instance(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = CopyCache::new(ctx);
    copy_type_cached(ctx, ty, &mut cache)
}

/// Create an instance using OCaml `Ctype.instance ~partial`.
///
/// With `keep = false`, non-generic subtrees without free universal variables
/// are forgotten as fresh variables at the current level instead of being
/// copied structurally. This is used by polymorphic variant pattern typing.
pub fn instance_partial(ctx: &TypeContext, ty: TypeExprRef, keep: bool) -> TypeExprRef {
    let mut cache = CopyCache::new_partial(ctx, ty, keep);
    copy_type_cached(ctx, ty, &mut cache)
}

/// Like instance_for_expansion, but also caches the result in simple_expansion_cache
/// Instantiate a list of types, sharing variable substitutions across all of them.
/// Matches OCaml's Ctype.instance_list.
pub fn instance_list(ctx: &TypeContext, types: &[TypeExprRef]) -> Vec<TypeExprRef> {
    let mut cache = CopyCache::new(ctx);
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
    ctx: &TypeContext,
    params: &[TypeExprRef],
    body: TypeExprRef,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new(ctx);
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
    ctx: &TypeContext,
    free_univars: &HashSet<TypeExprRef>,
    bound: &[TypeExprRef],
) -> bool {
    bound.iter().any(|ty| free_univars.contains(&ctx.repr(*ty)))
}

fn build_inverse_type_graph(
    ctx: &TypeContext,
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
    ctx: &TypeContext,
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
    ctx: &TypeContext,
    ty: TypeExprRef,
) -> HashMap<TypeExprRef, HashSet<TypeExprRef>> {
    let mut inverted: HashMap<TypeExprRef, Vec<TypeExprRef>> = HashMap::new();
    build_inverse_type_graph(ctx, None, ty, &mut inverted);

    let mut node_univars: HashMap<TypeExprRef, HashSet<TypeExprRef>> = HashMap::new();
    let nodes: Vec<TypeExprRef> = inverted.keys().copied().collect();
    for node in nodes {
        let node = ctx.repr(node);
        let desc = ctx.get_desc(node);
        let is_univar = matches!(&*desc, TypeDesc::Tunivar(..));
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
    ctx: &TypeContext,
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
                        link: if keep {
                            link
                        } else {
                            ctx.alloc_row_field(None)
                        },
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
    ctx: &TypeContext,
    ty: TypeExprRef,
    fixed: bool,
    free_univars: &HashMap<TypeExprRef, HashSet<TypeExprRef>>,
    bound: &[TypeExprRef],
    visited: &[CopySepVisitedEntry],
    delayed_copy: &mut Vec<(TypeExprRef, TypeExprRef)>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);
    let desc = ctx.get_desc(ty).into_desc();

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

    let ty_is_tunivar = matches!(desc, TypeDesc::Tunivar(..));
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
        // btype.ml:510: the static `Tvar None`.
        TypeDesc::Tvar(..) => TypeDesc::Tvar(None, super::type_expr::VarDescBlock::Static),
        // compiler/ml/btype.ml:422-423 maps every argument type and then ret.
        TypeDesc::Tarrow { args, ret } => TypeDesc::Tarrow {
            args: args
                .into_iter()
                .map(|mut arg| {
                    arg.typ = copy_sep_inner(
                        ctx,
                        arg.typ,
                        fixed,
                        free_univars,
                        bound,
                        &visited_for_children,
                        delayed_copy,
                    );
                    arg
                })
                .collect(),
            ret: copy_sep_inner(
                ctx,
                ret,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
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
        // `Btype.copy_type_desc` keeps the path.
        TypeDesc::Tconstr {
            path,
            args,
            path_block,
            ..
        } => TypeDesc::Tconstr {
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
            path_block: path_block.copied_from(ty),
        },
        TypeDesc::Tobject { fields } => TypeDesc::Tobject {
            fields: copy_sep_inner(
                ctx,
                fields,
                fixed,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            ),
        },
        TypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => {
            // btype.ml copy_type_desc: classify the row before copying either
            // child.
            let mutability = ctx.copy_field_mutability(mutability, rest, false, &|_| None);
            TypeDesc::Tfield {
                name,
                mutability,
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
            }
        }
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
        TypeDesc::Tunivar(name, block) => TypeDesc::Tunivar(name, block.copied_from(ty)),
        TypeDesc::Tvariant(row0) => {
            let row = row_repr_ref(ctx, &row0);
            let row = row.as_ref();
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
            TypeDesc::Tvariant(Box::new(copy_sep_row(
                ctx,
                row,
                fixed_prime,
                keep,
                more_copy,
                free_univars,
                bound,
                &visited_for_children,
                delayed_copy,
            )))
        }
        TypeDesc::Tpoly { body, vars } => {
            let vars: Vec<_> = vars.into_iter().map(|v| ctx.repr(v)).collect();
            let fresh_vars: Vec<_> = vars
                .iter()
                .map(|v| {
                    // ctype.ml:1047 `newty t.desc` shares the descriptor.
                    let copied = ctx.get_desc(*v).into_desc().shared_from(*v);
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
                vars: fresh_vars.into(),
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
    ctx: &TypeContext,
    keep_names: bool,
    fixed: bool,
    univars: &[TypeExprRef],
    sch: TypeExprRef,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    ctx.with_copy_session(|| instance_poly_in_session(ctx, keep_names, fixed, univars, sch))
}

fn instance_poly_in_session(
    ctx: &TypeContext,
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
                TypeDesc::Tunivar(name, ..) => {
                    if keep_names {
                        ctx.new_type(TypeDesc::Tvar(
                            name.clone(),
                            crate::types::type_expr::VarDescBlock::OWN,
                        ))
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
    let mut delayed_cache = CopyCache::joined(ctx);
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
    ctx: &TypeContext,
    cstr: &super::ConstructorDescription,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new(ctx);
    let ty_res = copy_type_cached(ctx, cstr.cstr_res, &mut cache);
    let ty_args: Vec<TypeExprRef> = cstr
        .cstr_args
        .iter()
        .map(|&arg| copy_type_cached(ctx, arg, &mut cache))
        .collect();
    (ty_args, ty_res)
}

/// Instantiate a constructor description in a pattern context, processing GADT
/// existential type variables. For each existential `'a`, creates an abstract
/// type `$a` (numbered when the name is taken) and links the copied
/// existential to it.
/// Matches OCaml's Ctype.instance_constructor ~in_pattern:(env, newtype_lev).
pub fn instance_constructor_in_pattern(
    ctx: &TypeContext,
    env: &mut super::env::Env,
    newtype_lev: i32,
    cstr: &super::ConstructorDescription,
) -> (Vec<TypeExprRef>, TypeExprRef) {
    let mut cache = CopyCache::new(ctx);

    // Process existential type variables before copying cstr_res/cstr_args.
    // This ensures the copy cache maps existential Tvars to abstract Tconstr nodes.
    for &existential in &cstr.cstr_existentials {
        let existential_repr = ctx.repr(existential);
        let name = {
            let desc = ctx.get_desc(existential_repr);
            match &*desc {
                // `$a` for the variable `'a`, numbered when the name is
                // taken, so that distinct existentials print differently
                // (ctype.ml:953-958).
                super::type_expr::TypeDesc::Tvar(Some(name), ..) => format!("${name}"),
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
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: super::decl::TypeRepresentation::Boxed,
            type_shape: crate::types::ValueShape::Unstated,
            type_inlined_types: vec![],
            type_path: None,
        };

        // OCaml compiler/ml/ctype.ml:1111-1123 creates existential abstract
        // type names with `Ident.create`, so they consume the same stamp
        // stream as typedtree binders.
        let id = ctx.create_ident(&ctx.next_reified_abstract_name(&name));
        ctx.record_existential_constructor(id.binding_time(), &cstr.cstr_name);
        let path = super::path::Path::pident(id);
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
    ctx: &TypeContext,
    label_ty: TypeExprRef,
    type_params: &[TypeExprRef],
) -> TypeExprRef {
    let label_ty = ctx.repr(label_ty);
    let desc = ctx.get_desc(label_ty);
    match &*desc {
        TypeDesc::Tvar(Some(name), ..) | TypeDesc::Tunivar(Some(name), ..) => {
            for &param in type_params {
                let param = ctx.repr(param);
                let param_desc = ctx.get_desc(param);
                match &*param_desc {
                    TypeDesc::Tvar(Some(param_name), ..)
                    | TypeDesc::Tunivar(Some(param_name), ..)
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
                TypeDesc::Tvar(Some(name), ..) | TypeDesc::Tunivar(Some(name), ..) => {
                    Some(name.clone())
                }
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
                    TypeDesc::Tvar(Some(param_name), ..)
                    | TypeDesc::Tunivar(Some(param_name), ..)
                        if *param_name == body_name =>
                    {
                        if param == body {
                            return label_ty;
                        }
                        let remapped = ctx.new_poly(param, vars.to_vec());
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
    ctx: &TypeContext,
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
    ctx: &TypeContext,
    fixed: bool,
    lbl: &super::LabelDescription,
) -> (Vec<TypeExprRef>, TypeExprRef, TypeExprRef) {
    // Match OCaml ctype.ml instance_label:
    //   let ty_res = copy lbl.lbl_res
    //   let vars, ty_arg = match repr lbl.lbl_arg with
    //     | Tpoly (ty, tl) -> instance_poly fixed tl ty
    //     | _ -> [], copy lbl.lbl_arg
    // copy lbl_res / copy lbl_arg must share the same copy window.
    let mut cache = CopyCache::new(ctx);
    let ty_res = copy_type_cached(ctx, lbl.lbl_res, &mut cache);
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
                (poly_vars, ty_arg)
            }
            _ => {
                drop(desc);
                let copied = copy_type_cached(ctx, lbl.lbl_arg, &mut cache);
                (vec![], copied)
            }
        }
    };
    (poly_vars, ty_arg, ty_res)
}

/// OCaml's check_univars: after typing a polymorphic field value,
/// convert any still-unresolved fresh Tvars back to Tunivar.
/// This preserves the universal quantification in the typed tree.
pub fn check_univars(ctx: &TypeContext, vars: &[TypeExprRef]) {
    for &v in vars {
        let v = ctx.repr(v);
        let desc = ctx.get_desc(v);
        if let super::TypeDesc::Tvar(name, ..) = &*desc {
            let name = name.clone();
            drop(desc);
            ctx.set_desc(
                v,
                super::TypeDesc::Tunivar(name, crate::types::type_expr::VarDescBlock::OWN),
            );
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
    ctx: &TypeContext,
    ty: TypeExprRef,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    if let Some(&cached) = cache.get(&ty) {
        return cached;
    }

    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvar(_name, ..) => {
            // OCaml's copy_type creates anonymous type variables (None name)
            // for fresh copies, matching the Tvar None in the sexp output
            let fresh = ctx.new_var(None);
            cache.insert(ty, fresh);
            fresh
        }
        TypeDesc::Tarrow { args, ret } => {
            // Create placeholder first to handle cycles
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let args = args.clone();
            let ret = *ret;
            drop(desc);
            let new_args = args
                .into_iter()
                .map(|mut arg| {
                    arg.typ = copy_type_deep(ctx, arg.typ, cache);
                    arg
                })
                .collect();
            let new_ret = copy_type_deep(ctx, ret, cache);
            let new_ty = ctx.new_type(TypeDesc::Tarrow {
                args: new_args,
                ret: new_ret,
            });
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
            let row = row_repr_ref(ctx, row);
            let row = row.as_ref();
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
                row_fields: new_row_fields.into(),
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
        TypeDesc::Tobject { fields } => {
            let fields = *fields;
            drop(desc);
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let new_fields = copy_type_deep(ctx, fields, cache);
            let result = ctx.new_type(TypeDesc::Tobject { fields: new_fields });
            ctx.set_desc(placeholder, TypeDesc::Tlink(result));
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => {
            let (name, mutability, typ, rest) = (name.clone(), *mutability, *typ, *rest);
            drop(desc);
            let placeholder = ctx.new_var(None);
            cache.insert(ty, placeholder);
            let mutability = {
                let nodes = &*cache;
                ctx.copy_field_mutability(mutability, rest, false, &|t| nodes.get(&t).copied())
            };
            let new_typ = copy_type_deep(ctx, typ, cache);
            let new_rest = copy_type_deep(ctx, rest, cache);
            let result = ctx.new_type(TypeDesc::Tfield {
                name,
                mutability,
                typ: new_typ,
                rest: new_rest,
            });
            ctx.set_desc(placeholder, TypeDesc::Tlink(result));
            cache.insert(ty, result);
            result
        }
        TypeDesc::Tsubst(target) => copy_type_deep(ctx, *target, cache),
        TypeDesc::Tlink(target) => copy_type_deep(ctx, *target, cache),
        TypeDesc::Tnil | TypeDesc::Tunivar(..) => ty, // Return as-is
        TypeDesc::Tpackage { path, lids, args } => {
            let new_args: Vec<_> = args
                .iter()
                .map(|t| copy_type_deep(ctx, *t, cache))
                .collect();
            let result = ctx.new_type(TypeDesc::Tpackage {
                path: path.clone(),
                lids: lids.clone(),
                args: new_args.into(),
            });
            cache.insert(ty, result);
            result
        }
    }
}

/// Cache for copy_type_cached: tracks node identity to preserve sharing.
///
/// A cache made with `new`/`new_partial` is one graph-copy operation and owns
/// a copy session (btype.ml `with_copy_session`), ended when the cache is
/// dropped; `joined` caches take part in the enclosing session.
pub(crate) struct CopyCache<'c> {
    ctx: &'c TypeContext,
    owns_session: bool,

    /// Node identity cache: maps original TypeExprRef → copied TypeExprRef.
    /// Ensures that if the same node is visited twice, we reuse the copy.
    nodes: super::type_expr::TypeExprRefMap<TypeExprRef>,

    /// Scoped marker table for OCaml Ctype.copy variant recursion handling.
    /// Mirrors `more.desc <- Tsubst(Ttuple [more'; t])` without mutating
    /// shared type descriptors in-place.
    row_more_markers: RowMoreMarkers,

    /// Optional OCaml `Ctype.copy ~partial` mode.
    partial: Option<CopyPartial>,
}

/// The variant rows currently being copied (at most a few at once), with
/// their `Tsubst` markers. A small vector: creating a `CopyCache` for every
/// `instance` must not build a hash table.
#[derive(Default)]
struct RowMoreMarkers(Vec<(TypeExprRef, CopyRowMoreMarker)>);

impl RowMoreMarkers {
    #[inline]
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    fn get(&self, key: &TypeExprRef) -> Option<&CopyRowMoreMarker> {
        self.0.iter().rev().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    fn insert(&mut self, key: TypeExprRef, value: CopyRowMoreMarker) -> Option<CopyRowMoreMarker> {
        if let Some(slot) = self.0.iter_mut().find(|(k, _)| *k == key) {
            return Some(std::mem::replace(&mut slot.1, value));
        }
        self.0.push((key, value));
        None
    }
}

struct CopyPartial {
    keep: bool,
    free_univars: HashMap<TypeExprRef, HashSet<TypeExprRef>>,
}

impl Drop for CopyCache<'_> {
    fn drop(&mut self) {
        if self.owns_session {
            self.ctx.end_copy_session();
        }
    }
}

impl<'c> CopyCache<'c> {
    pub(crate) fn new(ctx: &'c TypeContext) -> Self {
        ctx.begin_copy_session();
        CopyCache {
            ctx,
            owns_session: true,
            nodes: super::type_expr::TypeExprRefMap::new(),
            row_more_markers: RowMoreMarkers::default(),
            partial: None,
        }
    }

    /// A cache taking part in the enclosing copy session.
    pub(crate) fn joined(ctx: &'c TypeContext) -> Self {
        CopyCache {
            ctx,
            owns_session: false,
            nodes: super::type_expr::TypeExprRefMap::new(),
            row_more_markers: RowMoreMarkers::default(),
            partial: None,
        }
    }

    fn new_partial(ctx: &'c TypeContext, ty: TypeExprRef, keep: bool) -> Self {
        ctx.begin_copy_session();
        CopyCache {
            ctx,
            owns_session: true,
            nodes: super::type_expr::TypeExprRefMap::new(),
            row_more_markers: RowMoreMarkers::default(),
            partial: Some(CopyPartial {
                keep,
                free_univars: compute_univars_per_node(ctx, ty),
            }),
        }
    }
}

#[derive(Clone, Copy)]
struct CopyRowMoreMarker {
    tuple: TypeExprRef,
    variant: TypeExprRef,
}

/// Copy a type, creating fresh type variables for generic ones.
pub fn copy_type(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let mut cache = CopyCache::new(ctx);
    copy_type_cached(ctx, ty, &mut cache)
}

/// Full structural copy of a type, copying ALL nodes regardless of level.
/// Matches OCaml's `Subst.type_expr Subst.identity` which creates fresh
/// nodes for everything except Tvars/Tunivar.
/// Used in type_newtype to ensure replace_newtype_path doesn't corrupt
/// shared pattern types.
pub fn subst_identity_copy(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    subst_identity_copy_with_mode(ctx, ty, SubstCopyMode::IDENTITY)
}

pub fn subst_identity_copy_many(ctx: &TypeContext, types: &[TypeExprRef]) -> Vec<TypeExprRef> {
    let mut seen = HashMap::new();
    // OCaml compiler/ml/subst.ml:273-301 calls `typexp` for every type slot
    // in a declaration before the single `cleanup_types` call, so temporary
    // Tsubst markers preserve sharing between params, kind fields, and manifest.
    let mut row_more_markers = HashMap::new();
    ctx.with_copy_session(|| {
        types
            .iter()
            .map(|ty| {
                subst_identity_copy_rec(
                    ctx,
                    *ty,
                    SubstCopyMode::IDENTITY,
                    &mut seen,
                    &mut row_more_markers,
                )
            })
            .collect()
    })
}

pub fn subst_identity_copy_with_partial(
    ctx: &TypeContext,
    ty: TypeExprRef,
    reopen_closed_variant_rows: bool,
) -> TypeExprRef {
    subst_identity_copy_with_mode(
        ctx,
        ty,
        SubstCopyMode {
            reopen_closed_variant_rows,
            for_saving: false,
        },
    )
}

/// OCaml `Subst.type_expr (Subst.for_saving Subst.identity) ty`, which
/// `type_cases` and `type_function` use to "copy variables too"
/// (typecore.ml:4877-4880, typecore.ml:4171-4174): unlike
/// [`subst_identity_copy`], type variables and row variables get fresh
/// generic copies (subst.ml:135-143, 196-206).
pub fn subst_for_saving_copy(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    subst_identity_copy_with_mode(
        ctx,
        ty,
        SubstCopyMode {
            reopen_closed_variant_rows: false,
            for_saving: true,
        },
    )
}

/// OCaml `Subst.norm` (subst.ml:121-126) on the descriptor of variable
/// `node`: `Tvar None` and `Tunivar None` become the static constants every
/// such copy shares; a named variable's copy keeps `node`'s own descriptor.
fn subst_norm(desc: &TypeDesc, node: TypeExprRef) -> TypeDesc {
    use super::type_expr::VarDescBlock;
    match desc {
        TypeDesc::Tvar(None, _) => TypeDesc::Tvar(None, VarDescBlock::Static),
        TypeDesc::Tunivar(None, _) => TypeDesc::Tunivar(None, VarDescBlock::Static),
        TypeDesc::Tvar(name, block) => TypeDesc::Tvar(name.clone(), block.copied_from(node)),
        TypeDesc::Tunivar(name, block) => TypeDesc::Tunivar(name.clone(), block.copied_from(node)),
        _ => unreachable!("Subst.norm on a non-variable"),
    }
}

/// How [`subst_identity_copy_rec`] copies: `for_saving` is `Subst.for_saving`;
/// `reopen_closed_variant_rows` is the `instance ~partial:false` row reopening.
#[derive(Clone, Copy)]
struct SubstCopyMode {
    reopen_closed_variant_rows: bool,
    for_saving: bool,
}

impl SubstCopyMode {
    const IDENTITY: Self = Self {
        reopen_closed_variant_rows: false,
        for_saving: false,
    };
}

fn subst_identity_copy_with_mode(
    ctx: &TypeContext,
    ty: TypeExprRef,
    mode: SubstCopyMode,
) -> TypeExprRef {
    let mut seen = HashMap::new();
    // OCaml Subst.typexp uses a temporary `row_more.desc <- Tsubst(Ttuple [...])`
    // marker window to preserve recursive row sharing while copying.
    // Keep the same lifetime semantics in a scoped side table.
    let mut row_more_markers = HashMap::new();
    ctx.with_copy_session(|| {
        subst_identity_copy_rec(ctx, ty, mode, &mut seen, &mut row_more_markers)
    })
}

#[derive(Clone, Copy)]
struct SubstRowMoreMarker {
    tuple: TypeExprRef,
    variant: TypeExprRef,
}

fn subst_identity_copy_rec(
    ctx: &TypeContext,
    ty: TypeExprRef,
    mode: SubstCopyMode,
    seen: &mut HashMap<TypeExprRef, TypeExprRef>,
    row_more_markers: &mut HashMap<TypeExprRef, SubstRowMoreMarker>,
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

    let desc = ctx.borrow_desc(ty);
    match &*desc {
        // OCaml Subst.typexp returns identity for Tvar/Tunivar
        // (when not for_saving and id >= 0)
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) if mode.for_saving => {
            // subst.ml:135-142: `newpersty (norm desc)`, then `Tsubst`.
            let copied = ctx.new_generic_type(subst_norm(&desc, ty));
            drop(desc);
            seen.insert(ty, copied);
            copied
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {
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

            let desc = ctx.borrow_desc(ty);
            let new_desc = match &*desc {
                TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => unreachable!(),
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                    let target = *target;
                    drop(desc);
                    return subst_identity_copy_rec(ctx, target, mode, seen, row_more_markers);
                }
                TypeDesc::Tarrow { args, ret } => {
                    let args = args.clone();
                    let ret = *ret;
                    drop(desc);
                    let args = args
                        .into_iter()
                        .map(|mut arg| {
                            arg.typ =
                                subst_identity_copy_rec(ctx, arg.typ, mode, seen, row_more_markers);
                            arg
                        })
                        .collect();
                    let ret = subst_identity_copy_rec(ctx, ret, mode, seen, row_more_markers);
                    TypeDesc::Tarrow { args, ret }
                }
                TypeDesc::Ttuple(types) => {
                    let types = types.clone();
                    drop(desc);
                    let types_copy: Vec<_> = types
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, mode, seen, row_more_markers))
                        .collect();
                    TypeDesc::Ttuple(types_copy.into())
                }
                TypeDesc::Tconstr {
                    path,
                    args,
                    path_block,
                    ..
                } => {
                    // `Subst.type_path` keeps a `Pident` and rebuilds a
                    // `Pdot` (subst.ml:87-94).
                    let subst_path_block = match path {
                        Path::Pident(_) => path_block.copied_from(ty),
                        _ => crate::types::type_expr::PathBlock::OWN,
                    };
                    let path = path.clone();
                    let args = args.clone();
                    drop(desc);
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, mode, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tconstr {
                        path,
                        args: args_copy.into(),
                        abbrev: ctx.alloc_abbrev_nil(),
                        path_block: subst_path_block,
                    }
                }
                TypeDesc::Tobject { fields } => {
                    let fields = *fields;
                    drop(desc);
                    TypeDesc::Tobject {
                        fields: subst_identity_copy_rec(ctx, fields, mode, seen, row_more_markers),
                    }
                }
                TypeDesc::Tfield {
                    name,
                    mutability,
                    typ,
                    rest,
                } => {
                    let name = name.clone();
                    let mutability = *mutability;
                    let typ = *typ;
                    let rest = *rest;
                    drop(desc);
                    // btype.ml copy_type_desc (subst.ml typexp_rec, not
                    // for_saving): classify the row before copying either
                    // child.
                    let mutability = {
                        let seen = &*seen;
                        ctx.copy_field_mutability(mutability, rest, false, &|t| {
                            seen.get(&t).copied()
                        })
                    };
                    let rest_copy =
                        subst_identity_copy_rec(ctx, rest, mode, seen, row_more_markers);
                    let typ_copy = subst_identity_copy_rec(ctx, typ, mode, seen, row_more_markers);
                    TypeDesc::Tfield {
                        name,
                        mutability,
                        typ: typ_copy,
                        rest: rest_copy,
                    }
                }
                TypeDesc::Tpoly { body, vars } => {
                    let body = *body;
                    let vars = vars.clone();
                    drop(desc);
                    let body_copy =
                        subst_identity_copy_rec(ctx, body, mode, seen, row_more_markers);
                    let vars_copy: Vec<_> = vars
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, mode, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tpoly {
                        body: body_copy,
                        vars: vars_copy.into(),
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
                            let more_desc = ctx.get_desc(more).into_desc();
                            let more_is_constr = matches!(&more_desc, TypeDesc::Tconstr { .. });
                            let dup = mode.for_saving
                                || ctx.get_level(more) == GENERIC_LEVEL
                                || super::btype::static_row(ctx, &row)
                                || more_is_constr;
                            let more_copy = match more_desc {
                                TypeDesc::Tsubst(target) => target,
                                TypeDesc::Tconstr { .. } | TypeDesc::Tnil => {
                                    subst_identity_copy_rec(ctx, more, mode, seen, row_more_markers)
                                }
                                // subst.ml:203-206: `newpersty (norm more.desc)`
                                // when saving.
                                ref more_desc @ (TypeDesc::Tvar(..) | TypeDesc::Tunivar(..))
                                    if mode.for_saving =>
                                {
                                    ctx.new_generic_type(subst_norm(more_desc, more))
                                }
                                TypeDesc::Tunivar(..) => more,
                                TypeDesc::Tvar(name, block) => {
                                    if dup {
                                        // subst.ml:198-206 `newgenty more.desc`.
                                        ctx.new_generic_type(TypeDesc::Tvar(
                                            name,
                                            block.copied_from(more),
                                        ))
                                    } else {
                                        more
                                    }
                                }
                                TypeDesc::Tlink(target) => subst_identity_copy_rec(
                                    ctx,
                                    target,
                                    mode,
                                    seen,
                                    row_more_markers,
                                ),
                                _ => panic!("unexpected row_more in subst_identity_copy_rec"),
                            };
                            (dup, more_copy)
                        };
                        if mode.reopen_closed_variant_rows {
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
                        let marker_tuple = ctx.new_generic_type(TypeDesc::Ttuple(
                            vec![more_copy, placeholder].into(),
                        ));
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
                                        crate::types::type_expr::RowField::Rpresent(Some(
                                            subst_identity_copy_rec(
                                                ctx,
                                                ty,
                                                mode,
                                                seen,
                                                row_more_markers,
                                            ),
                                        ))
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
                                                    mode,
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
                                            mode,
                                            seen,
                                            row_more_markers,
                                        )
                                    })
                                    .collect(),
                            )
                        });

                        TypeDesc::Tvariant(Box::new(RowDesc {
                            row_fields: fields_copy.into(),
                            row_more: more_copy,
                            row_closed: row.row_closed,
                            row_fixed: row.row_fixed,
                            row_name: name_copy,
                        }))
                    }
                }
                TypeDesc::Tpackage { path, lids, args } => {
                    let path = path.clone();
                    let lids = lids.clone();
                    let args = args.clone();
                    drop(desc);
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| subst_identity_copy_rec(ctx, *t, mode, seen, row_more_markers))
                        .collect();
                    TypeDesc::Tpackage {
                        path,
                        lids,
                        args: args_copy.into(),
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
pub(crate) fn copy_type_cached(
    ctx: &TypeContext,
    ty: TypeExprRef,
    cache: &mut CopyCache<'_>,
) -> TypeExprRef {
    let ty = ctx.repr(ty);

    // OCaml Ctype.copy marker precedence:
    // if `more.desc` is temporarily `Tsubst(Ttuple [more'; t])`,
    // copying `more` itself must yield the tuple target.
    // (The marker table is almost always empty; skip hashing then.)
    if !cache.row_more_markers.is_empty()
        && let Some(marker) = cache.row_more_markers.get(&ty).copied()
    {
        return marker.tuple;
    }

    // Preserve sharing for already-copied nodes (OCaml Tsubst behavior).
    if let Some(&cached) = cache.nodes.get(ty) {
        return cached;
    }

    // Match OCaml ctype.ml copy marker handling for recursive variants:
    // if row_more currently carries a temporary marker, reuse the
    // already-registered variant copy directly.
    if !cache.row_more_markers.is_empty() && ctx.get_level(ty) == GENERIC_LEVEL {
        if let TypeDesc::Tvariant(row0) = &*ctx.borrow_desc(ty) {
            let row = row_repr_ref(ctx, row0);
            let row = row.as_ref();
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
        NewUnivar(Option<String>, super::type_expr::VarDescBlock),
        Arrow {
            args: super::type_expr::TypeArgList,
            ret: TypeExprRef,
        },
        Tuple(super::type_expr::TypeRefList),
        Constr {
            path: Path,
            args: super::type_expr::TypeRefList,
            path_block: super::type_expr::PathBlock,
        },
        Object {
            fields: TypeExprRef,
        },
        Field {
            name: String,
            mutability: MutabilityRef,
            typ: TypeExprRef,
            rest: TypeExprRef,
        },
        Nil,
        Poly {
            body: TypeExprRef,
            vars: super::type_expr::TypeRefList,
        },
        Variant(RowDesc),
        Package {
            path: Path,
            lids: Vec<crate::parser::longident::Longident>,
            args: super::type_expr::TypeRefList,
        },
        Link(TypeExprRef),
        Forget(i32),
    }

    let level = ctx.get_level(ty);

    // Determine action based on type level and descriptor.
    let action = {
        let desc = ctx.borrow_desc(ty);
        let partial_forget_level = cache.partial.as_ref().and_then(|partial| {
            if level == GENERIC_LEVEL {
                return None;
            }
            let has_free_univars = partial
                .free_univars
                .get(&ty)
                .is_some_and(|free_univars| !free_univars.is_empty());
            if has_free_univars {
                None
            } else if partial.keep {
                Some(level)
            } else {
                Some(ctx.current_level())
            }
        });

        if let TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) = &*desc {
            CopyAction::Link(*target)
        } else if let Some(forget_level) = partial_forget_level {
            CopyAction::Forget(forget_level)
        } else if level != GENERIC_LEVEL {
            match &*desc {
                // OCaml's copy returns identity for all non-generic type nodes.
                TypeDesc::Tvar(..)
                | TypeDesc::Tunivar(..)
                | TypeDesc::Ttuple(_)
                | TypeDesc::Tobject { .. }
                | TypeDesc::Tvariant(_)
                | TypeDesc::Tpoly { .. }
                | TypeDesc::Tpackage { .. }
                | TypeDesc::Tarrow { .. }
                | TypeDesc::Tfield { .. }
                | TypeDesc::Tnil
                | TypeDesc::Tconstr { .. } => CopyAction::ReturnSelf,
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => CopyAction::Link(*target),
            }
        } else {
            match &*desc {
                TypeDesc::Tvar(..) => CopyAction::NewVar(None),
                // btype.ml:508-516 `Tunivar _ as ty -> ty`: the copy keeps
                // the descriptor.
                TypeDesc::Tunivar(name, block) => {
                    CopyAction::NewUnivar(name.clone(), block.copied_from(ty))
                }
                TypeDesc::Tarrow { args, ret } => CopyAction::Arrow {
                    args: args.clone(),
                    ret: *ret,
                },
                TypeDesc::Ttuple(types) => CopyAction::Tuple(types.clone()),
                TypeDesc::Tconstr {
                    path,
                    args,
                    path_block,
                    ..
                } => CopyAction::Constr {
                    path: path.clone(),
                    args: args.clone(),
                    path_block: *path_block,
                },
                TypeDesc::Tobject { fields } => CopyAction::Object { fields: *fields },
                TypeDesc::Tfield {
                    name,
                    mutability,
                    typ,
                    rest,
                } => CopyAction::Field {
                    name: name.clone(),
                    mutability: *mutability,
                    typ: *typ,
                    rest: *rest,
                },
                TypeDesc::Tnil => CopyAction::Nil,
                TypeDesc::Tpoly { body, vars } => CopyAction::Poly {
                    body: *body,
                    vars: vars.clone(),
                },
                TypeDesc::Tvariant(row) => CopyAction::Variant(*row.clone()),
                TypeDesc::Tpackage { path, lids, args } => CopyAction::Package {
                    path: path.clone(),
                    lids: *lids.clone(),
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
        // ctype.ml:771: `newty2 forget (Tvar None)`, the static constant.
        CopyAction::Forget(level) => ctx.alloc_type_at_level(
            TypeDesc::Tvar(None, super::type_expr::VarDescBlock::Static),
            level,
        ),
        CopyAction::NewVar(name) => {
            // ctype.ml:775-829: a `newvar ()` stub whose descriptor becomes
            // `copy_type_desc copy desc`, the static `Tvar None`
            // (btype.ml:510).
            debug_assert!(name.is_none());
            let fresh = ctx.new_type(TypeDesc::Tvar(name, super::type_expr::VarDescBlock::Static));
            cache.nodes.insert(ty, fresh);
            fresh
        }
        CopyAction::NewUnivar(name, block) => {
            let fresh = ctx.new_type(TypeDesc::Tunivar(name, block));
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
                CopyAction::Arrow { args, ret } => {
                    let args = args
                        .iter()
                        .map(|arg| {
                            let mut arg = arg.clone();
                            arg.typ = copy_type_cached(ctx, arg.typ, cache);
                            arg
                        })
                        .collect();
                    let ret = copy_type_cached(ctx, ret, cache);
                    TypeDesc::Tarrow { args, ret }
                }
                CopyAction::Tuple(types) => {
                    let types_copy: super::type_expr::TypeRefList = types
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();
                    TypeDesc::Ttuple(types_copy)
                }
                CopyAction::Constr {
                    path,
                    args,
                    path_block,
                } => {
                    let abbrevs = ctx.current_abbreviations();
                    let lookup_abbrevs = proper_abbrevs(ctx, &path, &args, abbrevs);

                    // OCaml compiler/ml/ctype.ml:761-763: a memoized
                    // expansion of `p` (`find_repr p !abbrevs`) is linked to
                    // whenever it is not the stub being built. The memo's
                    // lifetime is governed by its clearing points
                    // (`generalize*`, `check_abbrev_env`, `cleanup_abbrev`).
                    if let Some(found_ty) = ctx.find_abbrev_repr(lookup_abbrevs, &path) {
                        let found_source = ctx.repr(found_ty);
                        // OCaml copy() mutates source nodes to Tsubst stubs while
                        // copying, so find_repr observes the copied representative.
                        // Rust keeps source nodes immutable during copy, so we must
                        // project through the local copy cache to recover the same
                        // representative.
                        let found_repr = cache
                            .nodes
                            .get(found_ty)
                            .copied()
                            .or_else(|| cache.nodes.get(found_source).copied())
                            .unwrap_or(found_ty);
                        if found_repr != placeholder {
                            cache.nodes.insert(ty, found_repr);
                            ctx.set_desc(placeholder, TypeDesc::Tlink(found_repr));
                            return found_repr;
                        }
                    }

                    let args_copy: super::type_expr::TypeRefList = args
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();

                    let copied_abbrev = match ctx.get_abbrev_memo(abbrevs) {
                        AbbrevMemo::Mcons { .. } => ctx.alloc_abbrev(AbbrevMemo::Mlink(abbrevs)),
                        memo => ctx.alloc_abbrev(memo),
                    };

                    TypeDesc::Tconstr {
                        path,
                        args: args_copy,
                        abbrev: copied_abbrev,
                        path_block: path_block.copied_from(ty),
                    }
                }
                CopyAction::Object { fields } => TypeDesc::Tobject {
                    fields: copy_type_cached(ctx, fields, cache),
                },
                CopyAction::Field {
                    name,
                    mutability,
                    typ,
                    rest,
                } => {
                    // btype.ml copy_type_desc: classify the row before
                    // copying either child.
                    let mutability = {
                        let nodes = &cache.nodes;
                        ctx.copy_field_mutability(mutability, rest, false, &|t| {
                            nodes.get(t).copied()
                        })
                    };
                    let typ_copy = copy_type_cached(ctx, typ, cache);
                    let rest_copy = copy_type_cached(ctx, rest, cache);
                    TypeDesc::Tfield {
                        name,
                        mutability,
                        typ: typ_copy,
                        rest: rest_copy,
                    }
                }
                CopyAction::Nil => TypeDesc::Tnil,
                CopyAction::Poly { body, vars } => {
                    let body_copy = copy_type_cached(ctx, body, cache);
                    let vars_copy: super::type_expr::TypeRefList = vars
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
                    let row = row_repr_ref(ctx, &row);
                    let row = row.as_ref();
                    let more = ctx.repr(row.row_more);
                    let more_level = ctx.get_level(more);
                    let keep = more_level != GENERIC_LEVEL;
                    let mut more_copy = match ctx.get_desc(more).into_desc() {
                        TypeDesc::Tconstr { .. } | TypeDesc::Tnil => {
                            copy_type_cached(ctx, more, cache)
                        }
                        TypeDesc::Tvar(name, ..) => {
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
                        TypeDesc::Tunivar(name, ..) => {
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
                    let mut opened_row = None;
                    if cache.partial.as_ref().is_some_and(|partial| !partial.keep) {
                        let has_reither = row.row_fields.iter().any(|(_, field)| {
                            matches!(
                                super::btype::row_field_repr(ctx, field),
                                crate::types::type_expr::RowField::Reither { .. }
                            )
                        });
                        let variant_has_free_univars = cache
                            .partial
                            .as_ref()
                            .and_then(|partial| partial.free_univars.get(&ty))
                            .is_some_and(|free_univars| !free_univars.is_empty());
                        if row.row_closed
                            && !row.row_fixed
                            && !variant_has_free_univars
                            && has_reither
                        {
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
                            let mut row_opened = row.clone();
                            row_opened.row_fields.retain(|(_, field)| {
                                !matches!(
                                    super::btype::row_field_repr(ctx, field),
                                    crate::types::type_expr::RowField::Reither { .. }
                                )
                            });
                            row_opened.row_more = more_copy;
                            row_opened.row_closed = false;
                            row_opened.row_fixed = false;
                            row_opened.row_name = None;
                            opened_row = Some(row_opened);
                        }
                    }
                    let marker_tuple =
                        ctx.new_generic_type(TypeDesc::Ttuple(vec![more_copy, placeholder].into()));
                    // OCaml ctype.ml:853 `more.desc <- Tsubst (Ttuple [more'; t])`:
                    // the marker stays until `cleanup_types` after the whole copy,
                    // so every later variant sharing this row variable reuses `t`
                    // (ctype.ml:786-791).
                    cache.row_more_markers.insert(
                        more,
                        CopyRowMoreMarker {
                            tuple: marker_tuple,
                            variant: placeholder,
                        },
                    );
                    let row_for_copy = opened_row.as_ref().unwrap_or(row);
                    let mut row_copy =
                        copy_row_cached(ctx, row_for_copy, true, keep, more_copy, cache);

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
                    TypeDesc::Tvariant(Box::new(row_copy))
                }
                CopyAction::Package { path, lids, args } => {
                    let args_copy: Vec<_> = args
                        .iter()
                        .map(|t| copy_type_cached(ctx, *t, cache))
                        .collect();
                    TypeDesc::Tpackage {
                        path,
                        lids: Box::new(lids),
                        args: args_copy.into(),
                    }
                }
                CopyAction::ReturnSelf
                | CopyAction::NewVar(_)
                | CopyAction::NewUnivar(..)
                | CopyAction::Link(_)
                | CopyAction::Forget(_) => unreachable!(),
            };
            ctx.set_desc(placeholder, copied_desc);
            placeholder
        }
    }
}

/// Copy a row descriptor.
fn copy_row_cached(
    ctx: &TypeContext,
    row: &RowDesc,
    fixed: bool,
    keep: bool,
    more: TypeExprRef,
    cache: &mut CopyCache<'_>,
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
                        link: if keep {
                            link
                        } else {
                            ctx.alloc_row_field(None)
                        },
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
pub fn is_function(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    let ty = ctx.repr(ty);
    matches!(*ctx.borrow_desc(ty), TypeDesc::Tarrow { .. })
}

/// Get the arity of a function type (number of arguments).
pub fn function_arity(ctx: &TypeContext, ty: TypeExprRef) -> usize {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Tarrow { args, ret } => {
            let count = args.len();
            let ret = *ret;
            drop(desc);
            count + function_arity(ctx, ret)
        }
        _ => 0,
    }
}

/// Extract the argument and return types from an arrow type.
pub fn split_arrow(ctx: &TypeContext, ty: TypeExprRef) -> Option<(TypeExprRef, TypeExprRef)> {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    let (args, ret) = match &*desc {
        TypeDesc::Tarrow { args, ret } => (args.clone(), *ret),
        _ => return None,
    };
    drop(desc);
    let arg = args.first()?;
    let remaining = if args.len() == 1 {
        ret
    } else {
        ctx.new_type(TypeDesc::Tarrow {
            args: args[1..].to_vec().into(),
            ret,
        })
    };
    Some((arg.typ, remaining))
}

/// Extract the argument type, label, and return type from an arrow type.
pub fn split_arrow_with_label(
    ctx: &TypeContext,
    ty: TypeExprRef,
) -> Option<(super::ArgLabel, TypeExprRef, TypeExprRef)> {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    let (args, ret) = match &*desc {
        TypeDesc::Tarrow { args, ret } => (args.clone(), *ret),
        _ => return None,
    };
    drop(desc);
    let arg = args.first()?;
    let remaining = if args.len() == 1 {
        ret
    } else {
        ctx.new_type(TypeDesc::Tarrow {
            args: args[1..].to_vec().into(),
            ret,
        })
    };
    Some((arg.label().clone(), arg.typ, remaining))
}

/// Extract the inner type from option<T>, returning T.
/// Returns None if the type is not option<T>.
pub fn extract_option_type(ctx: &TypeContext, ty: TypeExprRef) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
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
pub fn tuple_elements(ctx: &TypeContext, ty: TypeExprRef) -> Option<Vec<TypeExprRef>> {
    let ty = ctx.repr(ty);
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Ttuple(types) => Some(types.to_vec()),
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
pub fn normalize_type(ctx: &TypeContext, env: &Env, ty: TypeExprRef) {
    let mut visited = HashSet::new();
    normalize_type_rec(ctx, env, &mut visited, ty);
}

/// Sort ALL Tobject field chains alphabetically in the entire type context.
/// OCaml sorts object fields during type checking (flatten_fields/unify_fields),
/// so all Tobject types should have sorted fields. This function ensures that.
pub fn sort_all_object_fields(ctx: &TypeContext) {
    let count = ctx.type_expr_count();
    for i in 0..count {
        let ty = TypeExprRef::from_usize(i);
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
                    let new_desc = ctx.get_desc(new_fi).into_desc();
                    ctx.set_desc(fi_repr, new_desc);
                }
            }
        } else {
            drop(desc);
        }
    }
}

/// Normalize ALL type nodes in the context (sort variant/object fields).
pub fn normalize_all_types(ctx: &TypeContext) {
    let count = ctx.type_expr_count();
    for i in 0..count {
        let ty = TypeExprRef::from_usize(i);
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvariant(row) => {
                let row = row_repr(ctx, row);
                let mut fields: Vec<(Label, RowField)> = row
                    .row_fields
                    .iter()
                    .map(|(label, field)| {
                        let resolved = btype::row_field_repr(ctx, field);
                        (label.clone(), resolved)
                    })
                    .filter(|(_, field)| !matches!(field, RowField::Rabsent))
                    .collect();
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                drop(desc);
                ctx.set_desc(
                    ty,
                    TypeDesc::Tvariant(Box::new(RowDesc {
                        row_fields: fields.into(),
                        row_more: row.row_more,
                        row_closed: row.row_closed,
                        row_fixed: row.row_fixed,
                        row_name: row.row_name.clone(),
                    })),
                );
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
                        let new_desc = ctx.get_desc(new_fi).into_desc();
                        ctx.set_desc(fi_repr, new_desc);
                    }
                }
            }
            _ => {
                drop(desc);
            }
        }
    }
}

/// `Ctype.normalize_type_rec` (ctype.ml:4053-4110).
fn normalize_type_rec(
    ctx: &TypeContext,
    env: &Env,
    visited: &mut HashSet<TypeExprRef>,
    ty: TypeExprRef,
) {
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }

    let tm = btype::row_of_type(ctx, ty);
    if !btype::is_tconstr(ctx, ty) && btype::is_constr_row(ctx, tm, false) {
        // ctype.ml:4058-4065 (PR#7348): name the private row type by its
        // declaration instead of the `#row` type.
        let renamed = match &*ctx.get_desc(tm) {
            TypeDesc::Tconstr {
                path: path @ Path::Pdot(m, i, pos),
                args,
                ..
            } => {
                let i = i.as_str();
                let i_prime = &i[..i.len() - 4];
                // `String.sub` allocates a fresh suffix string (ctype.ml:4061);
                // keep the original prefix allocation, never a tracked carrier
                // reused for another suffix.
                let prefix = ctx
                    .dotted_allocation(path)
                    .map_or_else(|| m.clone(), |allocation| allocation.prefix);
                TypeDesc::Tconstr {
                    path: Path::Pdot(prefix, crate::name::Name::new(i_prime), *pos),
                    args: args.clone(),
                    abbrev: ctx.alloc_abbrev_nil(),
                    path_block: crate::types::type_expr::PathBlock::OWN,
                }
            }
            _ => unreachable!("is_constr_row implies a dotted Tconstr"),
        };
        ctx.set_desc(ty, renamed);
    } else {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvariant(row) => {
                let row = row_repr(ctx, row);
                drop(desc);
                // ctype.ml:4069-4092: drop conjuncts `equal` to an earlier one.
                // `row_field_repr` always rebuilds a `Reither`, so OCaml's
                // `f != f0` holds and the deduplicated list is used.
                let mut fields: Vec<(Label, RowField)> =
                    row.row_fields
                        .iter()
                        .map(|(label, field)| {
                            let resolved = match btype::row_field_repr(ctx, field) {
                                RowField::Reither {
                                    constant,
                                    types,
                                    matched,
                                    link,
                                } if types.len() >= 2 => {
                                    let mut kept: Vec<TypeExprRef> = vec![types[0]];
                                    for t in types.iter().skip(1) {
                                        if !kept.iter().any(|t_prime| {
                                            equal(ctx, env, false, &[*t], &[*t_prime])
                                        }) {
                                            kept.push(*t);
                                        }
                                    }
                                    RowField::Reither {
                                        constant,
                                        types: kept,
                                        matched,
                                        link,
                                    }
                                }
                                resolved => resolved,
                            };
                            (label.clone(), resolved)
                        })
                        .filter(|(_, field)| !matches!(field, RowField::Rabsent))
                        .collect();
                fields.sort_by(|(a, _), (b, _)| a.cmp(b));
                ctx.set_desc(
                    ty,
                    TypeDesc::Tvariant(Box::new(RowDesc {
                        row_fields: fields.into(),
                        row_more: row.row_more,
                        row_closed: row.row_closed,
                        row_fixed: row.row_fixed,
                        row_name: row.row_name.clone(),
                    })),
                );
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
            _ => drop(desc),
        }
    }

    iter_type_expr(ctx, ty, |child| {
        normalize_type_rec(ctx, env, visited, child);
    });
}

// ---------------------------------------------------------------------------
// nondep_type — OCaml ctype.ml nondep_type_rec / nondep_type
//
// Copies a type, expanding any Tconstr whose path depends on `mid`.
// The expanded type is looked up through `env` (which should already contain
// the argument module under the functor-parameter ident).
// ---------------------------------------------------------------------------

/// Copy a type while eliminating dependencies on module ident `mid`.
/// Any `Tconstr(p, tl, _)` where `p.is_free(mid)` is expanded via `env`.
/// Returns `None` if the dependency cannot be removed.
pub fn nondep_type(
    ctx: &TypeContext,
    env: &Env,
    mid: &Ident,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let mut cache: HashMap<TypeExprRef, TypeExprRef> = HashMap::new();
    // ctype.ml `with_nondep_copy_session`.
    ctx.with_copy_session(|| nondep_type_rec(ctx, env, mid, ty, &mut cache))
}

fn nondep_type_rec(
    ctx: &TypeContext,
    env: &Env,
    mid: &Ident,
    ty: TypeExprRef,
    cache: &mut HashMap<TypeExprRef, TypeExprRef>,
) -> Option<TypeExprRef> {
    let ty = ctx.repr(ty);

    // OCaml: Tvar | Tunivar -> ty (identity)
    {
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => return Some(ty),
            _ => {}
        }
    }

    if let Some(&cached) = cache.get(&ty) {
        return Some(cached);
    }

    // Create a stub for recursion (OCaml: newgenvar ())
    let stub = ctx.new_generic_type(TypeDesc::Tvar(
        None,
        crate::types::type_expr::VarDescBlock::OWN,
    ));
    cache.insert(ty, stub);

    let desc = ctx.get_desc(ty).into_desc();
    let new_desc = match &desc {
        TypeDesc::Tconstr {
            path,
            args,
            abbrev,
            path_block,
        } => {
            if path.is_free(mid) {
                let normalized_path = env.normalize_path_prefix(ctx, path);
                if normalized_path != *path && !normalized_path.is_free(mid) {
                    // OCaml `nondep_type_rec` expands parameter-dependent
                    // constructors with `expand_abbrev` (compiler/ml/ctype.ml:4319-4324).
                    // When the dependency goes through a module alias, Env
                    // first normalizes that alias path (compiler/ml/env.ml:912-914),
                    // e.g. `C.Key.t` -> `DB__Section_Type.Key.t`.
                    let new_args: Option<Vec<_>> = args
                        .iter()
                        .map(|a| nondep_type_rec(ctx, env, mid, *a, cache))
                        .collect();
                    let result = ctx.new_generic_constr(normalized_path, new_args?);
                    ctx.set_desc(stub, TypeDesc::Tlink(result));
                    cache.insert(ty, result);
                    return Some(result);
                }
                // Expand the abbreviation — this is the key operation.
                // OCaml: expand_abbrev env (newty2 ty.level ty.desc)
                //
                let expanded = {
                    // Prefer direct env lookup for types through the functor
                    // parameter. OCaml's expand_abbrev uses Env.find_type here;
                    // using the generic abbreviation cache first can preserve a
                    // stale self-manifest and fail to eliminate the dependency.
                    let decl = env.lookup_type(path).ok()?;
                    // `Env.find_type_expansion` (compiler/ml/env.ml:944-956):
                    // a private abstract abbreviation without a constructor
                    // row cannot be expanded, so the dependency stays.
                    if decl.type_manifest.is_some_and(|body| {
                        decl.type_private == PrivateFlag::Private
                            && matches!(decl.type_kind, super::TypeKind::TypeAbstract)
                            && !super::btype::has_constr_row(ctx, body)
                    }) {
                        return None;
                    }
                    if let Some(manifest) = decl.type_manifest {
                        let params = &decl.type_params;
                        if params.len() == args.len() {
                            // Substitute params -> args in manifest
                            let expanded = subst_with_memo(
                                ctx,
                                env,
                                ty,
                                proper_abbrevs(ctx, path, args, *abbrev),
                                PrivateFlag::Public,
                                params,
                                args,
                                manifest,
                            );
                            Some(expanded)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                .or_else(|| {
                    // Fall back to the general expand_head machinery for
                    // aliases that are not directly represented in the local
                    // module signature.
                    let temp = ctx.new_generic_type(desc.clone().shared_from(ty));
                    try_expand_head(ctx, env, temp)
                });
                match expanded {
                    Some(expanded) => {
                        let expanded = ctx.repr(expanded);
                        // Recurse on expansion (OCaml wraps in Tlink)
                        let result = nondep_type_rec(ctx, env, mid, expanded, cache)?;
                        ctx.set_desc(stub, TypeDesc::Tlink(result));
                        cache.insert(ty, result);
                        return Some(result);
                    }
                    None => {
                        // Cannot expand — dependency cannot be eliminated
                        return None;
                    }
                }
            } else {
                let new_args: Option<Vec<_>> = args
                    .iter()
                    .map(|a| nondep_type_rec(ctx, env, mid, *a, cache))
                    .collect();
                let new_args = new_args?;
                TypeDesc::Tconstr {
                    path: path.clone(),
                    args: new_args.into(),
                    abbrev: ctx.alloc_abbrev(AbbrevMemo::Mnil),
                    path_block: path_block.copied_from(ty),
                }
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            let args = args
                .iter()
                .map(|arg| Some(arg.with_type(nondep_type_rec(ctx, env, mid, arg.typ, cache)?)))
                .collect::<Option<Vec<_>>>()?;
            let ret = nondep_type_rec(ctx, env, mid, *ret, cache)?;
            TypeDesc::Tarrow {
                args: args.into(),
                ret,
            }
        }
        TypeDesc::Ttuple(types) => {
            let new_types: Option<Vec<_>> = types
                .iter()
                .map(|t| nondep_type_rec(ctx, env, mid, *t, cache))
                .collect();
            TypeDesc::Ttuple(new_types?.into())
        }
        TypeDesc::Tpoly { body, vars } => {
            let new_vars: Option<Vec<_>> = vars
                .iter()
                .map(|t| nondep_type_rec(ctx, env, mid, *t, cache))
                .collect();
            let new_body = nondep_type_rec(ctx, env, mid, *body, cache)?;
            TypeDesc::Tpoly {
                body: new_body,
                vars: new_vars?.into(),
            }
        }
        TypeDesc::Tvariant(row) => {
            let row = row_repr_ref(ctx, row);
            let row = row.as_ref();
            let new_more = nondep_type_rec(ctx, env, mid, row.row_more, cache)?;
            let new_fields: Option<Vec<_>> = row
                .row_fields
                .iter()
                .map(|(label, field)| {
                    let repr_field = super::btype::row_field_repr(ctx, field);
                    let new_field = match repr_field {
                        super::type_expr::RowField::Rpresent(Some(ty)) => {
                            super::type_expr::RowField::Rpresent(Some(nondep_type_rec(
                                ctx, env, mid, ty, cache,
                            )?))
                        }
                        super::type_expr::RowField::Rpresent(None) => {
                            super::type_expr::RowField::Rpresent(None)
                        }
                        super::type_expr::RowField::Reither {
                            constant,
                            types,
                            matched,
                            ..
                        } => {
                            let new_types: Option<Vec<_>> = types
                                .iter()
                                .map(|a| nondep_type_rec(ctx, env, mid, *a, cache))
                                .collect();
                            super::type_expr::RowField::Reither {
                                constant,
                                types: new_types?,
                                matched,
                                link: super::type_expr::RowFieldRef::null(),
                            }
                        }
                        super::type_expr::RowField::Rabsent => super::type_expr::RowField::Rabsent,
                    };
                    Some((label.clone(), new_field))
                })
                .collect();
            let new_name = match &row.row_name {
                Some((p, tl)) if !p.is_free(mid) => {
                    let new_tl: Option<Vec<_>> = tl
                        .iter()
                        .map(|t| nondep_type_rec(ctx, env, mid, *t, cache))
                        .collect();
                    new_tl.map(|tl| Some((p.clone(), tl))).unwrap_or(None)
                }
                _ => None,
            };
            TypeDesc::Tvariant(Box::new(super::type_expr::RowDesc {
                row_fields: new_fields?.into(),
                row_more: new_more,
                row_closed: row.row_closed,
                row_fixed: row.row_fixed,
                row_name: new_name,
            }))
        }
        TypeDesc::Tobject { fields } => TypeDesc::Tobject {
            fields: nondep_type_rec(ctx, env, mid, *fields, cache)?,
        },
        TypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => {
            // btype.ml copy_type_desc: classify the row before copying either
            // child. nondep_type_rec cannot use `Tsubst` marks.
            let mutability = ctx.copy_field_mutability(*mutability, *rest, false, &|_| None);
            let new_typ = nondep_type_rec(ctx, env, mid, *typ, cache)?;
            let new_rest = nondep_type_rec(ctx, env, mid, *rest, cache)?;
            TypeDesc::Tfield {
                name: name.clone(),
                mutability,
                typ: new_typ,
                rest: new_rest,
            }
        }
        TypeDesc::Tpackage { path, lids, args } => {
            if path.is_free(mid) {
                // OCaml: normalize_package_path then check again
                return None;
            }
            let new_args: Option<Vec<_>> = args
                .iter()
                .map(|a| nondep_type_rec(ctx, env, mid, *a, cache))
                .collect();
            TypeDesc::Tpackage {
                path: path.clone(),
                lids: lids.clone(),
                args: new_args?.into(),
            }
        }
        // Tlink should have been resolved by repr(), Tsubst shouldn't appear
        TypeDesc::Tlink(inner) => {
            return nondep_type_rec(ctx, env, mid, *inner, cache);
        }
        TypeDesc::Tsubst(_) | TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {
            return Some(ty);
        }
    };

    ctx.set_desc(stub, new_desc);
    ctx.set_level(stub, GENERIC_LEVEL);
    Some(stub)
}

/// Eliminate dependencies on functor parameter `mid` from a type declaration.
/// OCaml: Ctype.nondep_type_decl
fn unroll_abbrev(
    ctx: &TypeContext,
    id: &Ident,
    params: &[TypeExprRef],
    ty: TypeExprRef,
) -> TypeExprRef {
    let ty = ctx.repr(ty);
    {
        let desc = ctx.get_desc(ty);
        if matches!(&*desc, TypeDesc::Tvar(..) | TypeDesc::Tunivar(..))
            || params.iter().any(|param| deep_occur(ctx, ty, *param))
            || matches!(&*desc, TypeDesc::Tconstr { path, .. } if path.head_name().starts_with('#'))
        {
            return ty;
        }
    }

    let level = ctx.get_level(ty);
    let desc = ctx.get_desc(ty).into_desc();
    let unrolled = ctx.new_type(desc.shared_from(ty));
    ctx.set_level(unrolled, level);

    let constr = ctx.new_type(TypeDesc::Tconstr {
        path: Path::pident(*id),
        args: params.to_vec().into(),
        abbrev: ctx.alloc_abbrev(AbbrevMemo::Mnil),
        path_block: crate::types::type_expr::PathBlock::OWN,
    });
    ctx.set_level(constr, level);
    link_type(ctx, ty, constr);
    unrolled
}

pub fn nondep_type_decl(
    ctx: &TypeContext,
    env: &Env,
    mid: &Ident,
    _id: &Ident,
    is_covariant: bool,
    decl: &super::decl::TypeDeclaration,
) -> Option<super::decl::TypeDeclaration> {
    let params: Option<Vec<_>> = decl
        .type_params
        .iter()
        .map(|ty| nondep_type(ctx, env, mid, *ty))
        .collect();
    let params = params?;

    let type_kind = match nondep_type_kind(ctx, env, mid, &decl.type_kind) {
        Some(tk) => tk,
        None if is_covariant => super::decl::TypeKind::TypeAbstract,
        None => return None,
    };

    let type_manifest = match decl.type_manifest {
        Some(ty) => match nondep_type(ctx, env, mid, ty) {
            Some(ty) => Some(unroll_abbrev(ctx, _id, &params, ty)),
            None if is_covariant => None,
            None => return None,
        },
        None => None,
    };

    Some(super::decl::TypeDeclaration {
        type_params: params,
        type_arity: decl.type_arity,
        type_kind,
        type_private: decl.type_private,
        type_manifest,
        type_variance: decl.type_variance.clone(),
        type_newtype_level: None,
        type_loc: decl.type_loc,
        type_attributes: decl.type_attributes.clone(),
        type_immediate: decl.type_immediate,
        type_representation: decl.type_representation,
        type_path: decl.type_path.clone(),
        type_shape: decl.type_shape.clone(),
        type_inlined_types: decl.type_inlined_types.clone(),
    })
}

fn nondep_type_kind(
    ctx: &TypeContext,
    env: &Env,
    mid: &Ident,
    kind: &super::decl::TypeKind,
) -> Option<super::decl::TypeKind> {
    match kind {
        super::decl::TypeKind::TypeAbstract => Some(super::decl::TypeKind::TypeAbstract),
        super::decl::TypeKind::TypeOpen => Some(super::decl::TypeKind::TypeOpen),
        super::decl::TypeKind::TypeRecord(labels, repr) => {
            let new_labels: Option<Vec<_>> = labels
                .iter()
                .map(|label| {
                    let new_type = nondep_type(ctx, env, mid, label.ld_type)?;
                    Some(super::decl::LabelDeclaration {
                        ld_type: new_type,
                        ..label.clone()
                    })
                })
                .collect();
            Some(super::decl::TypeKind::TypeRecord(
                crate::types::decl::SharedVec::from(new_labels?),
                repr.clone(),
            ))
        }
        super::decl::TypeKind::TypeVariant(constructors, layout) => {
            let new_constructors: Option<Vec<_>> = constructors
                .iter()
                .map(|cd| {
                    let new_args = match &cd.cd_args {
                        super::decl::ConstructorArguments::CstrTuple(args) => {
                            let new_args: Option<Vec<_>> = args
                                .iter()
                                .map(|a| nondep_type(ctx, env, mid, *a))
                                .collect();
                            super::decl::ConstructorArguments::CstrTuple(new_args?)
                        }
                        super::decl::ConstructorArguments::CstrRecord(labels) => {
                            let new_labels: Option<Vec<_>> = labels
                                .iter()
                                .map(|label| {
                                    let new_type = nondep_type(ctx, env, mid, label.ld_type)?;
                                    Some(super::decl::LabelDeclaration {
                                        ld_type: new_type,
                                        ..label.clone()
                                    })
                                })
                                .collect();
                            super::decl::ConstructorArguments::CstrRecord(new_labels?)
                        }
                    };
                    let new_res = match cd.cd_res {
                        Some(ty) => Some(nondep_type(ctx, env, mid, ty)?),
                        None => None,
                    };
                    Some(super::decl::ConstructorDeclaration {
                        cd_args: new_args,
                        cd_res: new_res,
                        ..cd.clone()
                    })
                })
                .collect();
            Some(super::decl::TypeKind::TypeVariant(
                crate::types::decl::SharedVec::from(new_constructors?),
                *layout,
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::ident::Ident;
    use crate::types::asttypes::PrivateFlag;
    use crate::types::decl::{
        ModuleDeclaration, ModuleType, RecStatus, SignatureItem, TypeDeclaration, TypeKind,
    };

    /// `check_record_fields` (record_coercion.ml:15-58) on records whose
    /// fields have the given mutability, each field typed by a fresh
    /// variable: the violations and the paired types, in the order the
    /// callers pass them to `subtype_list`.
    fn check_mutability(
        ctx: &TypeContext,
        fields: &[(&str, MutableFlag, MutableFlag)],
    ) -> (
        Vec<RecordFieldSubtypeViolation>,
        Vec<(TypeExprRef, TypeExprRef)>,
        Vec<(TypeExprRef, TypeExprRef)>,
    ) {
        let label = |name: &str, mutable: MutableFlag, ty: TypeExprRef| LabelDeclaration {
            ld_id: ctx.create_ident(name),
            ld_runtime_name: None,
            ld_mutable: mutable,
            ld_optional: false,
            ld_type: ty,
            ld_loc: crate::types::DeclLoc::none(),
            ld_attributes: vec![],
        };
        let mut fields1 = Vec::new();
        let mut fields2 = Vec::new();
        let mut types = Vec::new();
        for (name, mutable1, mutable2) in fields {
            let (ty1, ty2) = (ctx.new_var(None), ctx.new_var(None));
            fields1.push(label(name, *mutable1, ty1));
            fields2.push(label(name, *mutable2, ty2));
            types.push((ty1, ty2));
        }
        let (violations, mut tl1, mut tl2) = check_record_fields(&fields1, &fields2);
        tl1.reverse();
        tl2.reverse();
        let pairs = tl1.into_iter().zip(tl2).collect();
        (violations, pairs, types)
    }

    #[test]
    fn record_coercion_rejects_making_a_field_writable() {
        use MutableFlag::{Immutable, Mutable};
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let (violations, pairs, types) = check_mutability(&ctx, &[("x", Immutable, Mutable)]);
        assert!(matches!(
            violations.as_slice(),
            [RecordFieldSubtypeViolation::MutableMismatch { label }] if label == "x"
        ));
        assert_eq!(pairs, vec![types[0]]);
        // A read-only view of a mutable field is sound.
        let (violations, pairs, types) = check_mutability(&ctx, &[("x", Mutable, Immutable)]);
        assert!(violations.is_empty());
        assert_eq!(pairs, vec![types[0]]);
    }

    #[test]
    fn record_coercion_relates_a_field_mutable_in_both_records_both_ways() {
        use MutableFlag::{Immutable, Mutable};
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let (violations, pairs, types) = check_mutability(
            &ctx,
            &[("a", Mutable, Mutable), ("b", Immutable, Immutable)],
        );
        assert!(violations.is_empty());
        let ((a1, a2), (b1, b2)) = (types[0], types[1]);
        // OCaml's cons lists after the fold over `a` then `b`:
        // `b1 :: a1 :: a2` and `b2 :: a2 :: a1`.
        assert_eq!(pairs, vec![(b1, b2), (a1, a2), (a2, a1)]);
    }

    #[test]
    fn repeated_normalization_allocates_fresh_dots_from_cached_resolution() {
        use crate::types::decl::AliasPresence;
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let mut env = Env::empty();
        let m = ctx.create_ident("M");
        let a = ctx.create_ident("A");
        let b = ctx.create_ident("B");
        let module = |md_type| ModuleDeclaration {
            md_type,
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        };
        let inner = module(ModuleType::MtySignature(std::sync::Arc::new(vec![])));
        env.add_module(
            m,
            module(ModuleType::MtySignature(std::sync::Arc::new(vec![
                SignatureItem::SigModule(a, inner, RecStatus::TrecNot),
            ]))),
        );
        // Two alias declarations with equal but separately allocated targets.
        let b_target = std::sync::Arc::new(Path::pident(m));
        let c = ctx.create_ident("C");
        let c_target = std::sync::Arc::new(Path::pident(m));
        env.add_module(
            b,
            module(ModuleType::MtyAlias(
                AliasPresence::MtaPresent,
                b_target.clone(),
            )),
        );
        env.add_module(
            c,
            module(ModuleType::MtyAlias(
                AliasPresence::MtaPresent,
                c_target.clone(),
            )),
        );

        // `M.A`: no alias, so each call returns its own fresh `Pdot` around
        // the caller's `Pident` block, keeping the suffix string.
        let root = std::sync::Arc::new(Path::pident(m));
        let source = ctx.dotted_from_ident(root.clone(), a, 0);
        let first = normalize_path_full(&ctx, &env, &source);
        assert!(
            ctx.find_normalized_path_full(env.scope_id(), &source)
                .is_some()
        );
        let second = normalize_path_full(&ctx, &env, &source);
        assert_eq!(first, source);
        assert_eq!(second, source);
        let keys: Vec<_> = [&source, &first, &second]
            .iter()
            .map(|p| ctx.dotted_allocation(p).unwrap().key())
            .collect();
        assert!(keys[0] != keys[1] && keys[1] != keys[2] && keys[0] != keys[2]);
        for p in [&first, &second] {
            let allocation = ctx.dotted_allocation(p).unwrap();
            assert!(std::sync::Arc::ptr_eq(&allocation.prefix, &root));
            assert_eq!(allocation.name, ctx.ident_name_allocation(&a));
        }
        // A distinct, equal-valued input hits the same cache entry, but the
        // result keeps that input's own prefix block.
        let other_root = std::sync::Arc::new(Path::pident(m));
        let other = ctx.dotted_from_ident(other_root.clone(), a, 0);
        let third = normalize_path_full(&ctx, &env, &other);
        assert!(std::sync::Arc::ptr_eq(
            &ctx.dotted_allocation(&third).unwrap().prefix,
            &other_root
        ));

        // `B.A` through `B = M`: the prefix comes from the alias's stored path,
        // the same block on every call; the dot itself is fresh.
        let through_alias = ctx.dotted_from_ident(std::sync::Arc::new(Path::pident(b)), a, 0);
        let x = normalize_path_full(&ctx, &env, &through_alias);
        let y = normalize_path_full(&ctx, &env, &through_alias);
        assert!(x.same(&source) && y.same(&source));
        let (x, y) = (
            ctx.dotted_allocation(&x).unwrap(),
            ctx.dotted_allocation(&y).unwrap(),
        );
        assert_ne!(x.key(), y.key());
        // The cached route and the direct Env route reach the declaration's
        // own target block, the same one on every call.
        assert!(std::sync::Arc::ptr_eq(&x.prefix, &b_target));
        assert!(std::sync::Arc::ptr_eq(&y.prefix, &b_target));
        assert!(
            ctx.find_normalized_path_full(env.scope_id(), &through_alias)
                .is_some()
        );
        assert_eq!(x.name, ctx.ident_name_allocation(&a));
        let direct = env.normalize_path(&ctx, &through_alias);
        assert!(std::sync::Arc::ptr_eq(
            &ctx.dotted_allocation(&direct).unwrap().prefix,
            &b_target
        ));
        // An equal-valued target of another declaration is its own block.
        let through_c = ctx.dotted_from_ident(std::sync::Arc::new(Path::pident(c)), a, 0);
        let z = normalize_path_full(&ctx, &env, &through_c);
        assert!(z.same(&source));
        let z_prefix = ctx.dotted_allocation(&z).unwrap().prefix;
        assert!(std::sync::Arc::ptr_eq(&z_prefix, &c_target));
        assert!(!std::sync::Arc::ptr_eq(&z_prefix, &b_target));
        let direct_c = env.normalize_path_prefix(&ctx, &through_c);
        assert!(std::sync::Arc::ptr_eq(
            &ctx.dotted_allocation(&direct_c).unwrap().prefix,
            &c_target
        ));
        // A copy of the declaration shares its target block.
        let copied = crate::types::typecore::copy_alias_target(&b_target);
        assert!(std::sync::Arc::ptr_eq(&copied, &b_target));

        // `Env.normalize_path_prefix` (env.ml:898-902) also rebuilds the dot
        // every call and keeps an unaliased `Pident` prefix block.
        let p = env.normalize_path_prefix(&ctx, &source);
        let q = env.normalize_path_prefix(&ctx, &source);
        let (p, q) = (
            ctx.dotted_allocation(&p).unwrap(),
            ctx.dotted_allocation(&q).unwrap(),
        );
        assert_ne!(p.key(), q.key());
        assert_ne!(p.key(), keys[0]);
        assert!(std::sync::Arc::ptr_eq(&p.prefix, &root));
        assert_eq!(p.name, q.name);
        let aliased = env.normalize_path_prefix(&ctx, &through_alias);
        assert!(aliased.same(&source));
        assert_eq!(
            ctx.dotted_allocation(&aliased).unwrap().name,
            ctx.ident_name_allocation(&a)
        );
        // `Env.normalize_path` follows the alias and rebuilds the dot.
        let full = env.normalize_path(&ctx, &through_alias);
        assert!(full.same(&source));
        assert_ne!(ctx.dotted_allocation(&full).unwrap().key(), keys[0]);
    }

    #[test]
    fn private_row_rename_keeps_prefix_without_reusing_a_tracked_carrier() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let root = std::sync::Arc::new(Path::Pident(ctx.create_ident("M")));
        let row_id = ctx.create_ident("t#row");
        let row_path = ctx.dotted_from_ident(root.clone(), row_id, crate::types::path::NOPOS);
        let row_more = ctx.new_constr(row_path, vec![]);
        let ty = ctx.new_type(TypeDesc::Tvariant(Box::new(
            crate::types::type_expr::RowDesc {
                row_fields: Vec::new().into(),
                row_more,
                row_closed: false,
                row_fixed: false,
                row_name: None,
            },
        )));
        normalize_type(&ctx, &super::super::env::Env::empty(), ty);
        // ctype.ml:4065 renames the variant node itself.
        let desc = ctx.get_desc(ctx.repr(ty));
        let TypeDesc::Tconstr {
            path: Path::Pdot(prefix, name, _),
            ..
        } = &*desc
        else {
            panic!("renamed constructor")
        };
        assert_eq!(name.as_str(), "t");
        // ctype.ml:4058-4065 shares the original prefix; the suffix is a fresh
        // `String.sub` string, so the renamed dot carries no suffix evidence.
        assert!(std::sync::Arc::ptr_eq(prefix, &root));
        assert!(ctx.dotted_allocation(&desc_path(&desc)).is_none());
    }

    fn desc_path(desc: &TypeDesc) -> Path {
        match desc {
            TypeDesc::Tconstr { path, .. } => path.clone(),
            _ => unreachable!(),
        }
    }

    #[test]
    fn qualified_and_rebound_declarations_keep_binder_name_allocations() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let mut arena = crate::parse_arena::ParseArena::new();
        let text = arena.push_string("t");
        let first = ctx.create_ast_ident(&arena, text);
        let second = ctx.create_ast_ident(&arena, text);
        let root = std::sync::Arc::new(Path::Pident(ctx.create_ident("Root")));
        let manifest = ctx.new_var(None);
        let decl = manifest_decl(manifest, None);
        let a = qualify_type_decl_for_module_access_path(&ctx, &root, &first, &decl);
        let b = qualify_type_decl_for_module_access_path(&ctx, &root, &second, &decl);
        let a_alloc = ctx
            .dotted_allocation(a.type_path.as_ref().unwrap())
            .unwrap();
        let b_alloc = ctx
            .dotted_allocation(b.type_path.as_ref().unwrap())
            .unwrap();
        assert!(std::sync::Arc::ptr_eq(&a_alloc.prefix, &root));
        assert!(std::sync::Arc::ptr_eq(&a_alloc.prefix, &b_alloc.prefix));
        assert_eq!(a_alloc.name, ctx.ident_name_allocation(&first));
        assert_eq!(a_alloc.name, b_alloc.name);
        assert_ne!(a_alloc.key(), b_alloc.key());
        assert_eq!(a.type_manifest, Some(manifest));
        assert!(decl.type_path.is_none());

        let old = Path::Pident(ctx.create_ident("Old"));
        let ty = ctx.new_generic_constr(old.clone(), vec![]);
        let mut sig = vec![SignatureItem::SigType(
            first,
            std::sync::Arc::new(manifest_decl(ty, Some(old))),
            RecStatus::TrecNot,
        )];
        super::super::typecore::rebind_direct_sig_type_family_to_access_path(&ctx, &root, &mut sig);
        let SignatureItem::SigType(_, rebound, _) = &sig[0] else {
            panic!("type")
        };
        let rebound_alloc = ctx
            .dotted_allocation(rebound.type_path.as_ref().unwrap())
            .unwrap();
        assert_eq!(rebound_alloc.name, ctx.ident_name_allocation(&first));
        assert!(rebound_alloc.prefix.same(&root));
        let desc = ctx.get_desc(ty);
        let TypeDesc::Tconstr { path, .. } = &*desc else {
            panic!("constructor")
        };
        assert_eq!(
            ctx.dotted_allocation(path).unwrap().key(),
            rebound_alloc.key()
        );
    }

    fn manifest_decl(manifest: TypeExprRef, type_path: Option<Path>) -> TypeDeclaration {
        TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: TypeKind::TypeAbstract,
            type_private: PrivateFlag::Public,
            type_manifest: Some(manifest),
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: crate::types::TypeRepresentation::Boxed,
            type_shape: crate::types::ValueShape::Unstated,
            type_inlined_types: vec![],
            type_path,
        }
    }

    fn module_with_t(type_id: Ident, type_decl: TypeDeclaration) -> ModuleDeclaration {
        ModuleDeclaration {
            md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![SignatureItem::SigType(
                type_id,
                std::sync::Arc::new(type_decl),
                RecStatus::TrecNot,
            )])),
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        }
    }

    fn assert_type_path(ctx: &TypeContext, ty: TypeExprRef, expected: &Path) {
        let ty = ctx.repr(ty);
        assert!(matches!(
            &*ctx.get_desc(ty),
            TypeDesc::Tconstr { path, .. } if path.same(expected)
        ));
    }

    #[test]
    fn type_arg_nary_copy_preserves_labels_and_shared_type_identity() {
        use crate::intern::StrIdx;
        use crate::location::{Location, Position};
        use crate::types::ArgLabel;
        use crate::types::type_expr::TypeArg;
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let shared = ctx.new_generic_var(Some("a".into()));
        let loc = Location {
            loc_start: Position::new(StrIdx(31), 2, 10, 12),
            loc_end: Position::new(StrIdx(32), 4, 25, 29),
            loc_ghost: true,
            origin: Default::default(),
        };
        let labels = [
            ArgLabel::Nolabel,
            ArgLabel::labelled("x", ctx.intern_loc(loc)),
            ArgLabel::optional("y", ctx.intern_loc(loc)),
        ];
        let arrow = ctx.new_type(TypeDesc::Tarrow {
            args: labels
                .iter()
                .map(|l| TypeArg::new(l.clone(), shared))
                .collect(),
            ret: shared,
        });
        let unused = ctx.new_generic_var(Some("unused".into()));
        let replacement = ctx.new_generic_var(Some("replacement".into()));
        assert_eq!(
            subst_type_params(&ctx, &[unused], &[replacement], arrow),
            arrow
        );
        let changed = subst_type_params(&ctx, &[shared], &[replacement], arrow);
        assert_ne!(changed, arrow);
        let changed_desc = ctx.get_desc(changed);
        let TypeDesc::Tarrow { args, ret } = &*changed_desc else {
            panic!("not arrow")
        };
        assert_eq!(*ret, replacement);
        for (arg, expected) in args.iter().zip(&labels) {
            assert_eq!(arg.typ, replacement);
            assert_eq!(arg.label(), expected);
            if let ArgLabel::Labelled(l) | ArgLabel::Optional(l) = arg.label() {
                assert_eq!(ctx.resolve_loc(l.loc), loc);
            }
        }
        let copied = copy_type_deep(&ctx, arrow, &mut HashMap::new());
        let desc = ctx.get_desc(copied);
        let TypeDesc::Tarrow { args, ret } = &*desc else {
            panic!("not arrow")
        };
        assert_eq!(args.len(), 3);
        assert_ne!(*ret, shared);
        for (arg, expected) in args.iter().zip(&labels) {
            assert_eq!(arg.typ, *ret);
            assert_eq!(arg.label(), expected);
            if let ArgLabel::Labelled(l) | ArgLabel::Optional(l) = arg.label() {
                assert_eq!(ctx.resolve_loc(l.loc), loc);
            }
        }
        let original = ctx.get_desc(arrow);
        let TypeDesc::Tarrow { args, ret } = &*original else {
            panic!("not arrow")
        };
        assert_eq!(*ret, shared);
        assert!(args.iter().all(|arg| arg.typ == shared));
    }

    #[test]
    fn test_unify_same_type() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut state = UnifyState::new();

        let t = ctx.new_var(None);
        assert!(unify(&ctx, &mut state, t, t).is_ok());
    }

    #[test]
    fn test_unify_var_with_type() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
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
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
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
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut state = UnifyState::new();

        let a = ctx.new_var(None);
        let tuple1 = ctx.new_tuple(vec![a]);
        let tuple2 = ctx.new_tuple(vec![a, a]);

        assert!(unify(&ctx, &mut state, tuple1, tuple2).is_err());
    }

    #[test]
    fn failed_unification_backtracks_partial_type_mutations() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let mut state = UnifyState::new();
        let variable = ctx.new_var(Some("kept".to_string()));
        let left = ctx.new_tuple(vec![variable, ctx.predef_int()]);
        let right = ctx.new_tuple(vec![ctx.predef_string(), ctx.predef_bool()]);
        let type_snapshot = ctx.snapshot_type_state();
        let state_snapshot = state.snapshot_backtrack_state();

        assert!(unify(&ctx, &mut state, left, right).is_err());
        assert_eq!(ctx.repr(variable), ctx.predef_string());
        ctx.restore_type_state(type_snapshot);
        state.restore_backtrack_state(state_snapshot);

        assert!(
            matches!(&*ctx.borrow_desc(variable), TypeDesc::Tvar(Some(name), ..) if name == "kept")
        );
    }

    #[test]
    fn test_occurs_check() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let tuple = ctx.new_tuple(vec![a, b]);

        assert!(!occurs(&ctx, a, b));
        assert!(occurs(&ctx, a, a));
        assert!(occurs(&ctx, a, tuple));
    }

    #[test]
    fn occurs_checks_agree_beyond_the_quick_walk_budget() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let needle = ctx.new_var(None);
        let other = ctx.new_var(None);
        // Share each level twice so the walk without a visited set exceeds
        // its budget long before the full walk would finish.
        let mut with_needle = needle;
        let mut without_needle = other;
        for _ in 0..40 {
            with_needle = ctx.new_tuple(vec![with_needle, with_needle]);
            without_needle = ctx.new_tuple(vec![without_needle, without_needle]);
        }
        assert!(occurs(&ctx, needle, with_needle));
        assert!(deep_occur(&ctx, needle, with_needle));
        assert!(!occurs(&ctx, needle, without_needle));
        assert!(!deep_occur(&ctx, needle, without_needle));
        let mut budget = 256;
        assert!(!surely_univar_free(&ctx, without_needle, &mut budget));
    }

    #[test]
    fn occurs_checks_terminate_on_cyclic_types() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let needle = ctx.new_var(None);
        let hole = ctx.new_var(None);
        let cycle = ctx.new_tuple(vec![hole, hole]);
        link_type(&ctx, hole, cycle);
        assert!(!occurs(&ctx, needle, cycle));
        assert!(!deep_occur(&ctx, needle, cycle));
        let mut budget = 256;
        assert!(!surely_univar_free(&ctx, cycle, &mut budget));
    }

    #[test]
    fn occur_univar_quick_walk_stops_at_univars() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let plain = ctx.new_tuple(vec![ctx.new_var(None), ctx.new_var(None)]);
        let mut budget = 256;
        assert!(surely_univar_free(&ctx, plain, &mut budget));
        let with_univar = ctx.new_tuple(vec![ctx.new_var(None), ctx.new_univar(None)]);
        let mut budget = 256;
        assert!(!surely_univar_free(&ctx, with_univar, &mut budget));
    }

    #[test]
    fn test_generalize_and_instance() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

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
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let a = ctx.new_var(None);
        let b = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(a, b);

        assert!(!is_function(&ctx, a));
        assert!(is_function(&ctx, arrow));
    }

    #[test]
    fn test_function_arity() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

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

    #[test]
    fn simple_abbrev_cache_clears_when_module_env_changes() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = crate::types::Env::empty();

        let module_id = Ident::create_local("M");
        let type_id = Ident::create_local("t");
        let module_path = Path::pident(module_id);
        let type_path = Path::pdot(module_path, "t".to_string());

        let int_ty = ctx.new_predef_constr(crate::types::predef::path_int(), vec![]);
        env.add_module(
            module_id,
            module_with_t(type_id, manifest_decl(int_ty, Some(type_path.clone()))),
        );

        let first = ctx.new_constr(type_path.clone(), vec![]);
        let first_expanded = try_expand_head(&ctx, &env, first).expect("expand first M.t");
        assert_type_path(&ctx, first_expanded, &crate::types::predef::path_int());
        assert!(
            ctx.find_abbrev_expansion(ctx.simple_abbrevs_memo(), PrivateFlag::Public, &type_path,)
                .is_some()
        );

        let old_env_id = env.id();
        let string_ty = ctx.new_predef_constr(crate::types::predef::path_string(), vec![]);
        env.add_module(
            module_id,
            module_with_t(type_id, manifest_decl(string_ty, Some(type_path.clone()))),
        );
        assert_ne!(env.id(), old_env_id);

        let second = ctx.new_constr(type_path.clone(), vec![]);
        let second_expanded = try_expand_head(&ctx, &env, second).expect("expand rebound M.t");
        assert_type_path(&ctx, second_expanded, &crate::types::predef::path_string());
    }

    #[test]
    fn resolve_type_item_through_env_keeps_original_module_signature_unmodified() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = crate::types::Env::empty();

        let module_id = Ident::create_local("M");
        let sibling_id = Ident::create_local("u");
        let type_id = Ident::create_local("t");

        let int_ty = ctx.new_predef_constr(crate::types::predef::path_int(), vec![]);
        let sibling_decl = TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: TypeKind::TypeAbstract,
            type_private: PrivateFlag::Public,
            type_manifest: Some(int_ty),
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: crate::types::TypeRepresentation::Boxed,
            type_shape: crate::types::ValueShape::Unstated,
            type_inlined_types: vec![],
            type_path: None,
        };
        let type_decl = TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: TypeKind::TypeAbstract,
            type_private: PrivateFlag::Public,
            type_manifest: Some(ctx.new_constr(crate::types::Path::pident(sibling_id), vec![])),
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: crate::types::TypeRepresentation::Boxed,
            type_shape: crate::types::ValueShape::Unstated,
            type_inlined_types: vec![],
            type_path: None,
        };

        env.add_module(
            module_id,
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![
                    SignatureItem::SigType(
                        sibling_id,
                        std::sync::Arc::new(sibling_decl),
                        RecStatus::TrecNot,
                    ),
                    SignatureItem::SigType(
                        type_id,
                        std::sync::Arc::new(type_decl),
                        RecStatus::TrecNot,
                    ),
                ])),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let queried_path =
            crate::types::Path::pdot(crate::types::Path::pident(module_id), "t".to_string());
        let (_, resolved_decl) =
            resolve_type_item_through_env(&ctx, &env, &queried_path, true).expect("resolve M.t");

        let resolved_manifest = resolved_decl.type_manifest.expect("resolved manifest");
        let resolved_manifest = ctx.repr(resolved_manifest);
        assert!(matches!(
            &*ctx.get_desc(resolved_manifest),
            TypeDesc::Tconstr { path, .. } if path.name() == "M.u"
        ));

        let module_decl = env.find_module("M").expect("module M");
        let ModuleType::MtySignature(sig_items) = &module_decl.md_type else {
            panic!("expected M to keep its original signature");
        };
        let Some((_, original_decl, _)) = sig_items.iter().find_map(|item| match item {
            SignatureItem::SigType(id, decl, rec_status) if id.name() == "t" => {
                Some((id, decl, rec_status))
            }
            _ => None,
        }) else {
            panic!("expected original type declaration for M.t");
        };
        let original_manifest = original_decl.type_manifest.expect("original manifest");
        let original_manifest = ctx.repr(original_manifest);
        assert!(matches!(
            &*ctx.get_desc(original_manifest),
            TypeDesc::Tconstr { path, .. } if matches!(path, crate::types::Path::Pident(id) if id.name() == "u")
        ));
    }

    #[test]
    fn ownership_lookup_keeps_cached_identity_and_owned_mutation_is_private() {
        use crate::types::decl::TypeDeclarationRef;
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let env = Env::empty();
        let parent = Path::pident(Ident::create_persistent("Ownership"));
        let path = Path::pdot(parent.clone(), "t");
        let manifest = ctx.new_generic_var(None);
        ctx.register_raw_module_sig(
            "Ownership",
            std::sync::Arc::new(vec![SignatureItem::SigType(
                Ident::create_local("t"),
                std::sync::Arc::new(manifest_decl(manifest, Some(path.clone()))),
                RecStatus::TrecNot,
            )]),
        );
        let before = ctx.type_expr_count();
        let first = lookup_type_decl_for_path(&ctx, &env, &path).expect("cold lookup");
        let second = lookup_type_decl_for_path(&ctx, &env, &path).expect("warm lookup");
        match (&first, &second) {
            (TypeDeclarationRef::Shared(a), TypeDeclarationRef::Shared(b)) => {
                assert!(std::sync::Arc::ptr_eq(a, b))
            }
            _ => panic!("persistent lookup should retain its cached declaration"),
        }
        assert_eq!(first.type_manifest, Some(manifest));
        assert_eq!(ctx.type_expr_count(), before);
        let mut owned = second.into_owned();
        owned.type_private = PrivateFlag::Private;
        owned.type_params.push(manifest);
        owned.type_manifest = None;
        assert_eq!(first.type_private, PrivateFlag::Public);
        assert!(first.type_params.is_empty());
        assert_eq!(first.type_manifest, Some(manifest));
        // The previous shallow container clone also shared TypeExprRef nodes.
        // Keep that sharing while independently owning writable metadata.
        assert_eq!(owned.type_params[0], manifest);
        ctx.set_desc(
            manifest,
            TypeDesc::Tvar(
                Some("shared".to_string()),
                crate::types::type_expr::VarDescBlock::OWN,
            ),
        );
        assert!(
            matches!(&*ctx.borrow_desc(first.type_manifest.unwrap()), TypeDesc::Tvar(Some(name), ..) if name == "shared")
        );
    }

    #[test]
    fn ownership_probe_does_not_publish_and_live_result_allows_recursive_lookup() {
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let env = Env::empty();
        let parent = Path::pident(Ident::create_persistent("ProbeOwnership"));
        let manifest = ctx.new_generic_var(None);
        ctx.register_raw_module_sig(
            "ProbeOwnership",
            std::sync::Arc::new(vec![SignatureItem::SigType(
                Ident::create_local("t"),
                std::sync::Arc::new(manifest_decl(manifest, None)),
                RecStatus::TrecNot,
            )]),
        );
        let mut pers = None;
        let probe = super::super::typecore::lookup_type_in_resolved_path_for_probe(
            &parent, "t", &env, &mut pers, &ctx,
        )
        .expect("probe");
        assert!(
            ctx.find_resolved_module_type(env.scope_id(), &parent, "t")
                .is_none()
        );
        let path = Path::pdot(parent.clone(), "t");
        let first = lookup_type_decl_for_path(&ctx, &env, &path).expect("real lookup");
        assert!(
            ctx.find_resolved_module_type(env.scope_id(), &parent, "t")
                .is_some()
        );
        let second = lookup_type_decl_for_path(&ctx, &env, &path)
            .expect("lookup while previous result is live");
        assert_eq!(first.type_manifest, second.type_manifest);
        assert_eq!(probe.2.type_manifest, first.type_manifest);
    }

    #[test]
    fn ownership_into_owned_moves_unique_storage_and_copies_shared_containers() {
        use crate::types::decl::TypeDeclarationRef;
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let manifest = ctx.new_generic_var(None);
        let mut decl = manifest_decl(manifest, None);
        decl.type_params.push(manifest);
        let data = decl.type_params.as_ptr();
        let unique = TypeDeclarationRef::Shared(std::sync::Arc::new(decl)).into_owned();
        assert_eq!(data, unique.type_params.as_ptr());
        let shared = std::sync::Arc::new(unique);
        let mut copied = TypeDeclarationRef::Shared(shared.clone()).into_owned();
        assert_ne!(shared.type_params.as_ptr(), copied.type_params.as_ptr());
        assert_eq!(shared.type_params, copied.type_params);
        copied.type_params.clear();
        assert_eq!(shared.type_params, vec![manifest]);
        let borrowed = TypeDeclarationRef::Borrowed(&shared).into_owned();
        assert_ne!(shared.type_params.as_ptr(), borrowed.type_params.as_ptr());
        let data = borrowed.type_params.as_ptr();
        let moved = TypeDeclarationRef::owned(borrowed).into_owned();
        assert_eq!(data, moved.type_params.as_ptr());
        assert!(std::mem::size_of::<TypeDeclarationRef<'_>>() <= 16);
    }
}
