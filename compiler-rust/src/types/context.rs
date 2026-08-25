//! Type checking context.
//!
//! This module provides `TypeContext`, the core context for type checking.
//! It replaces the global state from the OCaml implementation with explicit,
//! per-compilation state.
//!
//! # Design
//!
//! The `TypeContext` owns all type expressions through a `TypeArena`.
//! It maintains the type checking state including:
//! - Current generalization level
//! - Type variable tracking
//! - Unification state
//!
//! # Concurrency
//!
//! `TypeContext` is NOT thread-safe - it uses `RefCell` internally.
//! However, multiple `TypeContext` instances can exist concurrently,
//! one per compilation unit.

use super::asttypes::{ArgLabel, PrivateFlag};
use super::env::Env;
use super::path::Path;
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, Commutable, CommutableRef, FieldKind, FieldKindRef, GENERIC_LEVEL,
    RowDesc, RowField, RowFieldRef, TypeArg, TypeDesc, TypeExpr, TypeExprRef,
};
use super::typedtree::EnvRef;
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::parse_arena::LidentIdx;
use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::ptr::NonNull;
use std::sync::Arc;

/// Append-only type arena using chunked allocation for zero-copy access.
///
/// Safe because:
/// - `typed_arena::Arena<TypeExpr>` gives stable addresses for allocated nodes
/// - The pointer Vec only grows (push), never shrinks or reorders
/// - Individual TypeExpr.desc RefCells are independent
struct TypeArena {
    arena: typed_arena::Arena<TypeExpr>,
    types: std::cell::UnsafeCell<Vec<NonNull<TypeExpr>>>,
}

impl TypeArena {
    fn new() -> Self {
        TypeArena {
            arena: typed_arena::Arena::new(),
            types: std::cell::UnsafeCell::new(Vec::new()),
        }
    }

    #[inline]
    fn get(&self, r: TypeExprRef) -> &TypeExpr {
        // Safety: `r` is an arena index returned by `push`, and `types` only
        // grows append-only after the pointed `TypeExpr` has been arena
        // allocated.
        unsafe {
            let types = &*self.types.get();
            types[r.index()].as_ref()
        }
    }

    fn push(&self, ty: TypeExpr) -> TypeExprRef {
        let ptr = NonNull::from(self.arena.alloc(ty));
        // Safety: `types` is an append-only side table of stable arena
        // pointers. `UnsafeCell` is used so `TypeContext` can allocate through
        // shared references like OCaml's mutable type arena.
        unsafe {
            let types = &mut *self.types.get();
            let idx = types.len();
            types.push(ptr);
            TypeExprRef::from_usize(idx)
        }
    }

    fn len(&self) -> usize {
        // Safety: immutable length read from the append-only side table.
        unsafe { (*self.types.get()).len() }
    }
}

/// Type alias for the desc borrow returned by get_desc().
pub type TypeDescRef<'a> = std::cell::Ref<'a, TypeDesc>;

/// Cloned snapshot of a type descriptor, for cases where the caller
/// needs to hold the desc while also mutating the same type node.
pub struct TypeDescSnapshot(TypeDesc);

impl Deref for TypeDescSnapshot {
    type Target = TypeDesc;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Snapshot of mutable type-checker state for OCaml-style failed-unify
/// backtracking.
pub(crate) struct TypeMutationSnapshot {
    type_states: Vec<(TypeDesc, i32)>,
    row_field_states: Vec<Option<RowField>>,
    abbrev_states: Vec<AbbrevMemo>,
    memoized_abbrev_refs: Vec<AbbrevMemoRef>,
    current_abbreviations: AbbrevMemoRef,
    current_level: i32,
    nongen_level: i32,
    global_level: i32,
    saved_levels: Vec<(i32, i32)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct QualifiedModuleComponentsCacheKey {
    path: Path,
    env_id: Option<u64>,
}

impl QualifiedModuleComponentsCacheKey {
    pub(crate) fn new(path: Path, env_id: Option<u64>) -> Self {
        Self {
            path: normalize_component_cache_path(path),
            env_id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct QualifiedRecordLabelCacheKey {
    path: Path,
    env_id: u64,
    lbl_pos: i32,
}

impl QualifiedRecordLabelCacheKey {
    fn new(path: Path, env_id: u64, lbl_pos: i32) -> Self {
        Self {
            path: normalize_component_cache_path(path),
            env_id,
            lbl_pos,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RecordLabelDescriptionSummary {
    label_positions: Arc<ahash::AHashMap<String, usize>>,
    pub(crate) mandatory_count: usize,
    pub(crate) has_optional: bool,
    pub(crate) has_dotdotdot: bool,
    pub(crate) all_regular: bool,
}

impl RecordLabelDescriptionSummary {
    pub(crate) fn from_labels(labels: &[super::decl::LabelDescription]) -> Self {
        let mut label_positions = ahash::AHashMap::with_capacity(labels.len());
        let mut mandatory_count = 0;
        let mut has_optional = false;
        let mut has_dotdotdot = false;
        let mut all_regular = true;

        for (idx, label) in labels.iter().enumerate() {
            label_positions.insert(label.lbl_name.clone(), idx);
            if label.lbl_optional {
                has_optional = true;
            } else {
                mandatory_count += 1;
            }
            if label.lbl_name == "..." {
                has_dotdotdot = true;
            }
            if !matches!(
                label.lbl_repres,
                super::decl::RecordRepresentation::RecordRegular
            ) {
                all_regular = false;
            }
        }

        Self {
            label_positions: Arc::new(label_positions),
            mandatory_count,
            has_optional,
            has_dotdotdot,
            all_regular,
        }
    }

    #[inline]
    pub(crate) fn label_index(&self, name: &str) -> Option<usize> {
        self.label_positions.get(name).copied()
    }

    #[inline]
    pub(crate) fn contains_label(&self, name: &str) -> bool {
        self.label_positions.contains_key(name)
    }
}

fn normalize_component_cache_path(path: Path) -> Path {
    match path {
        Path::Pident(_) => path,
        Path::Pdot(parent, name, _) => {
            // OCaml compiler/ml/path.ml:20-24 ignores `Pdot` positions in
            // `Path.same`; component lookup in env.ml:781-793 keys module
            // identity by that path equality while still carrying positions in
            // the selected access path. Mirror that only for Rust's cache key.
            Path::pdot(
                normalize_component_cache_path(parent.as_ref().clone()),
                name,
            )
        }
        Path::Papply(functor, arg) => Path::papply(
            normalize_component_cache_path(functor.as_ref().clone()),
            normalize_component_cache_path(arg.as_ref().clone()),
        ),
    }
}

/// Type checking context.
///
/// This context is created for each type checking session (typically one
/// per source file). It owns all type expressions and maintains the state
/// needed for type inference.
///
/// # Example
///
/// ```rust,ignore
/// use rescript_compiler::types::TypeContext;
/// use rescript_compiler::context::IdGenerator;
///
/// let id_gen = IdGenerator::new();
/// let mut ctx = TypeContext::new(std::sync::Arc::new(id_gen));
///
/// // Create a type variable
/// let tvar = ctx.new_var(None);
///
/// // Create an arrow type
/// let int_type = ctx.new_constr(path_int, vec![]);
/// let func_type = ctx.new_arrow(tvar, int_type);
/// ```
pub struct TypeContext {
    /// ID generator for type IDs.
    /// Owned by `Arc` so the context can outlive its caller and live in
    /// thread-local worker storage (where a borrow can't be expressed).
    id_gen: Arc<IdGenerator>,

    /// Current generalization level
    current_level: Cell<i32>,

    /// Non-generalizable level
    nongen_level: Cell<i32>,

    /// Global level
    global_level: Cell<i32>,

    /// Saved levels stack
    saved_levels: RefCell<Vec<(i32, i32)>>,

    /// GADT instance tracking flag
    trace_gadt_instances: Cell<bool>,

    /// Dedicated memo ref for OCaml's simple_abbrevs (nullary, non-object
    /// abbreviations). This points to a mutable AbbrevMemo cell.
    simple_abbrevs: Cell<AbbrevMemoRef>,
    /// Counters for OCaml `Ctype.get_new_abstract_name` when reifying local
    /// GADT constraint variables.
    reified_var_counters: RefCell<ahash::AHashMap<String, usize>>,
    /// Previous env ID for check_abbrev_env (OCaml ctype.ml:1272)
    previous_env_id: Cell<u64>,

    /// Current abbreviation context during subst (OCaml: abbreviations = ref (ref Mnil)).
    /// Set during subst_with_memo so copy_type_cached can use find_repr to detect
    /// previously-expanded types and create Tlink sharing.
    current_abbreviations: Cell<AbbrevMemoRef>,

    /// Type expression storage. Uses UnsafeCell-based arena for zero-copy access.
    types: TypeArena,

    /// Cached value of `RESCRIPT_COMPILER_COUNTERS` for hot-path probes.
    compiler_counters_enabled: bool,

    /// Abbreviation memo storage
    abbrevs: RefCell<Vec<RefCell<AbbrevMemo>>>,
    /// Refs that have been written via memorize_abbrev_expansion since the
    /// last cleanup. Mirrors OCaml btype.ml `memo` list used by cleanup_abbrev.
    memoized_abbrev_refs: RefCell<Vec<AbbrevMemoRef>>,

    /// Row field storage
    row_fields: RefCell<Vec<RefCell<Option<RowField>>>>,

    /// Commutable storage
    commutables: RefCell<Vec<RefCell<Commutable>>>,

    /// Field kind storage
    field_kinds: RefCell<Vec<RefCell<Option<FieldKind>>>>,

    /// Global type declaration store, indexed by type name.
    /// Populated when loading CMI module signatures so that type alias
    /// expansion can find declarations for types not directly in the env.
    type_decl_store: RefCell<ahash::AHashMap<String, super::decl::TypeDeclaration>>,

    /// Global type declaration store, indexed by ident stamp.
    /// Used for looking up CMI-loaded type declarations by their stamp
    /// when the type name is too generic (e.g., "t").
    type_decl_by_stamp: RefCell<ahash::AHashMap<i32, super::decl::TypeDeclaration>>,

    /// Global type declaration store, indexed by full qualified path string.
    /// Used for looking up types via Pdot paths (e.g., "Js.Promise.t").
    type_decl_by_path: RefCell<ahash::AHashMap<String, super::decl::TypeDeclaration>>,
    type_item_by_path: RefCell<ahash::AHashMap<String, (Ident, super::decl::TypeDeclaration)>>,
    missing_type_item_by_path: RefCell<ahash::AHashSet<String>>,

    /// Cache for type declarations resolved through module signatures (Pdot paths).
    /// Separate from type_decl_by_path to avoid conflicts with expand_head_once
    /// entries which have unqualified paths. This approximates OCaml's
    /// components_of_module_maker lazy caching.
    resolved_pdot_type_cache: RefCell<ahash::AHashMap<String, Arc<super::decl::TypeDeclaration>>>,

    /// Cache for resolved module signatures. Keyed by module path name.
    /// OCaml `compiler/ml/env.ml:1513-1514,1516-1588` stores forced module
    /// components behind lazy cells; cache hits share the already-substituted
    /// signature snapshot instead of cloning every `SignatureItem`.
    resolved_module_sig_cache:
        RefCell<ahash::AHashMap<String, (Path, Arc<super::decl::Signature>)>>,

    /// Cached qualified module-component views keyed by access-path semantics.
    /// This is the Rust analogue of OCaml's lazy `components_of_module_maker`.
    qualified_module_components_cache: RefCell<
        ahash::AHashMap<
            QualifiedModuleComponentsCacheKey,
            Arc<super::env_lazy::QualifiedModuleComponents>,
        >,
    >,

    /// Module alias source paths discovered while building component tables.
    ///
    /// OCaml compiler/ml/env.ml:1517 scrapes `Mty_alias`/`Mty_ident` through
    /// `find_module`, and env.ml:1530-1578 stores component thunks under the
    /// selected path returned by `prefix_idents`. This relation keeps that
    /// declaration-derived source path available when Rust later reaches a
    /// cached component view without `PersistentEnv`; it must not be inferred
    /// from flattened module-name spelling.
    component_alias_sources: RefCell<ahash::AHashMap<Path, Vec<Path>>>,
    component_paths_by_alias_source: RefCell<ahash::AHashMap<Path, Vec<Path>>>,

    /// Cached dotted value lookups keyed by resolved module access path.
    resolved_module_value_cache: RefCell<
        ahash::AHashMap<Path, ahash::AHashMap<String, (Path, super::decl::ValueDescription)>>,
    >,

    /// Cached dotted type lookups keyed by resolved module access path.
    resolved_module_type_cache: RefCell<
        ahash::AHashMap<
            Path,
            ahash::AHashMap<String, (Path, Ident, Arc<super::decl::TypeDeclaration>)>,
        >,
    >,

    /// Cached child-module access paths keyed by resolved parent access path.
    resolved_child_module_path_cache: RefCell<ahash::AHashMap<Path, ahash::AHashMap<String, Path>>>,

    /// Cached forced module declarations from qualified component tables.
    qualified_module_decl_cache: RefCell<
        ahash::AHashMap<
            Path,
            ahash::AHashMap<String, (Ident, Arc<super::decl::ModuleDeclaration>)>,
        >,
    >,

    /// Cached full normalize_path results keyed by environment identity.
    normalized_path_full_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,

    /// Cached side-effectful normalize_path results keyed by environment identity.
    forced_normalized_path_full_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,

    /// Cached side-effectful type-path comparisons keyed by environment identity.
    forced_type_path_compare_cache: RefCell<ahash::AHashMap<(u64, Path, Path), bool>>,

    /// Load paths for resolving CMI files during type alias expansion.
    load_paths: RefCell<Vec<std::path::PathBuf>>,

    /// In-process persistent environment used by abbreviation expansion when a
    /// persistent module root is not present in the local Env. OCaml resolves
    /// persistent Pident module heads through Env.find_module_descr before
    /// reading lazy components (compiler/ml/env.ml:800-808,
    /// compiler/ml/env.ml:865-906); this gives Rust ctype the same lookup
    /// source without falling back to disk in in-process builds.
    persistent_env: RefCell<Option<crate::cmi::persistent_env::PersistentEnv>>,

    /// Cache of renamed module signatures.
    /// Matches OCaml's lazy ps_sig = Subst.signature Subst.identity sign.
    /// Populated by PersistentEnv::get_renamed_sig, consumed by normalize_path.
    pub(crate) renamed_module_sigs: RefCell<ahash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// Raw (un-renamed) module signatures for persistent modules.
    /// Used by trigger_module_sig_rename to lazily rename on first access
    /// from normalize_path, matching OCaml's lazy ps_sig forcing.
    raw_module_sigs: RefCell<ahash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// Raw signature copies used only by GenType's CMT-shaped alias scraping.
    ///
    /// OCaml GenType reads CMT data and then calls Env.scrape_alias at
    /// compiler/gentype/TranslateStructure.ml:174-183. In-process Rust crosses
    /// TypeContext boundaries through PortablePersStruct, so keep those raw
    /// copied signatures separate from `raw_module_sigs`; typechecking lookup
    /// paths expect the normal component/rename caches, not this CMT view.
    gentype_raw_module_sigs: RefCell<ahash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// Raw signatures loaded only for persistent component lookup.
    ///
    /// OCaml keeps `ps_comps` separate from `ps_sig`; this cache gives Rust the
    /// same one-shot component backing store without making
    /// `trigger_all_module_sig_renames` see modules that were only touched by
    /// descriptor lookup.
    raw_component_module_sigs: RefCell<ahash::AHashMap<String, Arc<super::decl::Signature>>>,

    /// String table for CMI-decoded Longident components.
    /// CMI decoding happens without a ParseArena, so we allocate synthetic
    /// StrIdx values here and resolve them later when needed.
    cmi_longident_names: RefCell<ahash::AHashMap<u32, String>>,

    /// String table for ParseArena Longident components whose StrIdx values are
    /// intentionally unique per source occurrence for marshal identity.
    arena_longident_names: RefCell<ahash::AHashMap<u32, String>>,

    /// Next synthetic StrIdx raw value for CMI longident strings.
    next_cmi_longident_idx: Cell<u32>,

    /// Cached predef type singletons at generic_level.
    /// Matches OCaml's Predef.type_int etc. which are module-level singletons
    /// created via newgenty at generic_level. Lazily initialized on first use.
    predef_int: Cell<Option<TypeExprRef>>,
    predef_char: Cell<Option<TypeExprRef>>,
    predef_string: Cell<Option<TypeExprRef>>,
    predef_float: Cell<Option<TypeExprRef>>,
    predef_bool: Cell<Option<TypeExprRef>>,
    predef_unit: Cell<Option<TypeExprRef>>,
    predef_exn: Cell<Option<TypeExprRef>>,
    predef_bigint: Cell<Option<TypeExprRef>>,
    predef_option_inner: Cell<Option<TypeExprRef>>,
    predef_option_type: Cell<Option<TypeExprRef>>,

    /// Arity update aliases: maps arity-updated TypeExprRef → original TypeExprRef.
    /// OCaml's `{t with desc = Tarrow(..., Some newarity)}` creates a new record
    /// sharing `t.id`, so the sexp serializer deduplicates them. In Rust, we create
    /// separate TypeExprRef nodes but record the alias here so the sexp serializer
    /// can use the original's dedup key.
    arity_aliases: RefCell<ahash::AHashMap<TypeExprRef, TypeExprRef>>,

    /// Record type labels cache.
    /// Maps type path (with stamp for uniqueness) → Vec<(field_name, position, mutable, repr, attributes)>.
    /// Populated during type checking when record patterns are processed.
    /// Used by raw lambda conversion to bind ALL record fields (matching OCaml's make_record_matching).
    record_labels_cache: RefCell<
        ahash::AHashMap<
            Path,
            Vec<(
                String,
                i32,
                super::asttypes::MutableFlag,
                super::decl::RecordRepresentation,
                Vec<super::decl::Attribute>,
            )>,
        >,
    >,

    /// Reconstructed record label descriptions keyed by type path.
    /// OCaml installs one shared `lbl_all` array for a record declaration and
    /// reuses it from record typing (`compiler/ml/typecore.ml:2802,2833-2842`).
    /// Rust reconstructs fallback label descriptions from declarations, so cache
    /// that reconstructed array per TypeContext and share it across record
    /// literals instead of rebuilding or cloning large records such as
    /// `JsxDOM.domProps` for every JSX literal.
    record_label_descriptions_cache:
        RefCell<ahash::AHashMap<super::path::Path, Arc<Vec<super::decl::LabelDescription>>>>,
    record_label_description_summaries_cache:
        RefCell<ahash::AHashMap<super::path::Path, Arc<RecordLabelDescriptionSummary>>>,

    /// Qualified persistent record labels keyed by environment and label slot.
    /// OCaml caches module components with already-substituted `lbl_all`
    /// descriptors (compiler/ml/env.ml:1513-1514,1542-1548); this avoids
    /// repeatedly copying the same persistent JSX prop label skeleton before
    /// each `instance_label` call.
    qualified_record_label_cache:
        RefCell<ahash::AHashMap<QualifiedRecordLabelCacheKey, super::decl::LabelDescription>>,

    /// Synthetic dict-pattern labels created by type-directed label lookup.
    /// OCaml mutates `lbl_all` on the predefined dict magic field as each dict
    /// pattern field is resolved; we model that with an append-only side table.
    dict_pattern_labels_cache: RefCell<
        Vec<(
            String,
            i32,
            super::asttypes::MutableFlag,
            super::decl::RecordRepresentation,
            Vec<super::decl::Attribute>,
        )>,
    >,

    /// Lident indices synthesized while filling omitted optional record fields.
    /// This avoids repeated reverse scans through the parse arena for large JSX
    /// DOM prop records while preserving the same index that the scan found.
    synthesized_record_lidents: RefCell<ahash::AHashMap<String, LidentIdx>>,

    /// Stored typedtree environment snapshots, keyed by EnvRef.
    typed_envs: RefCell<Vec<Arc<Env>>>,

    /// Reuse EnvRefs for identical logical environments.
    typed_envs_by_id: RefCell<ahash::AHashMap<u64, EnvRef>>,
}

fn push_unique_path(paths: &mut Vec<Path>, path: Path) {
    if !paths.iter().any(|existing| existing.same(&path)) {
        paths.push(path);
    }
}

impl TypeContext {
    /// Create a new type context.
    pub fn new(id_gen: Arc<IdGenerator>) -> Self {
        TypeContext {
            id_gen,
            current_level: Cell::new(0),
            nongen_level: Cell::new(0),
            global_level: Cell::new(1),
            saved_levels: RefCell::new(Vec::new()),
            trace_gadt_instances: Cell::new(false),
            simple_abbrevs: Cell::new(AbbrevMemoRef(1)),
            reified_var_counters: RefCell::new(ahash::AHashMap::new()),
            previous_env_id: Cell::new(0),
            current_abbreviations: Cell::new(AbbrevMemoRef::nil()),
            types: TypeArena::new(),
            compiler_counters_enabled: crate::perf_counters::enabled(),
            // Index 0 is reserved as canonical Mnil; index 1 is the dedicated
            // simple_abbrevs memo ref.
            abbrevs: RefCell::new(vec![
                RefCell::new(AbbrevMemo::Mnil),
                RefCell::new(AbbrevMemo::Mnil),
            ]),
            memoized_abbrev_refs: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            commutables: RefCell::new(Vec::new()),
            field_kinds: RefCell::new(Vec::new()),
            type_decl_store: RefCell::new(ahash::AHashMap::new()),
            type_decl_by_stamp: RefCell::new(ahash::AHashMap::new()),
            type_decl_by_path: RefCell::new(ahash::AHashMap::new()),
            type_item_by_path: RefCell::new(ahash::AHashMap::new()),
            missing_type_item_by_path: RefCell::new(ahash::AHashSet::new()),
            resolved_pdot_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_sig_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_module_components_cache: RefCell::new(ahash::AHashMap::new()),
            component_alias_sources: RefCell::new(ahash::AHashMap::new()),
            component_paths_by_alias_source: RefCell::new(ahash::AHashMap::new()),
            resolved_module_value_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_child_module_path_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_module_decl_cache: RefCell::new(ahash::AHashMap::new()),
            normalized_path_full_cache: RefCell::new(ahash::AHashMap::new()),
            forced_normalized_path_full_cache: RefCell::new(ahash::AHashMap::new()),
            forced_type_path_compare_cache: RefCell::new(ahash::AHashMap::new()),
            load_paths: RefCell::new(Vec::new()),
            persistent_env: RefCell::new(None),
            renamed_module_sigs: RefCell::new(ahash::AHashMap::new()),
            raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            gentype_raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            raw_component_module_sigs: RefCell::new(ahash::AHashMap::new()),
            cmi_longident_names: RefCell::new(ahash::AHashMap::new()),
            arena_longident_names: RefCell::new(ahash::AHashMap::new()),
            next_cmi_longident_idx: Cell::new(0xF000_0000),
            predef_int: Cell::new(None),
            predef_char: Cell::new(None),
            predef_string: Cell::new(None),
            predef_float: Cell::new(None),
            predef_bool: Cell::new(None),
            predef_unit: Cell::new(None),
            predef_exn: Cell::new(None),
            predef_bigint: Cell::new(None),
            predef_option_inner: Cell::new(None),
            predef_option_type: Cell::new(None),
            arity_aliases: RefCell::new(ahash::AHashMap::new()),
            record_labels_cache: RefCell::new(ahash::AHashMap::new()),
            record_label_descriptions_cache: RefCell::new(ahash::AHashMap::new()),
            record_label_description_summaries_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_record_label_cache: RefCell::new(ahash::AHashMap::new()),
            dict_pattern_labels_cache: RefCell::new(Vec::new()),
            synthesized_record_lidents: RefCell::new(ahash::AHashMap::new()),
            typed_envs: RefCell::new(Vec::new()),
            typed_envs_by_id: RefCell::new(ahash::AHashMap::new()),
        }
    }

    /// Store a typedtree environment snapshot and return a stable reference.
    pub fn store_typed_env(&self, env: &Env) -> EnvRef {
        if let Some(existing) = self.typed_envs_by_id.borrow().get(&env.id()).copied() {
            return existing;
        }

        let env_ref = {
            let mut typed_envs = self.typed_envs.borrow_mut();
            let env_ref = EnvRef::from_usize(typed_envs.len());
            typed_envs.push(Arc::new(env.clone_preserve_id()));
            env_ref
        };
        self.typed_envs_by_id.borrow_mut().insert(env.id(), env_ref);
        env_ref
    }

    /// Resolve a typedtree environment reference.
    pub fn get_typed_env(&self, env_ref: EnvRef) -> Option<Arc<Env>> {
        self.typed_envs.borrow().get(env_ref.index()).cloned()
    }

    #[inline]
    pub(crate) fn compiler_counters_enabled(&self) -> bool {
        self.compiler_counters_enabled
    }

    /// Intern a CMI longident component and return a synthetic StrIdx.
    pub fn intern_cmi_longident_name(&self, name: &str) -> StrIdx {
        let raw = self.next_cmi_longident_idx.get();
        self.next_cmi_longident_idx.set(raw.wrapping_add(1));
        self.cmi_longident_names
            .borrow_mut()
            .insert(raw, name.to_string());
        StrIdx::from_raw(raw)
    }

    pub(crate) fn cmi_longident_component_name(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_names.borrow().get(&idx.raw()).cloned()
    }

    /// Resolve a Longident component StrIdx to string, checking CMI synthetic
    /// indices first and falling back to the parse arena interner.
    pub fn resolve_longident_component(
        &self,
        arena: &crate::parse_arena::ParseArena,
        idx: StrIdx,
    ) -> String {
        self.cmi_longident_names
            .borrow()
            .get(&idx.raw())
            .cloned()
            .unwrap_or_else(|| arena.get_string(idx).to_string())
    }

    pub fn resolve_cmi_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_names.borrow().get(&idx.raw()).cloned()
    }

    pub(crate) fn register_arena_longident_names(&self, arena: &crate::parse_arena::ParseArena) {
        let mut names = self.arena_longident_names.borrow_mut();
        for raw in 0..arena.string_count() {
            let idx = StrIdx::from_raw(raw as u32);
            names
                .entry(raw as u32)
                .or_insert_with(|| arena.get_string(idx).to_string());
        }
    }

    pub(crate) fn resolve_any_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_names
            .borrow()
            .get(&idx.raw())
            .cloned()
            .or_else(|| self.arena_longident_names.borrow().get(&idx.raw()).cloned())
    }

    /// Snapshot synthetic CMI longident component names so portable signatures
    /// can move across TypeContexts without losing the side table.
    pub fn snapshot_cmi_longident_names(&self) -> Vec<(u32, String)> {
        self.cmi_longident_names
            .borrow()
            .iter()
            .map(|(raw, name)| (*raw, name.clone()))
            .collect()
    }

    /// Import synthetic CMI longident names from a portable signature.
    pub fn import_cmi_longident_names(&self, names: &[(u32, String)]) {
        let mut table = self.cmi_longident_names.borrow_mut();
        let mut next = self.next_cmi_longident_idx.get();
        for (raw, name) in names {
            table.insert(*raw, name.clone());
            if *raw >= next {
                next = raw.wrapping_add(1);
            }
        }
        self.next_cmi_longident_idx.set(next);
    }

    /// Register a type declaration for type alias expansion.
    /// Called when loading module signatures from CMI files.
    pub fn register_type_decl(&self, name: &str, decl: super::decl::TypeDeclaration) {
        self.type_decl_store
            .borrow_mut()
            .insert(name.to_string(), decl);
    }

    /// Register a type declaration by ident stamp for alias expansion.
    pub fn register_type_decl_by_stamp(&self, stamp: i32, decl: super::decl::TypeDeclaration) {
        self.type_decl_by_stamp.borrow_mut().insert(stamp, decl);
    }

    /// Match OCaml `Ctype.get_new_abstract_name`.
    pub(crate) fn next_reified_abstract_name(&self, prefix: &str) -> String {
        let mut counters = self.reified_var_counters.borrow_mut();
        let index = counters.get(prefix).map_or(0, |previous| previous + 1);
        counters.insert(prefix.to_string(), index);
        if index == 0 && !prefix.is_empty() && !prefix.ends_with('$') {
            prefix.to_string()
        } else {
            format!("{prefix}{index}")
        }
    }

    /// Look up a type declaration by name from the global store.
    pub fn find_type_decl(
        &self,
        name: &str,
    ) -> Option<std::cell::Ref<'_, super::decl::TypeDeclaration>> {
        let store = self.type_decl_store.borrow();
        if store.contains_key(name) {
            Some(std::cell::Ref::map(store, |s| s.get(name).unwrap()))
        } else {
            None
        }
    }

    /// Look up a type declaration by stamp from the global store.
    pub fn find_type_decl_by_stamp(
        &self,
        stamp: i32,
    ) -> Option<std::cell::Ref<'_, super::decl::TypeDeclaration>> {
        let store = self.type_decl_by_stamp.borrow();
        if store.contains_key(&stamp) {
            Some(std::cell::Ref::map(store, |s| s.get(&stamp).unwrap()))
        } else {
            None
        }
    }

    /// Register a type declaration by full qualified path string for alias expansion.
    pub fn register_type_decl_by_path(&self, path: &str, decl: super::decl::TypeDeclaration) {
        self.type_decl_by_path
            .borrow_mut()
            .insert(path.to_string(), decl);
    }

    pub(crate) fn register_type_item_by_path(
        &self,
        path: &str,
        id: Ident,
        decl: super::decl::TypeDeclaration,
    ) {
        self.type_item_by_path
            .borrow_mut()
            .insert(path.to_string(), (id, decl));
    }

    pub(crate) fn find_type_item_by_path(
        &self,
        path: &str,
    ) -> Option<(Ident, super::decl::TypeDeclaration)> {
        self.type_item_by_path.borrow().get(path).cloned()
    }

    pub(crate) fn register_missing_type_item_by_path(&self, path: &str) {
        self.missing_type_item_by_path
            .borrow_mut()
            .insert(path.to_string());
    }

    pub(crate) fn is_missing_type_item_by_path(&self, path: &str) -> bool {
        self.missing_type_item_by_path.borrow().contains(path)
    }

    /// Cache a type declaration resolved through module signatures (Pdot paths).
    pub fn register_resolved_pdot_type(&self, path: &str, decl: Arc<super::decl::TypeDeclaration>) {
        self.resolved_pdot_type_cache
            .borrow_mut()
            .insert(path.to_string(), decl);
    }

    /// Look up a cached resolved Pdot type declaration.
    pub fn find_resolved_pdot_type(&self, path: &str) -> Option<Arc<super::decl::TypeDeclaration>> {
        self.resolved_pdot_type_cache.borrow().get(path).cloned()
    }

    /// Cache a resolved module signature.
    pub fn register_resolved_module_sig(
        &self,
        path: &str,
        access_path: Path,
        sig: Arc<super::decl::Signature>,
    ) {
        self.resolved_module_sig_cache
            .borrow_mut()
            .insert(path.to_string(), (access_path, sig));
    }

    /// Look up a cached resolved module signature.
    pub fn find_resolved_module_sig(
        &self,
        path: &str,
    ) -> Option<(Path, Arc<super::decl::Signature>)> {
        self.resolved_module_sig_cache.borrow().get(path).cloned()
    }

    /// Cache a lazily-built qualified module-components view.
    pub(crate) fn register_qualified_module_components(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: super::env_lazy::QualifiedModuleComponents,
    ) {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_registered();
        }
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, Arc::new(components));
    }

    /// Borrow a cached qualified module-components view.
    /// OCaml stores lazy module components once and keeps that table visible to
    /// recursive lookup while forcing nested thunks (compiler/ml/env.ml:1513-1514,
    /// 1516-1588). Borrow the cached view directly; the view itself owns the
    /// shared lazy component state needed by recursive lookups.
    pub(crate) fn with_qualified_module_components<R>(
        &self,
        key: &QualifiedModuleComponentsCacheKey,
        f: impl FnOnce(&super::env_lazy::QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        let cache = self.qualified_module_components_cache.borrow();
        let Some(components) = cache.get(key) else {
            if self.compiler_counters_enabled {
                crate::perf_counters::record_qualified_component_miss();
            }
            return None;
        };
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_hit();
        }
        Some(f(components.as_ref()))
    }

    pub(crate) fn has_qualified_module_components(
        &self,
        key: &QualifiedModuleComponentsCacheKey,
    ) -> bool {
        // OCaml compiler/ml/env.ml:781-793 lets `find_module_descr` reuse
        // `ps_comps` without forcing `ps_sig`; Rust stores that selected
        // component view explicitly, so later normalization can observe that
        // the component table is already available.
        self.qualified_module_components_cache
            .borrow()
            .contains_key(key)
    }

    pub(crate) fn register_component_alias_source(&self, component_path: Path, alias_source: Path) {
        // OCaml compiler/ml/env.ml:1440-1446 scrapes aliases by resolving the
        // target path through `find_module`; env.ml:1530 then prefixes the
        // selected component path. Record exactly that pair so later helpers
        // recover alias identity from declarations, not from name spelling.
        let mut alias_sources = vec![alias_source];
        for backing_source in self.flattened_backing_sources_for_alias_source(&alias_sources[0]) {
            if !alias_sources
                .iter()
                .any(|source| source.same(&backing_source))
            {
                alias_sources.push(backing_source);
            }
        }

        for alias_source in alias_sources {
            let component_key = {
                let by_component = self.component_alias_sources.borrow();
                by_component
                    .keys()
                    .find(|existing| existing.same(&component_path))
                    .cloned()
                    .unwrap_or_else(|| component_path.clone())
            };
            let mut by_component = self.component_alias_sources.borrow_mut();
            push_unique_path(
                by_component.entry(component_key).or_default(),
                alias_source.clone(),
            );

            let source_key = {
                let by_source = self.component_paths_by_alias_source.borrow();
                by_source
                    .keys()
                    .find(|existing| existing.same(&alias_source))
                    .cloned()
                    .unwrap_or_else(|| alias_source.clone())
            };
            let mut by_source = self.component_paths_by_alias_source.borrow_mut();
            push_unique_path(
                by_source.entry(source_key).or_default(),
                component_path.clone(),
            );
        }
    }

    fn flattened_backing_sources_for_alias_source(&self, alias_source: &Path) -> Vec<Path> {
        let Ok((head, components)) = alias_source.flatten() else {
            return Vec::new();
        };
        if components.is_empty() {
            return Vec::new();
        }

        let persistent_env = self.persistent_env.borrow();
        let Some(pers) = persistent_env.as_ref() else {
            return Vec::new();
        };

        let mut sources = Vec::new();
        for split in 1..=components.len() {
            let mut qualified_prefix = Path::pident(head.clone());
            for component in &components[..split] {
                qualified_prefix = Path::pdot(qualified_prefix, *component);
            }

            for flat_head in pers.flattened_alias_heads_for_path(&qualified_prefix) {
                let mut source = Path::pident(Ident::create_persistent(&flat_head));
                for component in &components[split..] {
                    source = Path::pdot(source, *component);
                }
                if !sources.iter().any(|existing: &Path| existing.same(&source)) {
                    sources.push(source);
                }
            }
        }
        sources
    }

    pub(crate) fn component_paths_for_alias_source(&self, alias_source: &Path) -> Vec<Path> {
        let mut paths = Vec::new();
        for (source, component_paths) in self.component_paths_by_alias_source.borrow().iter() {
            if source.same(alias_source) {
                for component_path in component_paths {
                    push_unique_path(&mut paths, component_path.clone());
                }
            }
        }
        paths
    }

    /// Return alias source paths that back a selected component path.
    ///
    /// This mirrors the source path selected by OCaml compiler/ml/env.ml:1513
    /// through `scrape_alias`, while env.ml:1573-1578 stores child
    /// declaration/component thunks under the selected access path.
    pub(crate) fn alias_sources_for_component_path(&self, component_path: &Path) -> Vec<Path> {
        let mut sources = Vec::new();
        for (path, alias_sources) in self.component_alias_sources.borrow().iter() {
            if path.same(component_path) {
                for alias_source in alias_sources {
                    push_unique_path(&mut sources, alias_source.clone());
                }
            }
        }
        sources
    }

    /// Look up a module alias target from the qualified module components cache.
    ///
    /// For a path like `Pdot(Pident("Js"), "Exn", _)`, checks whether `Js`'s
    /// qualified components contain `Exn` as a `MtyAlias`. If so, returns the
    /// alias target (e.g., `Pident("Stdlib_Exn")`).
    ///
    /// Used by `matching.rs` to resolve persistent module aliases without
    /// access to the full `PersistentEnv`.
    pub fn find_module_alias_in_components(
        &self,
        parent_path: &Path,
        module_name: &str,
    ) -> Option<Path> {
        let key = QualifiedModuleComponentsCacheKey::new(parent_path.clone(), None);
        self.with_qualified_module_components(&key, |components| {
            let (_, _, md) = components.lookup_module(module_name)?;
            match &md.md_type {
                super::decl::ModuleType::MtyAlias(_, target) => Some(target.clone()),
                super::decl::ModuleType::MtyIdent(target) => Some(target.clone()),
                _ => None,
            }
        })
        .flatten()
    }

    /// Cache a dotted value lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_value(
        &self,
        module_path: &Path,
        value_name: &str,
        path: Path,
        desc: super::decl::ValueDescription,
    ) {
        self.resolved_module_value_cache
            .borrow_mut()
            .entry(module_path.clone())
            .or_default()
            .insert(value_name.to_string(), (path, desc));
    }

    /// Look up a cached dotted value lookup for a resolved module access path.
    pub(crate) fn find_resolved_module_value(
        &self,
        module_path: &Path,
        value_name: &str,
    ) -> Option<(Path, super::decl::ValueDescription)> {
        self.resolved_module_value_cache
            .borrow()
            .get(module_path)
            .and_then(|values| values.get(value_name))
            .cloned()
    }

    /// Cache a dotted type lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_type(
        &self,
        module_path: &Path,
        type_name: &str,
        access_path: Path,
        id: Ident,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_module_type_cache
            .borrow_mut()
            .entry(module_path.clone())
            .or_default()
            .insert(type_name.to_string(), (access_path, id, decl));
    }

    /// Look up a cached dotted type lookup for a resolved module access path.
    pub(crate) fn find_resolved_module_type(
        &self,
        module_path: &Path,
        type_name: &str,
    ) -> Option<(Path, Ident, Arc<super::decl::TypeDeclaration>)> {
        self.resolved_module_type_cache
            .borrow()
            .get(module_path)
            .and_then(|types| types.get(type_name))
            .cloned()
    }

    /// Cache a resolved child-module access path.
    pub(crate) fn register_resolved_child_module_path(
        &self,
        parent_path: &Path,
        child_name: &str,
        child_path: Path,
    ) {
        self.resolved_child_module_path_cache
            .borrow_mut()
            .entry(parent_path.clone())
            .or_default()
            .insert(child_name.to_string(), child_path);
    }

    /// Look up a cached resolved child-module access path.
    pub(crate) fn find_resolved_child_module_path(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<Path> {
        self.resolved_child_module_path_cache
            .borrow()
            .get(parent_path)
            .and_then(|children| children.get(child_name))
            .cloned()
    }

    /// Cache a forced qualified module declaration.
    pub(crate) fn register_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
        id: Ident,
        md: Arc<super::decl::ModuleDeclaration>,
    ) {
        self.qualified_module_decl_cache
            .borrow_mut()
            .entry(parent_path.clone())
            .or_default()
            .insert(child_name.to_string(), (id, md));
    }

    /// Look up a forced qualified module declaration.
    pub(crate) fn find_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<(Ident, Arc<super::decl::ModuleDeclaration>)> {
        self.qualified_module_decl_cache
            .borrow()
            .get(parent_path)
            .and_then(|modules| modules.get(child_name))
            .cloned()
    }

    /// Cache a normalized path for a specific environment identity.
    pub(crate) fn register_normalized_path_full(
        &self,
        env_id: u64,
        original_path: &Path,
        normalized_path: Path,
    ) {
        self.normalized_path_full_cache
            .borrow_mut()
            .insert((env_id, original_path.clone()), normalized_path);
    }

    /// Look up a cached normalized path for a specific environment identity.
    pub(crate) fn find_normalized_path_full(
        &self,
        env_id: u64,
        original_path: &Path,
    ) -> Option<Path> {
        self.normalized_path_full_cache
            .borrow()
            .get(&(env_id, original_path.clone()))
            .cloned()
    }

    /// Cache a normalized path after the side-effectful normalize path has run.
    pub(crate) fn register_forced_normalized_path_full(
        &self,
        env_id: u64,
        original_path: &Path,
        normalized_path: Path,
    ) {
        self.forced_normalized_path_full_cache
            .borrow_mut()
            .insert((env_id, original_path.clone()), normalized_path);
    }

    /// Look up a side-effectful normalize path result for this environment.
    pub(crate) fn find_forced_normalized_path_full(
        &self,
        env_id: u64,
        original_path: &Path,
    ) -> Option<Path> {
        self.forced_normalized_path_full_cache
            .borrow()
            .get(&(env_id, original_path.clone()))
            .cloned()
    }

    /// Cache a side-effectful type-path comparison after the first comparison
    /// has already forced the same lazies OCaml would force at that call site.
    pub(crate) fn register_forced_type_path_compare(
        &self,
        env_id: u64,
        left: &Path,
        right: &Path,
        same: bool,
    ) {
        let mut cache = self.forced_type_path_compare_cache.borrow_mut();
        cache.insert((env_id, left.clone(), right.clone()), same);
        cache.insert((env_id, right.clone(), left.clone()), same);
    }

    /// Look up a side-effectful type-path comparison for this environment.
    pub(crate) fn find_forced_type_path_compare(
        &self,
        env_id: u64,
        left: &Path,
        right: &Path,
    ) -> Option<bool> {
        self.forced_type_path_compare_cache
            .borrow()
            .get(&(env_id, left.clone(), right.clone()))
            .copied()
    }

    /// Set load paths for resolving CMI files.
    pub fn set_load_paths(&self, paths: Vec<std::path::PathBuf>) {
        *self.load_paths.borrow_mut() = paths;
    }

    /// Get the load paths.
    pub fn load_paths(&self) -> std::cell::Ref<'_, Vec<std::path::PathBuf>> {
        self.load_paths.borrow()
    }

    pub(crate) fn set_persistent_env(&self, env: crate::cmi::persistent_env::PersistentEnv) {
        *self.persistent_env.borrow_mut() = Some(env);
    }

    pub(crate) fn persistent_env_clone(&self) -> Option<crate::cmi::persistent_env::PersistentEnv> {
        self.persistent_env.borrow().clone()
    }

    /// Drop the per-compile `PersistentEnv` reference held inside this
    /// `TypeContext` before the context is parked in worker thread-local
    /// storage. The shared `PersStruct` cache lives behind an `Arc` and
    /// outlives this drop; only the compile-scoped wrapper struct is
    /// released so the next compile can install its own.
    pub(crate) fn clear_persistent_env_for_park(&self) {
        *self.persistent_env.borrow_mut() = None;
    }

    pub(crate) fn persistent_env_is_in_process(&self) -> bool {
        self.persistent_env
            .borrow()
            .as_ref()
            .is_some_and(crate::cmi::persistent_env::PersistentEnv::is_in_process_mode)
    }

    /// Look up a type declaration by full qualified path string.
    pub fn find_type_decl_by_path(
        &self,
        path: &str,
    ) -> Option<std::cell::Ref<'_, super::decl::TypeDeclaration>> {
        let store = self.type_decl_by_path.borrow();
        if store.contains_key(path) {
            Some(std::cell::Ref::map(store, |s| s.get(path).unwrap()))
        } else {
            None
        }
    }

    // ========================================================================
    // Type Creation
    // ========================================================================

    /// Create a new type expression.
    fn alloc_type(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        let id = self.id_gen.next_type_id();
        self.types.push(TypeExpr::new(desc, level, id))
    }

    /// Create a new type at a specific level.
    pub fn alloc_type_at_level(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        self.alloc_type(desc, level)
    }

    /// Create a new type at the current level.
    pub fn new_type(&self, desc: TypeDesc) -> TypeExprRef {
        self.alloc_type(desc, self.current_level.get())
    }

    /// Create a new type at the generic level.
    pub fn new_generic_type(&self, desc: TypeDesc) -> TypeExprRef {
        self.alloc_type(desc, GENERIC_LEVEL)
    }

    /// Create a new type variable.
    pub fn new_var(&self, name: Option<String>) -> TypeExprRef {
        self.new_type(TypeDesc::Tvar(name))
    }

    /// Create a new type variable at the global level.
    pub fn new_global_var(&self, name: Option<String>) -> TypeExprRef {
        self.alloc_type(TypeDesc::Tvar(name), self.global_level.get())
    }

    /// Create a new generic type variable.
    pub fn new_generic_var(&self, name: Option<String>) -> TypeExprRef {
        self.new_generic_type(TypeDesc::Tvar(name))
    }

    /// Create an arrow (function) type.
    pub fn new_arrow(
        &self,
        arg_label: ArgLabel,
        arg_type: TypeExprRef,
        ret_type: TypeExprRef,
        arity: Option<i32>,
    ) -> TypeExprRef {
        let _ = arity;
        self.new_type(TypeDesc::Tarrow {
            args: vec![TypeArg::new(arg_label, arg_type)],
            ret: ret_type,
        })
    }

    pub(crate) fn new_arrow_with_commutable(
        &self,
        arg_label: ArgLabel,
        arg_type: TypeExprRef,
        ret_type: TypeExprRef,
        _commutable: Commutable,
        arity: Option<i32>,
    ) -> TypeExprRef {
        self.new_arrow(arg_label, arg_type, ret_type, arity)
    }

    /// Create an unlabeled arrow type.
    pub fn new_arrow_simple(&self, arg: TypeExprRef, ret: TypeExprRef) -> TypeExprRef {
        self.new_arrow(ArgLabel::Nolabel, arg, ret, None)
    }

    /// Create a tuple type.
    pub fn new_tuple(&self, types: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Ttuple(types))
    }

    /// Create a type constructor application.
    pub fn new_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.new_type(TypeDesc::Tconstr { path, args, abbrev })
    }

    /// Create a type constructor at generic level (for type schemes).
    pub fn new_generic_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.new_generic_type(TypeDesc::Tconstr { path, args, abbrev })
    }

    /// Get or create a cached predef singleton helper.
    fn get_or_create_predef(&self, cache: &Cell<Option<TypeExprRef>>, path: Path) -> TypeExprRef {
        if let Some(ty) = cache.get() {
            ty
        } else {
            let ty = self.new_generic_constr(path, vec![]);
            cache.set(Some(ty));
            ty
        }
    }

    /// Get the predef int singleton (generic_level).
    pub fn predef_int(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_int, super::predef::path_int())
    }
    /// Get the predef char singleton (generic_level).
    pub fn predef_char(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_char, super::predef::path_char())
    }
    /// Get the predef string singleton (generic_level).
    pub fn predef_string(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_string, super::predef::path_string())
    }
    /// Get the predef float singleton (generic_level).
    pub fn predef_float(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_float, super::predef::path_float())
    }
    /// Get the predef bool singleton (generic_level).
    pub fn predef_bool(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bool, super::predef::path_bool())
    }
    /// Get the predef unit singleton (generic_level).
    pub fn predef_unit(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_unit, super::predef::path_unit())
    }
    /// Get the predef exn singleton (generic_level).
    pub fn predef_exn(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_exn, super::predef::path_exn())
    }
    /// Get the predef bigint singleton (generic_level).
    pub fn predef_bigint(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bigint, super::predef::path_bigint())
    }

    /// Get the cached generic option constructor scheme types.
    /// Returns (`'a`, `option('a)`), both allocated once at generic level.
    pub fn predef_option_scheme(&self) -> (TypeExprRef, TypeExprRef) {
        match (
            self.predef_option_inner.get(),
            self.predef_option_type.get(),
        ) {
            (Some(inner), Some(option_ty)) => (inner, option_ty),
            _ => {
                let inner = self.new_generic_var(None);
                let option_ty = self.new_generic_constr(super::predef::path_option(), vec![inner]);
                self.predef_option_inner.set(Some(inner));
                self.predef_option_type.set(Some(option_ty));
                (inner, option_ty)
            }
        }
    }

    /// Create an arrow type at generic level (for type schemes).
    pub fn new_generic_arrow(
        &self,
        arg_label: ArgLabel,
        arg_type: TypeExprRef,
        ret_type: TypeExprRef,
        arity: Option<i32>,
    ) -> TypeExprRef {
        let _ = arity;
        self.new_generic_type(TypeDesc::Tarrow {
            args: vec![TypeArg::new(arg_label, arg_type)],
            ret: ret_type,
        })
    }

    /// Create a link type (for unification).
    pub fn new_link(&self, target: TypeExprRef) -> TypeExprRef {
        self.new_type(TypeDesc::Tlink(target))
    }

    /// Create a polymorphic type.
    pub fn new_poly(&self, body: TypeExprRef, vars: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Tpoly { body, vars })
    }

    /// Create a universal type variable.
    pub fn new_univar(&self, name: Option<String>) -> TypeExprRef {
        self.new_type(TypeDesc::Tunivar(name))
    }

    /// Create a variant type.
    pub fn new_variant(&self, row: RowDesc) -> TypeExprRef {
        self.new_type(TypeDesc::Tvariant(row))
    }

    // ========================================================================
    // Type Access
    // ========================================================================

    /// Get the descriptor of a type.
    /// Returns a cloned snapshot to avoid RefCell borrow conflicts when
    /// the desc is held across function calls that may modify the same node.
    #[inline]
    pub fn get_desc(&self, r: TypeExprRef) -> TypeDescSnapshot {
        TypeDescSnapshot(self.types.get(r).desc().clone())
    }

    /// Borrow the descriptor of a type without cloning it.
    ///
    /// Prefer this in short read-only hot paths. Use `get_desc()` when the
    /// descriptor must be held across code that may mutate the same type node.
    #[inline]
    pub fn borrow_desc(&self, r: TypeExprRef) -> TypeDescRef<'_> {
        self.types.get(r).desc()
    }

    /// Get the level of a type.
    #[inline]
    pub fn get_level(&self, r: TypeExprRef) -> i32 {
        self.types.get(r).level()
    }

    /// Number of allocated type expressions.
    pub fn type_expr_count(&self) -> usize {
        self.types.len()
    }

    /// Set the level of a type.
    #[inline]
    pub fn set_level(&self, r: TypeExprRef, level: i32) {
        self.types.get(r).set_level(level);
    }

    /// Set the descriptor of a type.
    #[inline]
    pub fn set_desc(&self, r: TypeExprRef, desc: TypeDesc) {
        self.types.get(r).set_desc(desc);
    }

    /// Save mutable type state before a speculative unification.
    ///
    /// OCaml compiler/ml/typecore.ml:3187-3211 and 3321-3329 use
    /// `Btype.snapshot`/`Btype.backtrack` (with saved Ctype levels) around
    /// unifications that may fail. Rust keeps type nodes in append-only
    /// arenas, so this snapshots mutable contents of pre-existing nodes and
    /// cells, while intentionally leaving newly allocated nodes and lazy
    /// environment caches alive after restore.
    pub(crate) fn snapshot_type_state(&self) -> TypeMutationSnapshot {
        let type_len = self.types.len();
        let mut type_states = Vec::with_capacity(type_len);
        for idx in 0..type_len {
            let ty = TypeExprRef::from_usize(idx);
            type_states.push((self.get_desc(ty).0, self.get_level(ty)));
        }

        let row_field_states = self
            .row_fields
            .borrow()
            .iter()
            .map(|cell| cell.borrow().clone())
            .collect();
        let abbrev_states = self
            .abbrevs
            .borrow()
            .iter()
            .map(|cell| cell.borrow().clone())
            .collect();

        TypeMutationSnapshot {
            type_states,
            row_field_states,
            abbrev_states,
            memoized_abbrev_refs: self.memoized_abbrev_refs.borrow().clone(),
            current_abbreviations: self.current_abbreviations.get(),
            current_level: self.current_level.get(),
            nongen_level: self.nongen_level.get(),
            global_level: self.global_level.get(),
            saved_levels: self.saved_levels.borrow().clone(),
        }
    }

    /// Restore a snapshot created by `snapshot_type_state`.
    pub(crate) fn restore_type_state(&self, snapshot: TypeMutationSnapshot) {
        for (idx, (desc, level)) in snapshot.type_states.into_iter().enumerate() {
            let ty = TypeExprRef::from_usize(idx);
            self.set_desc(ty, desc);
            self.set_level(ty, level);
        }

        {
            let row_fields = self.row_fields.borrow();
            for (idx, field) in snapshot.row_field_states.into_iter().enumerate() {
                if let Some(cell) = row_fields.get(idx) {
                    *cell.borrow_mut() = field;
                }
            }
        }

        {
            let abbrevs = self.abbrevs.borrow();
            for (idx, memo) in snapshot.abbrev_states.into_iter().enumerate() {
                if let Some(cell) = abbrevs.get(idx) {
                    *cell.borrow_mut() = memo;
                }
            }
        }

        *self.memoized_abbrev_refs.borrow_mut() = snapshot.memoized_abbrev_refs;
        self.current_abbreviations
            .set(snapshot.current_abbreviations);
        self.current_level.set(snapshot.current_level);
        self.nongen_level.set(snapshot.nongen_level);
        self.global_level.set(snapshot.global_level);
        *self.saved_levels.borrow_mut() = snapshot.saved_levels;
    }

    // ========================================================================
    // Arity Aliases (sexp dedup for update_uncurried_arity)
    // ========================================================================

    /// Record that `new_ref` is an arity-updated version of `original_ref`.
    /// The sexp serializer will use `original_ref` as the dedup key for both.
    pub fn set_arity_alias(&self, new_ref: TypeExprRef, original_ref: TypeExprRef) {
        self.arity_aliases
            .borrow_mut()
            .insert(new_ref, original_ref);
    }

    /// Get the arity alias for a TypeExprRef, if any.
    pub fn get_arity_alias(&self, te: TypeExprRef) -> Option<TypeExprRef> {
        self.arity_aliases.borrow().get(&te).copied()
    }

    /// Cache record label info for a type path.
    /// Called during type checking when record patterns are processed.
    pub fn register_record_labels(
        &self,
        type_path: &Path,
        labels: Vec<(
            String,
            i32,
            super::asttypes::MutableFlag,
            super::decl::RecordRepresentation,
            Vec<super::decl::Attribute>,
        )>,
    ) {
        self.record_labels_cache
            .borrow_mut()
            .insert(type_path.clone(), labels);
    }

    /// Look up cached record labels for a type path.
    pub fn get_record_labels(
        &self,
        type_path: &Path,
    ) -> Option<
        Vec<(
            String,
            i32,
            super::asttypes::MutableFlag,
            super::decl::RecordRepresentation,
            Vec<super::decl::Attribute>,
        )>,
    > {
        self.record_labels_cache
            .borrow()
            .get(type_path)
            .cloned()
    }

    /// Cache reconstructed record label descriptions for a type path.
    pub fn register_record_label_descriptions(
        &self,
        type_path: &Path,
        labels: Arc<Vec<super::decl::LabelDescription>>,
    ) {
        let summary = Arc::new(RecordLabelDescriptionSummary::from_labels(&labels));
        self.record_label_descriptions_cache
            .borrow_mut()
            .insert(type_path.clone(), labels);
        self.record_label_description_summaries_cache
            .borrow_mut()
            .insert(type_path.clone(), summary);
    }

    /// Look up reconstructed record label descriptions for a type path.
    pub fn get_record_label_descriptions(
        &self,
        type_path: &Path,
    ) -> Option<Arc<Vec<super::decl::LabelDescription>>> {
        self.record_label_descriptions_cache
            .borrow()
            .get(type_path)
            .cloned()
    }

    pub(crate) fn get_record_label_description_summary(
        &self,
        type_path: &Path,
    ) -> Option<Arc<RecordLabelDescriptionSummary>> {
        self.record_label_description_summaries_cache
            .borrow()
            .get(type_path)
            .cloned()
    }

    pub(crate) fn get_qualified_record_label(
        &self,
        env_id: u64,
        type_path: &Path,
        lbl_pos: i32,
    ) -> Option<super::decl::LabelDescription> {
        self.qualified_record_label_cache
            .borrow()
            .get(&QualifiedRecordLabelCacheKey::new(
                type_path.clone(),
                env_id,
                lbl_pos,
            ))
            .cloned()
    }

    pub(crate) fn cache_qualified_record_label(
        &self,
        env_id: u64,
        type_path: &Path,
        lbl_pos: i32,
        label: super::decl::LabelDescription,
    ) {
        self.qualified_record_label_cache.borrow_mut().insert(
            QualifiedRecordLabelCacheKey::new(type_path.clone(), env_id, lbl_pos),
            label,
        );
    }

    /// Return a cached synthesized record-field lident by label name.
    pub fn get_synthesized_record_lident(&self, label_name: &str) -> Option<LidentIdx> {
        self.synthesized_record_lidents
            .borrow()
            .get(label_name)
            .copied()
    }

    /// Cache the lident chosen for a synthesized record field.
    pub fn cache_synthesized_record_lident(&self, label_name: String, lid: LidentIdx) {
        self.synthesized_record_lidents
            .borrow_mut()
            .entry(label_name)
            .or_insert(lid);
    }

    /// Replace the synthetic dict-pattern label cache.
    pub fn set_dict_pattern_labels(
        &self,
        labels: Vec<(
            String,
            i32,
            super::asttypes::MutableFlag,
            super::decl::RecordRepresentation,
            Vec<super::decl::Attribute>,
        )>,
    ) {
        *self.dict_pattern_labels_cache.borrow_mut() = labels;
    }

    /// Snapshot the synthetic dict-pattern labels created so far.
    pub fn get_dict_pattern_labels(
        &self,
    ) -> Vec<(
        String,
        i32,
        super::asttypes::MutableFlag,
        super::decl::RecordRepresentation,
        Vec<super::decl::Attribute>,
    )> {
        self.dict_pattern_labels_cache.borrow().clone()
    }

    // ========================================================================
    // Simple Abbreviations (cross-instance sharing for nullary Tconstr)
    // ========================================================================

    /// OCaml's check_abbrev_env: clear abbreviation cache when environment changes.
    /// OCaml calls cleanup_abbrev() which clears ALL registered memo refs including
    /// simple_abbrevs when it has memoized entries.
    /// OCaml uses physical env inequality (!=); Rust uses env ID comparison.
    pub fn check_abbrev_env(&self, env: &crate::types::env::Env) {
        let env_id = env.id();
        if env_id != self.previous_env_id.get() {
            self.clear_abbrev_memos();
            self.previous_env_id.set(env_id);
        }
    }

    /// Access the dedicated simple_abbrevs memo reference.
    pub fn simple_abbrevs_memo(&self) -> AbbrevMemoRef {
        self.simple_abbrevs.get()
    }

    /// Clear simple abbreviations. Called during generalize/generalize_structure,
    /// matching OCaml's `simple_abbrevs := Mnil`.
    pub fn clear_simple_abbrevs(&self) {
        let simple = self.simple_abbrevs.get();
        if simple != AbbrevMemoRef::nil() {
            self.clear_abbrev_memo(simple);
        }
    }

    /// Clear all per-node abbreviation memo chains (OCaml cleanup_abbrev).
    pub fn clear_abbrev_memos(&self) {
        let refs = self.memoized_abbrev_refs.borrow().clone();
        let abbrevs = self.abbrevs.borrow();
        for memo in refs {
            if let Some(cell) = abbrevs.get(memo.index()) {
                *cell.borrow_mut() = AbbrevMemo::Mnil;
            }
        }
        drop(abbrevs);
        self.memoized_abbrev_refs.borrow_mut().clear();
    }

    /// Get the current abbreviation context (set during subst_with_memo).
    pub fn current_abbreviations(&self) -> AbbrevMemoRef {
        self.current_abbreviations.get()
    }

    /// Set the current abbreviation context.
    pub fn set_current_abbreviations(&self, abbrev: AbbrevMemoRef) {
        self.current_abbreviations.set(abbrev);
    }

    /// Find a cached expansion for `(priv,path)` in an abbreviation memo chain.
    pub fn find_abbrev_expansion(
        &self,
        memo: AbbrevMemoRef,
        private_flag: PrivateFlag,
        path: &Path,
    ) -> Option<TypeExprRef> {
        let mut current = memo;
        for _ in 0..128 {
            let node = {
                let abbrevs = self.abbrevs.borrow();
                abbrevs
                    .get(current.index())
                    .map(|cell| cell.borrow().clone())
                    .unwrap_or(AbbrevMemo::Mnil)
            };
            match node {
                AbbrevMemo::Mnil => return None,
                AbbrevMemo::Mcons {
                    private_flag: cached_private,
                    path: cached_path,
                    expansion,
                    next,
                    ..
                } => {
                    if private_flag <= cached_private && path.same(&cached_path) {
                        return Some(expansion);
                    }
                    current = next;
                }
                AbbrevMemo::Mlink(next) => {
                    current = next;
                }
            }
        }
        None
    }

    /// Find the original type (abbrev field) for a path in a memo chain.
    /// This is OCaml's `find_repr` — returns the ORIGINAL type node that was
    /// memoized, creating Tlink sharing in copy_type_cached.
    pub fn find_abbrev_repr(&self, memo: AbbrevMemoRef, path: &Path) -> Option<TypeExprRef> {
        let mut current = memo;
        for _ in 0..128 {
            let node = {
                let abbrevs = self.abbrevs.borrow();
                abbrevs
                    .get(current.index())
                    .map(|cell| cell.borrow().clone())
                    .unwrap_or(AbbrevMemo::Mnil)
            };
            match node {
                AbbrevMemo::Mnil => return None,
                AbbrevMemo::Mcons {
                    private_flag: cached_private,
                    path: cached_path,
                    abbrev,
                    next,
                    ..
                } => {
                    // Match OCaml find_repr: only public memo entries participate
                    // in repr reuse during copy.
                    if cached_private == PrivateFlag::Public && path.same(&cached_path) {
                        return Some(abbrev);
                    }
                    current = next;
                }
                AbbrevMemo::Mlink(next) => {
                    current = next;
                }
            }
        }
        None
    }

    /// Snapshot an abbreviation memo node.
    pub fn get_abbrev_memo(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        let abbrevs = self.abbrevs.borrow();
        abbrevs
            .get(memo.index())
            .map(|cell| cell.borrow().clone())
            .unwrap_or(AbbrevMemo::Mnil)
    }

    /// Debug snapshot of an abbreviation memo chain.
    pub fn debug_abbrev_memo_snapshot(&self, memo: AbbrevMemoRef, limit: usize) -> String {
        let mut current = memo;
        let mut parts = Vec::new();
        for idx in 0..limit {
            match self.get_abbrev_memo(current) {
                AbbrevMemo::Mnil => {
                    if idx == 0 {
                        parts.push("Mnil".to_string());
                    }
                    break;
                }
                AbbrevMemo::Mlink(next) => {
                    parts.push(format!("Mlink({})", next.0));
                    current = next;
                }
                AbbrevMemo::Mcons {
                    private_flag,
                    path,
                    abbrev,
                    expansion,
                    next,
                } => {
                    let abbrev = self.repr(abbrev);
                    let expansion = self.repr(expansion);
                    parts.push(format!(
                        "{}:{} abbrev={}@{} expansion={}@{} next={}",
                        idx,
                        path.name(),
                        abbrev.0,
                        self.get_level(abbrev),
                        expansion.0,
                        self.get_level(expansion),
                        next.0
                    ));
                    if matches!(private_flag, PrivateFlag::Private) {
                        parts.push("private".to_string());
                    }
                    current = next;
                }
            }
        }
        if parts.is_empty() {
            "Mnil".to_string()
        } else {
            parts.join(" | ")
        }
    }

    /// Reset a per-node abbreviation memo chain to Mnil.
    pub fn clear_abbrev_memo(&self, memo: AbbrevMemoRef) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        let abbrevs = self.abbrevs.borrow();
        if let Some(cell) = abbrevs.get(memo.index()) {
            *cell.borrow_mut() = AbbrevMemo::Mnil;
        }
    }

    /// Overwrite a per-node abbreviation memo chain with a saved snapshot.
    pub fn restore_abbrev_memo(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        let abbrevs = self.abbrevs.borrow();
        if let Some(cell) = abbrevs.get(memo.index()) {
            *cell.borrow_mut() = value;
        }
    }

    /// Prepend a cached abbreviation expansion to a node-local memo chain.
    pub fn memorize_abbrev_expansion(
        &self,
        memo: AbbrevMemoRef,
        private_flag: PrivateFlag,
        path: Path,
        abbrev: TypeExprRef,
        expansion: TypeExprRef,
    ) {
        // Nil is a shared sentinel and must not be mutated.
        if memo == AbbrevMemoRef::nil() {
            return;
        }

        {
            let mut abbrevs = self.abbrevs.borrow_mut();
            let memo_idx = memo.index();
            if memo_idx >= abbrevs.len() {
                return;
            }

            let previous = abbrevs[memo_idx].borrow().clone();
            let next = if matches!(previous, AbbrevMemo::Mnil) {
                AbbrevMemoRef::nil()
            } else {
                let idx = abbrevs.len();
                abbrevs.push(RefCell::new(previous));
                AbbrevMemoRef::from_usize(idx)
            };

            *abbrevs[memo_idx].borrow_mut() = AbbrevMemo::Mcons {
                private_flag,
                path,
                abbrev,
                expansion,
                next,
            };
        }
        self.memoized_abbrev_refs.borrow_mut().push(memo);
    }

    // ========================================================================
    // Abbreviation Memos
    // ========================================================================

    /// Allocate an abbreviation memo (Mnil).
    pub fn alloc_abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    /// Allocate an abbreviation memo.
    pub fn alloc_abbrev(&self, memo: AbbrevMemo) -> AbbrevMemoRef {
        let mut abbrevs = self.abbrevs.borrow_mut();
        let idx = abbrevs.len();
        abbrevs.push(RefCell::new(memo));
        AbbrevMemoRef::from_usize(idx)
    }

    // ========================================================================
    // Row Fields
    // ========================================================================

    /// Allocate a row field reference.
    pub fn alloc_row_field(&self, field: Option<RowField>) -> RowFieldRef {
        let mut row_fields = self.row_fields.borrow_mut();
        let idx = row_fields.len();
        row_fields.push(RefCell::new(field));
        RowFieldRef::from_usize(idx)
    }

    /// Get the value stored in a row field reference.
    pub fn get_row_field(&self, rf: RowFieldRef) -> Option<RowField> {
        if rf.is_null() {
            return None;
        }
        let row_fields = self.row_fields.borrow();
        row_fields
            .get(rf.index())
            .and_then(|cell| cell.borrow().clone())
    }

    /// Set the value of a row field reference (like OCaml's set_row_field).
    pub fn set_row_field(&self, rf: RowFieldRef, field: RowField) {
        if rf.is_null() {
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.index()) {
            *cell.borrow_mut() = Some(field);
        }
    }

    /// Clear the value stored in a row field reference.
    pub fn clear_row_field(&self, rf: RowFieldRef) {
        if rf.is_null() {
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.index()) {
            *cell.borrow_mut() = None;
        }
    }

    // ========================================================================
    // Commutables
    // ========================================================================

    /// Allocate a commutable reference.
    pub(crate) fn alloc_commutable(&self, c: Commutable) -> CommutableRef {
        let mut commutables = self.commutables.borrow_mut();
        let idx = commutables.len();
        commutables.push(RefCell::new(c));
        CommutableRef::from_usize(idx)
    }

    pub(crate) fn get_commutable(&self, c: CommutableRef) -> Commutable {
        let commutables = self.commutables.borrow();
        commutables
            .get(c.index())
            .map(|cell| cell.borrow().clone())
            .unwrap_or(Commutable::Cunknown)
    }

    pub(crate) fn set_commutable(&self, c: CommutableRef, value: Commutable) {
        let commutables = self.commutables.borrow();
        if let Some(cell) = commutables.get(c.index()) {
            *cell.borrow_mut() = value;
        }
    }

    pub(crate) fn commutable_repr(&self, c: &Commutable) -> Commutable {
        match c {
            Commutable::Clink(link) => {
                let linked = self.get_commutable(*link);
                match linked {
                    Commutable::Cunknown => c.clone(),
                    _ => self.commutable_repr(&linked),
                }
            }
            _ => c.clone(),
        }
    }

    // ========================================================================
    // Field Kinds
    // ========================================================================

    /// Allocate a field kind reference.
    fn alloc_field_kind(&self, kind: Option<FieldKind>) -> FieldKindRef {
        let mut field_kinds = self.field_kinds.borrow_mut();
        let idx = field_kinds.len();
        field_kinds.push(RefCell::new(kind));
        FieldKindRef::from_usize(idx)
    }

    // ========================================================================
    // Level Management
    // ========================================================================

    /// Get the current level.
    pub fn current_level(&self) -> i32 {
        self.current_level.get()
    }

    /// Temporarily set the current level. Used by subst_with_memo to match
    /// OCaml's `current_level := level` which ensures fresh copies during
    /// instance_parameterized_type are created at the Tconstr's level.
    pub fn set_current_level(&self, level: i32) {
        self.current_level.set(level);
    }

    /// Get the non-generalizable level.
    pub fn nongen_level(&self) -> i32 {
        self.nongen_level.get()
    }

    /// Get the global level.
    pub fn global_level(&self) -> i32 {
        self.global_level.get()
    }

    /// Get the current ident stamp value (equivalent of OCaml's `Ident.current_time()`).
    pub fn current_stamp(&self) -> i32 {
        // OCaml compiler/ext/ident.ml:57-58 reads the single active
        // `Ident.create` stamp counter. Rust's `Ident::create_local` counter is
        // for helper-created paths and test fixtures; letting it feed
        // Ctype.init_def shifts later typedtree binders after unrelated helper
        // path construction.
        self.id_gen.current_stamp()
    }

    /// Consume one identifier stamp without materializing an `Ident`.
    ///
    /// This mirrors OCaml save-signature renaming in places where the renamed
    /// identifier is immediately discarded but the stamp stream must advance.
    pub fn consume_ident_stamp(&self) {
        let _ = self.id_gen.next_stamp();
    }

    /// Consume multiple identifier stamps without materializing `Ident`s.
    pub fn consume_ident_stamps(&self, count: i32) {
        let _ = self.id_gen.advance_stamp_by(count);
    }

    /// Set the ident stamp counter to at least `t`.
    /// Matches OCaml's `Ident.set_current_time`.
    pub fn set_current_time(&self, t: i32) {
        self.id_gen.set_current_stamp(t);
    }

    pub(crate) fn current_id_gen_stamp(&self) -> i32 {
        self.id_gen.current_stamp()
    }

    pub(crate) fn current_def_level_state(&self) -> (i32, i32, i32, usize) {
        (
            self.current_level.get(),
            self.nongen_level.get(),
            self.global_level.get(),
            self.saved_levels.borrow().len(),
        )
    }

    pub(crate) fn restore_source_fallback_state(
        &self,
        id_gen_stamp: i32,
        local_stamp: i32,
        current_level: i32,
        nongen_level: i32,
        global_level: i32,
        saved_levels_len: usize,
    ) {
        // OCaml compiler/ml/env.ml:669-678 acknowledges a persistent structure
        // and builds `ps_comps` without making that dependency load consume the
        // current unit's later `Ident` stamps or Ctype definition levels.
        // Source fallback does real typechecking in Rust, so restore the
        // current-unit counters after the isolated load completes.
        self.id_gen.restore_current_stamp(id_gen_stamp);
        Ident::set_current_time(local_stamp);
        self.current_level.set(current_level);
        self.nongen_level.set(nongen_level);
        self.global_level.set(global_level);
        self.saved_levels.borrow_mut().truncate(saved_levels_len);
    }

    /// Register a raw module signature for lazy renaming.
    /// Called during load_pervasives to store sigs for normalize_path.
    pub fn register_raw_module_sig(&self, name: &str, sig: Arc<super::decl::Signature>) {
        self.raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn register_gentype_raw_module_sig(
        &self,
        name: &str,
        sig: Arc<super::decl::Signature>,
    ) {
        self.gentype_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn get_gentype_raw_module_sig(
        &self,
        name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        self.gentype_raw_module_sigs.borrow().get(name).cloned()
    }

    pub fn has_raw_module_sig(&self, name: &str) -> bool {
        self.raw_module_sigs.borrow().contains_key(name)
    }

    pub(crate) fn find_raw_module_sig(&self, name: &str) -> Option<super::decl::Signature> {
        self.raw_module_sigs
            .borrow()
            .get(name)
            .cloned()
            .map(|sig| (*sig).clone())
    }

    pub(crate) fn with_raw_module_sig<T>(
        &self,
        name: &str,
        f: impl FnOnce(&super::decl::Signature) -> T,
    ) -> Option<T> {
        let raw = self.raw_module_sigs.borrow();
        raw.get(name).map(|sig| f(sig.as_ref()))
    }

    pub(crate) fn get_or_load_raw_module_sig(
        &self,
        module_name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        if let Some(sig) = self.raw_module_sigs.borrow().get(module_name).cloned() {
            return Some(sig);
        }
        if let Some(sig) = self
            .raw_component_module_sigs
            .borrow()
            .get(module_name)
            .cloned()
        {
            return Some(sig);
        }
        // OCaml compiler/ml/env.ml:669-678 creates persistent `ps_comps` from
        // the CMI signature separately from `ps_sig`, and env.ml:781-788 returns
        // those components for exact persistent `Pident` descriptor lookup.
        // Keep this fallback separate from `raw_module_sigs`: that map drives
        // ps_sig lazy renaming, and caching component-only loads there makes a
        // later `trigger_all_module_sig_renames` freshen modules OCaml has only
        // looked up through ps_comps.
        let sig = self.load_lazy_raw_module_sig_for_rename(module_name)?;
        self.raw_component_module_sigs
            .borrow_mut()
            .insert(module_name.to_string(), sig.clone());
        Some(sig)
    }

    /// Trigger module signature renaming for a persistent module.
    /// Matches OCaml's find_module → Lazy.force ps.ps_sig which renames
    /// bound idents the first time a module is accessed during normalize_path.
    pub fn trigger_module_sig_rename(&self, module_name: &str) {
        if self.renamed_module_sigs.borrow().contains_key(module_name) {
            return; // Already renamed
        }
        self.rename_one_module_sig(module_name);
    }

    /// Trigger renaming for ALL registered module signatures.
    /// In OCaml, accessing one module (e.g. Console) via components_of_module_maker
    /// cascades into scrape_alias → find_module for dependent modules (e.g. Pervasives),
    /// forcing ALL their ps_sig lazies. We match this by renaming all registered
    /// modules when any one is first accessed.
    pub fn trigger_all_module_sig_renames(&self) {
        let names: Vec<String> = self.raw_module_sigs.borrow().keys().cloned().collect();
        for name in &names {
            if !self
                .renamed_module_sigs
                .borrow()
                .contains_key(name.as_str())
            {
                self.rename_one_module_sig(name);
            }
        }
    }

    fn rename_one_module_sig(&self, module_name: &str) {
        let raw_sig = {
            let raw = self.raw_module_sigs.borrow();
            raw.get(module_name).cloned()
        }
        .or_else(|| {
            self.raw_component_module_sigs
                .borrow()
                .get(module_name)
                .cloned()
        })
        .or_else(|| self.load_lazy_raw_module_sig_for_rename(module_name));
        if let Some(sig) = raw_sig {
            self.raw_module_sigs
                .borrow_mut()
                .entry(module_name.to_string())
                .or_insert_with(|| sig.clone());
            if self.compiler_counters_enabled() {
                crate::perf_counters::record_signature_freshen_name(
                    "type_context_lazy_rename",
                    module_name,
                    sig.len(),
                );
            }
            // OCaml `Subst.signature` copies and freshens in one traversal
            // sequence (compiler/ml/subst.ml:358-364). Keep this lazy rename
            // to that single pass instead of copying before calling the
            // freshening helper.
            let renamed = Arc::new(
                crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
                    "type_context_lazy_rename",
                    sig.as_ref(),
                    self,
                ),
            );
            self.renamed_module_sigs
                .borrow_mut()
                .insert(module_name.to_string(), renamed);
        }
    }

    fn load_lazy_raw_module_sig_for_rename(
        &self,
        module_name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        if self.persistent_env_is_in_process() {
            let mut pers_env = self.persistent_env_clone().unwrap_or_else(|| {
                panic!(
                    "in-process invariant violated: missing PersistentEnv while forcing raw signature for {module_name}"
                )
            });
            // Source fallback can re-enter normalization while the same module
            // has only a cache placeholder. The rename force is a side effect;
            // skip the transient miss and let a later lookup force the
            // published signature.
            return pers_env.read_raw_sig_shared(module_name, self);
        }

        let cmi_path = {
            let load_paths = self.load_paths.borrow();
            let cmi_filename = format!("{module_name}.cmi");
            load_paths.iter().find_map(|dir| {
                let exact = dir.join(&cmi_filename);
                if exact.exists() {
                    return Some(exact);
                }

                let first = module_name.chars().next()?;
                if !first.is_ascii_uppercase() {
                    return None;
                }
                let uncap_name = format!("{}{}", first.to_ascii_lowercase(), &module_name[1..]);
                let uncap = dir.join(format!("{uncap_name}.cmi"));
                uncap.exists().then_some(uncap)
            })
        };
        let cmi_path = cmi_path?;
        let cmi = crate::cmi::cmi_format::read_cmi(&cmi_path.to_string_lossy()).ok()?;
        let mut sig_ctx = crate::cmi::sig_reader::SigReadContext::new(self);
        let mut sig = sig_ctx.read_signature(&cmi.cmi_sign);
        let module_path = Path::Pident(Ident::create_persistent(module_name));
        // OCaml compiler/ml/env.ml:1000-1007 reaches `lookup_module_descr`
        // for dotted accesses, and env.ml:568-571/1516-1605 forces the
        // persistent structure's component lazy. Loading whichever CMI the
        // force requested lets the Rust force point consume the same
        // `Subst.signature` stamps instead of special-casing one module family.
        crate::cmi::persistent_env::substitute_type_paths_in_sig(&sig, &module_path, self);
        crate::cmi::persistent_env::substitute_sig_decl_paths_in_place(&mut sig, &module_path);
        crate::cmi::persistent_env::substitute_submodule_paths_pub(&sig, &module_path, self);
        Some(Arc::new(sig))
    }

    /// Create a new identifier using the typing context's shared stamp source.
    pub fn create_ident(&self, name: &str) -> Ident {
        // OCaml compiler/ext/ident.ml:28-40 increments the active
        // currentstamp directly in `Ident.create`/`Ident.rename`; unrelated
        // helper-created local identifiers must not advance the typedtree
        // context's stamp stream.
        self.id_gen.create(name)
    }

    /// Rename an identifier using the typing context's shared stamp source.
    pub fn rename_ident(&self, id: &Ident) -> Ident {
        // See `create_ident`: this mirrors compiler/ext/ident.ml:38-40.
        id.rename(&self.id_gen)
    }

    /// Initialize definition level (equivalent of OCaml's `Ctype.init_def`).
    pub fn init_def(&self, level: i32) {
        self.current_level.set(level);
        self.nongen_level.set(level);
    }

    /// Begin a new definition scope.
    pub fn begin_def(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.current_level.set(current + 1);
        self.nongen_level.set(current + 1);
    }

    /// Begin a class definition scope.
    pub fn begin_class_def(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.current_level.set(current + 1);
    }

    /// Raise the non-generalizable level.
    pub fn raise_nongen_level(&self) {
        let current = self.current_level.get();
        let nongen = self.nongen_level.get();
        self.saved_levels.borrow_mut().push((current, nongen));
        self.nongen_level.set(current);
    }

    /// End a definition scope.
    pub fn end_def(&self) {
        if let Some((current, nongen)) = self.saved_levels.borrow_mut().pop() {
            self.current_level.set(current);
            self.nongen_level.set(nongen);
        }
    }

    /// Reset the global level.
    pub fn reset_global_level(&self) {
        self.global_level.set(self.current_level.get() + 1);
    }

    /// Increase the global level and return the old value.
    pub fn increase_global_level(&self) -> i32 {
        let old = self.global_level.get();
        self.global_level.set(self.current_level.get());
        old
    }

    /// Restore the global level.
    pub fn restore_global_level(&self, level: i32) {
        self.global_level.set(level);
    }

    // ========================================================================
    // GADT Tracking
    // ========================================================================

    /// Check and set GADT instance tracing.
    pub fn check_trace_gadt_instances(&self, has_constraints: bool) -> bool {
        if !self.trace_gadt_instances.get() && has_constraints {
            self.trace_gadt_instances.set(true);
            true
        } else {
            false
        }
    }

    /// Reset GADT instance tracing.
    pub fn reset_trace_gadt_instances(&self, was_set: bool) {
        if was_set {
            self.trace_gadt_instances.set(false);
        }
    }

    /// Is GADT instance tracing currently enabled?
    pub fn trace_gadt_instances(&self) -> bool {
        self.trace_gadt_instances.get()
    }

    // ========================================================================
    // Type Representative (Union-Find)
    // ========================================================================

    /// Get the representative of a type (follow Tlink chains).
    ///
    /// This uses path compression to update intermediate links
    /// to point directly to the representative, improving
    /// subsequent lookup performance.
    pub fn repr(&self, t: TypeExprRef) -> TypeExprRef {
        // Fast path: check if t is already a representative (no link).
        // This avoids any allocation for the common case.
        let first_next = {
            let desc = self.borrow_desc(t);
            match &*desc {
                TypeDesc::Tlink(next) => *next,
                TypeDesc::Tfield {
                    kind: FieldKind::Fabsent,
                    rest,
                    ..
                } => *rest,
                _ => return t,
            }
        };

        // Follow chain to the end, collecting nodes for path compression.
        // Uses a fixed-size stack buffer — chains longer than 32 are
        // vanishingly rare and just won't get full compression.
        let mut chain = [TypeExprRef(0); 32];
        let mut chain_len: usize = 1;
        chain[0] = t;

        let mut current = first_next;
        for _ in 0..10_000 {
            let next = {
                let desc = self.borrow_desc(current);
                match &*desc {
                    TypeDesc::Tlink(next) => Some(*next),
                    TypeDesc::Tfield {
                        kind: FieldKind::Fabsent,
                        rest,
                        ..
                    } => Some(*rest),
                    _ => None,
                }
            };
            match next {
                Some(next_ref) => {
                    if chain_len < 32 {
                        chain[chain_len] = current;
                        chain_len += 1;
                    }
                    current = next_ref;
                }
                None => break,
            }
        }

        // Path compression: relink all traversed nodes to the representative.
        for i in 0..chain_len {
            let node = chain[i];
            if node != current {
                self.set_desc(node, TypeDesc::Tlink(current));
            }
        }

        current
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_var() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let v1 = ctx.new_var(Some("a".to_string()));
        let v2 = ctx.new_var(None);

        assert_ne!(v1, v2);
    }

    #[test]
    fn test_new_arrow() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(t1, t2);

        let desc = ctx.get_desc(arrow);
        assert!(matches!(*desc, TypeDesc::Tarrow { .. }));
    }

    #[test]
    fn test_level_management() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        assert_eq!(ctx.current_level(), 0);

        ctx.begin_def();
        assert_eq!(ctx.current_level(), 1);

        ctx.begin_def();
        assert_eq!(ctx.current_level(), 2);

        ctx.end_def();
        assert_eq!(ctx.current_level(), 1);

        ctx.end_def();
        assert_eq!(ctx.current_level(), 0);
    }

    #[test]
    fn component_alias_sources_are_path_based() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let selected_path = Path::pdot_pos(
            Path::pident(Ident::create_persistent("Selected")),
            "Child",
            7,
        );
        let selected_path_no_pos =
            Path::pdot(Path::pident(Ident::create_persistent("Selected")), "Child");
        let alias_source = Path::pdot_pos(
            Path::pident(Ident::create_persistent("Selected__Backing")),
            "Child",
            3,
        );
        let alias_source_no_pos = Path::pdot(
            Path::pident(Ident::create_persistent("Selected__Backing")),
            "Child",
        );
        let spelling_only_source = Path::pident(Ident::create_persistent("Other__Child"));

        assert!(
            ctx.component_paths_for_alias_source(&alias_source_no_pos)
                .is_empty()
        );
        assert!(
            ctx.alias_sources_for_component_path(&selected_path_no_pos)
                .is_empty()
        );

        ctx.register_component_alias_source(selected_path.clone(), alias_source.clone());

        assert!(
            ctx.component_paths_for_alias_source(&alias_source_no_pos)
                .iter()
                .any(|path| path.same(&selected_path_no_pos))
        );
        assert!(
            ctx.alias_sources_for_component_path(&selected_path_no_pos)
                .iter()
                .any(|path| path.same(&alias_source_no_pos))
        );
        assert!(
            ctx.component_paths_for_alias_source(&spelling_only_source)
                .is_empty()
        );
    }

    #[test]
    fn test_repr() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_link(t1);
        let t3 = ctx.new_link(t2);

        // repr should follow the chain
        assert_eq!(ctx.repr(t3), t1);
        assert_eq!(ctx.repr(t2), t1);
        assert_eq!(ctx.repr(t1), t1);
    }

    #[test]
    fn test_repr_path_compression() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_link(t1);
        let t3 = ctx.new_link(t2);

        // First call to repr(t3) should do path compression
        assert_eq!(ctx.repr(t3), t1);

        // After path compression, t3 should now point directly to t1
        let desc = ctx.get_desc(t3);
        match &*desc {
            TypeDesc::Tlink(target) => assert_eq!(*target, t1),
            _ => panic!("Expected Tlink after path compression"),
        }
    }

    #[test]
    fn test_tuple() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let tuple = ctx.new_tuple(vec![t1, t2]);

        let desc = ctx.get_desc(tuple);
        match &*desc {
            TypeDesc::Ttuple(types) => assert_eq!(types.len(), 2),
            _ => panic!("Expected tuple"),
        }
    }
}
