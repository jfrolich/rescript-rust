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
    AbbrevMemo, AbbrevMemoRef, FieldKind, FieldKindRef, GENERIC_LEVEL, RowDesc, RowField,
    RowFieldRef, TypeArg, TypeDesc, TypeExpr, TypeExprRef,
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
pub(crate) struct TypeArena {
    arena: typed_arena::Arena<TypeExpr>,
    types: std::cell::UnsafeCell<Vec<NonNull<TypeExpr>>>,
}

impl TypeArena {
    pub(crate) fn new() -> Self {
        TypeArena {
            arena: typed_arena::Arena::new(),
            types: std::cell::UnsafeCell::new(Vec::new()),
        }
    }

    #[inline]
    fn get(&self, r: TypeExprRef) -> &TypeExpr {
        self.get_at(r.index())
    }

    /// Node at raw arena position `idx` (local index or store index; the
    /// caller has already stripped the store tag).
    #[inline]
    pub(crate) fn get_at(&self, idx: usize) -> &TypeExpr {
        // Safety: `idx` is an arena index returned by `push_raw`, and `types`
        // only grows append-only after the pointed `TypeExpr` has been arena
        // allocated.
        unsafe {
            let types = &*self.types.get();
            types[idx].as_ref()
        }
    }

    fn push(&self, ty: TypeExpr) -> TypeExprRef {
        TypeExprRef::from_usize(self.push_raw(ty))
    }

    /// Append a node and return its raw arena position.
    pub(crate) fn push_raw(&self, ty: TypeExpr) -> usize {
        let ptr = NonNull::from(self.arena.alloc(ty));
        // Safety: `types` is an append-only side table of stable arena
        // pointers. `UnsafeCell` is used so `TypeContext` can allocate through
        // shared references like OCaml's mutable type arena.
        unsafe {
            let types = &mut *self.types.get();
            let idx = types.len();
            types.push(ptr);
            idx
        }
    }

    pub(crate) fn len(&self) -> usize {
        // Safety: immutable length read from the append-only side table.
        unsafe { (*self.types.get()).len() }
    }
}

/// Borrow of a type descriptor. Shared dependency nodes are borrowed through
/// `TypeContext::shared_pages` (`Ref::map`), so every borrow is a `Ref`.
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
    store_desc_states: Vec<TypeDesc>,
    store_desc_overlay: super::thread_store::PagedOverlay<usize>,
    store_level_overlay: super::thread_store::PagedOverlay<i32>,
    row_field_states: Vec<Option<RowField>>,
    abbrev_states: Vec<AbbrevMemo>,
    store_abbrev_overlay: super::thread_store::PagedOverlay<AbbrevMemo>,
    store_row_field_overlay: super::thread_store::PagedOverlay<Option<RowField>>,
    shared_desc_overlay: super::thread_store::PagedOverlay<usize>,
    shared_level_overlay: super::thread_store::PagedOverlay<i32>,
    shared_abbrev_overlay: super::thread_store::PagedOverlay<AbbrevMemo>,
    memoized_abbrev_refs: Vec<AbbrevMemoRef>,
    current_abbreviations: AbbrevMemoRef,
    current_level: i32,
    nongen_level: i32,
    global_level: i32,
    saved_levels: Vec<(i32, i32)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct QualifiedModuleComponentsCacheKey {
    // OCaml compiler/ml/path.ml:20-24 ignores `Pdot` positions in
    // `Path.same`; component lookup in env.ml:781-793 keys module identity by
    // that path equality while still carrying positions in the selected access
    // path. `SamePathKey` compares and hashes with that equality directly.
    path: SamePathKey,
    env_id: Option<u64>,
}

impl QualifiedModuleComponentsCacheKey {
    pub(crate) fn new(path: Path, env_id: Option<u64>) -> Self {
        Self {
            path: SamePathKey(path),
            env_id,
        }
    }

    /// Whether the view for this key is the same in every compilation: a
    /// path rooted at a persistent unit, not scoped to one environment.
    pub(crate) fn is_worker_shareable(&self) -> bool {
        fn persistent_root(path: &Path) -> bool {
            match path {
                Path::Pident(id) => id.is_persistent(),
                Path::Pdot(parent, _, _) => persistent_root(parent),
                Path::Papply(_, _) => false,
            }
        }
        self.env_id.is_none() && persistent_root(&self.path.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct QualifiedRecordLabelCacheKey {
    path: SamePathKey,
    env_id: u64,
    lbl_pos: i32,
}

impl QualifiedRecordLabelCacheKey {
    fn new(path: Path, env_id: u64, lbl_pos: i32) -> Self {
        Self {
            path: SamePathKey(path),
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

    /// Exclusive lease of the worker's persistent arena for this compilation.
    /// Returned on drop; overlapping contexts get independent stores.
    store: super::thread_store::StoreLease,
    /// Descriptor writes preserve the stored handle's physical identity, but
    /// live only for this compilation. The append-only arena keeps descriptor
    /// borrows valid while another stored node is written.
    store_descs: TypeArena,
    store_desc_overlay: RefCell<super::thread_store::PagedOverlay<usize>>,
    /// Level marking and lowering are also compilation-local, including on
    /// diagnostic exits that do not finish a mark/unmark traversal.
    store_level_overlay: RefCell<super::thread_store::PagedOverlay<i32>>,
    /// This compilation's writes to abbreviation memo cells of store nodes;
    /// unset cells read the store's initial `Mnil`, matching a fresh process
    /// (`compiler/ml/subst.ml:173-177`).
    store_abbrev_overlay: RefCell<super::thread_store::PagedOverlay<AbbrevMemo>>,
    /// This compilation's writes to row field cells of store rows.
    store_row_field_overlay: RefCell<super::thread_store::PagedOverlay<Option<RowField>>>,
    /// The same overlays for nodes of the process-wide shared pool, keyed by
    /// shared index (descriptor overlays point into `store_descs`).
    shared_desc_overlay: RefCell<super::thread_store::PagedOverlay<usize>>,
    shared_level_overlay: RefCell<super::thread_store::PagedOverlay<i32>>,
    shared_abbrev_overlay: RefCell<super::thread_store::PagedOverlay<AbbrevMemo>>,
    /// Direct handle to the shared pool's page table for node reads. Never
    /// borrowed mutably: the `RefCell` only lets shared descriptor borrows be
    /// `Ref`s like local ones (`Ref::map`), so callers see one borrow type.
    shared_pages: RefCell<super::shared_store::SharedPages>,

    /// Nesting depth of `build_in_store`; allocations go to the worker store
    /// while it is non-zero.
    store_build_depth: Cell<u32>,
    /// Store arena lengths when the outermost store build started: nodes and
    /// row fields at or above these are still being built and are written in
    /// place.
    store_build_type_start: Cell<usize>,
    store_build_row_start: Cell<usize>,
    /// The current store build read compilation-local state, so its result
    /// must stay private to this compilation.
    store_build_poisoned: Cell<bool>,
    /// Effects of the current store build on this compilation.
    store_build_effects: RefCell<Vec<StoreEffect>>,
    /// Shared pieces whose effects this compilation has already applied.
    touched_store_pieces: RefCell<ahash::AHashSet<u64>>,

    /// Cached value of `RESCRIPT_COMPILER_COUNTERS` for hot-path probes.
    compiler_counters_enabled: bool,

    /// Abbreviation memo storage
    abbrevs: RefCell<Vec<RefCell<AbbrevMemo>>>,
    /// Refs that have been written via memorize_abbrev_expansion since the
    /// last cleanup. Mirrors OCaml btype.ml `memo` list used by cleanup_abbrev.
    memoized_abbrev_refs: RefCell<Vec<AbbrevMemoRef>>,

    /// Stable forward references for canonical variant layouts. Entries are
    /// allocated before translating a recursive declaration group and completed
    /// exactly once after the group is available in the environment.
    variant_layouts: RefCell<Vec<RefCell<super::variant_runtime::LayoutState>>>,

    /// Row field storage
    row_fields: RefCell<Vec<RefCell<Option<RowField>>>>,

    /// Field kind storage
    field_kinds: RefCell<Vec<RefCell<Option<FieldKind>>>>,

    /// Global type declaration store, indexed by type name.
    /// Populated when loading CMI module signatures so that type alias
    /// expansion can find declarations for types not directly in the env.
    type_decl_store: RefCell<ahash::AHashMap<smol_str::SmolStr, Arc<super::decl::TypeDeclaration>>>,

    /// Global type declaration store, indexed by ident stamp.
    /// Used for looking up CMI-loaded type declarations by their stamp
    /// when the type name is too generic (e.g., "t").
    type_decl_by_stamp: RefCell<ahash::AHashMap<i32, Arc<super::decl::TypeDeclaration>>>,

    /// Global type declaration store, indexed by full qualified path string.
    /// Used for looking up types via Pdot paths (e.g., "Js.Promise.t").
    type_decl_by_path: RefCell<ahash::AHashMap<smol_str::SmolStr, Arc<super::decl::TypeDeclaration>>>,
    /// Qualified declarations keyed by Path identity, preserving local stamps.
    /// Only single `Exact` registrations, with their log position; batches
    /// are kept whole in `exact_path_batches` and probed through their shared
    /// index, so a unit never copies every dependency type into this map.
    type_decl_by_exact_path:
        RefCell<ahash::AHashMap<Path, (usize, Arc<super::decl::TypeDeclaration>)>>,
    exact_path_batches: RefCell<Vec<(usize, Arc<super::thread_store::SigTypeBatch>)>>,
    /// Exact-path answers, valid while the log length equals the first field.
    exact_path_memo: RefCell<(
        usize,
        ahash::AHashMap<Path, Option<Arc<super::decl::TypeDeclaration>>>,
    )>,
    /// Registrations for the four maps above, in registration order. Each map
    /// replays the log up to the present only when it is read: modules
    /// register every type of every loaded dependency but read these maps
    /// rarely, and most registrations come as one shared batch per signature.
    type_decl_log: RefCell<Vec<TypeDeclRegistration>>,
    /// Log position each map has been replayed to: name, stamp, path, exact.
    type_decl_log_replayed: [Cell<usize>; 4],
    type_item_by_path: RefCell<ahash::AHashMap<String, (Ident, super::decl::TypeDeclaration)>>,
    missing_type_item_by_path: RefCell<ahash::AHashSet<String>>,

    /// Cache for type declarations resolved through module signatures (Pdot paths).
    /// Separate from type_decl_by_path to avoid conflicts with expand_head_once
    /// entries which have unqualified paths. This approximates OCaml's
    /// components_of_module_maker lazy caching.
    resolved_pdot_type_cache: RefCell<ahash::AHashMap<SamePathKey, Arc<super::decl::TypeDeclaration>>>,

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
    component_alias_sources: RefCell<ahash::AHashMap<SamePathKey, Vec<Path>>>,
    /// Component-table name indexes of compilation-local signatures, keyed by
    /// address; the entry keeps the signature alive so the key stays unique.
    signature_indexes: RefCell<
        ahash::AHashMap<usize, (Arc<super::decl::Signature>, Arc<super::env_lazy::SignatureIndex>)>,
    >,
    component_paths_by_alias_source: RefCell<ahash::AHashMap<SamePathKey, Vec<Path>>>,

    /// Cached dotted value lookups keyed by resolved module access path.
    resolved_module_value_cache: RefCell<
        ahash::AHashMap<Path, ahash::AHashMap<String, (Path, Arc<super::decl::ValueDescription>)>>,
    >,

    /// Cached dotted type lookups keyed by resolved module access path.
    /// Keyed by env id as well: OCaml's Env is persistent, so a binding can
    /// never change under an existing path, but Rust's Env is mutated in
    /// place (`add_module`) and must invalidate these derived entries.
    resolved_module_type_cache: RefCell<
        ahash::AHashMap<
            (u64, Path),
            ahash::AHashMap<String, (Path, Ident, Arc<super::decl::TypeDeclaration>)>,
        >,
    >,

    /// Cached child-module access paths keyed by resolved parent access path.
    resolved_child_module_path_cache: RefCell<ahash::AHashMap<Path, ahash::AHashMap<String, Path>>>,

    /// Forced declarations shared by persistent/global alias component views.
    /// Local component views keep their own thunk state in StructureComponentTables.
    qualified_module_decl_cache: RefCell<
        ahash::AHashMap<
            Path,
            ahash::AHashMap<String, (Ident, Arc<super::decl::ModuleDeclaration>)>,
        >,
    >,

    /// Resolved dotted type paths keyed by `Env::scope_id`, path, and whether
    /// alias targets were strengthened (see `ctype::resolve_type_item_through_env`).
    resolved_type_item_cache: RefCell<
        ahash::AHashMap<(u64, Path, bool), (Ident, Arc<super::decl::TypeDeclaration>)>,
    >,

    /// Cached full normalize_path results keyed by environment identity.
    normalized_path_full_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,
    /// Answers of `raw_lambda::typeopt` queries while the finished typed tree
    /// is lowered (`None` outside that phase): the types no longer change.
    typeopt_answers: RefCell<Option<ahash::AHashMap<(u64, TypeExprRef, u8), bool>>>,
    /// Outcome of expanding a `Pdot`-headed constructor, per module scope
    /// (see `ctype::PdotExpansion`).
    pdot_expansions: RefCell<hashbrown::HashMap<PdotExpansionKey, super::ctype::PdotExpansion, ahash::RandomState>>,

    /// Cached forward-only (unification) normalize_path results, keyed like
    /// `normalized_path_full_cache`.
    normalized_path_forward_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,

    /// `occur_univar` argument masks per (scope, constructor path): bit `i`
    /// is set when argument `i` has a may-positive or may-negative variance;
    /// `None` when the declaration is not found (every argument is visited).
    occur_variance_masks: RefCell<ahash::AHashMap<(u64, Path), Option<u64>>>,

    /// `Ctype.get_level` declaration levels per (scope, type path): the
    /// `type_newtype_level` of the declaration `Env.find_type` returns.
    type_newtype_levels: RefCell<ahash::AHashMap<(u64, Path), Option<i32>>>,

    /// Cached side-effectful normalize_path results keyed by environment identity.
    forced_normalized_path_full_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,

    /// Cached side-effectful type-path comparisons keyed by environment identity.
    forced_type_path_compare_cache: RefCell<ahash::AHashMap<(u64, Path, Path), bool>>,

    /// Load paths for resolving CMI files during type alias expansion.
    load_paths: RefCell<Arc<Vec<std::path::PathBuf>>>,

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
    pub(crate) renamed_module_sigs: RefCell<ahash::AHashMap<String, Arc<DeferredRenamedSig>>>,

    /// Reserved stamp cursor `(next, last)` used while materializing a
    /// [`DeferredRenamedSig`], so its binders get the stamps reserved when the
    /// rename was forced.
    reserved_rename_stamps: Cell<Option<(i32, i32)>>,

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
    gentype_portable_raw_module_sigs:
        RefCell<ahash::AHashMap<String, Arc<crate::cmi::portable_types::PortablePersStruct>>>,

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
    /// Registered arenas' strings in registration order; the first arena
    /// that has an index names it.
    arena_longident_names: RefCell<Vec<crate::intern::InternedStrings>>,

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
    predef_option_layout: Cell<Option<super::variant_runtime::LayoutRef>>,

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

/// Effect of building shared store data on the state of the compilation that
/// built it. Another compilation that reuses the data replays these effects
/// the first time it touches the data, so its own state (identifier stamps,
/// forced pieces) evolves exactly as if it had built the data itself.
#[derive(Debug, Clone)]
pub(crate) enum StoreEffect {
    /// Local identifier stamps consumed.
    Stamps(i32),
    /// A shared piece forced while building this one.
    Piece(Arc<StorePiece>),
    /// A component view registered in this compilation's component cache.
    RegisterComponents(
        QualifiedModuleComponentsCacheKey,
        Arc<super::env_lazy::QualifiedModuleComponents>,
    ),
    /// `PersistentEnv::find_pers_struct` for this unit, which prepares the
    /// module for the compilation on first use.
    PreparePers(smol_str::SmolStr),
    /// `trigger_module_sig_rename`: forces the lazy rename of a persistent
    /// signature (reserving its binder stamps) in this compilation.
    TriggerRename(smol_str::SmolStr),
    /// Registrations in this compilation's declaration and alias tables.
    RegisterTypeDecl(smol_str::SmolStr, Arc<super::decl::TypeDeclaration>),
    RegisterTypeDeclByStamp(i32, Arc<super::decl::TypeDeclaration>),
    RegisterAliasSource(Path, Path),
    RegisterQualifiedModuleDecl(Path, smol_str::SmolStr, Ident, Arc<super::decl::ModuleDeclaration>),
}

/// Replay record of one piece of shared store data (see
/// `TypeContext::build_in_store`).
#[derive(Debug)]
pub(crate) struct StorePiece {
    id: u64,
    effects: Vec<StoreEffect>,
}

pub(crate) fn store_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_STORE_DEBUG").is_some())
}

static NEXT_STORE_PIECE_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// One registration for the global type-declaration maps.
#[derive(Debug)]
enum TypeDeclRegistration {
    /// Every type of a store-owned signature, for all four maps.
    Batch(Arc<super::thread_store::SigTypeBatch>),
    Name(smol_str::SmolStr, Arc<super::decl::TypeDeclaration>),
    Stamp(i32, Arc<super::decl::TypeDeclaration>),
    Path(smol_str::SmolStr, Arc<super::decl::TypeDeclaration>),
    Exact(Path, Arc<super::decl::TypeDeclaration>),
}

/// A map key that compares paths with `Path::same` (ignoring `Pdot`
/// positions and comparing identifiers by stamp, or by name when persistent).
#[derive(Clone, Debug)]
pub(crate) struct SamePathKey(Path);

impl SamePathKey {
    pub(crate) fn new(path: Path) -> Self {
        SamePathKey(path)
    }
}

impl PartialEq for SamePathKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.same(&other.0)
    }
}

impl Eq for SamePathKey {}

impl std::hash::Hash for SamePathKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        fn hash_path<H: std::hash::Hasher>(path: &Path, state: &mut H) {
            match path {
                Path::Pident(id) => {
                    if id.stamp() != 0 {
                        state.write_u8(0);
                        state.write_i32(id.stamp());
                    } else {
                        state.write_u8(1);
                        std::hash::Hash::hash(&id.name_atom(), state);
                    }
                }
                Path::Pdot(parent, name, _) => {
                    state.write_u8(2);
                    std::hash::Hash::hash(name, state);
                    hash_path(parent, state);
                }
                Path::Papply(functor, argument) => {
                    state.write_u8(3);
                    hash_path(functor, state);
                    hash_path(argument, state);
                }
            }
        }
        hash_path(&self.0, state);
    }
}

/// Key of `TypeContext::pdot_expansions`.
#[derive(PartialEq, Eq, Hash)]
struct PdotExpansionKey {
    scope_id: u64,
    mode: u8,
    arity: usize,
    path: Path,
}

/// Borrowed form of [`PdotExpansionKey`], so lookups do not clone the path.
/// Field order and hashing match the owned key.
#[derive(Hash)]
struct PdotExpansionKeyRef<'a> {
    scope_id: u64,
    mode: u8,
    arity: usize,
    path: &'a Path,
}

impl hashbrown::Equivalent<PdotExpansionKey> for PdotExpansionKeyRef<'_> {
    fn equivalent(&self, key: &PdotExpansionKey) -> bool {
        self.scope_id == key.scope_id
            && self.mode == key.mode
            && self.arity == key.arity
            && *self.path == key.path
    }
}

fn push_unique_path(paths: &mut Vec<Path>, path: Path) {
    if !paths.iter().any(|existing| existing.same(&path)) {
        paths.push(path);
    }
}

/// A forced persistent-signature rename whose copy is built on first read.
/// See [`TypeContext::defer_renamed_sig`].
#[derive(Debug)]
pub(crate) struct DeferredRenamedSig {
    kind: &'static str,
    source: Arc<super::decl::Signature>,
    first_stamp: i32,
    stamp_count: i32,
    renamed: std::sync::OnceLock<Arc<super::decl::Signature>>,
}

impl TypeContext {
    /// Create a new type context.
    pub fn new(id_gen: Arc<IdGenerator>) -> Self {
        let store = super::thread_store::current();
        let shared_pages = store.shared_pool().pages();
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
            store,
            store_descs: TypeArena::new(),
            store_desc_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            store_level_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            store_abbrev_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            store_row_field_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            shared_desc_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            shared_level_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            shared_abbrev_overlay: RefCell::new(super::thread_store::PagedOverlay::new()),
            shared_pages: RefCell::new(shared_pages),
            store_build_depth: Cell::new(0),
            store_build_type_start: Cell::new(0),
            store_build_row_start: Cell::new(0),
            store_build_poisoned: Cell::new(false),
            store_build_effects: RefCell::new(Vec::new()),
            touched_store_pieces: RefCell::new(ahash::AHashSet::new()),
            compiler_counters_enabled: crate::perf_counters::enabled(),
            // Index 0 is reserved as canonical Mnil; index 1 is the dedicated
            // simple_abbrevs memo ref.
            abbrevs: RefCell::new(vec![
                RefCell::new(AbbrevMemo::Mnil),
                RefCell::new(AbbrevMemo::Mnil),
            ]),
            memoized_abbrev_refs: RefCell::new(Vec::new()),
            variant_layouts: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            field_kinds: RefCell::new(Vec::new()),
            type_decl_store: RefCell::new(ahash::AHashMap::new()),
            type_decl_by_stamp: RefCell::new(ahash::AHashMap::new()),
            type_decl_by_path: RefCell::new(ahash::AHashMap::new()),
            type_decl_by_exact_path: RefCell::new(ahash::AHashMap::new()),
            exact_path_batches: RefCell::new(Vec::new()),
            exact_path_memo: RefCell::new((0, ahash::AHashMap::new())),
            type_decl_log: RefCell::new(Vec::new()),
            type_decl_log_replayed: Default::default(),
            type_item_by_path: RefCell::new(ahash::AHashMap::new()),
            missing_type_item_by_path: RefCell::new(ahash::AHashSet::new()),
            resolved_pdot_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_sig_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_module_components_cache: RefCell::new(ahash::AHashMap::new()),
            component_alias_sources: RefCell::new(ahash::AHashMap::new()),
            signature_indexes: RefCell::new(ahash::AHashMap::new()),
            component_paths_by_alias_source: RefCell::new(ahash::AHashMap::new()),
            resolved_module_value_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_child_module_path_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_module_decl_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_type_item_cache: RefCell::new(ahash::AHashMap::new()),
            normalized_path_full_cache: RefCell::new(ahash::AHashMap::new()),
            pdot_expansions: RefCell::new(hashbrown::HashMap::default()),
            typeopt_answers: RefCell::new(None),
            normalized_path_forward_cache: RefCell::new(ahash::AHashMap::new()),
            occur_variance_masks: RefCell::new(ahash::AHashMap::new()),
            type_newtype_levels: RefCell::new(ahash::AHashMap::new()),
            forced_normalized_path_full_cache: RefCell::new(ahash::AHashMap::new()),
            forced_type_path_compare_cache: RefCell::new(ahash::AHashMap::new()),
            load_paths: RefCell::new(Arc::new(Vec::new())),
            persistent_env: RefCell::new(None),
            renamed_module_sigs: RefCell::new(ahash::AHashMap::new()),
            reserved_rename_stamps: Cell::new(None),
            raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            gentype_raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            gentype_portable_raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            raw_component_module_sigs: RefCell::new(ahash::AHashMap::new()),
            cmi_longident_names: RefCell::new(ahash::AHashMap::new()),
            arena_longident_names: RefCell::new(Vec::new()),
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
            predef_option_layout: Cell::new(None),
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

    pub fn pending_variant_layout(&self) -> super::variant_runtime::LayoutRef {
        // A pending layout is completed later by this compilation.
        self.poison_store_build();
        let mut layouts = self.variant_layouts.borrow_mut();
        let layout_ref = super::variant_runtime::LayoutRef::from_usize(layouts.len());
        layouts.push(RefCell::new(super::variant_runtime::LayoutState::Pending));
        layout_ref
    }

    pub fn alloc_complete_variant_layout(
        &self,
        layout: super::variant_runtime::Layout,
    ) -> super::variant_runtime::LayoutRef {
        // Like `alloc_type`: a store build allocates in the worker store, where
        // layouts are complete on allocation.
        if self.in_store_build() {
            return self.store.alloc_complete_variant_layout(layout);
        }
        let layout_ref = self.pending_variant_layout();
        self.complete_variant_layout(layout_ref, layout);
        layout_ref
    }

    pub fn complete_variant_layout(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
        layout: super::variant_runtime::Layout,
    ) {
        assert!(
            !layout_ref.is_store(),
            "variant layouts in the thread store are complete on allocation"
        );
        let layouts = self.variant_layouts.borrow();
        let Some(state) = layouts.get(layout_ref.index()) else {
            panic!("variant layout reference belongs to another TypeContext")
        };
        let mut state = state.borrow_mut();
        match &*state {
            super::variant_runtime::LayoutState::Pending => {
                *state = super::variant_runtime::LayoutState::Complete(layout)
            }
            super::variant_runtime::LayoutState::Complete(_) => {
                panic!("variant layout completed twice")
            }
        }
    }

    /// Read a completed variant layout without copying its constructor table.
    pub fn with_variant_layout<R>(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
        read: impl FnOnce(&super::variant_runtime::Layout) -> R,
    ) -> R {
        if layout_ref.is_shared() {
            return read(self.store.shared_pool().layout(layout_ref));
        }
        if layout_ref.is_store() {
            return self.store.with_variant_layout(layout_ref, read);
        }
        let layouts = self.variant_layouts.borrow();
        let Some(state) = layouts.get(layout_ref.index()) else {
            panic!("variant layout reference belongs to another TypeContext")
        };
        match &*state.borrow() {
            super::variant_runtime::LayoutState::Complete(layout) => read(layout),
            super::variant_runtime::LayoutState::Pending => {
                panic!("variant layout accessed before declaration completion")
            }
        }
    }

    pub fn variant_layout(
        &self,
        layout_ref: super::variant_runtime::LayoutRef,
    ) -> super::variant_runtime::Layout {
        self.with_variant_layout(layout_ref, Clone::clone)
    }

    /// Store a typedtree environment snapshot and return a stable reference.
    pub fn store_typed_env(&self, env: &Env) -> EnvRef {
        self.poison_store_build_for("store_typed_env");
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
        self.poison_store_build_for("intern_cmi_longident_name");
        let raw = self.next_cmi_longident_idx.get();
        self.next_cmi_longident_idx.set(raw.wrapping_add(1));
        self.cmi_longident_names
            .borrow_mut()
            .insert(raw, name.to_string());
        StrIdx::from_raw(raw)
    }

    pub(crate) fn cmi_longident_component_name(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_names
            .borrow()
            .get(&idx.raw())
            .cloned()
            .or_else(|| self.store.longident_name(idx))
            .or_else(|| self.store.shared_pool().longident_name(idx))
    }

    /// The worker's persistent store leased by this compilation.
    pub(crate) fn thread_store(&self) -> &super::thread_store::ThreadTypeStore {
        &self.store
    }

    /// Whether `r` names an allocated node of this compilation's arena or of
    /// the worker store.
    pub fn contains_type_ref(&self, r: TypeExprRef) -> bool {
        if r.is_shared() {
            self.store.shared_pool().contains(r.shared_index())
        } else if r.is_store() {
            r.store_index() < self.store.type_count()
        } else {
            r.index() < self.types.len()
        }
    }

    /// Resolve a Longident component StrIdx to string, checking CMI synthetic
    /// indices first and falling back to the parse arena interner.
    pub fn resolve_longident_component(
        &self,
        arena: &crate::parse_arena::ParseArena,
        idx: StrIdx,
    ) -> String {
        self.cmi_longident_component_name(idx)
            .unwrap_or_else(|| arena.get_string(idx).to_string())
    }

    pub fn resolve_cmi_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_component_name(idx)
    }

    pub(crate) fn register_arena_longident_names(&self, arena: &crate::parse_arena::ParseArena) {
        self.poison_store_build_for("register_arena_longident_names");
        if arena.string_count() > 0 {
            self.arena_longident_names
                .borrow_mut()
                .push(arena.snapshot_strings());
        }
    }

    pub(crate) fn resolve_any_longident_component(&self, idx: StrIdx) -> Option<String> {
        self.cmi_longident_component_name(idx)
            .or_else(|| {
                self.arena_longident_names
                    .borrow()
                    .iter()
                    .find_map(|strings| strings.get(idx).map(str::to_string))
            })
    }

    /// Snapshot synthetic CMI longident component names so portable signatures
    /// can move across TypeContexts without losing the side table.
    pub fn snapshot_cmi_longident_names(&self) -> Vec<(u32, String)> {
        let mut names: Vec<(u32, String)> = self
            .cmi_longident_names
            .borrow()
            .iter()
            .map(|(raw, name)| (*raw, name.clone()))
            .collect();
        names.extend(self.store.snapshot_longident_names());
        names.extend(self.store.shared_pool().snapshot_longident_names());
        names
    }

    /// Import synthetic CMI longident names from a portable signature.
    pub fn import_cmi_longident_names(&self, names: &[(u32, String)]) {
        self.poison_store_build_for("import_cmi_longident_names");
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
    pub fn register_type_decl(&self, name: &str, decl: impl Into<Arc<super::decl::TypeDeclaration>>) {
        self.register_shared_type_decl(name, decl.into());
    }

    pub(crate) fn register_shared_type_decl(
        &self,
        name: &str,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::RegisterTypeDecl(name.into(), decl.clone()));
        }
        self.type_decl_log
            .borrow_mut()
            .push(TypeDeclRegistration::Name(smol_str::SmolStr::new(name), decl));
    }

    /// Install the type registrations of a store-owned signature, in order.
    /// Equivalent to calling the four `register_shared_type_decl*` methods for
    /// each entry.
    pub(crate) fn register_sig_type_registrations(
        &self,
        registrations: &Arc<super::thread_store::SigTypeBatch>,
    ) {
        self.poison_store_build_for("register_sig_type_registrations");
        self.type_decl_log
            .borrow_mut()
            .push(TypeDeclRegistration::Batch(registrations.clone()));
    }

    /// Bring map `map` (0 name, 1 stamp, 2 path, 3 exact) up to date with the
    /// registration log.
    fn replay_type_decl_log(&self, map: usize) {
        let log = self.type_decl_log.borrow();
        let start = self.type_decl_log_replayed[map].get();
        if start == log.len() {
            return;
        }
        let pending = &log[start..];
        // Upper bound on inserts, so the map grows once instead of rehashing
        // repeatedly while a batch is replayed.
        let additional: usize = pending
            .iter()
            .map(|entry| match entry {
                TypeDeclRegistration::Batch(registrations) => registrations.len(),
                _ => 1,
            })
            .sum();
        match map {
            0 => {
                let mut by_name = self.type_decl_store.borrow_mut();
                by_name.reserve(additional);
                for entry in pending {
                    match entry {
                        TypeDeclRegistration::Batch(registrations) => {
                            for registration in registrations.iter() {
                                by_name.insert(registration.name.clone(), registration.decl.clone());
                            }
                        }
                        TypeDeclRegistration::Name(name, decl) => {
                            by_name.insert(name.clone(), decl.clone());
                        }
                        _ => {}
                    }
                }
            }
            1 => {
                let mut by_stamp = self.type_decl_by_stamp.borrow_mut();
                by_stamp.reserve(additional);
                for entry in pending {
                    match entry {
                        TypeDeclRegistration::Batch(registrations) => {
                            for registration in registrations.iter() {
                                if registration.stamp != 0 {
                                    by_stamp.insert(registration.stamp, registration.decl.clone());
                                }
                            }
                        }
                        TypeDeclRegistration::Stamp(stamp, decl) => {
                            by_stamp.insert(*stamp, decl.clone());
                        }
                        _ => {}
                    }
                }
            }
            2 => {
                let mut by_path = self.type_decl_by_path.borrow_mut();
                by_path.reserve(additional);
                for entry in pending {
                    match entry {
                        TypeDeclRegistration::Batch(registrations) => {
                            for registration in registrations.iter() {
                                by_path.insert(
                                    registration.qualified_name.clone(),
                                    registration.decl.clone(),
                                );
                            }
                        }
                        TypeDeclRegistration::Path(path, decl) => {
                            by_path.insert(path.clone(), decl.clone());
                        }
                        _ => {}
                    }
                }
            }
            _ => {
                let mut by_exact_path = self.type_decl_by_exact_path.borrow_mut();
                let mut batches = self.exact_path_batches.borrow_mut();
                for (offset, entry) in pending.iter().enumerate() {
                    let position = start + offset;
                    match entry {
                        TypeDeclRegistration::Batch(registrations) => {
                            batches.push((position, registrations.clone()));
                        }
                        TypeDeclRegistration::Exact(path, decl) => {
                            by_exact_path.insert(path.clone(), (position, decl.clone()));
                        }
                        _ => {}
                    }
                }
            }
        }
        self.type_decl_log_replayed[map].set(log.len());
    }

    /// Register a type declaration by ident stamp for alias expansion.
    pub fn register_type_decl_by_stamp(&self, stamp: i32, decl: impl Into<Arc<super::decl::TypeDeclaration>>) {
        self.register_shared_type_decl_by_stamp(stamp, decl.into());
    }

    pub(crate) fn register_shared_type_decl_by_stamp(
        &self,
        stamp: i32,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::RegisterTypeDeclByStamp(stamp, decl.clone()));
        }
        self.type_decl_log
            .borrow_mut()
            .push(TypeDeclRegistration::Stamp(stamp, decl));
    }

    /// Match OCaml `Ctype.get_new_abstract_name`.
    pub(crate) fn next_reified_abstract_name(&self, prefix: &str) -> String {
        self.poison_store_build_for("next_reified_abstract_name");
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
        self.replay_type_decl_log(0);
        let store = self.type_decl_store.borrow();
        if store.contains_key(name) {
            Some(std::cell::Ref::map(store, |s| {
                s.get(name).unwrap().as_ref()
            }))
        } else {
            None
        }
    }

    /// Look up a type declaration by stamp from the global store.
    pub(crate) fn find_type_decl_arc_by_stamp(
        &self,
        stamp: i32,
    ) -> Option<Arc<super::decl::TypeDeclaration>> {
        self.replay_type_decl_log(1);
        self.type_decl_by_stamp.borrow().get(&stamp).cloned()
    }

    pub fn find_type_decl_by_stamp(
        &self,
        stamp: i32,
    ) -> Option<std::cell::Ref<'_, super::decl::TypeDeclaration>> {
        self.replay_type_decl_log(1);
        let store = self.type_decl_by_stamp.borrow();
        if store.contains_key(&stamp) {
            Some(std::cell::Ref::map(store, |s| {
                s.get(&stamp).unwrap().as_ref()
            }))
        } else {
            None
        }
    }

    /// Register a type declaration by full qualified path string for alias expansion.
    pub fn register_type_decl_by_path(&self, path: &str, decl: impl Into<Arc<super::decl::TypeDeclaration>>) {
        self.register_shared_type_decl_by_path(path, decl.into());
    }

    pub(crate) fn register_shared_type_decl_by_path(
        &self,
        path: &str,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.poison_store_build_for("register_shared_type_decl_by_path");
        self.type_decl_log
            .borrow_mut()
            .push(TypeDeclRegistration::Path(smol_str::SmolStr::new(path), decl));
    }

    /// Register a qualified declaration by exact Path identity.
    pub fn register_type_decl_by_exact_path(&self, path: Path, decl: impl Into<Arc<super::decl::TypeDeclaration>>) {
        self.register_shared_type_decl_by_exact_path(path, decl.into());
    }

    pub(crate) fn register_shared_type_decl_by_exact_path(
        &self,
        path: Path,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.poison_store_build_for("register_shared_type_decl_by_exact_path");
        self.type_decl_log
            .borrow_mut()
            .push(TypeDeclRegistration::Exact(path, decl));
    }

    pub(crate) fn register_type_item_by_path(
        &self,
        path: &str,
        id: Ident,
        decl: super::decl::TypeDeclaration,
    ) {
        self.poison_store_build_for("register_type_item_by_path");
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
        self.poison_store_build_for("register_missing_type_item_by_path");
        self.missing_type_item_by_path
            .borrow_mut()
            .insert(path.to_string());
    }

    pub(crate) fn is_missing_type_item_by_path(&self, path: &str) -> bool {
        self.missing_type_item_by_path.borrow().contains(path)
    }

    /// Cache a type declaration resolved through module signatures (Pdot paths).
    /// Keyed by `Path::same` identity; only paths without a functor
    /// application are cached.
    pub(crate) fn register_resolved_pdot_type(
        &self,
        path: &Path,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_pdot_type_cache
            .borrow_mut()
            .insert(SamePathKey(path.clone()), decl);
    }

    /// Look up a cached resolved Pdot type declaration.
    pub(crate) fn find_resolved_pdot_type(
        &self,
        path: &Path,
    ) -> Option<Arc<super::decl::TypeDeclaration>> {
        self.resolved_pdot_type_cache
            .borrow()
            .get(&SamePathKey(path.clone()))
            .cloned()
    }

    /// Look up a cached resolved declaration by printed name: only paths
    /// rooted at a persistent (stamp-0) identifier are reachable this way.
    pub(crate) fn find_resolved_pdot_type_by_name(
        &self,
        path: &Path,
    ) -> Option<Arc<super::decl::TypeDeclaration>> {
        fn persistent_dotted(path: &Path) -> bool {
            match path {
                Path::Pident(id) => id.is_persistent() || id.stamp() == 0,
                Path::Pdot(parent, _, _) => persistent_dotted(parent),
                Path::Papply(_, _) => false,
            }
        }
        if !matches!(path, Path::Pdot(..)) || !persistent_dotted(path) {
            return None;
        }
        self.find_resolved_pdot_type(path)
    }

    /// Cache a resolved module signature.
    pub fn register_resolved_module_sig(
        &self,
        path: &str,
        access_path: Path,
        sig: Arc<super::decl::Signature>,
    ) {
        self.poison_store_build_for("register_resolved_module_sig");
        self.resolved_module_sig_cache
            .borrow_mut()
            .insert(path.to_string(), (access_path, sig));
    }

    /// Look up a cached resolved module signature.
    pub fn find_resolved_module_sig(
        &self,
        path: &str,
    ) -> Option<(Path, Arc<super::decl::Signature>)> {
        self.poison_store_build_for("read:find_resolved_module_sig");
        self.resolved_module_sig_cache.borrow().get(path).cloned()
    }

    /// Cache a lazily-built qualified module-components view.
    /// Register a (possibly shared) component view in this compilation's
    /// component cache.
    pub(crate) fn register_qualified_module_components_arc(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: Arc<super::env_lazy::QualifiedModuleComponents>,
    ) {
        if self.compiler_counters_enabled {
            crate::perf_counters::record_qualified_component_registered();
        }
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::RegisterComponents(
                key.clone(),
                components.clone(),
            ));
        }
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, components);
    }

    pub(crate) fn register_qualified_module_components(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: super::env_lazy::QualifiedModuleComponents,
    ) {
        self.poison_store_build_for("register_qualified_module_components");
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
        self.poison_store_build_for("read:with_qualified_module_components");
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
        self.poison_store_build_for("read:has_qualified_module_components");
        // OCaml compiler/ml/env.ml:781-793 lets `find_module_descr` reuse
        // `ps_comps` without forcing `ps_sig`; Rust stores that selected
        // component view explicitly, so later normalization can observe that
        // the component table is already available.
        self.qualified_module_components_cache
            .borrow()
            .contains_key(key)
    }

    /// Name index for the component tables of `sig`, shared by every table
    /// built from the same signature.
    pub(crate) fn signature_index(
        &self,
        sig: &Arc<super::decl::Signature>,
    ) -> Arc<super::env_lazy::SignatureIndex> {
        if self.store.owns_signature(sig) {
            return self.store.signature_index(sig);
        }
        let key = Arc::as_ptr(sig) as usize;
        if let Some((_, found)) = self.signature_indexes.borrow().get(&key) {
            return found.clone();
        }
        let built = Arc::new(super::env_lazy::SignatureIndex::build(sig));
        self.signature_indexes
            .borrow_mut()
            .insert(key, (sig.clone(), built.clone()));
        built
    }

    pub(crate) fn register_component_alias_source(&self, component_path: Path, alias_source: Path) {
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::RegisterAliasSource(
                component_path.clone(),
                alias_source.clone(),
            ));
        }
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
            push_unique_path(
                self.component_alias_sources
                    .borrow_mut()
                    .entry(SamePathKey(component_path.clone()))
                    .or_default(),
                alias_source.clone(),
            );
            push_unique_path(
                self.component_paths_by_alias_source
                    .borrow_mut()
                    .entry(SamePathKey(alias_source))
                    .or_default(),
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
        self.component_paths_by_alias_source
            .borrow()
            .get(&SamePathKey(alias_source.clone()))
            .cloned()
            .unwrap_or_default()
    }

    /// Return alias source paths that back a selected component path.
    ///
    /// This mirrors the source path selected by OCaml compiler/ml/env.ml:1513
    /// through `scrape_alias`, while env.ml:1573-1578 stores child
    /// declaration/component thunks under the selected access path.
    pub(crate) fn alias_sources_for_component_path(&self, component_path: &Path) -> Vec<Path> {
        self.component_alias_sources
            .borrow()
            .get(&SamePathKey(component_path.clone()))
            .cloned()
            .unwrap_or_default()
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
        self.poison_store_build_for("read:find_module_alias_in_components");
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
        desc: Arc<super::decl::ValueDescription>,
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
    ) -> Option<(Path, Arc<super::decl::ValueDescription>)> {
        self.resolved_module_value_cache
            .borrow()
            .get(module_path)
            .and_then(|values| values.get(value_name))
            .cloned()
    }

    /// Cache a dotted type lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_type(
        &self,
        env_id: u64,
        module_path: &Path,
        type_name: &str,
        access_path: Path,
        id: Ident,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_module_type_cache
            .borrow_mut()
            .entry((env_id, module_path.clone()))
            .or_default()
            .insert(type_name.to_string(), (access_path, id, decl));
    }

    /// Start or stop answering repeated `typeopt` queries from a cache. Only
    /// enabled while a finished typed tree is lowered to lambda.
    pub(crate) fn set_typeopt_cache(&self, enabled: bool) {
        *self.typeopt_answers.borrow_mut() = enabled.then(ahash::AHashMap::new);
    }

    /// Answer a `typeopt` query `query` about `ty` in the env `env_id`,
    /// reusing an earlier answer while the cache is enabled.
    pub(crate) fn typeopt_answer(
        &self,
        env_id: u64,
        ty: TypeExprRef,
        query: u8,
        compute: impl FnOnce() -> bool,
    ) -> bool {
        if self.typeopt_answers.borrow().is_none() {
            return compute();
        }
        let ty = self.repr(ty);
        if let Some(answer) = self
            .typeopt_answers
            .borrow()
            .as_ref()
            .and_then(|answers| answers.get(&(env_id, ty, query)))
        {
            return *answer;
        }
        let answer = compute();
        if let Some(answers) = self.typeopt_answers.borrow_mut().as_mut() {
            answers.insert((env_id, ty, query), answer);
        }
        answer
    }

    /// The cached expansion outcome of a `Pdot` head (`ctype::PdotExpansion`).
    pub(crate) fn find_pdot_expansion(
        &self,
        scope_id: u64,
        mode: u8,
        arity: usize,
        path: &Path,
    ) -> Option<super::ctype::PdotExpansion> {
        self.pdot_expansions
            .borrow()
            .get(&PdotExpansionKeyRef { scope_id, mode, arity, path })
            .cloned()
    }

    pub(crate) fn register_pdot_expansion(
        &self,
        scope_id: u64,
        mode: u8,
        arity: usize,
        path: &Path,
        expansion: super::ctype::PdotExpansion,
    ) {
        self.pdot_expansions.borrow_mut().insert(
            PdotExpansionKey { scope_id, mode, arity, path: path.clone() },
            expansion,
        );
    }

    /// Look up a cached dotted type lookup for a resolved module access path.
    pub(crate) fn find_resolved_type_item(
        &self,
        scope_id: u64,
        path: &Path,
        strengthen_alias_types: bool,
    ) -> Option<(Ident, Arc<super::decl::TypeDeclaration>)> {
        self.resolved_type_item_cache
            .borrow()
            .get(&(scope_id, path.clone(), strengthen_alias_types))
            .cloned()
    }

    pub(crate) fn register_resolved_type_item(
        &self,
        scope_id: u64,
        path: &Path,
        strengthen_alias_types: bool,
        id: Ident,
        decl: Arc<super::decl::TypeDeclaration>,
    ) {
        self.resolved_type_item_cache
            .borrow_mut()
            .insert((scope_id, path.clone(), strengthen_alias_types), (id, decl));
    }

    pub(crate) fn find_resolved_module_type(
        &self,
        env_id: u64,
        module_path: &Path,
        type_name: &str,
    ) -> Option<(Path, Ident, Arc<super::decl::TypeDeclaration>)> {
        self.resolved_module_type_cache
            .borrow()
            .get(&(env_id, module_path.clone()))
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

    /// Share a forced declaration across persistent/global alias component views.
    ///
    /// Local declarations and functor-application paths are intentionally not
    /// published here: OCaml keeps descriptor component tables and later
    /// `find_module` thunks distinct.
    pub(crate) fn register_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
        id: Ident,
        md: Arc<super::decl::ModuleDeclaration>,
    ) {
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::RegisterQualifiedModuleDecl(
                parent_path.clone(),
                child_name.into(),
                id.clone(),
                md.clone(),
            ));
        }
        let Some(head) = parent_path.head_opt() else {
            return;
        };
        if !head.is_persistent() && !head.is_global() && head.stamp() != 0 {
            return;
        }
        self.qualified_module_decl_cache
            .borrow_mut()
            .entry(parent_path.clone())
            .or_default()
            .insert(child_name.to_string(), (id, md));
    }

    /// Look up a forced persistent/global qualified module declaration.
    pub(crate) fn find_qualified_module_decl(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<(Ident, Arc<super::decl::ModuleDeclaration>)> {
        let head = parent_path.head_opt()?;
        if !head.is_persistent() && !head.is_global() && head.stamp() != 0 {
            return None;
        }
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

    pub(crate) fn find_type_newtype_level(&self, scope_id: u64, path: &Path) -> Option<Option<i32>> {
        self.type_newtype_levels
            .borrow()
            .get(&(scope_id, path.clone()))
            .copied()
    }

    pub(crate) fn register_type_newtype_level(&self, scope_id: u64, path: &Path, level: Option<i32>) {
        self.type_newtype_levels
            .borrow_mut()
            .insert((scope_id, path.clone()), level);
    }

    pub(crate) fn find_occur_variance_mask(&self, scope_id: u64, path: &Path) -> Option<Option<u64>> {
        self.occur_variance_masks
            .borrow()
            .get(&(scope_id, path.clone()))
            .copied()
    }

    pub(crate) fn register_occur_variance_mask(&self, scope_id: u64, path: &Path, mask: Option<u64>) {
        self.occur_variance_masks
            .borrow_mut()
            .insert((scope_id, path.clone()), mask);
    }

    pub(crate) fn register_normalized_path_forward(
        &self,
        env_id: u64,
        original_path: &Path,
        normalized_path: Path,
    ) {
        self.normalized_path_forward_cache
            .borrow_mut()
            .insert((env_id, original_path.clone()), normalized_path);
    }

    pub(crate) fn find_normalized_path_forward(
        &self,
        env_id: u64,
        original_path: &Path,
    ) -> Option<Path> {
        self.normalized_path_forward_cache
            .borrow()
            .get(&(env_id, original_path.clone()))
            .cloned()
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
        self.poison_store_build_for("register_forced_normalized_path_full");
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
        self.poison_store_build_for("register_forced_type_path_compare");
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
        *self.load_paths.borrow_mut() = Arc::new(paths);
    }

    /// Set the load paths from a shared list.
    pub fn set_load_paths_shared(&self, paths: Arc<Vec<std::path::PathBuf>>) {
        *self.load_paths.borrow_mut() = paths;
    }

    /// Get the load paths.
    pub fn load_paths(&self) -> std::cell::Ref<'_, Vec<std::path::PathBuf>> {
        std::cell::Ref::map(self.load_paths.borrow(), |paths| paths.as_ref())
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
        self.replay_type_decl_log(2);
        let store = self.type_decl_by_path.borrow();
        if store.contains_key(path) {
            Some(std::cell::Ref::map(store, |s| {
                s.get(path).unwrap().as_ref()
            }))
        } else {
            None
        }
    }

    /// Look up a qualified declaration by exact Path identity.
    /// The declaration registered last under exactly `path`.
    pub fn find_type_decl_by_exact_path(
        &self,
        path: &Path,
    ) -> Option<Arc<super::decl::TypeDeclaration>> {
        self.replay_type_decl_log(3);
        let log_len = self.type_decl_log.borrow().len();
        {
            let mut memo = self.exact_path_memo.borrow_mut();
            if memo.0 != log_len {
                memo.0 = log_len;
                memo.1.clear();
            } else if let Some(found) = memo.1.get(path) {
                return found.clone();
            }
        }
        let singles = self.type_decl_by_exact_path.borrow();
        let single = singles.get(path);
        let mut found = None;
        for (position, batch) in self.exact_path_batches.borrow().iter().rev() {
            if single.is_some_and(|(single_position, _)| position < single_position) {
                break;
            }
            if let Some(decl) = batch.find_exact(path) {
                found = Some(decl.clone());
                break;
            }
        }
        let found = found.or_else(|| single.map(|(_, decl)| decl.clone()));
        self.exact_path_memo
            .borrow_mut()
            .1
            .insert(path.clone(), found.clone());
        found
    }

    // ========================================================================
    // Type Creation
    // ========================================================================

    /// Create a new type expression.
    fn alloc_type(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        // A n-ary arrow owns exactly the parameters supplied by its syntax
        // node. Its return type may itself be an arrow (a sequential
        // application such as `f(a)(b)`); never flatten that nested boundary.
        if self.in_store_build() {
            self.check_store_desc(&desc);
            return self.store.alloc_type(desc, level);
        }
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
        let mut args = vec![TypeArg::new(arg_label, arg_type)];
        let ret = {
            let desc = self.get_desc(self.repr(ret_type));
            match &*desc {
                TypeDesc::Tarrow {
                    args: ret_args,
                    ret,
                } => {
                    args.extend(ret_args.iter().cloned());
                    *ret
                }
                _ => ret_type,
            }
        };
        self.new_type(TypeDesc::Tarrow { args: args.into(), ret })
    }

    /// Create an unlabeled arrow type.
    pub fn new_arrow_simple(&self, arg: TypeExprRef, ret: TypeExprRef) -> TypeExprRef {
        self.new_arrow(ArgLabel::Nolabel, arg, ret, None)
    }

    /// Create a tuple type.
    pub fn new_tuple(&self, types: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Ttuple(types.into()))
    }

    /// Create a type constructor application.
    pub fn new_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.new_type(TypeDesc::Tconstr { path, args: args.into(), abbrev })
    }

    /// Create a type constructor at generic level (for type schemes).
    pub fn new_generic_constr(&self, path: Path, args: Vec<TypeExprRef>) -> TypeExprRef {
        let abbrev = self.alloc_abbrev(AbbrevMemo::Mnil);
        self.new_generic_type(TypeDesc::Tconstr { path, args: args.into(), abbrev })
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
    pub fn predef_option_layout(&self) -> super::variant_runtime::LayoutRef {
        if let Some(layout) = self.predef_option_layout.get() {
            layout
        } else {
            let layout = super::variant_runtime::plain_layout(
                self,
                [("None".to_string(), false), ("Some".to_string(), true)],
            );
            self.predef_option_layout.set(Some(layout));
            layout
        }
    }

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
        let mut args = vec![TypeArg::new(arg_label, arg_type)];
        let ret = {
            let desc = self.get_desc(self.repr(ret_type));
            match &*desc {
                TypeDesc::Tarrow {
                    args: ret_args,
                    ret,
                } => {
                    args.extend(ret_args.iter().cloned());
                    *ret
                }
                _ => ret_type,
            }
        };
        self.new_generic_type(TypeDesc::Tarrow { args: args.into(), ret })
    }

    /// Create a link type (for unification).
    pub fn new_link(&self, target: TypeExprRef) -> TypeExprRef {
        self.new_type(TypeDesc::Tlink(target))
    }

    /// Create a polymorphic type.
    pub fn new_poly(&self, body: TypeExprRef, vars: Vec<TypeExprRef>) -> TypeExprRef {
        self.new_type(TypeDesc::Tpoly { body, vars: vars.into() })
    }

    /// Create a universal type variable.
    pub fn new_univar(&self, name: Option<String>) -> TypeExprRef {
        self.new_type(TypeDesc::Tunivar(name))
    }

    /// Create a variant type.
    pub fn new_variant(&self, row: RowDesc) -> TypeExprRef {
        self.new_type(TypeDesc::Tvariant(Box::new(row)))
    }

    // ========================================================================
    // Type Access
    // ========================================================================

    /// Borrow the descriptor of a stored (worker-store or shared) node:
    /// this compilation's overlay copy if it wrote one, else the immutable
    /// published descriptor.
    #[inline(never)]
    fn store_desc_ref(&self, r: TypeExprRef) -> TypeDescRef<'_> {
        if r.is_shared() {
            let idx = r.shared_index();
            if let Some(index) = self.shared_desc_overlay.borrow().get(idx as usize) {
                return self.store_descs.get_at(*index).desc();
            }
            return std::cell::Ref::map(self.shared_pages.borrow(), |pages| {
                &super::shared_store::page_node(pages, idx).desc
            });
        }
        if let Some(index) = self.store_desc_overlay.borrow().get(r.store_index()) {
            return self.store_descs.get_at(*index).desc();
        }
        self.store.node(r).desc()
    }

    /// Clone the descriptor so callers can hold it across node mutations.
    #[inline]
    pub fn get_desc(&self, r: TypeExprRef) -> TypeDescSnapshot {
        TypeDescSnapshot(self.with_desc(r, TypeDesc::clone))
    }

    /// Apply `f` to the descriptor of `r`. The local path is a plain
    /// `RefCell` borrow, so hot readers (`repr`, `get_desc`) inline exactly as
    /// they did before stored nodes had two representations.
    #[inline(always)]
    pub(crate) fn with_desc<R>(&self, r: TypeExprRef, f: impl FnOnce(&TypeDesc) -> R) -> R {
        if r.is_store() {
            return f(&self.store_desc_ref(r));
        }
        self.poison_store_build();
        f(&self.types.get(r).desc())
    }

    /// Borrow the descriptor of a type without cloning it.
    ///
    /// Prefer this in short read-only hot paths. Use `get_desc()` when the
    /// descriptor must be held across code that may mutate the same type node.
    /// Local nodes are by far the most common (hundreds of millions of reads
    /// per build), so their path is inlined into callers.
    #[inline]
    pub fn borrow_desc(&self, r: TypeExprRef) -> TypeDescRef<'_> {
        if r.is_store() {
            return self.store_desc_ref(r);
        }
        self.poison_store_build();
        self.types.get(r).desc()
    }

    /// Get the level of a type.
    #[inline]
    pub fn get_level(&self, r: TypeExprRef) -> i32 {
        if r.is_store() {
            return self.store_level(r);
        }
        self.poison_store_build();
        self.types.get(r).level()
    }

    #[inline(never)]
    fn store_level(&self, r: TypeExprRef) -> i32 {
        if r.is_shared() {
            let idx = r.shared_index();
            return self
                .shared_level_overlay
                .borrow()
                .get(idx as usize)
                .copied()
                .unwrap_or_else(|| super::shared_store::page_node(&self.shared_pages.borrow(), idx).level);
        }
        self.store_level_overlay
            .borrow()
            .get(r.store_index())
            .copied()
            .unwrap_or_else(|| self.store.node(r).level())
    }

    /// Number of allocated type expressions.
    pub fn type_expr_count(&self) -> usize {
        self.types.len()
    }

    /// Set the level of a type. Stored nodes are never written in place
    /// unless the current store build is still creating them: the write goes
    /// to this compilation's overlay.
    #[inline]
    pub fn set_level(&self, r: TypeExprRef, level: i32) {
        if r.is_store() {
            if r.is_shared() {
                self.shared_level_overlay
                    .borrow_mut()
                    .set(r.shared_index() as usize, level);
                return;
            }
            if self.store_build_owns(r) {
                self.store.set_level_backing(r, level);
                return;
            }
            self.store_level_overlay
                .borrow_mut()
                .set(r.store_index(), level);
        } else {
            self.poison_store_build();
            self.types.get(r).set_level(level);
        }
    }

    /// Set the descriptor without changing the immutable dependency graph.
    #[inline]
    pub fn set_desc(&self, r: TypeExprRef, desc: TypeDesc) {
        if r.is_store() {
            if r.is_shared() {
                self.set_shared_desc(r, desc);
                return;
            }
            if self.store_build_owns(r) {
                self.check_store_desc(&desc);
                self.store.set_desc_backing(r, desc);
                return;
            }
            let index = self
                .store_desc_overlay
                .borrow()
                .get(r.store_index())
                .copied();
            if let Some(index) = index {
                self.store_descs.get_at(index).set_desc(desc);
            } else {
                let original = self.store.node(r);
                let index =
                    self.store_descs
                        .push_raw(TypeExpr::new(desc, original.level(), original.id()));
                self.store_desc_overlay
                    .borrow_mut()
                    .set(r.store_index(), index);
            }
        } else {
            self.poison_store_build();
            self.types.get(r).set_desc(desc);
        }
    }

    /// Descriptor write to a shared dependency node: copy-on-write into this
    /// compilation's overlay; the published node is never mutated.
    #[inline(never)]
    fn set_shared_desc(&self, r: TypeExprRef, desc: TypeDesc) {
        let idx = r.shared_index();
        let index = self.shared_desc_overlay.borrow().get(idx as usize).copied();
        if let Some(index) = index {
            self.store_descs.get_at(index).set_desc(desc);
        } else {
            let (level, id) = {
                let pages = self.shared_pages.borrow();
                let original = super::shared_store::page_node(&pages, idx);
                (original.level, original.id)
            };
            let index = self.store_descs.push_raw(TypeExpr::new(desc, level, id));
            self.shared_desc_overlay
                .borrow_mut()
                .set(idx as usize, index);
        }
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
            store_desc_states: (0..self.store_descs.len())
                .map(|index| self.store_descs.get_at(index).desc().clone())
                .collect(),
            store_desc_overlay: self.store_desc_overlay.borrow().clone(),
            store_level_overlay: self.store_level_overlay.borrow().clone(),
            row_field_states,
            abbrev_states,
            store_abbrev_overlay: self.store_abbrev_overlay.borrow().clone(),
            store_row_field_overlay: self.store_row_field_overlay.borrow().clone(),
            shared_desc_overlay: self.shared_desc_overlay.borrow().clone(),
            shared_level_overlay: self.shared_level_overlay.borrow().clone(),
            shared_abbrev_overlay: self.shared_abbrev_overlay.borrow().clone(),
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

        for (index, desc) in snapshot.store_desc_states.into_iter().enumerate() {
            self.store_descs.get_at(index).set_desc(desc);
        }
        *self.store_desc_overlay.borrow_mut() = snapshot.store_desc_overlay;
        *self.store_level_overlay.borrow_mut() = snapshot.store_level_overlay;
        *self.store_abbrev_overlay.borrow_mut() = snapshot.store_abbrev_overlay;
        *self.store_row_field_overlay.borrow_mut() = snapshot.store_row_field_overlay;
        *self.shared_desc_overlay.borrow_mut() = snapshot.shared_desc_overlay;
        *self.shared_level_overlay.borrow_mut() = snapshot.shared_level_overlay;
        *self.shared_abbrev_overlay.borrow_mut() = snapshot.shared_abbrev_overlay;
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
        self.poison_store_build_for("set_arity_alias");
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
        self.poison_store_build_for("register_record_labels");
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
        self.record_labels_cache.borrow().get(type_path).cloned()
    }

    /// Cache reconstructed record label descriptions for a type path.
    pub fn register_record_label_descriptions(
        &self,
        type_path: &Path,
        labels: Arc<Vec<super::decl::LabelDescription>>,
    ) {
        self.poison_store_build_for("register_record_label_descriptions");
        let summary = Arc::new(RecordLabelDescriptionSummary::from_labels(&labels));
        self.record_label_descriptions_cache
            .borrow_mut()
            .insert(type_path.clone(), labels);
        self.record_label_description_summaries_cache
            .borrow_mut()
            .insert(type_path.clone(), summary);
    }

    /// Register label descriptions and their already-built summary.
    pub(crate) fn register_record_label_descriptions_with_summary(
        &self,
        type_path: &Path,
        labels: Arc<Vec<super::decl::LabelDescription>>,
        summary: Arc<RecordLabelDescriptionSummary>,
    ) {
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
        self.poison_store_build_for("cache_qualified_record_label");
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
        self.poison_store_build_for("cache_synthesized_record_lident");
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
        self.poison_store_build_for("set_dict_pattern_labels");
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
        for memo in refs {
            self.write_abbrev(memo, AbbrevMemo::Mnil);
        }
        self.memoized_abbrev_refs.borrow_mut().clear();
    }

    /// Current value of a memo cell: this compilation's overlay for store
    /// cells, the local table otherwise. Missing cells read as `Mnil`.
    fn read_abbrev(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        if memo.is_shared() {
            return self
                .shared_abbrev_overlay
                .borrow()
                .get(memo.shared_index())
                .cloned()
                .unwrap_or(AbbrevMemo::Mnil);
        }
        if memo.is_store() {
            if let Some(value) = self.store_abbrev_overlay.borrow().get(memo.store_index()) {
                return value.clone();
            }
            return self.store.abbrev(memo);
        }
        let abbrevs = self.abbrevs.borrow();
        abbrevs
            .get(memo.index())
            .map(|cell| cell.borrow().clone())
            .unwrap_or(AbbrevMemo::Mnil)
    }

    /// Apply `f` to a memo cell without copying it (the chain scans below
    /// only compare paths and follow `next`).
    fn with_abbrev<R>(&self, memo: AbbrevMemoRef, f: impl FnOnce(&AbbrevMemo) -> R) -> R {
        if memo.is_shared() {
            return match self.shared_abbrev_overlay.borrow().get(memo.shared_index()) {
                Some(value) => f(value),
                None => f(&AbbrevMemo::Mnil),
            };
        }
        if memo.is_store() {
            if let Some(value) = self.store_abbrev_overlay.borrow().get(memo.store_index()) {
                return f(value);
            }
            return self.store.with_abbrev(memo, f);
        }
        let abbrevs = self.abbrevs.borrow();
        match abbrevs.get(memo.index()) {
            Some(cell) => f(&cell.borrow()),
            None => f(&AbbrevMemo::Mnil),
        }
    }

    /// Write a memo cell; store cells are written to this compilation's
    /// overlay only. Missing local cells are ignored.
    fn write_abbrev(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if memo.is_shared() {
            self.shared_abbrev_overlay
                .borrow_mut()
                .set(memo.shared_index(), value);
            return;
        }
        if memo.is_store() {
            self.store_abbrev_overlay
                .borrow_mut()
                .set(memo.store_index(), value);
            return;
        }
        let abbrevs = self.abbrevs.borrow();
        if let Some(cell) = abbrevs.get(memo.index()) {
            *cell.borrow_mut() = value;
        }
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
            let step = self.with_abbrev(current, |node| match node {
                AbbrevMemo::Mnil => Err(None),
                AbbrevMemo::Mcons {
                    private_flag: cached_private,
                    path: cached_path,
                    expansion,
                    next,
                    ..
                } => {
                    if private_flag <= *cached_private && path.same(cached_path) {
                        Err(Some(*expansion))
                    } else {
                        Ok(*next)
                    }
                }
                AbbrevMemo::Mlink(next) => Ok(*next),
            });
            match step {
                Ok(next) => current = next,
                Err(found) => return found,
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
            let step = self.with_abbrev(current, |node| match node {
                AbbrevMemo::Mnil => Err(None),
                AbbrevMemo::Mcons {
                    private_flag: cached_private,
                    path: cached_path,
                    abbrev,
                    next,
                    ..
                } => {
                    // Match OCaml find_repr: only public memo entries participate
                    // in repr reuse during copy.
                    if *cached_private == PrivateFlag::Public && path.same(cached_path) {
                        Err(Some(*abbrev))
                    } else {
                        Ok(*next)
                    }
                }
                AbbrevMemo::Mlink(next) => Ok(*next),
            });
            match step {
                Ok(next) => current = next,
                Err(found) => return found,
            }
        }
        None
    }

    /// Snapshot an abbreviation memo node.
    pub fn get_abbrev_memo(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        self.read_abbrev(memo)
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
        self.write_abbrev(memo, AbbrevMemo::Mnil);
    }

    /// Overwrite a per-node abbreviation memo chain with a saved snapshot.
    pub fn restore_abbrev_memo(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        self.write_abbrev(memo, value);
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

        if memo.is_store() {
            let previous = self.read_abbrev(memo);
            let next = if matches!(previous, AbbrevMemo::Mnil) {
                AbbrevMemoRef::nil()
            } else {
                self.alloc_abbrev(previous)
            };
            self.write_abbrev(
                memo,
                AbbrevMemo::Mcons {
                    private_flag,
                    path,
                    abbrev,
                    expansion,
                    next,
                },
            );
            self.memoized_abbrev_refs.borrow_mut().push(memo);
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
        if self.in_store_build() {
            if let AbbrevMemo::Mcons {
                abbrev, expansion, next, ..
            } = &memo
            {
                self.check_store_ref(*abbrev);
                self.check_store_ref(*expansion);
                self.check_store_memo(*next);
            }
            return self.store.alloc_abbrev(memo);
        }
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
        if self.in_store_build() {
            if let Some(field) = &field {
                self.check_store_row_field(field);
            }
            return self.store.alloc_row_field(field);
        }
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
        if rf.is_store() {
            if let Some(value) = self.store_row_field_overlay.borrow().get(rf.store_index()) {
                return value.clone();
            }
            return self.store.row_field(rf);
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
        if rf.is_store() {
            if self.in_store_build() && rf.store_index() >= self.store_build_row_start.get() {
                self.check_store_row_field(&field);
                self.store.set_row_field_backing(rf, Some(field));
                return;
            }
            self.store_row_field_overlay
                .borrow_mut()
                .set(rf.store_index(), Some(field));
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
        if rf.is_store() {
            if self.in_store_build() && rf.store_index() >= self.store_build_row_start.get() {
                self.store.set_row_field_backing(rf, None);
                return;
            }
            self.store_row_field_overlay
                .borrow_mut()
                .set(rf.store_index(), None);
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.index()) {
            *cell.borrow_mut() = None;
        }
    }

    // ========================================================================
    // Field Kinds
    // ========================================================================

    /// Allocate a field kind reference.
    fn alloc_field_kind(&self, kind: Option<FieldKind>) -> FieldKindRef {
        if self.in_store_build() {
            // Field-kind cells are never read back; `Fvar` links stay unchecked.
            return self.store.alloc_field_kind(kind);
        }
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

    /// Shares the compilation's identifier stream with additive downstream
    /// stages. M5's inactive indexed path uses this instead of reconstructing
    /// a fresh generator from a scanned stamp frontier.
    pub(crate) fn id_generator(&self) -> Arc<IdGenerator> {
        Arc::clone(&self.id_gen)
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
        self.poison_store_build_for("register_raw_module_sig");
        self.raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn register_gentype_raw_module_sig(
        &self,
        name: &str,
        sig: Arc<super::decl::Signature>,
    ) {
        self.poison_store_build_for("register_gentype_raw_module_sig");
        self.gentype_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
    }

    pub(crate) fn register_gentype_portable_raw_module_sig(
        &self,
        name: &str,
        pers_struct: Arc<crate::cmi::portable_types::PortablePersStruct>,
    ) {
        self.poison_store_build_for("register_gentype_portable_raw_module_sig");
        self.gentype_portable_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), pers_struct);
    }

    pub(crate) fn get_gentype_raw_module_sig(
        &self,
        name: &str,
    ) -> Option<Arc<super::decl::Signature>> {
        if let Some(sig) = self.gentype_raw_module_sigs.borrow().get(name).cloned() {
            return Some(sig);
        }
        let portable = self
            .gentype_portable_raw_module_sigs
            .borrow_mut()
            .remove(name)?;
        let sig = Arc::new(crate::cmi::portable_types::internalize_raw_signature(
            &portable, self,
        )?);
        self.gentype_raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig.clone());
        Some(sig)
    }

    pub fn has_raw_module_sig(&self, name: &str) -> bool {
        self.poison_store_build_for("read:has_raw_module_sig");
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
        self.poison_store_build_for("get_or_load_raw_module_sig");
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
        if self.in_store_build() {
            self.record_store_effect(StoreEffect::TriggerRename(module_name.into()));
            self.suspend_store_build(|| self.trigger_module_sig_rename(module_name));
            return;
        }
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
        self.poison_store_build_for("rename_one_module_sig");
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
            let renamed = self.defer_renamed_sig("type_context_lazy_rename", sig);
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
        if self.in_store_build() {
            return self.store_binder(&Ident::create_persistent(name));
        }
        // OCaml compiler/ext/ident.ml:28-40 increments the active
        // currentstamp directly in `Ident.create`/`Ident.rename`; unrelated
        // helper-created local identifiers must not advance the typedtree
        // context's stamp stream.
        self.id_gen.create(name)
    }

    /// Fresh binder for shared store data. The compilation's own stamp stream
    /// advances exactly as it would have (and later users replay that), but
    /// the binder gets a store stamp so it can never be `Ident::same` as an
    /// identifier of another compilation.
    fn store_binder(&self, id: &Ident) -> Ident {
        self.id_gen.next_stamp();
        let mut effects = self.store_build_effects.borrow_mut();
        match effects.last_mut() {
            Some(StoreEffect::Stamps(count)) => *count += 1,
            _ => effects.push(StoreEffect::Stamps(1)),
        }
        let stamp = super::thread_store::next_store_stamp();
        let mut fresh = id.with_stamp(stamp);
        if id.is_persistent() {
            fresh = Ident::new(id.name(), stamp, crate::ident::IdentFlags::NONE);
        }
        fresh
    }

    /// Whether allocations currently go to the worker store.
    #[inline(always)]
    pub(crate) fn in_store_build(&self) -> bool {
        self.store_build_depth.get() != 0
    }

    /// Record that the current store build depends on compilation-local
    /// state; its result is then kept private to this compilation.
    #[inline(always)]
    pub(crate) fn poison_store_build(&self) {
        self.poison_store_build_for("local-read");
    }

    #[inline(always)]
    pub(crate) fn poison_store_build_for(&self, reason: &'static str) {
        if self.store_build_depth.get() != 0 {
            self.poison_store_build_slow(reason);
        }
    }

    #[cold]
    #[inline(never)]
    fn poison_store_build_slow(&self, reason: &'static str) {
        if !self.store_build_poisoned.replace(true) && store_debug_enabled() {
            eprintln!("[store-poison] {reason}");
            if std::env::var_os("RESCRIPT_STORE_DEBUG_BT").is_some() {
                let bt = std::backtrace::Backtrace::force_capture().to_string();
                let frames: Vec<&str> = bt
                    .lines()
                    .filter(|l| l.contains("rescript_compiler::") && !l.contains("poison_store"))
                    .take(8)
                    .collect();
                eprintln!(
                    "[store-poison-bt] {reason} :: {}",
                    frames.join(" <- ").replace("rescript_compiler::", "")
                );
            }
        }
    }

    /// Whether `r` is a store node created by the current store build.
    #[inline]
    fn store_build_owns(&self, r: TypeExprRef) -> bool {
        self.in_store_build()
            && !r.is_shared()
            && r.store_index() >= self.store_build_type_start.get()
    }

    #[inline]
    fn check_store_ref(&self, r: TypeExprRef) {
        if !r.is_store() {
            self.poison_store_build();
        }
    }

    #[inline]
    fn check_store_memo(&self, memo: AbbrevMemoRef) {
        // Memo cells 0 (`Mnil`) and 1 (`simple_abbrevs`) have the same role in
        // every compilation.
        if !memo.is_store() && memo.0 > 1 {
            self.poison_store_build();
        }
    }

    fn check_store_row_field(&self, field: &RowField) {
        match field {
            RowField::Rpresent(Some(ty)) => self.check_store_ref(*ty),
            RowField::Rpresent(None) | RowField::Rabsent => {}
            RowField::Reither { types, link, .. } => {
                for ty in types {
                    self.check_store_ref(*ty);
                }
                if !link.is_null() && !link.is_store() {
                    self.poison_store_build();
                }
            }
        }
    }

    /// Poison the store build if `desc` refers to compilation-local cells.
    fn check_store_desc(&self, desc: &TypeDesc) {
        match desc {
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
            TypeDesc::Tarrow { args, ret } => {
                for arg in args.iter() {
                    self.check_store_ref(arg.typ);
                }
                self.check_store_ref(*ret);
            }
            TypeDesc::Ttuple(items) => {
                for ty in items.iter() {
                    self.check_store_ref(*ty);
                }
            }
            TypeDesc::Tconstr { args, abbrev, .. } => {
                for ty in args.iter() {
                    self.check_store_ref(*ty);
                }
                self.check_store_memo(*abbrev);
            }
            TypeDesc::Tobject { fields, name } => {
                self.check_store_ref(*fields);
                if let Some((_, args)) = name {
                    for ty in args.iter() {
                        self.check_store_ref(*ty);
                    }
                }
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                self.check_store_ref(*typ);
                self.check_store_ref(*rest);
            }
            TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => self.check_store_ref(*ty),
            TypeDesc::Tvariant(row) => {
                self.check_store_ref(row.row_more);
                for (_, field) in row.row_fields.iter() {
                    self.check_store_row_field(field);
                }
                if let Some((_, args)) = &row.row_name {
                    for ty in args {
                        self.check_store_ref(*ty);
                    }
                }
            }
            TypeDesc::Tpoly { body, vars } => {
                self.check_store_ref(*body);
                for ty in vars.iter() {
                    self.check_store_ref(*ty);
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for ty in args.iter() {
                    self.check_store_ref(*ty);
                }
            }
        }
    }

    /// Run `build` with every type-graph allocation going to the worker
    /// store, so its result can be shared with later compilations on this
    /// worker. Returns the replay record to publish with the result, or
    /// `None` when the build read compilation-local state (the result is
    /// then only valid in this compilation).
    pub(crate) fn build_in_store<R>(&self, build: impl FnOnce() -> R) -> (R, Option<Arc<StorePiece>>) {
        let depth = self.store_build_depth.get();
        let outer_effects = std::mem::take(&mut *self.store_build_effects.borrow_mut());
        let outer_poisoned = self.store_build_poisoned.replace(false);
        if depth == 0 {
            self.store_build_type_start.set(self.store.type_count());
            self.store_build_row_start.set(self.store.row_field_count());
        }
        self.store_build_depth.set(depth + 1);
        super::thread_store::set_store_build_depth(depth + 1);
        let result = build();
        self.store_build_depth.set(depth);
        super::thread_store::set_store_build_depth(depth);
        let effects = std::mem::replace(&mut *self.store_build_effects.borrow_mut(), outer_effects);
        let poisoned = self.store_build_poisoned.replace(outer_poisoned);
        if poisoned {
            if depth > 0 {
                // The enclosing build may hold this result.
                self.store_build_poisoned.set(true);
                self.store_build_effects.borrow_mut().extend(effects);
            }
            return (result, None);
        }
        let piece = Arc::new(StorePiece {
            id: NEXT_STORE_PIECE_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            effects,
        });
        self.touched_store_pieces.borrow_mut().insert(piece.id);
        if depth > 0 {
            self.store_build_effects
                .borrow_mut()
                .push(StoreEffect::Piece(piece.clone()));
        }
        (result, Some(piece))
    }

    /// Note that this compilation is using shared store data built by `piece`:
    /// the first time, apply the effects that building it had.
    pub(crate) fn touch_store_piece(&self, piece: &Arc<StorePiece>) {
        if self.in_store_build() {
            self.store_build_effects
                .borrow_mut()
                .push(StoreEffect::Piece(piece.clone()));
        }
        if self.touched_store_pieces.borrow().contains(&piece.id) {
            return;
        }
        self.suspend_store_build(|| self.replay_store_piece(piece));
    }

    fn replay_store_piece(&self, piece: &StorePiece) {
        if !self.touched_store_pieces.borrow_mut().insert(piece.id) {
            return;
        }
        for effect in &piece.effects {
            match effect {
                StoreEffect::Stamps(count) => {
                    self.id_gen.advance_stamp_by(*count);
                }
                StoreEffect::Piece(inner) => self.replay_store_piece(inner),
                StoreEffect::RegisterComponents(key, components) => {
                    self.qualified_module_components_cache
                        .borrow_mut()
                        .insert(key.clone(), components.clone());
                }
                StoreEffect::PreparePers(name) => {
                    if let Some(mut pers) = self.persistent_env_clone() {
                        let _ = pers.find_pers_struct(name, self);
                    }
                }
                StoreEffect::TriggerRename(name) => self.trigger_module_sig_rename(name),
                StoreEffect::RegisterTypeDecl(name, decl) => {
                    self.register_shared_type_decl(name, decl.clone())
                }
                StoreEffect::RegisterTypeDeclByStamp(stamp, decl) => {
                    self.register_shared_type_decl_by_stamp(*stamp, decl.clone())
                }
                StoreEffect::RegisterAliasSource(component, source) => {
                    self.register_component_alias_source(component.clone(), source.clone())
                }
                StoreEffect::RegisterQualifiedModuleDecl(parent, name, id, md) => {
                    self.register_qualified_module_decl(parent, name, id.clone(), md.clone())
                }
            }
        }
    }

    /// Record an effect of the current store build on this compilation.
    pub(crate) fn record_store_effect(&self, effect: StoreEffect) {
        if !self.in_store_build() {
            return;
        }
        let mut effects = self.store_build_effects.borrow_mut();
        let duplicate = match &effect {
            StoreEffect::PreparePers(name) => effects
                .iter()
                .any(|e| matches!(e, StoreEffect::PreparePers(other) if other == name)),
            StoreEffect::TriggerRename(name) => effects
                .iter()
                .any(|e| matches!(e, StoreEffect::TriggerRename(other) if other == name)),
            _ => false,
        };
        if !duplicate {
            effects.push(effect);
        }
    }

    /// Run `f` as this compilation (allocating locally), in the middle of a
    /// store build: used for effects on the compilation that are journaled
    /// separately.
    pub(crate) fn suspend_store_build<R>(&self, f: impl FnOnce() -> R) -> R {
        let depth = self.store_build_depth.replace(0);
        super::thread_store::set_store_build_depth(0);
        let result = f();
        self.store_build_depth.set(depth);
        super::thread_store::set_store_build_depth(depth);
        result
    }

    /// Rename an identifier using the typing context's shared stamp source.
    pub fn rename_ident(&self, id: &Ident) -> Ident {
        if self.in_store_build() {
            if self.reserved_rename_stamps.get().is_some() {
                // A deferred rename uses stamps this compilation reserved.
                self.poison_store_build();
            } else {
                return self.store_binder(id);
            }
        }
        if let Some((next, last)) = self.reserved_rename_stamps.get() {
            assert!(
                next <= last,
                "deferred signature rename used more stamps than it reserved"
            );
            self.reserved_rename_stamps.set(Some((next + 1, last)));
            return id.with_stamp(next);
        }
        // See `create_ident`: this mirrors compiler/ext/ident.ml:38-40.
        id.rename(&self.id_gen)
    }

    /// Force a lazy `Subst.signature Subst.identity` rename of `source`.
    ///
    /// OCaml `ps_sig` (compiler/ml/env.ml:669-678) is forced by `find_module`
    /// (compiler/ml/env.ml:865-875), and most forces only come from
    /// `normalize_path` (compiler/ml/env.ml:903-914), which discards the
    /// signature unless it is an alias. The only observable effect of the
    /// force is the fresh binder stamps allocated by `Subst.signature`
    /// (compiler/ml/subst.ml:358-364), so reserve exactly those stamps now and
    /// copy the signature with them when its contents are first read.
    pub(crate) fn defer_renamed_sig(
        &self,
        kind: &'static str,
        source: Arc<super::decl::Signature>,
    ) -> Arc<DeferredRenamedSig> {
        let stamp_count = crate::cmi::persistent_env::signature_freshen_stamp_count(&source);
        let first_stamp = self.id_gen.current_stamp() + 1;
        self.id_gen.advance_stamp_by(stamp_count);
        Arc::new(DeferredRenamedSig {
            kind,
            source,
            first_stamp,
            stamp_count,
            renamed: std::sync::OnceLock::new(),
        })
    }

    /// Copy a deferred renamed signature, using its reserved stamps.
    pub(crate) fn materialize_renamed_sig(
        &self,
        deferred: &DeferredRenamedSig,
    ) -> Arc<super::decl::Signature> {
        deferred
            .renamed
            .get_or_init(|| {
                let last = deferred.first_stamp + deferred.stamp_count - 1;
                let saved = self
                    .reserved_rename_stamps
                    .replace(Some((deferred.first_stamp, last)));
                let renamed = crate::cmi::persistent_env::freshened_signature_bound_idents_from_kind(
                    deferred.kind,
                    deferred.source.as_ref(),
                    self,
                );
                let cursor = self.reserved_rename_stamps.replace(saved);
                assert_eq!(
                    cursor,
                    Some((last + 1, last)),
                    "deferred signature rename used fewer stamps than it reserved"
                );
                Arc::new(renamed)
            })
            .clone()
    }

    /// Materialized renamed signature for `module_name`, if it was forced.
    pub(crate) fn renamed_module_sig(&self, module_name: &str) -> Option<Arc<super::decl::Signature>> {
        self.poison_store_build_for("read:renamed_module_sig");
        let deferred = self.renamed_module_sigs.borrow().get(module_name).cloned()?;
        Some(self.materialize_renamed_sig(&deferred))
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
    #[inline]
    pub fn repr(&self, t: TypeExprRef) -> TypeExprRef {
        // Fast path, inlined into callers: `t` is already a representative.
        let next = self.with_desc(t, |desc| match desc {
            TypeDesc::Tlink(next) => Some(*next),
            TypeDesc::Tfield {
                kind: FieldKind::Fabsent,
                rest,
                ..
            } => Some(*rest),
            _ => None,
        });
        let Some(first_next) = next else {
            return t;
        };
        self.repr_chain(t, first_next)
    }

    /// Follow a link chain starting at `t` (whose next node is `first_next`)
    /// and compress it.
    #[inline(never)]
    fn repr_chain(&self, t: TypeExprRef, first_next: TypeExprRef) -> TypeExprRef {

        // Follow chain to the end, collecting nodes for path compression.
        // Uses a fixed-size stack buffer — chains longer than 32 are
        // vanishingly rare and just won't get full compression.
        let mut chain = [TypeExprRef(0); 32];
        let mut chain_len: usize = 1;
        chain[0] = t;

        let mut current = first_next;
        for _ in 0..10_000 {
            let next = self.with_desc(current, |desc| match desc {
                TypeDesc::Tlink(next) => Some(*next),
                TypeDesc::Tfield {
                    kind: FieldKind::Fabsent,
                    rest,
                    ..
                } => Some(*rest),
                _ => None,
            });
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

        // Path compression: relink all traversed nodes to the representative
        // (OCaml `Btype.repr_link`). Stored handles use compilation-local
        // descriptor overlays, just like ordinary unification writes.
        for i in 0..chain_len {
            let node = chain[i];
            if node != current {
                // A direct link already points at the representative. OCaml
                // btype.ml:107-115 does not log/write it (`compress = false`).
                let direct =
                    matches!(*self.borrow_desc(node), TypeDesc::Tlink(target) if target == current);
                if !direct {
                    self.set_desc(node, TypeDesc::Tlink(current));
                }
            }
        }

        current
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_node_writes_stay_in_the_writing_compilation() {
        let a = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        let pool = a.store.shared_pool();
        let base = pool
            .publish(2, 0, |_| {
                (
                    vec![(TypeDesc::Tvar(None), GENERIC_LEVEL), (TypeDesc::Tnil, GENERIC_LEVEL)],
                    Vec::new(),
                )
            })
            .expect("pool has room");
        let var = super::super::shared_store::shared_ref(base, 0);
        let nil = super::super::shared_store::shared_ref(base, 1);
        assert!(var.is_shared() && a.contains_type_ref(var));

        // OCaml `link_type`/level updates on a dependency node: visible in this
        // compilation only.
        a.set_desc(var, TypeDesc::Tlink(nil));
        a.set_level(var, 3);
        assert_eq!(a.repr(var), nil);
        assert_eq!(a.get_level(var), 3);

        let b = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        assert!(matches!(*b.borrow_desc(var), TypeDesc::Tvar(None)));
        assert_eq!(b.get_level(var), GENERIC_LEVEL);
        std::thread::spawn(move || {
            let c = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
            assert!(matches!(*c.borrow_desc(var), TypeDesc::Tvar(None)));
            assert!(matches!(*c.borrow_desc(nil), TypeDesc::Tnil));
        })
        .join()
        .unwrap();

        // Backtracking restores the published view.
        let snapshot = b.snapshot_type_state();
        b.set_desc(var, TypeDesc::Tnil);
        b.restore_type_state(snapshot);
        assert!(matches!(*b.borrow_desc(var), TypeDesc::Tvar(None)));
    }

    #[test]
    fn store_build_allocates_shared_nodes_and_replays_stamps() {
        let builder = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        let ((ty, binder), piece) = builder.build_in_store(|| {
            let var = builder.new_generic_var(Some("a".into()));
            let ty = builder.new_generic_type(TypeDesc::Ttuple(vec![var, var].into()));
            let binder = builder.rename_ident(&Ident::create_persistent("t"));
            (ty, binder)
        });
        let piece = piece.expect("store build stays shareable");
        assert!(ty.is_store(), "store builds allocate in the worker store");
        // The builder's own stamp stream advanced as for a local rename, but
        // the binder is in the store range, disjoint from local stamps.
        assert_eq!(builder.current_stamp(), 11);
        assert!(binder.stamp() > super::super::thread_store::next_store_stamp() - 1000);
        assert!(binder.stamp() >= 1 << 29);
        drop(builder);

        // A later compilation on the worker reuses the node and replays the
        // stamp once, on first touch.
        let user = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(10)));
        user.touch_store_piece(&piece);
        user.touch_store_piece(&piece);
        assert_eq!(user.current_stamp(), 11);
        match &*user.get_desc(ty) {
            TypeDesc::Ttuple(items) => assert_eq!(items.len(), 2),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn store_build_reading_local_nodes_is_private() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_generic_var(None);
        let (_, piece) = ctx.build_in_store(|| {
            ctx.new_generic_type(TypeDesc::Ttuple(vec![local].into()))
        });
        assert!(piece.is_none(), "a build referring to a local node is not shared");
        let (_, piece) = ctx.build_in_store(|| ctx.repr(local));
        assert!(piece.is_none(), "a build reading a local node is not shared");
    }

    #[test]
    fn downstream_id_generator_accessor_keeps_compilation_identity() {
        let generator = Arc::new(IdGenerator::with_start_stamp(17));
        let ctx = TypeContext::new(generator.clone());
        let downstream = ctx.id_generator();
        assert!(Arc::ptr_eq(&generator, &downstream));
        assert_eq!(downstream.create("downstream").stamp(), 18);
        assert_eq!(ctx.current_stamp(), 18);
    }

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
    fn variant_layout_can_be_read_without_cloning() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let layout_ref = super::super::variant_runtime::plain_layout(
            &ctx,
            [("First".to_string(), false), ("Second".to_string(), true)],
        );

        let constructor_count =
            ctx.with_variant_layout(layout_ref, |layout| layout.constructors.len());

        assert_eq!(constructor_count, 2);
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
    fn store_access_and_overlay_backtracking() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let local = ctx.new_var(None);
        let stored = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        assert!(matches!(*ctx.borrow_desc(stored), TypeDesc::Tnil));
        assert_eq!(ctx.get_level(stored), GENERIC_LEVEL);
        assert_eq!(ctx.repr(stored), stored);
        let link = ctx.new_link(stored);
        assert_eq!(ctx.repr(link), stored);
        assert_ne!(local, stored);

        let memo = ctx.store.alloc_abbrev(AbbrevMemo::Mnil);
        let row = ctx.store.alloc_row_field(Some(RowField::Rabsent));
        let snapshot = ctx.snapshot_type_state();
        ctx.restore_abbrev_memo(memo, AbbrevMemo::Mlink(AbbrevMemoRef::nil()));
        ctx.set_row_field(row, RowField::Rpresent(Some(local)));
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mlink(_)));
        assert!(matches!(ctx.get_row_field(row), Some(RowField::Rpresent(Some(t))) if t == local));
        assert!(matches!(ctx.store.abbrev(memo), AbbrevMemo::Mnil));
        assert!(matches!(ctx.store.row_field(row), Some(RowField::Rabsent)));
        ctx.restore_type_state(snapshot);
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mnil));
        assert!(matches!(ctx.get_row_field(row), Some(RowField::Rabsent)));

        ctx.clear_row_field(row);
        assert!(ctx.get_row_field(row).is_none());
        assert!(matches!(ctx.store.row_field(row), Some(RowField::Rabsent)));
        ctx.memoized_abbrev_refs.borrow_mut().push(memo);
        ctx.restore_abbrev_memo(memo, AbbrevMemo::Mlink(AbbrevMemoRef::nil()));
        ctx.clear_abbrev_memos();
        assert!(matches!(ctx.get_abbrev_memo(memo), AbbrevMemo::Mnil));
    }

    #[test]
    fn store_descriptor_and_level_writes_are_isolated_and_backtracked() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let ty = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        let untouched = ctx.store.alloc_type(TypeDesc::Tvar(None), GENERIC_LEVEL);
        let initial = ctx.snapshot_type_state();
        ctx.set_desc(ty, TypeDesc::Tvar(Some("stored".into())));
        ctx.set_level(ty, 12);
        let changed = ctx.snapshot_type_state();
        let local = ctx.new_var(None);
        super::super::ctype::link_type(&ctx, ty, local);
        assert_eq!(ctx.repr(ty), local);
        assert_eq!(ctx.get_level(ty), 12);
        assert!(
            matches!(*ctx.borrow_desc(local), TypeDesc::Tvar(Some(ref name)) if name == "stored")
        );
        ctx.set_desc(untouched, TypeDesc::Tlink(local));
        ctx.set_level(untouched, 5);
        assert!(matches!(*ctx.store.node(ty).desc(), TypeDesc::Tnil));
        assert_eq!(ctx.store.node(ty).level(), GENERIC_LEVEL);
        ctx.restore_type_state(changed);
        assert!(matches!(*ctx.borrow_desc(ty), TypeDesc::Tvar(Some(ref name)) if name == "stored"));
        assert_eq!(ctx.get_level(ty), 12);
        assert!(matches!(*ctx.borrow_desc(untouched), TypeDesc::Tvar(None)));
        assert_eq!(ctx.get_level(untouched), GENERIC_LEVEL);
        ctx.restore_type_state(initial);
        assert!(matches!(*ctx.borrow_desc(ty), TypeDesc::Tnil));
        assert_eq!(ctx.get_level(ty), GENERIC_LEVEL);
        // Writing after rollback cannot reuse a descriptor from the abandoned
        // snapshot (its arena allocation intentionally remains alive).
        ctx.set_desc(ty, TypeDesc::Ttuple(vec![local].into()));
        assert!(matches!(*ctx.borrow_desc(ty), TypeDesc::Ttuple(ref ts) if ts == &[local]));
    }

    #[test]
    fn failed_unification_restores_stored_constructor_links() {
        use super::super::ctype::{UnifyState, unify};
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int_path = super::super::predef::path_int();
        let stored_int = ctx.store.alloc_type(
            TypeDesc::Tconstr {
                path: int_path.clone(),
                args: vec![].into(),
                abbrev: ctx.store.alloc_abbrev(AbbrevMemo::Mnil),
            },
            GENERIC_LEVEL,
        );
        let local_int = ctx.new_constr(int_path, vec![]);
        let left_bool = ctx.new_constr(super::super::predef::path_bool(), vec![]);
        let right_string = ctx.new_constr(super::super::predef::path_string(), vec![]);
        let left = ctx.new_tuple(vec![stored_int, left_bool]);
        let right = ctx.new_tuple(vec![local_int, right_string]);
        let snapshot = ctx.snapshot_type_state();
        let mut state = UnifyState::new();
        assert!(unify(&ctx, &mut state, left, right).is_err());
        // The first tuple element unified before the second element failed.
        // Skipping stored-source links would incorrectly leave it unchanged.
        assert_eq!(ctx.repr(stored_int), local_int);
        ctx.restore_type_state(snapshot);
        assert_eq!(ctx.repr(stored_int), stored_int);
        assert_eq!(ctx.get_level(stored_int), GENERIC_LEVEL);
        assert!(matches!(
            *ctx.store.node(stored_int).desc(),
            TypeDesc::Tconstr { .. }
        ));
    }

    #[test]
    fn store_links_compress_without_mutating_dependencies() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let target = ctx.new_var(None);
        let middle = ctx.new_link(target);
        let stored = ctx.store.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
        super::super::ctype::link_type(&ctx, stored, middle);
        assert_eq!(ctx.repr(stored), target);
        assert!(matches!(*ctx.borrow_desc(stored), TypeDesc::Tlink(t) if t == target));
        assert!(matches!(*ctx.store.node(stored).desc(), TypeDesc::Tnil));
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
