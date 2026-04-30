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
use std::sync::Arc;

/// Append-only type arena using UnsafeCell for zero-copy access.
///
/// Safe because:
/// - `Box<TypeExpr>` gives stable heap addresses
/// - The Vec only grows (push), never shrinks or reorders
/// - Individual TypeExpr.desc RefCells are independent
struct TypeArena {
    types: std::cell::UnsafeCell<Vec<Box<TypeExpr>>>,
}

impl TypeArena {
    fn new() -> Self {
        TypeArena {
            types: std::cell::UnsafeCell::new(Vec::new()),
        }
    }

    #[inline]
    fn get(&self, r: TypeExprRef) -> &TypeExpr {
        unsafe {
            let types = &*self.types.get();
            types[r.0].as_ref()
        }
    }

    fn push(&self, ty: TypeExpr) -> TypeExprRef {
        unsafe {
            let types = &mut *self.types.get();
            let idx = types.len();
            types.push(Box::new(ty));
            TypeExprRef(idx)
        }
    }

    fn len(&self) -> usize {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct QualifiedModuleComponentsCacheKey {
    path: Path,
    env_id: Option<u64>,
}

impl QualifiedModuleComponentsCacheKey {
    pub(crate) fn new(path: Path, env_id: Option<u64>) -> Self {
        Self { path, env_id }
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
/// let mut ctx = TypeContext::new(&id_gen);
///
/// // Create a type variable
/// let tvar = ctx.new_var(None);
///
/// // Create an arrow type
/// let int_type = ctx.new_constr(path_int, vec![]);
/// let func_type = ctx.new_arrow(tvar, int_type);
/// ```
pub struct TypeContext<'a> {
    /// ID generator for type IDs
    id_gen: &'a IdGenerator,

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
    /// Reuse cache for generic dotted nullary constructors coming from cached
    /// persistent signatures. Keyed by the original source node identity for
    /// the lifetime of this typing context.
    generic_dotted_constr_copies: RefCell<ahash::AHashMap<TypeExprRef, TypeExprRef>>,
    /// Previous env ID for check_abbrev_env (OCaml ctype.ml:1272)
    previous_env_id: Cell<u64>,

    /// Current abbreviation context during subst (OCaml: abbreviations = ref (ref Mnil)).
    /// Set during subst_with_memo so copy_type_cached can use find_repr to detect
    /// previously-expanded types and create Tlink sharing.
    current_abbreviations: Cell<AbbrevMemoRef>,

    /// Type expression storage. Uses UnsafeCell-based arena for zero-copy access.
    types: TypeArena,

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

    /// Cache for type declarations resolved through module signatures (Pdot paths).
    /// Separate from type_decl_by_path to avoid conflicts with expand_head_once
    /// entries which have unqualified paths. This approximates OCaml's
    /// components_of_module_maker lazy caching.
    resolved_pdot_type_cache: RefCell<ahash::AHashMap<String, super::decl::TypeDeclaration>>,

    /// Cache for resolved module signatures. Keyed by module path name.
    /// Prevents repeated calls to resolve_module_signature_for_path from
    /// creating fresh type copies via copy_lookup_signature_for_subst.
    resolved_module_sig_cache: RefCell<ahash::AHashMap<String, (Path, super::decl::Signature)>>,

    /// Cached qualified module-component views keyed by access-path semantics.
    /// This is the Rust analogue of OCaml's lazy `components_of_module_maker`.
    qualified_module_components_cache: RefCell<
        ahash::AHashMap<
            QualifiedModuleComponentsCacheKey,
            super::env_lazy::QualifiedModuleComponents,
        >,
    >,

    /// Cached dotted value lookups keyed by resolved module access path.
    resolved_module_value_cache:
        RefCell<ahash::AHashMap<(Path, String), (Path, super::decl::ValueDescription)>>,

    /// Cached dotted type lookups keyed by resolved module access path.
    resolved_module_type_cache:
        RefCell<ahash::AHashMap<(Path, String), (Path, Ident, super::decl::TypeDeclaration)>>,

    /// Cached child-module access paths keyed by resolved parent access path.
    resolved_child_module_path_cache: RefCell<ahash::AHashMap<(Path, String), Path>>,

    /// Cached full normalize_path results keyed by environment identity.
    normalized_path_full_cache: RefCell<ahash::AHashMap<(u64, Path), Path>>,

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
    pub(crate) renamed_module_sigs: RefCell<ahash::AHashMap<String, super::decl::Signature>>,

    /// Raw (un-renamed) module signatures for persistent modules.
    /// Used by trigger_module_sig_rename to lazily rename on first access
    /// from normalize_path, matching OCaml's lazy ps_sig forcing.
    raw_module_sigs: RefCell<ahash::AHashMap<String, super::decl::Signature>>,

    /// String table for CMI-decoded Longident components.
    /// CMI decoding happens without a ParseArena, so we allocate synthetic
    /// StrIdx values here and resolve them later when needed.
    cmi_longident_names: RefCell<ahash::AHashMap<u32, String>>,

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
            String,
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
    /// that reconstructed array per TypeContext instead of rebuilding large
    /// records such as `JsxDOM.domProps` for every JSX literal.
    record_label_descriptions_cache:
        RefCell<ahash::AHashMap<String, Vec<super::decl::LabelDescription>>>,

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

impl<'a> TypeContext<'a> {
    /// Create a new type context.
    pub fn new(id_gen: &'a IdGenerator) -> Self {
        TypeContext {
            id_gen,
            current_level: Cell::new(0),
            nongen_level: Cell::new(0),
            global_level: Cell::new(1),
            saved_levels: RefCell::new(Vec::new()),
            trace_gadt_instances: Cell::new(false),
            simple_abbrevs: Cell::new(AbbrevMemoRef(1)),
            generic_dotted_constr_copies: RefCell::new(ahash::AHashMap::new()),
            previous_env_id: Cell::new(0),
            current_abbreviations: Cell::new(AbbrevMemoRef::nil()),
            types: TypeArena::new(),
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
            resolved_pdot_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_sig_cache: RefCell::new(ahash::AHashMap::new()),
            qualified_module_components_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_value_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_module_type_cache: RefCell::new(ahash::AHashMap::new()),
            resolved_child_module_path_cache: RefCell::new(ahash::AHashMap::new()),
            normalized_path_full_cache: RefCell::new(ahash::AHashMap::new()),
            load_paths: RefCell::new(Vec::new()),
            persistent_env: RefCell::new(None),
            renamed_module_sigs: RefCell::new(ahash::AHashMap::new()),
            raw_module_sigs: RefCell::new(ahash::AHashMap::new()),
            cmi_longident_names: RefCell::new(ahash::AHashMap::new()),
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
            let env_ref = EnvRef(typed_envs.len());
            typed_envs.push(Arc::new(env.clone_preserve_id()));
            env_ref
        };
        self.typed_envs_by_id.borrow_mut().insert(env.id(), env_ref);
        env_ref
    }

    /// Resolve a typedtree environment reference.
    pub fn get_typed_env(&self, env_ref: EnvRef) -> Option<Arc<Env>> {
        self.typed_envs.borrow().get(env_ref.0).cloned()
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

    /// Cache a type declaration resolved through module signatures (Pdot paths).
    pub fn register_resolved_pdot_type(&self, path: &str, decl: super::decl::TypeDeclaration) {
        self.resolved_pdot_type_cache
            .borrow_mut()
            .insert(path.to_string(), decl);
    }

    /// Look up a cached resolved Pdot type declaration.
    pub fn find_resolved_pdot_type(&self, path: &str) -> Option<super::decl::TypeDeclaration> {
        self.resolved_pdot_type_cache.borrow().get(path).cloned()
    }

    /// Cache a resolved module signature.
    pub fn register_resolved_module_sig(
        &self,
        path: &str,
        access_path: Path,
        sig: super::decl::Signature,
    ) {
        self.resolved_module_sig_cache
            .borrow_mut()
            .insert(path.to_string(), (access_path, sig));
    }

    /// Look up a cached resolved module signature.
    pub fn find_resolved_module_sig(&self, path: &str) -> Option<(Path, super::decl::Signature)> {
        self.resolved_module_sig_cache.borrow().get(path).cloned()
    }

    /// Cache a lazily-built qualified module-components view.
    pub(crate) fn register_qualified_module_components(
        &self,
        key: QualifiedModuleComponentsCacheKey,
        components: super::env_lazy::QualifiedModuleComponents,
    ) {
        self.qualified_module_components_cache
            .borrow_mut()
            .insert(key, components);
    }

    /// Borrow a cached qualified module-components view.
    /// OCaml stores lazy module components once and reads the cached component
    /// tables directly (compiler/ml/env.ml:1513-1514,1516-1588). Move the
    /// cached value out while running `f` so recursive lookups can still mutate
    /// this cache without cloning the full signature/component graph.
    pub(crate) fn with_qualified_module_components<R>(
        &self,
        key: &QualifiedModuleComponentsCacheKey,
        f: impl FnOnce(&super::env_lazy::QualifiedModuleComponents) -> R,
    ) -> Option<R> {
        let components = self
            .qualified_module_components_cache
            .borrow_mut()
            .remove(key)?;
        let result = f(&components);
        self.qualified_module_components_cache
            .borrow_mut()
            .entry(key.clone())
            .or_insert(components);
        Some(result)
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
            .insert((module_path.clone(), value_name.to_string()), (path, desc));
    }

    /// Look up a cached dotted value lookup for a resolved module access path.
    pub(crate) fn find_resolved_module_value(
        &self,
        module_path: &Path,
        value_name: &str,
    ) -> Option<(Path, super::decl::ValueDescription)> {
        self.resolved_module_value_cache
            .borrow()
            .get(&(module_path.clone(), value_name.to_string()))
            .cloned()
    }

    /// Cache a dotted type lookup for a resolved module access path.
    pub(crate) fn register_resolved_module_type(
        &self,
        module_path: &Path,
        type_name: &str,
        access_path: Path,
        id: Ident,
        decl: super::decl::TypeDeclaration,
    ) {
        self.resolved_module_type_cache.borrow_mut().insert(
            (module_path.clone(), type_name.to_string()),
            (access_path, id, decl),
        );
    }

    /// Look up a cached dotted type lookup for a resolved module access path.
    pub(crate) fn find_resolved_module_type(
        &self,
        module_path: &Path,
        type_name: &str,
    ) -> Option<(Path, Ident, super::decl::TypeDeclaration)> {
        self.resolved_module_type_cache
            .borrow()
            .get(&(module_path.clone(), type_name.to_string()))
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
            .insert((parent_path.clone(), child_name.to_string()), child_path);
    }

    /// Look up a cached resolved child-module access path.
    pub(crate) fn find_resolved_child_module_path(
        &self,
        parent_path: &Path,
        child_name: &str,
    ) -> Option<Path> {
        self.resolved_child_module_path_cache
            .borrow()
            .get(&(parent_path.clone(), child_name.to_string()))
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
        let commutable = self.alloc_commutable(Commutable::Cok);
        self.new_type(TypeDesc::Tarrow {
            arg: TypeArg::new(arg_label, arg_type),
            ret: ret_type,
            commutable: Commutable::Clink(commutable),
            arity,
        })
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
        let commutable = self.alloc_commutable(Commutable::Cok);
        self.new_generic_type(TypeDesc::Tarrow {
            arg: TypeArg::new(arg_label, arg_type),
            ret: ret_type,
            commutable: Commutable::Clink(commutable),
            arity,
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
        type_path_name: &str,
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
            .insert(type_path_name.to_string(), labels);
    }

    /// Look up cached record labels for a type path.
    pub fn get_record_labels(
        &self,
        type_path_name: &str,
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
            .get(type_path_name)
            .cloned()
    }

    /// Cache reconstructed record label descriptions for a type path.
    pub fn register_record_label_descriptions(
        &self,
        type_path_name: &str,
        labels: Vec<super::decl::LabelDescription>,
    ) {
        self.record_label_descriptions_cache
            .borrow_mut()
            .insert(type_path_name.to_string(), labels);
    }

    /// Look up reconstructed record label descriptions for a type path.
    pub fn get_record_label_descriptions(
        &self,
        type_path_name: &str,
    ) -> Option<Vec<super::decl::LabelDescription>> {
        self.record_label_descriptions_cache
            .borrow()
            .get(type_path_name)
            .cloned()
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

    pub fn find_generic_dotted_constr_copy(&self, source: TypeExprRef) -> Option<TypeExprRef> {
        self.generic_dotted_constr_copies
            .borrow()
            .get(&source)
            .copied()
    }

    pub fn remember_generic_dotted_constr_copy(&self, source: TypeExprRef, copied: TypeExprRef) {
        self.generic_dotted_constr_copies
            .borrow_mut()
            .entry(source)
            .or_insert(copied);
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
            if let Some(cell) = abbrevs.get(memo.0) {
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
                    .get(current.0)
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
                    .get(current.0)
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
            .get(memo.0)
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
        if let Some(cell) = abbrevs.get(memo.0) {
            *cell.borrow_mut() = AbbrevMemo::Mnil;
        }
    }

    /// Overwrite a per-node abbreviation memo chain with a saved snapshot.
    pub fn restore_abbrev_memo(&self, memo: AbbrevMemoRef, value: AbbrevMemo) {
        if memo == AbbrevMemoRef::nil() {
            return;
        }
        let abbrevs = self.abbrevs.borrow();
        if let Some(cell) = abbrevs.get(memo.0) {
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
            if memo.0 >= abbrevs.len() {
                return;
            }

            let previous = abbrevs[memo.0].borrow().clone();
            let next = if matches!(previous, AbbrevMemo::Mnil) {
                AbbrevMemoRef::nil()
            } else {
                let idx = abbrevs.len();
                abbrevs.push(RefCell::new(previous));
                AbbrevMemoRef(idx)
            };

            *abbrevs[memo.0].borrow_mut() = AbbrevMemo::Mcons {
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
        AbbrevMemoRef(idx)
    }

    // ========================================================================
    // Row Fields
    // ========================================================================

    /// Allocate a row field reference.
    pub fn alloc_row_field(&self, field: Option<RowField>) -> RowFieldRef {
        let mut row_fields = self.row_fields.borrow_mut();
        let idx = row_fields.len();
        row_fields.push(RefCell::new(field));
        RowFieldRef(idx)
    }

    /// Get the value stored in a row field reference.
    pub fn get_row_field(&self, rf: RowFieldRef) -> Option<RowField> {
        if rf.is_null() {
            return None;
        }
        let row_fields = self.row_fields.borrow();
        row_fields.get(rf.0).and_then(|cell| cell.borrow().clone())
    }

    /// Set the value of a row field reference (like OCaml's set_row_field).
    pub fn set_row_field(&self, rf: RowFieldRef, field: RowField) {
        if rf.is_null() {
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.0) {
            *cell.borrow_mut() = Some(field);
        }
    }

    /// Clear the value stored in a row field reference.
    pub fn clear_row_field(&self, rf: RowFieldRef) {
        if rf.is_null() {
            return;
        }
        let row_fields = self.row_fields.borrow();
        if let Some(cell) = row_fields.get(rf.0) {
            *cell.borrow_mut() = None;
        }
    }

    // ========================================================================
    // Commutables
    // ========================================================================

    /// Allocate a commutable reference.
    fn alloc_commutable(&self, c: Commutable) -> CommutableRef {
        let mut commutables = self.commutables.borrow_mut();
        let idx = commutables.len();
        commutables.push(RefCell::new(c));
        CommutableRef(idx)
    }

    // ========================================================================
    // Field Kinds
    // ========================================================================

    /// Allocate a field kind reference.
    fn alloc_field_kind(&self, kind: Option<FieldKind>) -> FieldKindRef {
        let mut field_kinds = self.field_kinds.borrow_mut();
        let idx = field_kinds.len();
        field_kinds.push(RefCell::new(kind));
        FieldKindRef(idx)
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
        std::cmp::max(self.id_gen.current_stamp(), Ident::current_local_stamp())
    }

    /// Set the ident stamp counter to at least `t`.
    /// Matches OCaml's `Ident.set_current_time`.
    pub fn set_current_time(&self, t: i32) {
        self.id_gen.set_current_stamp(t);
    }

    /// Register a raw module signature for lazy renaming.
    /// Called during load_pervasives to store sigs for normalize_path.
    pub fn register_raw_module_sig(&self, name: &str, sig: super::decl::Signature) {
        self.raw_module_sigs
            .borrow_mut()
            .insert(name.to_string(), sig);
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
        };
        if let Some(sig) = raw_sig {
            let renamed: super::decl::Signature = sig
                .iter()
                .map(|item| match item {
                    super::decl::SignatureItem::SigValue(id, desc) => {
                        super::decl::SignatureItem::SigValue(self.rename_ident(id), desc.clone())
                    }
                    super::decl::SignatureItem::SigType(id, decl, rec_status) => {
                        super::decl::SignatureItem::SigType(
                            self.rename_ident(id),
                            decl.clone(),
                            *rec_status,
                        )
                    }
                    super::decl::SignatureItem::SigTypext(id, ext, ext_status) => {
                        super::decl::SignatureItem::SigTypext(
                            self.rename_ident(id),
                            ext.clone(),
                            *ext_status,
                        )
                    }
                    super::decl::SignatureItem::SigModule(id, md, rec_status) => {
                        super::decl::SignatureItem::SigModule(
                            self.rename_ident(id),
                            md.clone(),
                            *rec_status,
                        )
                    }
                    super::decl::SignatureItem::SigModtype(id, mtd) => {
                        super::decl::SignatureItem::SigModtype(self.rename_ident(id), mtd.clone())
                    }
                    super::decl::SignatureItem::SigClass => super::decl::SignatureItem::SigClass,
                    super::decl::SignatureItem::SigClassType => {
                        super::decl::SignatureItem::SigClassType
                    }
                })
                .collect();
            self.renamed_module_sigs
                .borrow_mut()
                .insert(module_name.to_string(), renamed);
        }
    }

    /// Create a new identifier using the typing context's shared stamp source.
    pub fn create_ident(&self, name: &str) -> Ident {
        self.id_gen.set_current_stamp(Ident::current_local_stamp());
        self.id_gen.create(name)
    }

    /// Rename an identifier using the typing context's shared stamp source.
    pub fn rename_ident(&self, id: &Ident) -> Ident {
        self.id_gen.set_current_stamp(Ident::current_local_stamp());
        id.rename(self.id_gen)
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
            let desc = self.types.get(t).desc();
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
                let desc = self.types.get(current).desc();
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
        let ctx = TypeContext::new(&id_gen);

        let v1 = ctx.new_var(Some("a".to_string()));
        let v2 = ctx.new_var(None);

        assert_ne!(v1, v2);
    }

    #[test]
    fn test_new_arrow() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(t1, t2);

        let desc = ctx.get_desc(arrow);
        assert!(matches!(*desc, TypeDesc::Tarrow { .. }));
    }

    #[test]
    fn test_level_management() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

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
    fn test_repr() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(&id_gen);

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
        let ctx = TypeContext::new(&id_gen);

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
        let ctx = TypeContext::new(&id_gen);

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
