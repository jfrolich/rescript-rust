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
use super::path::{Path, NOPOS};
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, Commutable, CommutableRef, FieldKind, FieldKindRef, GENERIC_LEVEL,
    RowDesc, RowField, RowFieldRef, TypeArg, TypeDesc, TypeExpr, TypeExprRef,
};
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::intern::StrIdx;
use std::cell::{Cell, RefCell};
use std::ops::Deref;

/// Snapshot wrapper for a type descriptor.
///
/// This keeps call sites ergonomic (`*ctx.get_desc(t)`, `&*desc`) while
/// avoiding long-lived borrows into arena storage.
pub struct TypeDescSnapshot(TypeDesc);

impl Deref for TypeDescSnapshot {
    type Target = TypeDesc;

    fn deref(&self) -> &Self::Target {
        &self.0
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

    /// Simple abbreviations memo: maps nullary Tconstr paths (identity-aware)
    /// to previously-expanded Tconstr nodes. This matches OCaml's
    /// `Path.same`-based lookup in `simple_abbrevs`.
    simple_abbrevs: RefCell<std::collections::HashMap<Path, TypeExprRef>>,
    /// Previous env ID for check_abbrev_env (OCaml ctype.ml:1272)
    previous_env_id: Cell<u64>,

    /// Nullary expansion cache: maps nullary Tconstr paths to cached expansion
    /// DESCRIPTIONS. On cache hit, a fresh TypeExprRef is created with the cached
    /// description. This avoids corruption from link_type while still sharing
    /// child TypeExprRefs (e.g., the float nodes inside a tuple expansion).
    nullary_expansion_cache: RefCell<std::collections::HashMap<Path, TypeDesc>>,

    /// Set of paths with "safe" expansions (Ttuple or Tconstr, not Tvariant).
    /// Persists across generalize, only cleared on env change.
    /// Used by copy_type_cached for per-copy sharing of simple alias types.
    safe_expansion_paths: RefCell<std::collections::HashSet<Path>>,

    /// Current abbreviation context during subst (OCaml: abbreviations = ref (ref Mnil)).
    /// Set during subst_with_memo so copy_type_cached can use find_repr to detect
    /// previously-expanded types and create Tlink sharing.
    current_abbreviations: Cell<AbbrevMemoRef>,

    /// Type expression storage (for indexed access).
    /// Boxed values keep stable addresses as the vector grows.
    types: RefCell<Vec<Box<TypeExpr>>>,

    /// Abbreviation memo storage
    abbrevs: RefCell<Vec<RefCell<AbbrevMemo>>>,

    /// Row field storage
    row_fields: RefCell<Vec<RefCell<Option<RowField>>>>,

    /// Commutable storage
    commutables: RefCell<Vec<RefCell<Commutable>>>,

    /// Field kind storage
    field_kinds: RefCell<Vec<RefCell<Option<FieldKind>>>>,

    /// Global type declaration store, indexed by type name.
    /// Populated when loading CMI module signatures so that type alias
    /// expansion can find declarations for types not directly in the env.
    type_decl_store: RefCell<std::collections::HashMap<String, super::decl::TypeDeclaration>>,

    /// Global type declaration store, indexed by ident stamp.
    /// Used for looking up CMI-loaded type declarations by their stamp
    /// when the type name is too generic (e.g., "t").
    type_decl_by_stamp: RefCell<std::collections::HashMap<i32, super::decl::TypeDeclaration>>,

    /// Global type declaration store, indexed by full qualified path string.
    /// Used for looking up types via Pdot paths (e.g., "Js.Promise.t").
    type_decl_by_path: RefCell<std::collections::HashMap<String, super::decl::TypeDeclaration>>,

    /// Cache for type declarations resolved through module signatures (Pdot paths).
    /// Separate from type_decl_by_path to avoid conflicts with expand_head_once
    /// entries which have unqualified paths. This approximates OCaml's
    /// components_of_module_maker lazy caching.
    resolved_pdot_type_cache: RefCell<std::collections::HashMap<String, super::decl::TypeDeclaration>>,

    /// Cache for resolved module signatures. Keyed by module path name.
    /// Prevents repeated calls to resolve_module_signature_for_path from
    /// creating fresh type copies via copy_lookup_signature_for_subst.
    resolved_module_sig_cache: RefCell<std::collections::HashMap<String, (Path, super::decl::Signature)>>,

    /// Load paths for resolving CMI files during type alias expansion.
    load_paths: RefCell<Vec<std::path::PathBuf>>,

    /// String table for CMI-decoded Longident components.
    /// CMI decoding happens without a ParseArena, so we allocate synthetic
    /// StrIdx values here and resolve them later when needed.
    cmi_longident_names: RefCell<std::collections::HashMap<u32, String>>,

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

    /// Arity update aliases: maps arity-updated TypeExprRef → original TypeExprRef.
    /// OCaml's `{t with desc = Tarrow(..., Some newarity)}` creates a new record
    /// sharing `t.id`, so the sexp serializer deduplicates them. In Rust, we create
    /// separate TypeExprRef nodes but record the alias here so the sexp serializer
    /// can use the original's dedup key.
    arity_aliases: RefCell<std::collections::HashMap<TypeExprRef, TypeExprRef>>,
}

impl<'a> TypeContext<'a> {
    /// Canonicalize path keys for simple_abbrevs to match OCaml Path.same:
    /// ignore Pdot position hints when comparing paths.
    fn canonicalize_simple_abbrev_path(path: &Path) -> Path {
        match path {
            Path::Pident(id) => Path::Pident(id.clone()),
            Path::Pdot(prefix, name, _) => Path::Pdot(
                Box::new(Self::canonicalize_simple_abbrev_path(prefix)),
                name.clone(),
                NOPOS,
            ),
            Path::Papply(functor, arg) => Path::Papply(
                Box::new(Self::canonicalize_simple_abbrev_path(functor)),
                Box::new(Self::canonicalize_simple_abbrev_path(arg)),
            ),
        }
    }

    /// Create a new type context.
    pub fn new(id_gen: &'a IdGenerator) -> Self {
        TypeContext {
            id_gen,
            current_level: Cell::new(0),
            nongen_level: Cell::new(0),
            global_level: Cell::new(1),
            saved_levels: RefCell::new(Vec::new()),
            trace_gadt_instances: Cell::new(false),
            simple_abbrevs: RefCell::new(std::collections::HashMap::new()),
            previous_env_id: Cell::new(0),
            nullary_expansion_cache: RefCell::new(std::collections::HashMap::new()),
            safe_expansion_paths: RefCell::new(std::collections::HashSet::new()),
            current_abbreviations: Cell::new(AbbrevMemoRef::nil()),
            types: RefCell::new(Vec::new()),
            // Index 0 is reserved as the canonical Mnil sentinel so
            // AbbrevMemoRef::nil() is never a mutable per-node cache.
            abbrevs: RefCell::new(vec![RefCell::new(AbbrevMemo::Mnil)]),
            row_fields: RefCell::new(Vec::new()),
            commutables: RefCell::new(Vec::new()),
            field_kinds: RefCell::new(Vec::new()),
            type_decl_store: RefCell::new(std::collections::HashMap::new()),
            type_decl_by_stamp: RefCell::new(std::collections::HashMap::new()),
            type_decl_by_path: RefCell::new(std::collections::HashMap::new()),
            resolved_pdot_type_cache: RefCell::new(std::collections::HashMap::new()),
            resolved_module_sig_cache: RefCell::new(std::collections::HashMap::new()),
            load_paths: RefCell::new(Vec::new()),
            cmi_longident_names: RefCell::new(std::collections::HashMap::new()),
            next_cmi_longident_idx: Cell::new(0xF000_0000),
            predef_int: Cell::new(None),
            predef_char: Cell::new(None),
            predef_string: Cell::new(None),
            predef_float: Cell::new(None),
            predef_bool: Cell::new(None),
            predef_unit: Cell::new(None),
            predef_exn: Cell::new(None),
            predef_bigint: Cell::new(None),
            arity_aliases: RefCell::new(std::collections::HashMap::new()),
        }
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
    pub fn register_resolved_module_sig(&self, path: &str, access_path: Path, sig: super::decl::Signature) {
        self.resolved_module_sig_cache
            .borrow_mut()
            .insert(path.to_string(), (access_path, sig));
    }

    /// Look up a cached resolved module signature.
    pub fn find_resolved_module_sig(&self, path: &str) -> Option<(Path, super::decl::Signature)> {
        self.resolved_module_sig_cache.borrow().get(path).cloned()
    }

    /// Set load paths for resolving CMI files.
    pub fn set_load_paths(&self, paths: Vec<std::path::PathBuf>) {
        *self.load_paths.borrow_mut() = paths;
    }

    /// Get the load paths.
    pub fn load_paths(&self) -> std::cell::Ref<'_, Vec<std::path::PathBuf>> {
        self.load_paths.borrow()
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
        let mut types = self.types.borrow_mut();
        let idx = types.len();
        types.push(Box::new(TypeExpr::new(desc, level, id)));
        TypeExprRef(idx)
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
    fn get_or_create_predef(
        &self,
        cache: &Cell<Option<TypeExprRef>>,
        name: &str,
    ) -> TypeExprRef {
        if let Some(ty) = cache.get() {
            ty
        } else {
            let ty = self.new_generic_constr(
                Path::pident(Ident::create_persistent(name)),
                vec![],
            );
            cache.set(Some(ty));
            ty
        }
    }

    /// Get the predef int singleton (generic_level).
    pub fn predef_int(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_int, "int")
    }
    /// Get the predef char singleton (generic_level).
    pub fn predef_char(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_char, "char")
    }
    /// Get the predef string singleton (generic_level).
    pub fn predef_string(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_string, "string")
    }
    /// Get the predef float singleton (generic_level).
    pub fn predef_float(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_float, "float")
    }
    /// Get the predef bool singleton (generic_level).
    pub fn predef_bool(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bool, "bool")
    }
    /// Get the predef unit singleton (generic_level).
    pub fn predef_unit(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_unit, "unit")
    }
    /// Get the predef exn singleton (generic_level).
    pub fn predef_exn(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_exn, "exn")
    }
    /// Get the predef bigint singleton (generic_level).
    pub fn predef_bigint(&self) -> TypeExprRef {
        self.get_or_create_predef(&self.predef_bigint, "bigint")
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

    /// Access a type expression by reference.
    fn with_type<R>(&self, r: TypeExprRef, f: impl FnOnce(&TypeExpr) -> R) -> R {
        let types = self.types.borrow();
        f(types[r.0].as_ref())
    }

    /// Get the descriptor of a type.
    pub fn get_desc(&self, r: TypeExprRef) -> TypeDescSnapshot {
        self.with_type(r, |ty| TypeDescSnapshot(ty.desc().clone()))
    }

    /// Get the level of a type.
    pub fn get_level(&self, r: TypeExprRef) -> i32 {
        self.with_type(r, |ty| ty.level())
    }

    /// Number of allocated type expressions.
    pub fn type_expr_count(&self) -> usize {
        self.types.borrow().len()
    }

    /// Set the level of a type.
    pub fn set_level(&self, r: TypeExprRef, level: i32) {
        self.with_type(r, |ty| ty.set_level(level));
    }

    /// Set the descriptor of a type.
    pub fn set_desc(&self, r: TypeExprRef, desc: TypeDesc) {
        self.with_type(r, |ty| ty.set_desc(desc));
    }

    // ========================================================================
    // Arity Aliases (sexp dedup for update_uncurried_arity)
    // ========================================================================

    /// Record that `new_ref` is an arity-updated version of `original_ref`.
    /// The sexp serializer will use `original_ref` as the dedup key for both.
    pub fn set_arity_alias(&self, new_ref: TypeExprRef, original_ref: TypeExprRef) {
        self.arity_aliases.borrow_mut().insert(new_ref, original_ref);
    }

    /// Get the arity alias for a TypeExprRef, if any.
    pub fn get_arity_alias(&self, te: TypeExprRef) -> Option<TypeExprRef> {
        self.arity_aliases.borrow().get(&te).copied()
    }

    // ========================================================================
    // Simple Abbreviations (cross-instance sharing for nullary Tconstr)
    // ========================================================================

    /// OCaml's check_abbrev_env: clear abbreviation cache when environment changes.
    /// This prevents stale abbreviations from causing incorrect cross-instance sharing.
    pub fn check_abbrev_env(&self, env: &crate::types::env::Env) {
        let env_id = env.id();
        if env_id != self.previous_env_id.get() {
            self.clear_simple_abbrevs();
            self.clear_abbrev_memos();
            // Don't clear safe_expansion_paths: Ttuple expansion status is a stable
            // property of the type declaration, independent of environment context.
            self.previous_env_id.set(env_id);
        }
    }

    /// Record a nullary Tconstr expansion for cross-instance sharing.
    /// Matches OCaml's memorize_abbrev into simple_abbrevs.
    pub fn memorize_simple_abbrev(&self, path: Path, ty: TypeExprRef) {
        // OCaml stores abbreviations as an Mcons stack; later entries shadow
        // earlier ones for the same path during find_repr.
        let path = Self::canonicalize_simple_abbrev_path(&path);
        self.simple_abbrevs.borrow_mut().insert(path, ty);
    }

    /// Look up a previously-expanded nullary Tconstr by path identity.
    /// Matches OCaml's find_repr on simple_abbrevs.
    pub fn find_simple_abbrev(&self, path: &Path) -> Option<TypeExprRef> {
        let path = Self::canonicalize_simple_abbrev_path(path);
        self.simple_abbrevs.borrow().get(&path).copied()
    }

    /// Clear simple abbreviations. Called during generalize/generalize_structure.
    pub fn clear_simple_abbrevs(&self) {
        self.simple_abbrevs.borrow_mut().clear();
        self.nullary_expansion_cache.borrow_mut().clear();
    }

    /// Save current simple_abbrevs state (for temporary isolation).
    pub fn save_simple_abbrevs(&self) -> (std::collections::HashMap<Path, TypeExprRef>, std::collections::HashMap<Path, TypeDesc>) {
        (self.simple_abbrevs.borrow().clone(), self.nullary_expansion_cache.borrow().clone())
    }

    /// Restore saved simple_abbrevs state.
    pub fn restore_simple_abbrevs(&self, saved: (std::collections::HashMap<Path, TypeExprRef>, std::collections::HashMap<Path, TypeDesc>)) {
        *self.simple_abbrevs.borrow_mut() = saved.0;
        *self.nullary_expansion_cache.borrow_mut() = saved.1;
    }

    /// Check if a path has a "safe" expansion (Ttuple or Tconstr, not Tvariant).
    /// This persists across generalize (only cleared on env change), enabling
    /// per-copy sharing in copy_type_cached for known simple alias types.
    pub fn has_safe_nullary_expansion(&self, path: &Path) -> bool {
        let path = Self::canonicalize_simple_abbrev_path(path);
        self.safe_expansion_paths.borrow().contains(&path)
    }

    /// Cache a nullary expansion DESCRIPTION for cross-expansion sharing.
    /// Stores the TypeDesc so cache hits create fresh nodes with shared children.
    pub fn cache_nullary_expansion(&self, path: Path, desc: TypeDesc) {
        let path = Self::canonicalize_simple_abbrev_path(&path);
        // Record safe expansion paths for per-copy sharing within copy():
        // Only Ttuple expansions are safe — structural types with no identity risks.
        // Nullary Tconstr (even predef like int, string) cause over-sharing regressions
        // (js_string_test, reasonReactRouter, unit_undefined_test).
        let is_safe = matches!(&desc, TypeDesc::Ttuple(_));
        if is_safe {
            self.safe_expansion_paths.borrow_mut().insert(path.clone());
        }
        self.nullary_expansion_cache.borrow_mut().insert(path, desc);
    }

    /// Look up a cached nullary expansion description.
    /// Returns a clone of the cached TypeDesc (caller creates a fresh node with it).
    pub fn find_nullary_expansion(&self, path: &Path) -> Option<TypeDesc> {
        let path = Self::canonicalize_simple_abbrev_path(path);
        self.nullary_expansion_cache.borrow().get(&path).cloned()
    }

    /// Clear all per-node abbreviation memo chains (OCaml cleanup_abbrev).
    pub fn clear_abbrev_memos(&self) {
        let abbrevs = self.abbrevs.borrow();
        for cell in abbrevs.iter() {
            *cell.borrow_mut() = AbbrevMemo::Mnil;
        }
        self.current_abbreviations.set(AbbrevMemoRef::nil());
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
                    path: cached_path,
                    abbrev,
                    next,
                    ..
                } => {
                    if path.same(&cached_path) {
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

    // ========================================================================
    // Type Representative (Union-Find)
    // ========================================================================

    /// Get the representative of a type (follow Tlink chains).
    ///
    /// This uses path compression to update intermediate links
    /// to point directly to the representative, improving
    /// subsequent lookup performance.
    pub fn repr(&self, t: TypeExprRef) -> TypeExprRef {
        // Iterative traversal avoids recursive stack growth on long link chains
        // and protects against accidental cycles in malformed link graphs.
        let mut current = t;
        let mut chain: Vec<TypeExprRef> = Vec::new();
        let mut seen: std::collections::HashSet<TypeExprRef> = std::collections::HashSet::new();

        loop {
            if !seen.insert(current) {
                break;
            }

            let next = {
                let desc = self.get_desc(current);
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
                    chain.push(current);
                    current = next_ref;
                }
                None => break,
            }
        }

        // Path compression for every traversed node.
        for node in chain {
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
