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

use super::asttypes::ArgLabel;
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

    /// Load paths for resolving CMI files during type alias expansion.
    load_paths: RefCell<Vec<std::path::PathBuf>>,

    /// String table for CMI-decoded Longident components.
    /// CMI decoding happens without a ParseArena, so we allocate synthetic
    /// StrIdx values here and resolve them later when needed.
    cmi_longident_names: RefCell<std::collections::HashMap<u32, String>>,

    /// Next synthetic StrIdx raw value for CMI longident strings.
    next_cmi_longident_idx: Cell<u32>,
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
            types: RefCell::new(Vec::new()),
            abbrevs: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            commutables: RefCell::new(Vec::new()),
            field_kinds: RefCell::new(Vec::new()),
            type_decl_store: RefCell::new(std::collections::HashMap::new()),
            type_decl_by_stamp: RefCell::new(std::collections::HashMap::new()),
            type_decl_by_path: RefCell::new(std::collections::HashMap::new()),
            load_paths: RefCell::new(Vec::new()),
            cmi_longident_names: RefCell::new(std::collections::HashMap::new()),
            next_cmi_longident_idx: Cell::new(0xF000_0000),
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
    // Simple Abbreviations (cross-instance sharing for nullary Tconstr)
    // ========================================================================

    /// OCaml's check_abbrev_env: clear abbreviation cache when environment changes.
    /// This prevents stale abbreviations from causing incorrect cross-instance sharing.
    pub fn check_abbrev_env(&self, env: &crate::types::env::Env) {
        let env_id = env.id();
        if env_id != self.previous_env_id.get() {
            self.clear_simple_abbrevs();
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
    }

    // ========================================================================
    // Abbreviation Memos
    // ========================================================================

    /// Allocate an abbreviation memo (Mnil).
    pub fn alloc_abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    /// Allocate an abbreviation memo.
    fn alloc_abbrev(&self, memo: AbbrevMemo) -> AbbrevMemoRef {
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
