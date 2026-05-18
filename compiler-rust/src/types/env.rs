//! Type environment.
//!
//! This module provides `Env`, the typing environment that tracks all
//! bindings during type checking. The environment is immutable and uses
//! a persistent structure for efficient scope management.
//!
//! # Design
//!
//! The environment is modeled as a linked list of bindings, allowing
//! efficient shadowing and scope nesting. Each binding type (values,
//! types, modules) is tracked separately for fast lookup.
//!
//! # Key Components
//!
//! - `Env` - The main environment type
//! - `EnvSummary` - A summary of bindings for debugging
//! - Lookup functions for values, types, and modules

use super::asttypes::{MutableFlag, PrivateFlag};
use super::context::TypeContext;
use super::decl::{
    ConstructorArguments, ConstructorDeclaration, ConstructorDescription, ConstructorTag,
    LabelDeclaration, LabelDescription, ModtypeDeclaration, ModuleDeclaration, ModuleType,
    RecordRepresentation, Signature, SignatureItem, TypeDeclaration, TypeKind, ValueDescription,
};
use super::path::Path;
use super::type_expr::{TypeDesc, TypeExprRef};
use crate::ident::{Ident, IdentFlags};
use crate::location::Location;
use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use std::cell::RefCell;
use std::sync::Arc;

/// Collect free type variables (Tvar nodes) from a type expression.
/// Matches OCaml's Datarepr.free_vars.
fn free_vars(ctx: &TypeContext, ty: TypeExprRef) -> HashSet<TypeExprRef> {
    let mut result = HashSet::new();
    let mut visited = HashSet::new();
    free_vars_rec(ctx, ty, &mut result, &mut visited);
    result
}

fn predef_exception_ident(name: &str) -> Option<Ident> {
    let stamp = match name {
        "Match_failure" => 17,
        "Invalid_argument" => 18,
        "Failure" => 19,
        "JsExn" => 23,
        "Not_found" => 24,
        "End_of_file" => 25,
        "Division_by_zero" => 26,
        "Assert_failure" => 27,
        "Undefined_recursive_module" => 28,
        _ => return None,
    };
    Some(Ident::new(
        name,
        stamp,
        IdentFlags::PREDEF_EXN.with_global(),
    ))
}

fn free_vars_rec(
    ctx: &TypeContext,
    ty: TypeExprRef,
    result: &mut HashSet<TypeExprRef>,
    visited: &mut HashSet<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvar(_) => {
            result.insert(ty);
        }
        _ => {
            drop(desc);
            super::btype::iter_type_expr(ctx, ty, |child| {
                free_vars_rec(ctx, child, result, visited);
            });
        }
    }
}

/// Compute existential type variables for a GADT constructor.
/// Existentials are type variables that appear in the args but not in the result type.
/// Matches OCaml's Datarepr.constructor_existentials.
pub fn constructor_existentials(
    ctx: &TypeContext,
    cstr_args: &[TypeExprRef],
    cd_res: Option<TypeExprRef>,
) -> Vec<TypeExprRef> {
    match cd_res {
        None => vec![],
        Some(res_ty) => {
            // Collect free vars from all args (via a Ttuple wrapper like OCaml)
            let mut arg_vars = HashSet::new();
            for &arg in cstr_args {
                for v in free_vars(ctx, arg) {
                    arg_vars.insert(v);
                }
            }
            // Collect free vars from the result type
            let res_vars = free_vars(ctx, res_ty);
            // Existentials = args vars - result vars
            arg_vars.difference(&res_vars).copied().collect()
        }
    }
}

// ============================================================================
// Environment Errors
// ============================================================================

/// Errors that can occur during environment operations.
#[derive(Debug, Clone)]
pub enum EnvError {
    /// Value not found.
    ValueNotFound(String),
    /// Type not found.
    TypeNotFound(String),
    /// Module not found.
    ModuleNotFound(String),
    /// Constructor not found.
    ConstructorNotFound(String),
    /// Label not found.
    LabelNotFound(String),
    /// Inconsistent import.
    InconsistentImport {
        name: String,
        source1: String,
        source2: String,
    },
    /// Illegal value name.
    IllegalValueName(Location, String),
}

/// Result type for environment operations.
pub type EnvResult<T> = Result<T, EnvError>;

/// Check that a value identifier is accepted by the environment.
///
/// Mirrors OCaml `Env.check_value_name`: most lexical validity is enforced
/// before this point, but forged AST/CMI values named `->` or multi-`#`
/// method identifiers must be rejected when values enter the environment.
pub fn check_value_name(name: &str, loc: Location) -> EnvResult<()> {
    if name == "->" {
        return Err(EnvError::IllegalValueName(loc, name.to_string()));
    }
    if let Some(rest) = name.strip_prefix('#') {
        if rest.as_bytes().contains(&b'#') {
            return Err(EnvError::IllegalValueName(loc, name.to_string()));
        }
    }
    Ok(())
}

// ============================================================================
// Environment Summary
// ============================================================================

/// Summary of environment bindings.
///
/// This is used for debugging and for computing the environment
/// delta when creating module interfaces.
#[derive(Debug, Clone)]
pub enum EnvSummary {
    /// Empty environment.
    Empty,
    /// Value binding.
    Value(Arc<EnvSummary>, Ident, Arc<ValueDescription>),
    /// Type binding.
    Type(Arc<EnvSummary>, Ident, Arc<TypeDeclaration>),
    /// Module binding.
    Module(Arc<EnvSummary>, Ident, Arc<ModuleDeclaration>),
    /// Module type binding.
    ModType(Arc<EnvSummary>, Ident, Arc<ModtypeDeclaration>),
    /// Open a module.
    Open(Arc<EnvSummary>, Path),
    /// Functor argument.
    FunctorArg(Arc<EnvSummary>, Ident),
}

// ============================================================================
// Binding Tables
// ============================================================================

/// Symbolic opened layer for identifier-indexed tables.
///
/// Mirrors OCaml `Env.IdTbl.opened`: one open layer contains the opened
/// module root, its component table, and the table that existed before the
/// open.
#[derive(Debug, Clone)]
struct IdOpened<T> {
    root: Option<Path>,
    components: im_rc::HashMap<String, (Ident, T, i32)>,
    next: Arc<IdTbl<T>>,
}

/// A table of bindings indexed by identifier.
///
/// This matches OCaml `Env.IdTbl`: local bindings live in `current`, and each
/// open is represented symbolically as an `opened` layer rather than flattening
/// every opened binding into the same name map with an origin boolean.
#[derive(Debug, Clone)]
pub struct IdTbl<T> {
    current: im_rc::HashMap<String, Vec<(Ident, T)>>,
    current_by_stamp: im_rc::HashMap<i32, (Ident, T)>,
    opened: Option<Arc<IdOpened<T>>>,
}

impl<T: Clone> IdTbl<T> {
    pub fn new() -> Self {
        Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: None,
        }
    }

    pub fn add(&mut self, id: Ident, value: T) {
        let name = id.name().to_string();
        let stamp = id.stamp();
        if stamp != 0 {
            self.current_by_stamp
                .insert(stamp, (id.clone(), value.clone()));
        }
        match self.current.get_mut(&name) {
            Some(entries) => entries.push((id, value)),
            None => {
                self.current.insert(name.clone(), vec![(id, value)]);
            }
        }
    }

    pub fn add_open_layer(&mut self, root: Path, components: Vec<(Ident, T, i32)>) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        let opened_components = components
            .into_iter()
            .map(|(id, value, pos)| (id.name().to_string(), (id, value, pos)))
            .collect();
        *self = Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: Some(Arc::new(IdOpened {
                root: Some(root),
                components: opened_components,
                next: Arc::new(next),
            })),
        };
    }

    /// Compatibility insertion for existing open code.
    ///
    /// This keeps the table shape OCaml-like even before all callers are routed
    /// through a batched `add_open_layer`: each inserted opened binding becomes
    /// a symbolic layer and exact identifier lookup still skips opened layers.
    pub fn add_opened(&mut self, id: Ident, value: T) {
        let next = std::mem::take(self);
        let mut components = im_rc::HashMap::new();
        components.insert(id.name().to_string(), (id, value, 0));
        *self = Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: Some(Arc::new(IdOpened {
                root: None,
                components,
                next: Arc::new(next),
            })),
        };
    }

    fn opened_names_added_since(&self, previous: &Self) -> HashSet<String> {
        let current_counts = self.opened_name_counts();
        let previous_counts = previous.opened_name_counts();
        let mut names = HashSet::new();
        for (name, count) in current_counts {
            if count > previous_counts.get(&name).copied().unwrap_or(0) {
                names.insert(name.clone());
            }
        }
        names
    }

    fn opened_name_counts(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        self.collect_opened_name_counts(&mut counts);
        counts
    }

    fn collect_opened_name_counts(&self, counts: &mut HashMap<String, usize>) {
        if let Some(opened) = &self.opened {
            for name in opened.components.keys() {
                *counts.entry(name.clone()).or_default() += 1;
            }
            opened.next.collect_opened_name_counts(counts);
        }
    }

    fn find_current_by_ident(&self, id: &Ident) -> Option<&T> {
        let stamp = id.stamp();
        if stamp != 0
            && let Some((entry_id, value)) = self.current_by_stamp.get(&stamp)
            && entry_id.same(id)
            && entry_id.name() == id.name()
        {
            return Some(value);
        }

        self.current.get(id.name()).and_then(|entries| {
            entries
                .iter()
                .rev()
                .find(|(entry_id, _)| {
                    if stamp == 0 {
                        entry_id.is_persistent() && entry_id.name() == id.name()
                    } else {
                        entry_id.same(id) && entry_id.name() == id.name()
                    }
                })
                .map(|(_, value)| value)
        })
    }

    fn find_name_entry(&self, name: &str) -> Option<(&Ident, &T)> {
        if let Some((id, value)) = self.current.get(name).and_then(|entries| entries.last()) {
            return Some((id, value));
        }

        match &self.opened {
            Some(opened) => opened
                .components
                .get(name)
                .map(|(id, value, _)| (id, value))
                .or_else(|| opened.next.find_name_entry(name)),
            None => None,
        }
    }

    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        self.find_name_entry(name).map(|(_, value)| value)
    }

    pub fn find_by_name_with_id(&self, name: &str) -> Option<(&Ident, &T)> {
        self.find_name_entry(name)
    }

    pub fn find_by_name_with_path(&self, name: &str) -> Option<(Path, &T)> {
        if let Some((id, value)) = self.current.get(name).and_then(|entries| entries.last()) {
            return Some((Path::pident(id.clone()), value));
        }

        match &self.opened {
            Some(opened) => opened
                .components
                .get(name)
                .map(|(id, value, pos)| {
                    let path = opened
                        .root
                        .as_ref()
                        .map(|root| Path::pdot_pos(root.clone(), name.to_string(), *pos))
                        .unwrap_or_else(|| Path::pident(id.clone()));
                    (path, value)
                })
                .or_else(|| opened.next.find_by_name_with_path(name)),
            None => None,
        }
    }

    /// Find a binding by identifier, matching OCaml `IdTbl.find_same`.
    ///
    /// Exact identifier lookup walks `current` bindings through open layers and
    /// intentionally skips opened component tables.
    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        if let Some(value) = self.find_current_by_ident(id) {
            return Some(value);
        }
        self.opened
            .as_ref()
            .and_then(|opened| opened.next.find_by_ident(id))
    }

    pub fn find_local_by_ident(&self, id: &Ident) -> Option<&T> {
        self.find_by_ident(id)
    }

    pub fn update_by_name<F>(&mut self, name: &str, f: &mut F) -> Option<(Ident, T)>
    where
        F: FnMut(&T) -> T,
    {
        if let Some(entries) = self.current.get_mut(name)
            && let Some((id, value)) = entries.last_mut()
        {
            let updated = f(value);
            *value = updated.clone();
            if id.stamp() != 0 {
                self.current_by_stamp
                    .insert(id.stamp(), (id.clone(), updated.clone()));
            }
            return Some((id.clone(), updated));
        }

        if let Some(opened) = self.opened.as_mut() {
            let opened = Arc::make_mut(opened);
            if let Some((id, value, _)) = opened.components.get_mut(name) {
                let updated = f(value);
                *value = updated.clone();
                return Some((id.clone(), updated));
            }
            return Arc::make_mut(&mut opened.next).update_by_name(name, f);
        }

        None
    }

    pub fn find_all(&self, name: &str) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(entries) = self.current.get(name) {
            items.extend(entries.iter().rev().map(|(_, value)| value));
        }
        if let Some(opened) = &self.opened {
            if let Some((_, value, _)) = opened.components.get(name) {
                items.push(value);
            }
            items.extend(opened.next.find_all(name));
        }
        items
    }

    pub fn contains(&self, name: &str) -> bool {
        self.find_by_name(name).is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut items = Vec::new();
        self.collect_iter(&mut items);
        items.into_iter()
    }

    fn collect_iter<'a>(&'a self, items: &mut Vec<(&'a Ident, &'a T)>) {
        for entries in self.current.values() {
            items.extend(entries.iter().map(|(id, value)| (id, value)));
        }
        if let Some(opened) = &self.opened {
            items.extend(
                opened
                    .components
                    .values()
                    .map(|(id, value, _)| (id, value)),
            );
            opened.next.collect_iter(items);
        }
    }

    pub fn visible_local_entries(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut seen = HashSet::new();
        let mut items = Vec::new();
        self.collect_visible_local_entries(&mut seen, &mut items);
        items.into_iter()
    }

    fn collect_visible_local_entries<'a>(
        &'a self,
        seen: &mut HashSet<&'a str>,
        items: &mut Vec<(&'a Ident, &'a T)>,
    ) {
        for (name, entries) in self.current.iter() {
            if seen.insert(name.as_str())
                && let Some((id, value)) = entries.last()
            {
                items.push((id, value));
            }
        }
        if let Some(opened) = &self.opened {
            for name in opened.components.keys() {
                seen.insert(name.as_str());
            }
            opened.next.collect_visible_local_entries(seen, items);
        }
    }
}

impl<T: Clone> Default for IdTbl<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
struct TycompOpened<T> {
    components: im_rc::HashMap<String, Vec<(Ident, T)>>,
    next: Arc<TycompTbl<T>>,
}

/// OCaml-shaped table for constructors and labels.
///
/// This mirrors `Env.TycompTbl`: local bindings are kept in `current`; opened
/// constructor/label buckets stay in symbolic `opened` layers and are returned
/// as lists.
#[derive(Debug, Clone)]
pub struct TycompTbl<T> {
    current: im_rc::HashMap<String, Vec<(Ident, T)>>,
    current_by_stamp: im_rc::HashMap<i32, (Ident, T)>,
    opened: Option<Arc<TycompOpened<T>>>,
}

impl<T: Clone> TycompTbl<T> {
    pub fn new() -> Self {
        Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: None,
        }
    }

    pub fn add(&mut self, id: Ident, value: T) {
        let name = id.name().to_string();
        if id.stamp() != 0 {
            self.current_by_stamp
                .insert(id.stamp(), (id.clone(), value.clone()));
        }
        match self.current.get_mut(&name) {
            Some(entries) => entries.push((id, value)),
            None => {
                self.current.insert(name.clone(), vec![(id, value)]);
            }
        }
    }

    pub fn add_opened(&mut self, id: Ident, value: T) {
        let next = std::mem::take(self);
        let name = id.name().to_string();
        let mut components = im_rc::HashMap::new();
        components.insert(name, vec![(id, value)]);
        *self = Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: Some(Arc::new(TycompOpened {
                components,
                next: Arc::new(next),
            })),
        };
    }

    pub fn add_open_layer(&mut self, components: Vec<(Ident, T)>) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        let mut opened_components: im_rc::HashMap<String, Vec<(Ident, T)>> =
            im_rc::HashMap::new();
        for (id, value) in components {
            let name = id.name().to_string();
            match opened_components.get_mut(&name) {
                Some(entries) => entries.insert(0, (id, value)),
                None => {
                    opened_components.insert(name, vec![(id, value)]);
                }
            }
        }
        *self = Self {
            current: im_rc::HashMap::new(),
            current_by_stamp: im_rc::HashMap::new(),
            opened: Some(Arc::new(TycompOpened {
                components: opened_components,
                next: Arc::new(next),
            })),
        };
    }

    fn opened_names_added_since(&self, previous: &Self) -> HashSet<String> {
        let current_counts = self.opened_name_counts();
        let previous_counts = previous.opened_name_counts();
        let mut names = HashSet::new();
        for (name, count) in current_counts {
            if count > previous_counts.get(&name).copied().unwrap_or(0) {
                names.insert(name.clone());
            }
        }
        names
    }

    fn opened_name_counts(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        self.collect_opened_name_counts(&mut counts);
        counts
    }

    fn collect_opened_name_counts(&self, counts: &mut HashMap<String, usize>) {
        if let Some(opened) = &self.opened {
            for (name, entries) in opened.components.iter() {
                *counts.entry(name.clone()).or_default() += entries.len();
            }
            opened.next.collect_opened_name_counts(counts);
        }
    }

    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        if let Some((_, value)) = self.current.get(name).and_then(|entries| entries.last()) {
            return Some(value);
        }
        match &self.opened {
            Some(opened) => opened
                .components
                .get(name)
                .and_then(|entries| entries.first())
                .map(|(_, value)| value)
                .or_else(|| opened.next.find_by_name(name)),
            None => None,
        }
    }

    pub fn find_by_name_with_origin(&self, name: &str) -> Option<(&Ident, &T, bool)> {
        if let Some((id, value)) = self.current.get(name).and_then(|entries| entries.last()) {
            return Some((id, value, true));
        }
        match &self.opened {
            Some(opened) => opened
                .components
                .get(name)
                .and_then(|entries| entries.first())
                .map(|(id, value)| (id, value, false))
                .or_else(|| opened.next.find_by_name_with_origin(name)),
            None => None,
        }
    }

    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        let stamp = id.stamp();
        if stamp != 0
            && let Some((entry_id, value)) = self.current_by_stamp.get(&stamp)
            && entry_id.same(id)
            && entry_id.name() == id.name()
        {
            return Some(value);
        }
        if let Some(value) = self.current.get(id.name()).and_then(|entries| {
            entries
                .iter()
                .rev()
                .find(|(entry_id, _)| {
                    if stamp == 0 {
                        entry_id.is_persistent() && entry_id.name() == id.name()
                    } else {
                        entry_id.same(id) && entry_id.name() == id.name()
                    }
                })
                .map(|(_, value)| value)
        }) {
            return Some(value);
        }
        self.opened
            .as_ref()
            .and_then(|opened| opened.next.find_by_ident(id))
    }

    pub fn find_all(&self, name: &str) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(entries) = self.current.get(name) {
            items.extend(entries.iter().rev().map(|(_, value)| value));
        }
        if let Some(opened) = &self.opened {
            if let Some(entries) = opened.components.get(name) {
                items.extend(entries.iter().map(|(_, value)| value));
            }
            items.extend(opened.next.find_all(name));
        }
        items
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut items = Vec::new();
        self.collect_iter(&mut items);
        items.into_iter()
    }

    fn collect_iter<'a>(&'a self, items: &mut Vec<(&'a Ident, &'a T)>) {
        for entries in self.current.values() {
            items.extend(entries.iter().map(|(id, value)| (id, value)));
        }
        if let Some(opened) = &self.opened {
            for entries in opened.components.values() {
                items.extend(entries.iter().map(|(id, value)| (id, value)));
            }
            opened.next.collect_iter(items);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct OpenedBindingNames {
    pub(crate) values: HashSet<String>,
    pub(crate) types: HashSet<String>,
    pub(crate) modules: HashSet<String>,
    pub(crate) modtypes: HashSet<String>,
    pub(crate) constructors: HashSet<String>,
    pub(crate) labels: HashSet<String>,
}

impl<T: Clone> Default for TycompTbl<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// The Environment
// ============================================================================

/// The typing environment.
///
/// This tracks all bindings visible during type checking.
/// The environment is immutable - extending it creates a new environment.
/// Global counter for unique Env IDs.
static NEXT_ENV_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

#[derive(Debug)]
pub struct Env {
    /// Unique identity for this environment instance.
    /// Incremented when bindings are added, to detect env changes.
    id: u64,

    /// Value bindings.
    values: IdTbl<Arc<ValueDescription>>,

    /// Type bindings.
    types: IdTbl<Arc<TypeDeclaration>>,

    /// Constructor bindings (for variant types).
    constrs: TycompTbl<Arc<ConstructorDescription>>,

    /// Label bindings (for record fields).
    labels: TycompTbl<Arc<LabelDescription>>,

    /// Module bindings.
    modules: IdTbl<Arc<ModuleDeclaration>>,

    /// Lazily-forced qualified component views for local module bindings.
    /// This mirrors OCaml's `env.components` table for local `Pident` paths.
    module_components: IdTbl<Arc<super::env_lazy::StoredModuleComponents>>,

    /// Module type bindings.
    modtypes: IdTbl<Arc<ModtypeDeclaration>>,

    /// Intentional Rust performance cache for active local module aliases.
    ///
    /// OCaml walks the current Env tables when resolving module components
    /// (compiler/ml/env.ml:781-813, 1516-1538). Rust memoizes that derived
    /// view per immutable Env instance because the env_lazy-backed
    /// module-components cache key logic consults it frequently in
    /// module-heavy files. This cache must stay derived from bindings only; it
    /// must not become a path-spelling alias-equivalence shortcut.

    /// Module identifiers that are functor parameters.
    /// Mirrors OCaml `Env.functor_args` and drives aliasability checks.
    functor_args: HashSet<Ident>,

    local_module_aliases_cache: RefCell<Option<Vec<(Ident, Path)>>>,

    /// Intentional Rust performance cache for env-scoped component cache keys.
    ///
    /// This preserves OCaml's lookup boundary from find_module_descr/find_type
    /// into components_of_module_maker (compiler/ml/env.ml:781-813,
    /// 1516-1538) but avoids recomputing the same alias-scope predicate for
    /// every qualified component lookup.
    module_path_requires_env_scoped_cache_cache: RefCell<HashMap<String, bool>>,

    /// Persistent roots opened by the initial environment.
    ///
    /// OCaml compiler/core/res_compmisc.ml:48-63 installs implicit opens before
    /// typechecking source items. `Env.normalize_path` can still force those
    /// roots through compiler/ml/env.ml:865-875 because no source open selected
    /// them. Source-level opens use the same component tables but should not be
    /// classified as initial-env roots.
    implicit_open_roots: im_rc::HashSet<String>,

    /// Summary of bindings.
    ///
    /// OCaml keeps `Env.summary` for paths that reconstruct environment
    /// deltas. The Rust checker does not read summaries outside this module;
    /// all semantic lookup state lives in the binding tables below. Keep the
    /// public accessor stable but avoid building an unused persistent chain on
    /// every binding addition.
    summary: EnvSummary,

    /// Local constraints (for GADTs).
    local_constraints: im_rc::HashMap<Path, Arc<TypeDeclaration>>,

    /// GADT instance levels.
    gadt_instances: Vec<(i32, Vec<TypeExprRef>)>,

    /// Environment flags.
    flags: EnvFlags,
}

impl Clone for Env {
    fn clone(&self) -> Self {
        Env {
            // Keep clone-induced env changes visible to abbreviation caching by
            // default. Callers that are only snapshotting the same logical env
            // must opt into `clone_preserve_id()`.
            id: NEXT_ENV_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            values: self.values.clone(),
            types: self.types.clone(),
            constrs: self.constrs.clone(),
            labels: self.labels.clone(),
            modules: self.modules.clone(),
            module_components: self.module_components.clone(),
            modtypes: self.modtypes.clone(),
            functor_args: self.functor_args.clone(),
            // These are Rust-only memo tables derived from the binding tables.
            // Do not duplicate them when creating a fresh Env identity; OCaml
            // Env snapshots carry semantic bindings, not copied memoized
            // lookup results.
            local_module_aliases_cache: RefCell::new(None),
            module_path_requires_env_scoped_cache_cache: RefCell::new(HashMap::new()),
            implicit_open_roots: self.implicit_open_roots.clone(),
            summary: self.summary.clone(),
            local_constraints: self.local_constraints.clone(),
            gadt_instances: self.gadt_instances.clone(),
            flags: self.flags,
        }
    }
}

/// Environment flags.
#[derive(Debug, Clone, Copy, Default)]
pub struct EnvFlags {
    /// Check for dependency cycles.
    pub check_dependency: bool,
    /// Allow hiding of bindings.
    pub allow_hiding: bool,
}

impl Env {
    /// Create an empty environment.
    pub fn empty() -> Self {
        Env {
            id: NEXT_ENV_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            values: IdTbl::new(),
            types: IdTbl::new(),
            constrs: TycompTbl::new(),
            labels: TycompTbl::new(),
            modules: IdTbl::new(),
            module_components: IdTbl::new(),
            modtypes: IdTbl::new(),
            functor_args: HashSet::new(),
            local_module_aliases_cache: RefCell::new(None),
            module_path_requires_env_scoped_cache_cache: RefCell::new(HashMap::new()),
            implicit_open_roots: im_rc::HashSet::new(),
            summary: EnvSummary::Empty,
            local_constraints: im_rc::HashMap::new(),
            gadt_instances: Vec::new(),
            flags: EnvFlags::default(),
        }
    }

    /// Unique identifier for this environment instance.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Clone an environment while preserving its current identity.
    /// This is for storing a snapshot of the same logical env value rather
    /// than creating a fresh env instance.
    pub fn clone_preserve_id(&self) -> Self {
        Env {
            id: self.id,
            values: self.values.clone(),
            types: self.types.clone(),
            constrs: self.constrs.clone(),
            labels: self.labels.clone(),
            modules: self.modules.clone(),
            module_components: self.module_components.clone(),
            modtypes: self.modtypes.clone(),
            functor_args: self.functor_args.clone(),
            // These are Rust-only memo tables derived from the binding tables.
            // Do not duplicate them when snapshotting environments for unifier
            // state; OCaml Env snapshots carry semantic bindings, not copied
            // memoized lookup results.
            local_module_aliases_cache: RefCell::new(None),
            module_path_requires_env_scoped_cache_cache: RefCell::new(HashMap::new()),
            implicit_open_roots: self.implicit_open_roots.clone(),
            summary: self.summary.clone(),
            local_constraints: self.local_constraints.clone(),
            gadt_instances: self.gadt_instances.clone(),
            flags: self.flags,
        }
    }

    /// Get the environment summary.
    pub fn summary(&self) -> &EnvSummary {
        &self.summary
    }

    /// Mark this environment as changed.
    fn bump_id(&mut self) {
        self.id = NEXT_ENV_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    fn invalidate_module_alias_caches(&self) {
        // These caches are purely derived from visible bindings. Every Env
        // mutation that can change OCaml component lookup visibility must drop
        // them before later lookups rebuild the same derived view.
        self.local_module_aliases_cache.borrow_mut().take();
        self.module_path_requires_env_scoped_cache_cache
            .borrow_mut()
            .clear();
    }

    fn path_has_prefix(path: &Path, prefix: &Path) -> bool {
        if path.same(prefix) {
            return true;
        }
        match path {
            Path::Pdot(parent, _, _) => Self::path_has_prefix(parent, prefix),
            Path::Pident(_) | Path::Papply(_, _) => false,
        }
    }

    fn module_path_scope_cache_key(path: &Path) -> Option<String> {
        // Match `Path.flatten` in compiler/ml/path.ml:63-69: any nested
        // `Papply` is `Contains_apply`, so env-scoped cache keys that need a
        // single head identifier are only valid for regular dotted paths.
        let (head, _) = path.flatten().ok()?;
        let name = path.name();
        if head.is_persistent() || head.stamp() == 0 {
            Some(name)
        } else {
            Some(format!("{name}#{}", head.stamp()))
        }
    }

    pub(crate) fn with_current_local_module_aliases<R>(
        &self,
        f: impl FnOnce(&[(Ident, Path)]) -> R,
    ) -> R {
        if self.local_module_aliases_cache.borrow().is_none() {
            let mut aliases: Vec<_> = self
                .modules
                .visible_local_entries()
                .filter_map(|(id, decl)| {
                    match &decl.md_type {
                        ModuleType::MtyAlias(_, target) | ModuleType::MtyIdent(target) => {
                            Some((id.clone(), target.clone()))
                        }
                        _ => None,
                    }
                })
                .collect();
            aliases.sort_by(|(left_id, left_target), (right_id, right_target)| {
                right_target
                    .name()
                    .len()
                    .cmp(&left_target.name().len())
                    .then_with(|| right_target.name().cmp(&left_target.name()))
                    .then_with(|| right_id.stamp().cmp(&left_id.stamp()))
            });
            *self.local_module_aliases_cache.borrow_mut() = Some(aliases);
        }

        let cache = self.local_module_aliases_cache.borrow();
        f(cache.as_deref().unwrap_or(&[]))
    }

    pub(crate) fn module_path_requires_env_scoped_cache(&self, module_path: &Path) -> bool {
        if module_path.head().is_persistent() {
            return false;
        }

        let Some(cache_key) = Self::module_path_scope_cache_key(module_path) else {
            return false;
        };

        if let Some(cached) = self
            .module_path_requires_env_scoped_cache_cache
            .borrow()
            .get(&cache_key)
            .copied()
        {
            return cached;
        }

        let requires = self.with_current_local_module_aliases(|aliases| {
            aliases.iter().any(|(_, target_path)| {
                let target_head = target_path.head();
                self.has_module_ident(target_head)
                    && Self::path_has_prefix(module_path, target_path)
            })
        });
        self.module_path_requires_env_scoped_cache_cache
            .borrow_mut()
            .insert(cache_key, requires);
        requires
    }

    // ========================================================================
    // Value Bindings
    // ========================================================================

    /// Add a value binding.
    pub fn add_value(&mut self, id: Ident, desc: ValueDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.values.add(id, desc);
    }

    /// Add a value binding from an opened module (lower priority than local bindings).
    pub fn add_opened_value(&mut self, id: Ident, desc: ValueDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.values.add_opened(id, desc);
    }

    /// Find a value by name.
    pub fn find_value(&self, name: &str) -> EnvResult<&ValueDescription> {
        self.values
            .find_by_name(name)
            .map(|v| v.as_ref())
            .ok_or_else(|| EnvError::ValueNotFound(name.to_string()))
    }

    /// Find a value by name, returning both the identifier and description.
    pub fn find_value_with_id(&self, name: &str) -> EnvResult<(&Ident, &ValueDescription)> {
        self.values
            .find_by_name_with_id(name)
            .map(|(id, v)| (id, v.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.to_string()))
    }

    /// Find a value by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_value_with_path(&self, name: &str) -> EnvResult<(Path, &ValueDescription)> {
        self.values
            .find_by_name_with_path(name)
            .map(|(path, desc)| (path, desc.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.to_string()))
    }

    /// Iterate over visible value bindings.
    pub fn iter_values(&self) -> impl Iterator<Item = (&Ident, &ValueDescription)> {
        self.values.iter().map(|(id, v)| (id, v.as_ref()))
    }

    /// Update the visible value binding for `name` with a replacement type.
    /// This replaces the current binding in-place rather than adding a shadowing entry.
    pub fn update_value_type_by_name(&mut self, name: &str, new_type: TypeExprRef) -> bool {
        let mut update = |desc: &Arc<ValueDescription>| {
            let mut updated = (**desc).clone();
            updated.val_type = new_type;
            Arc::new(updated)
        };
        if self.values.update_by_name(name, &mut update).is_none() {
            return false;
        }

        self.bump_id();
        true
    }

    /// Count how many value bindings exist for a given name.
    pub fn count_value_bindings(&self, name: &str) -> usize {
        self.values.find_all(name).len()
    }

    /// Find a value by path.
    pub fn lookup_value(&self, path: &Path) -> EnvResult<&ValueDescription> {
        match path {
            Path::Pident(id) => self
                .values
                .find_by_ident(id)
                .map(|v| v.as_ref())
                .ok_or_else(|| EnvError::ValueNotFound(id.name().to_string())),
            Path::Pdot(_, name, _) => self.find_value(name),
            Path::Papply(_, _) => Err(EnvError::ValueNotFound("(functor application)".to_string())),
        }
    }

    // ========================================================================
    // Type Bindings
    // ========================================================================

    /// Add a type binding.
    pub fn add_type(&mut self, id: Ident, decl: TypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.types.add(id, decl);
    }

    /// Add a type binding from an opened module (lower priority than local bindings).
    pub fn add_opened_type(&mut self, id: Ident, decl: TypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.types.add_opened(id, decl);
    }

    /// Find a type by name.
    pub fn find_type(&self, name: &str) -> EnvResult<&TypeDeclaration> {
        self.types
            .find_by_name(name)
            .map(|t| t.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(name.to_string()))
    }

    /// Find a type by name, returning the identifier and declaration.
    /// The returned identifier has the canonical stamp from the environment
    /// (e.g., persistent ident for predef types).
    pub fn find_type_with_id(&self, name: &str) -> EnvResult<(&Ident, &TypeDeclaration)> {
        self.types
            .find_by_name_with_id(name)
            .map(|(id, decl)| (id, decl.as_ref()))
            .ok_or_else(|| EnvError::TypeNotFound(name.to_string()))
    }

    /// Find a type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_type_with_path(&self, name: &str) -> EnvResult<(Path, &TypeDeclaration)> {
        self.types
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::TypeNotFound(name.to_string()))
    }

    /// Iterate over visible type bindings.
    pub fn iter_types(&self) -> impl Iterator<Item = (&Ident, &TypeDeclaration)> {
        self.types.iter().map(|(id, decl)| (id, decl.as_ref()))
    }

    pub(crate) fn find_type_by_ident(&self, id: &Ident) -> EnvResult<&TypeDeclaration> {
        // OCaml compiler/ml/env.ml:800-813 dispatches Pident type lookup to
        // `IdTbl.find_same`, so same-name bindings must not be treated as an
        // exact hit when expanding a constructor path by identifier.
        self.types
            .find_by_ident(id)
            .map(|t| t.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(id.name().to_string()))
    }

    /// Find a type by path.
    pub fn lookup_type(&self, path: &Path) -> EnvResult<&TypeDeclaration> {
        match path {
            Path::Pident(id) => self
                .types
                .find_by_ident(id)
                .or_else(|| {
                    // Some in-process callers still pass copied signature ids
                    // whose stamp does not match the current table entry. Keep
                    // the existing recovery here; expansion paths that must
                    // mirror OCaml `IdTbl.find_same` use
                    // `lookup_type_ident_exact` instead
                    // (compiler/ml/env.ml:800-813,862).
                    self.types.find_by_name(id.name())
                })
                .map(|t| t.as_ref())
                .ok_or_else(|| EnvError::TypeNotFound(id.name().to_string())),
            Path::Pdot(parent, name, _) => {
                // Try to find the type through the parent module's signature first.
                // Follow MtyIdent/MtyAlias to resolve the module type to a signature.
                if let Ok(parent_md) = self.lookup_module(parent) {
                    // Search parent module's signature for the type
                    fn find_type_in_module_type<'a>(
                        env: &'a Env,
                        mty: &'a super::decl::ModuleType,
                        name: &str,
                        depth: usize,
                    ) -> Option<&'a super::decl::TypeDeclaration> {
                        if depth > 10 {
                            return None;
                        }
                        match mty {
                            super::decl::ModuleType::MtySignature(sig) => {
                                for item in sig {
                                    if let super::decl::SignatureItem::SigType(id, decl, _) = item {
                                        if id.name() == name {
                                            return Some(decl);
                                        }
                                    }
                                }
                                None
                            }
                            super::decl::ModuleType::MtyIdent(type_path)
                            | super::decl::ModuleType::MtyAlias(_, type_path) => {
                                if let Ok(mtd) = env.lookup_modtype(type_path) {
                                    if let Some(resolved) = &mtd.mtd_type {
                                        return find_type_in_module_type(
                                            env,
                                            resolved,
                                            name,
                                            depth + 1,
                                        );
                                    }
                                }
                                if let Ok(md) = env.lookup_module(type_path) {
                                    return find_type_in_module_type(
                                        env,
                                        &md.md_type,
                                        name,
                                        depth + 1,
                                    );
                                }
                                None
                            }
                            _ => None,
                        }
                    }
                    if let Some(decl) = find_type_in_module_type(self, &parent_md.md_type, name, 0)
                    {
                        return Ok(decl);
                    }
                }
                // Fallback to name-based lookup
                self.find_type(name)
            }
            Path::Papply(_, _) => Err(EnvError::TypeNotFound("(functor application)".to_string())),
        }
    }

    // ========================================================================
    // Constructor Bindings
    // ========================================================================

    /// Add a constructor binding.
    pub fn add_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.constrs.add(id, desc);
    }

    /// Add a constructor binding from an opened module (lower priority than local bindings).
    pub fn add_opened_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.constrs.add_opened(id, desc);
    }

    /// Find a constructor by name.
    pub fn find_constructor(&self, name: &str) -> EnvResult<&ConstructorDescription> {
        self.constrs
            .find_by_name(name)
            .map(|c| c.as_ref())
            .ok_or_else(|| EnvError::ConstructorNotFound(name.to_string()))
    }

    /// Find a constructor by name with its local/opened origin flag.
    pub fn find_constructor_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &ConstructorDescription, bool)> {
        self.constrs
            .find_by_name_with_origin(name)
            .map(|(id, c, is_local)| (id, c.as_ref(), is_local))
            .ok_or_else(|| EnvError::ConstructorNotFound(name.to_string()))
    }

    /// Find all constructors with a given name.
    pub fn find_all_constructors(&self, name: &str) -> Vec<&ConstructorDescription> {
        self.constrs
            .find_all(name)
            .into_iter()
            .map(|c| c.as_ref())
            .collect()
    }

    /// Iterate over visible constructor bindings.
    pub fn iter_constructors(&self) -> impl Iterator<Item = (&Ident, &ConstructorDescription)> {
        self.constrs.iter().map(|(id, c)| (id, c.as_ref()))
    }

    // ========================================================================
    // Label Bindings
    // ========================================================================

    /// Add a label binding.
    pub fn add_label(&mut self, id: Ident, desc: LabelDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.labels.add(id, desc);
    }

    /// Add a label binding from an opened module (lower priority than local bindings).
    pub fn add_opened_label(&mut self, id: Ident, desc: LabelDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.labels.add_opened(id, desc);
    }

    /// Find a label by name.
    pub fn find_label(&self, name: &str) -> EnvResult<&LabelDescription> {
        self.labels
            .find_by_name(name)
            .map(|l| l.as_ref())
            .ok_or_else(|| EnvError::LabelNotFound(name.to_string()))
    }

    /// Find a label by name with its local/opened origin flag.
    pub fn find_label_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &LabelDescription, bool)> {
        self.labels
            .find_by_name_with_origin(name)
            .map(|(id, l, is_local)| (id, l.as_ref(), is_local))
            .ok_or_else(|| EnvError::LabelNotFound(name.to_string()))
    }

    /// Find all labels with a given name.
    pub fn find_all_labels(&self, name: &str) -> Vec<&LabelDescription> {
        self.labels
            .find_all(name)
            .into_iter()
            .map(|l| l.as_ref())
            .collect()
    }

    /// Iterate over visible label bindings.
    pub fn iter_labels(&self) -> impl Iterator<Item = (&Ident, &LabelDescription)> {
        self.labels.iter().map(|(id, l)| (id, l.as_ref()))
    }

    pub(crate) fn opened_binding_names_added_since(&self, previous: &Env) -> OpenedBindingNames {
        // OCaml compiler/ml/env.ml:1874-1911 attaches the open warning slot
        // while `open_signature` installs the opened component tables through
        // env.ml:181-187 and env.ml:277-283. Derive Rust warning names from the
        // same just-added opened bindings instead of resolving the module again.
        OpenedBindingNames {
            values: self.values.opened_names_added_since(&previous.values),
            types: self.types.opened_names_added_since(&previous.types),
            modules: self.modules.opened_names_added_since(&previous.modules),
            modtypes: self.modtypes.opened_names_added_since(&previous.modtypes),
            constructors: self.constrs.opened_names_added_since(&previous.constrs),
            labels: self.labels.opened_names_added_since(&previous.labels),
        }
    }

    // ========================================================================
    // Module Bindings
    // ========================================================================

    pub(crate) fn add_module_with_component_path(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_path: Path,
    ) {
        self.add_module_with_component_context(id, decl.clone(), decl, component_path, None);
    }

    pub(crate) fn add_module_with_component_context(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_decl: ModuleDeclaration,
        component_path: Path,
        parent_context: Option<(Path, Arc<Signature>)>,
    ) {
        let seed_env = self.clone_preserve_id();
        let stored_components = Arc::new(
            super::env_lazy::StoredModuleComponents::new_with_parent_context(
                seed_env,
                component_path,
                component_decl,
                parent_context,
            ),
        );
        self.bump_id();
        self.invalidate_module_alias_caches();
        let decl = Arc::new(decl);
        self.modules.add(id.clone(), decl);
        self.module_components.add(id.clone(), stored_components);
    }

    /// Add a module binding.
    pub fn add_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module_with_component_path(id.clone(), decl, Path::pident(id));
    }

    /// Add a functor-parameter module binding.
    pub fn add_module_arg(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module(id.clone(), decl);
        self.functor_args.insert(id);
    }

    /// Check whether a module path is rooted in a functor parameter.
    pub fn is_functor_arg_path(&self, path: &Path) -> bool {
        match path {
            Path::Pident(id) => self.functor_args.iter().any(|arg| arg.same(id)),
            Path::Pdot(parent, _, _) => self.is_functor_arg_path(parent),
            Path::Papply(_, _) => true,
        }
    }

    /// Add a module binding from an opened module (lower priority than local bindings).
    pub fn add_opened_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.bump_id();
        self.invalidate_module_alias_caches();
        let decl = Arc::new(decl);
        self.modules.add_opened(id, decl);
    }

    pub(crate) fn add_opened_module_with_components(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        components: Arc<super::env_lazy::StoredModuleComponents>,
    ) {
        // OCaml compiler/ml/env.ml:1841-1877 `open_signature` adds both
        // `comp_modules` and `comp_components` to the opened environment. Keep
        // the opened component thunk with the opened module declaration so a
        // source `Lident` lookup can reuse env.ml:1874-1877's component table
        // instead of rebuilding through the parent module path.
        self.bump_id();
        self.invalidate_module_alias_caches();
        self.modules.add_opened(id.clone(), Arc::new(decl));
        self.module_components.add_opened(id, components);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_opened_component_layers(
        &mut self,
        root: Path,
        values: Vec<(Ident, ValueDescription, i32)>,
        types: Vec<(Ident, TypeDeclaration)>,
        constructors: Vec<(Ident, ConstructorDescription)>,
        labels: Vec<(Ident, LabelDescription)>,
        modules: Vec<(Ident, ModuleDeclaration, i32)>,
        module_components: Vec<(Ident, Arc<super::env_lazy::StoredModuleComponents>, i32)>,
        modtypes: Vec<(Ident, ModtypeDeclaration)>,
    ) {
        let has_bindings = !values.is_empty()
            || !types.is_empty()
            || !constructors.is_empty()
            || !labels.is_empty()
            || !modules.is_empty()
            || !module_components.is_empty()
            || !modtypes.is_empty();
        if !has_bindings {
            return;
        }

        self.bump_id();
        self.invalidate_module_alias_caches();
        self.values.add_open_layer(
            root.clone(),
            values
                .into_iter()
                .map(|(id, desc, pos)| (id, Arc::new(desc), pos))
                .collect(),
        );
        self.types.add_open_layer(
            root.clone(),
            types
                .into_iter()
                .map(|(id, decl)| (id, Arc::new(decl), crate::types::path::NOPOS))
                .collect(),
        );
        self.constrs.add_open_layer(
            constructors
                .into_iter()
                .map(|(id, desc)| (id, Arc::new(desc)))
                .collect(),
        );
        self.labels.add_open_layer(
            labels
                .into_iter()
                .map(|(id, desc)| (id, Arc::new(desc)))
                .collect(),
        );
        self.modules.add_open_layer(
            root.clone(),
            modules
                .into_iter()
                .map(|(id, decl, pos)| (id, Arc::new(decl), pos))
                .collect(),
        );
        self.module_components
            .add_open_layer(root.clone(), module_components);
        self.modtypes.add_open_layer(
            root,
            modtypes
                .into_iter()
                .map(|(id, decl)| (id, Arc::new(decl), crate::types::path::NOPOS))
                .collect(),
        );
    }

    /// Find a module by name.
    pub fn find_module(&self, name: &str) -> EnvResult<&ModuleDeclaration> {
        self.modules
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Find a module by name, returning both the identifier and declaration.
    pub fn find_module_with_id(&self, name: &str) -> EnvResult<(&Ident, &ModuleDeclaration)> {
        self.modules
            .find_by_name_with_id(name)
            .map(|(id, m)| (id, m.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Find a module by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_module_with_path(&self, name: &str) -> EnvResult<(Path, &ModuleDeclaration)> {
        self.modules
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    fn first_dotted_component_path(path: &Path) -> Option<Path> {
        match path {
            Path::Pdot(parent, name, pos) => match parent.as_ref() {
                Path::Pident(_) => {
                    Some(Path::pdot_pos(parent.as_ref().clone(), name.clone(), *pos))
                }
                _ => Self::first_dotted_component_path(parent),
            },
            Path::Pident(_) | Path::Papply(_, _) => None,
        }
    }

    pub(crate) fn path_starts_with_opened_component(&self, path: &Path) -> bool {
        // OCaml compiler/core/res_compmisc.ml:56-62 installs implicit opens
        // through Env.open_signature; compiler/ml/env.ml:1874-1877 adds the
        // opened components without a root module binding. Detect those
        // component-origin paths from the Env binding itself, not by spelling
        // roots such as `Stdlib` or `Pervasives`.
        let Some(component_path) = Self::first_dotted_component_path(path) else {
            return false;
        };
        self.find_module_with_path(component_path.last())
            .ok()
            .is_some_and(|(selected_path, _)| selected_path.same(&component_path))
    }

    pub(crate) fn mark_implicit_open_root(&mut self, name: &str) {
        self.implicit_open_roots.insert(name.to_string());
    }

    pub(crate) fn path_starts_with_implicit_opened_component(&self, path: &Path) -> bool {
        let Some(component_path) = Self::first_dotted_component_path(path) else {
            return false;
        };
        self.implicit_open_roots
            .contains(component_path.head().name())
            && self.path_starts_with_opened_component(path)
    }

    /// Iterate over visible module bindings.
    pub fn iter_modules(&self) -> impl Iterator<Item = (&Ident, &ModuleDeclaration)> {
        self.modules.iter().map(|(id, m)| (id, m.as_ref()))
    }

    pub(crate) fn has_module_ident(&self, id: &Ident) -> bool {
        self.modules.find_by_ident(id).is_some()
    }

    pub(crate) fn lookup_module_ident_exact(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        // OCaml compiler/ml/env.ml:781-788 uses `IdTbl.find_same` for
        // path-based `Pident` lookup. Source `Longident.Lident` lookup has its
        // own name fallback in env.ml:1000-1007; exact paths must not resolve to
        // a local/opened same-name module.
        self.modules
            .find_by_ident(id)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string()))
    }

    pub(crate) fn find_module_same(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        // OCaml compiler/ml/env.ml:865-875 uses `IdTbl.find_same` for
        // `Path.Pident` module lookup, and IdTbl.find_same at env.ml:285-290
        // skips opened components. This keeps alias scraping from resolving a
        // persistent alias target through an unrelated opened component with
        // the same name.
        self.modules
            .find_local_by_ident(id)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string()))
    }

    pub(crate) fn with_local_module_components<R>(
        &self,
        path: &Path,
        f: impl FnOnce(&super::env_lazy::StoredModuleComponents) -> R,
    ) -> Option<R> {
        let Path::Pident(id) = path else {
            return None;
        };
        let components = self.module_components.find_by_ident(id)?;
        Some(f(components.as_ref()))
    }

    pub(crate) fn local_module_components_arc(
        &self,
        path: &Path,
    ) -> Option<Arc<super::env_lazy::StoredModuleComponents>> {
        let Path::Pident(id) = path else {
            return None;
        };
        // OCaml compiler/ml/env.ml:1573-1578 stores component thunks in the
        // component table and shares the forced lazy value. Return the stored
        // Arc directly so child component maps keep the same thunk instead of
        // deep-cloning its captured seed environment.
        self.module_components.find_by_ident(id).cloned()
    }

    /// Find a module by path.
    pub fn lookup_module(&self, path: &Path) -> EnvResult<&ModuleDeclaration> {
        fn lookup_submodule_in_module_type<'a>(
            env: &'a Env,
            mty: &'a ModuleType,
            name: &str,
            visiting: &mut HashSet<Path>,
        ) -> Option<&'a ModuleDeclaration> {
            match mty {
                ModuleType::MtySignature(sig) => sig.iter().find_map(|item| match item {
                    SignatureItem::SigModule(id, md, _) if id.name() == name => Some(md),
                    _ => None,
                }),
                ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                    let md = lookup_module_inner(env, alias_path, visiting).ok()?;
                    lookup_submodule_in_module_type(env, &md.md_type, name, visiting)
                }
                ModuleType::MtyFunctor { .. } => None,
            }
        }

        fn lookup_module_inner<'a>(
            env: &'a Env,
            path: &Path,
            visiting: &mut HashSet<Path>,
        ) -> EnvResult<&'a ModuleDeclaration> {
            if !visiting.insert(path.clone()) {
                return Err(EnvError::ModuleNotFound(path.name()));
            }

            match path {
                Path::Pident(id) => {
                    let result = env
                        .modules
                        .find_by_ident(id)
                        .or_else(|| {
                            // Fallback: try name-based lookup for stamp mismatches
                            env.modules.find_by_name(id.name())
                        })
                        .map(|m| m.as_ref())
                        .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string()));
                    result
                }
                Path::Pdot(parent, name, _) => {
                    let parent_md = lookup_module_inner(env, parent, visiting)?;
                    lookup_submodule_in_module_type(env, &parent_md.md_type, name, visiting)
                        .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
                }
                Path::Papply(_, _) => Err(EnvError::ModuleNotFound(
                    "(functor application)".to_string(),
                )),
            }
        }

        let mut visiting = HashSet::new();
        lookup_module_inner(self, path, &mut visiting)
    }

    /// Normalize a path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path`.
    /// For `Pdot(p, s)`, first normalizes the prefix `p`, then checks
    /// if the resulting module is an alias and follows it.
    /// For `Pident(id)`, checks if it's a module alias and follows it.
    pub fn normalize_path(&self, path: &Path) -> Path {
        self.normalize_path_inner(path, 0)
    }

    /// Normalize the prefix of a value/extension path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path_prefix`.
    pub fn normalize_path_prefix(&self, path: &Path) -> Path {
        match path {
            Path::Pdot(prefix, name, pos) => {
                let normalized_prefix = self.normalize_path(prefix);
                if normalized_prefix == **prefix {
                    path.clone()
                } else {
                    Path::Pdot(std::sync::Arc::new(normalized_prefix), name.clone(), *pos)
                }
            }
            Path::Pident(_) => path.clone(),
            Path::Papply(_, _) => panic!("normalize_path_prefix called on Papply"),
        }
    }

    fn normalize_path_inner(&self, path: &Path, depth: usize) -> Path {
        if depth > 20 {
            return path.clone(); // Prevent infinite loops
        }
        // First, recursively normalize the prefix for Pdot paths
        let path = match path {
            Path::Pdot(p, s, pos) => {
                let p_norm = self.normalize_path_inner(p, depth + 1);
                if p_norm == **p {
                    path.clone()
                } else {
                    Path::Pdot(std::sync::Arc::new(p_norm), s.clone(), *pos)
                }
            }
            _ => path.clone(),
        };

        // Then check if the path itself is a module alias
        if let Ok(md) = self.lookup_module(&path) {
            if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
                return self.normalize_path_inner(alias_path, depth + 1);
            }
        }
        path
    }

    // ========================================================================
    // Module Type Bindings
    // ========================================================================

    /// Add a module type binding.
    pub fn add_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.modtypes.add(id, decl);
    }

    /// Add a module type binding from an opened module (lower priority than local bindings).
    pub fn add_opened_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.modtypes.add_opened(id, decl);
    }

    /// Find a module type by name.
    pub fn find_modtype(&self, name: &str) -> EnvResult<&ModtypeDeclaration> {
        self.modtypes
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Find a module type by name, returning both the identifier and declaration.
    pub fn find_modtype_with_id(&self, name: &str) -> EnvResult<(&Ident, &ModtypeDeclaration)> {
        self.modtypes
            .find_by_name_with_id(name)
            .map(|(id, decl)| (id, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Find a module type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_modtype_with_path(&self, name: &str) -> EnvResult<(Path, &ModtypeDeclaration)> {
        self.modtypes
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Iterate over visible module type bindings.
    pub fn iter_modtypes(&self) -> impl Iterator<Item = (&Ident, &ModtypeDeclaration)> {
        self.modtypes.iter().map(|(id, mtd)| (id, mtd.as_ref()))
    }

    /// Find a module type by path.
    pub fn lookup_modtype(&self, path: &Path) -> EnvResult<&ModtypeDeclaration> {
        match path {
            Path::Pident(id) => self
                .modtypes
                .find_by_ident(id)
                .map(|m| m.as_ref())
                .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string())),
            Path::Pdot(parent, name, _) => {
                // Try to find the modtype through the parent module's signature.
                // First try ident-based lookup, then name-based for stamp mismatches.
                let parent_md = self.lookup_module(parent).or_else(|_| {
                    // Fallback: try by name if stamp doesn't match
                    self.find_module(parent.last())
                });
                if let Ok(parent_md) = parent_md {
                    if let super::decl::ModuleType::MtySignature(ref sig) = parent_md.md_type {
                        for item in sig {
                            if let super::decl::SignatureItem::SigModtype(id, decl) = item {
                                if id.name() == name {
                                    return Ok(decl);
                                }
                            }
                        }
                    }
                }
                Err(EnvError::ModuleNotFound(name.clone()))
            }
            Path::Papply(_, _) => Err(EnvError::ModuleNotFound(
                "(functor application)".to_string(),
            )),
        }
    }

    // ========================================================================
    // GADT Support
    // ========================================================================

    /// Check if the environment has local constraints.
    pub fn has_local_constraints(&self) -> bool {
        !self.local_constraints.is_empty()
    }

    /// Add a local constraint.
    pub fn add_local_constraint(&mut self, path: Path, decl: TypeDeclaration) {
        self.bump_id();
        self.local_constraints.insert(path, Arc::new(decl));
    }

    /// Find a local constraint.
    pub fn find_local_constraint(&self, path: &Path) -> Option<&TypeDeclaration> {
        self.local_constraints.get(path).map(|d| d.as_ref())
    }

    /// Iterate over all local constraints.
    pub fn iter_local_constraints(&self) -> impl Iterator<Item = (&Path, &TypeDeclaration)> {
        self.local_constraints.iter().map(|(p, d)| (p, d.as_ref()))
    }

    /// Add a GADT instance level.
    pub fn add_gadt_instance_level(&mut self, level: i32, types: Vec<TypeExprRef>) {
        self.bump_id();
        self.gadt_instances.push((level, types));
    }

    /// Get GADT instance level for a type.
    pub fn gadt_instance_level(&self, _ty: TypeExprRef) -> Option<i32> {
        // TODO: Implement proper GADT instance tracking
        None
    }

    // ========================================================================
    // Environment Extension
    // ========================================================================

    /// Create a new environment with an additional value.
    pub fn with_value(&self, id: Ident, desc: ValueDescription) -> Env {
        let mut env = self.clone();
        env.add_value(id, desc);
        env
    }

    /// Create a new environment with an additional type.
    pub fn with_type(&self, id: Ident, decl: TypeDeclaration) -> Env {
        let mut env = self.clone();
        env.add_type(id, decl);
        env
    }

    /// Create a new environment with an additional module.
    pub fn with_module(&self, id: Ident, decl: ModuleDeclaration) -> Env {
        let mut env = self.clone();
        env.add_module(id, decl);
        env
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::empty()
    }
}

// ============================================================================
// Initial Environment
// ============================================================================

/// Create the initial environment with built-in types.
///
/// Matches OCaml's `Predef.common_initial_env`:
/// - Defines abstract types (int, float, string, char, bigint, etc.)
/// - Defines variant types with constructors (bool, unit, option, list, result)
/// - Registers constructors in the environment so they can be looked up
pub fn initial_env(ctx: &TypeContext) -> Env {
    let mut env = Env::empty();

    // Helper: create an abstract type declaration
    let decl_abstr = |arity: i32, immediate: bool| TypeDeclaration {
        type_params: vec![],
        type_arity: arity,
        type_kind: TypeKind::TypeAbstract,
        type_private: PrivateFlag::Public,
        type_manifest: None,
        type_variance: vec![],
        type_newtype_level: None,
        type_loc: Location::none(),
        type_attributes: vec![],
        type_immediate: immediate,
        type_unboxed: super::decl::UnboxedStatus::default(),
        type_inlined_types: vec![],
        type_path: None,
    };

    // Helper: create a constructor declaration (like OCaml's Predef.cstr)
    let cstr = |id: Ident, args: Vec<TypeExprRef>| ConstructorDeclaration {
        cd_id: id,
        cd_args: ConstructorArguments::CstrTuple(args),
        cd_res: None,
        cd_loc: Location::none(),
        cd_attributes: vec![],
    };

    // Helper: add a type with its constructors to the environment
    // This matches OCaml's Env.store_type which calls Datarepr.constructors_of_type
    let add_type_with_constrs = |env: &mut Env,
                                 id: Ident,
                                 decl: TypeDeclaration,
                                 ctx: &TypeContext| {
        let type_path = Path::pident(id.clone());

        // Extract constructors/labels from predef declarations so they are
        // available for disambiguation just like OCaml's initial environment.
        match &decl.type_kind {
            TypeKind::TypeVariant(constrs) => {
                let num_consts = constrs.iter()
                    .filter(|c| matches!(c.cd_args, ConstructorArguments::CstrTuple(ref args) if args.is_empty()))
                    .count() as i32;
                let num_nonconsts = constrs.len() as i32 - num_consts;
                let mut const_idx = 0i32;
                let mut nonconst_idx = 0i32;

                for cd in constrs {
                    let is_constant = matches!(cd.cd_args, ConstructorArguments::CstrTuple(ref args) if args.is_empty());

                    let cstr_tag = if decl.type_unboxed.unboxed {
                        ConstructorTag::CstrUnboxed
                    } else if is_constant {
                        let tag = ConstructorTag::CstrConstant(const_idx);
                        const_idx += 1;
                        tag
                    } else {
                        let tag = ConstructorTag::CstrBlock(nonconst_idx);
                        nonconst_idx += 1;
                        tag
                    };

                    let (cstr_args, cstr_arity) = match &cd.cd_args {
                        ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
                        ConstructorArguments::CstrRecord(labels) => {
                            let args: Vec<TypeExprRef> = labels.iter().map(|l| l.ld_type).collect();
                            let arity = args.len() as i32;
                            (args, arity)
                        }
                    };

                    let cstr_res = if let Some(res_ty) = cd.cd_res {
                        res_ty
                    } else {
                        ctx.new_generic_constr(type_path.clone(), decl.type_params.clone())
                    };

                    let cstr_existentials = constructor_existentials(ctx, &cstr_args, cd.cd_res);

                    let cstr_desc = ConstructorDescription {
                        cstr_name: cd.cd_id.name().to_string(),
                        cstr_res,
                        cstr_existentials,
                        cstr_args,
                        cstr_arity,
                        cstr_tag,
                        cstr_consts: num_consts,
                        cstr_nonconsts: num_nonconsts,
                        cstr_generalized: cd.cd_res.is_some(),
                        cstr_private: decl.type_private,
                        cstr_loc: Location::none(),
                        cstr_attributes:
                            crate::types::decl::constructor_description_attrs_for_variant(
                                constrs, cd,
                            ),
                        cstr_inlined: None,
                    };

                    env.add_constructor(cd.cd_id.clone(), cstr_desc);
                }
            }
            TypeKind::TypeRecord(labels, repr) => {
                let res_ty = ctx.new_generic_constr(type_path.clone(), decl.type_params.clone());
                for (pos, ld) in labels.iter().enumerate() {
                    let label_desc = LabelDescription {
                        lbl_name: ld.ld_id.name().to_string(),
                        lbl_res: res_ty,
                        lbl_arg: crate::types::ctype::remap_label_type_to_params(
                            ctx,
                            ld.ld_type,
                            &decl.type_params,
                        ),
                        lbl_mut: ld.ld_mutable,
                        lbl_optional: ld.ld_optional,
                        lbl_pos: pos as i32,
                        lbl_all: crate::types::decl::LabelArrayRef(0),
                        lbl_repres: repr.clone(),
                        lbl_private: decl.type_private,
                        lbl_loc: ld.ld_loc,
                        lbl_attributes: ld.ld_attributes.clone(),
                    };
                    env.add_label(ld.ld_id.clone(), label_desc);
                }
            }
            _ => {}
        }
        env.add_type(id, decl);
    };
    let add_internal_type_only = |env: &mut Env, id: Ident, decl: TypeDeclaration| {
        // OCaml compiler/ml/predef.ml:388-405 installs only the real language
        // predefs into the initial environment. The Rust comptime reflection
        // records are compiler-internal, so they must not add labels to the
        // `Typetexp.find_all_labels` scope used by typecore.ml:3666-3670.
        env.add_type(id, decl);
    };

    use super::predef;

    // ---- Abstract types ----
    // Order matches OCaml's Predef.common_initial_env add_type order
    add_type_with_constrs(
        &mut env,
        predef::ident_bool(),
        TypeDeclaration {
            type_kind: TypeKind::TypeVariant(vec![
                cstr(predef::ident_false(), vec![]),
                cstr(predef::ident_true(), vec![]),
            ]),
            type_immediate: true,
            ..decl_abstr(0, true)
        },
        ctx,
    );
    add_type_with_constrs(&mut env, predef::ident_int(), decl_abstr(0, true), ctx);
    add_type_with_constrs(&mut env, predef::ident_float(), decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, predef::ident_bigint(), decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, predef::ident_string(), decl_abstr(0, false), ctx);
    add_type_with_constrs(
        &mut env,
        predef::ident_unit(),
        TypeDeclaration {
            type_kind: TypeKind::TypeVariant(vec![cstr(predef::ident_void(), vec![])]),
            type_immediate: true,
            ..decl_abstr(0, true)
        },
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_extension_constructor(),
        decl_abstr(0, false),
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_exn(),
        TypeDeclaration {
            type_kind: TypeKind::TypeOpen,
            ..decl_abstr(0, false)
        },
        ctx,
    );
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_option(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr(predef::ident_none(), vec![]),
                    cstr(predef::ident_some(), vec![tvar]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar1 = ctx.new_generic_var(None);
        let tvar2 = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_result(),
            TypeDeclaration {
                type_params: vec![tvar1, tvar2],
                type_arity: 2,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr(predef::ident_ok(), vec![tvar1]),
                    cstr(predef::ident_error(), vec![tvar2]),
                ]),
                type_variance: vec![
                    crate::types::variance::Variance::covariant(),
                    crate::types::variance::Variance::covariant(),
                ],
                ..decl_abstr(2, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_promise(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    add_type_with_constrs(
        &mut env,
        predef::ident_array(),
        TypeDeclaration {
            type_variance: vec![crate::types::variance::Variance::full()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    // Upstream #8355: iterable / asyncIterable predef types (abstract,
    // covariant, 1 type parameter).
    add_type_with_constrs(
        &mut env,
        predef::ident_iterable(),
        TypeDeclaration {
            type_variance: vec![crate::types::variance::Variance::covariant()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_async_iterable(),
        TypeDeclaration {
            type_variance: vec![crate::types::variance::Variance::covariant()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    {
        let tvar = ctx.new_generic_var(None);
        let list_ty = ctx.new_generic_constr(predef::path_list(), vec![tvar]);
        add_type_with_constrs(
            &mut env,
            predef::ident_list(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr(predef::ident_nil(), vec![]),
                    cstr(predef::ident_cons(), vec![tvar, list_ty]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        let option_t = ctx.new_generic_constr(predef::path_option(), vec![tvar]);
        let dict_label = crate::types::decl::LabelDeclaration {
            ld_id: predef::ident_dict_magic_field(),
            ld_mutable: MutableFlag::Immutable,
            ld_optional: true,
            ld_type: option_t,
            ld_loc: Location::none(),
            ld_attributes: vec![],
        };
        add_type_with_constrs(
            &mut env,
            predef::ident_dict(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeRecord(
                    vec![dict_label],
                    crate::types::decl::RecordRepresentation::RecordRegular,
                ),
                type_variance: vec![crate::types::variance::Variance::full()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        let type_unknown = ctx.new_generic_constr(predef::path_unknown(), vec![]);
        add_type_with_constrs(
            &mut env,
            predef::ident_unknown(),
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: TypeKind::TypeVariant(vec![ConstructorDeclaration {
                    cd_id: predef::ident_ctor_unknown(),
                    cd_args: ConstructorArguments::CstrTuple(vec![tvar]),
                    cd_res: Some(type_unknown),
                    cd_loc: Location::none(),
                    cd_attributes: vec![],
                }]),
                type_unboxed: super::decl::UnboxedStatus::TRUE_FALSE,
                ..decl_abstr(0, false)
            },
            ctx,
        );
    }

    // ---- Comptime type reflection types ----
    // typeInfo is a recursive variant type:
    //   type rec typeInfo = Int | Float | String | Bool | Unit | Char | Bigint
    //     | Record({name: string, fields: array<fieldInfo>, unboxed: bool})
    //     | Variant({name: string, constructors: array<constructorInfo>, unboxed: bool})
    //     | Array({element: typeInfo}) | Option({inner: typeInfo})
    //     | Function({args: array<typeInfo>, returnType: typeInfo})
    //     | External({name: string}) | Opaque({name: string}) | TiUnknown
    //   and fieldInfo = { name: string, typ: typeInfo, optional: bool, mutable_: bool }
    //   and constructorInfo = { name: string, args: array<typeInfo> }
    {
        // Create the recursive type references
        let type_info_path = predef::path_type_info();
        let type_info_ty = ctx.new_generic_constr(type_info_path.clone(), vec![]);
        let field_info_ty = ctx.new_generic_constr(predef::path_field_info(), vec![]);
        let constructor_info_ty = ctx.new_generic_constr(predef::path_constructor_info(), vec![]);
        let string_ty = ctx.new_generic_constr(predef::path_string(), vec![]);
        let bool_ty = ctx.new_generic_constr(predef::path_bool(), vec![]);
        let array_field_info_ty = ctx.new_generic_constr(predef::path_array(), vec![field_info_ty]);
        let array_constructor_info_ty =
            ctx.new_generic_constr(predef::path_array(), vec![constructor_info_ty]);
        let array_type_info_ty = ctx.new_generic_constr(predef::path_array(), vec![type_info_ty]);

        // Simple no-arg constructors
        let simple_ctors: Vec<_> = vec![
            predef::ident_ti_int(),
            predef::ident_ti_float(),
            predef::ident_ti_string(),
            predef::ident_ti_bool(),
            predef::ident_ti_unit(),
            predef::ident_ti_char(),
            predef::ident_ti_bigint(),
            predef::ident_ti_unknown(),
        ]
        .into_iter()
        .map(|id| cstr(id, vec![]))
        .collect();

        // Record({name: string, fields: array<fieldInfo>, unboxed: bool})
        let record_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_record(),
            cd_args: ConstructorArguments::CstrRecord(vec![
                LabelDeclaration {
                    ld_id: predef::ident_fi_name(),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: string_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
                LabelDeclaration {
                    ld_id: Ident::new("fields", 900, IdentFlags::NONE), // reuse a stamp for inline record
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: array_field_info_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
                LabelDeclaration {
                    ld_id: Ident::new("unboxed", 901, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: bool_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
            ]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        // Variant({name: string, constructors: array<constructorInfo>, unboxed: bool})
        let variant_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_variant(),
            cd_args: ConstructorArguments::CstrRecord(vec![
                LabelDeclaration {
                    ld_id: Ident::new("name", 902, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: string_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
                LabelDeclaration {
                    ld_id: Ident::new("constructors", 903, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: array_constructor_info_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
                LabelDeclaration {
                    ld_id: Ident::new("unboxed", 901, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: bool_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
            ]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        // Array({element: typeInfo})
        let array_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_array(),
            cd_args: ConstructorArguments::CstrRecord(vec![LabelDeclaration {
                ld_id: Ident::new("element", 900, IdentFlags::NONE),
                ld_mutable: MutableFlag::Immutable,
                ld_optional: false,
                ld_type: type_info_ty,
                ld_loc: Location::none(),
                ld_attributes: vec![],
            }]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        // Option({inner: typeInfo})
        let option_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_option(),
            cd_args: ConstructorArguments::CstrRecord(vec![LabelDeclaration {
                ld_id: Ident::new("inner", 901, IdentFlags::NONE),
                ld_mutable: MutableFlag::Immutable,
                ld_optional: false,
                ld_type: type_info_ty,
                ld_loc: Location::none(),
                ld_attributes: vec![],
            }]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        // Function({args: array<typeInfo>, returnType: typeInfo})
        let function_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_function(),
            cd_args: ConstructorArguments::CstrRecord(vec![
                LabelDeclaration {
                    ld_id: Ident::new("args", 902, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: array_type_info_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
                LabelDeclaration {
                    ld_id: Ident::new("returnType", 903, IdentFlags::NONE),
                    ld_mutable: MutableFlag::Immutable,
                    ld_optional: false,
                    ld_type: type_info_ty,
                    ld_loc: Location::none(),
                    ld_attributes: vec![],
                },
            ]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        // External({name: string}) and Opaque({name: string})
        let external_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_external(),
            cd_args: ConstructorArguments::CstrRecord(vec![LabelDeclaration {
                ld_id: Ident::new("name", 904, IdentFlags::NONE),
                ld_mutable: MutableFlag::Immutable,
                ld_optional: false,
                ld_type: string_ty,
                ld_loc: Location::none(),
                ld_attributes: vec![],
            }]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        let opaque_ctor = ConstructorDeclaration {
            cd_id: predef::ident_ti_opaque(),
            cd_args: ConstructorArguments::CstrRecord(vec![LabelDeclaration {
                ld_id: Ident::new("name", 905, IdentFlags::NONE),
                ld_mutable: MutableFlag::Immutable,
                ld_optional: false,
                ld_type: string_ty,
                ld_loc: Location::none(),
                ld_attributes: vec![],
            }]),
            cd_res: None,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        };

        let mut all_ctors = simple_ctors;
        all_ctors.push(record_ctor);
        all_ctors.push(variant_ctor);
        all_ctors.push(array_ctor);
        all_ctors.push(option_ctor);
        all_ctors.push(function_ctor);
        all_ctors.push(external_ctor);
        all_ctors.push(opaque_ctor);

        // OCaml compiler/ml/predef.ml:388-405 only installs source-visible
        // language predefs into the initial environment. Keeping Rust's
        // comptime-only `typeInfo` constructors out of TycompTbl mirrors
        // compiler/ml/env.ml:1103-1114: `Typetexp.find_all_constructors` must
        // not see internal constructors like `String`, otherwise
        // compiler/ml/typecore.ml:990-1010 takes the wrong disambiguation path
        // before the expected-type `lookup_from_type` fallback.
        add_internal_type_only(
            &mut env,
            predef::ident_type_info(),
            TypeDeclaration {
                type_kind: TypeKind::TypeVariant(all_ctors),
                ..decl_abstr(0, false)
            },
        );

        // fieldInfo record type: { name: string, typ: typeInfo, optional: bool, mutable_: bool }
        add_internal_type_only(
            &mut env,
            predef::ident_field_info(),
            TypeDeclaration {
                type_kind: TypeKind::TypeRecord(
                    vec![
                        LabelDeclaration {
                            ld_id: predef::ident_fi_name(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: string_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                        LabelDeclaration {
                            ld_id: predef::ident_fi_typ(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: type_info_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                        LabelDeclaration {
                            ld_id: predef::ident_fi_optional(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: bool_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                        LabelDeclaration {
                            ld_id: predef::ident_fi_mutable(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: bool_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                    ],
                    RecordRepresentation::RecordRegular,
                ),
                ..decl_abstr(0, false)
            },
        );

        // constructorInfo record type: { name: string, args: array<typeInfo> }
        add_internal_type_only(
            &mut env,
            predef::ident_constructor_info(),
            TypeDeclaration {
                type_kind: TypeKind::TypeRecord(
                    vec![
                        LabelDeclaration {
                            ld_id: predef::ident_ci_name(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: string_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                        LabelDeclaration {
                            ld_id: predef::ident_ci_args(),
                            ld_mutable: MutableFlag::Immutable,
                            ld_optional: false,
                            ld_type: array_type_info_ty,
                            ld_loc: Location::none(),
                            ld_attributes: vec![],
                        },
                    ],
                    RecordRepresentation::RecordRegular,
                ),
                ..decl_abstr(0, false)
            },
        );
    }

    // Standard exception constructors (extension constructors of exn)
    {
        let exn_ty = ctx.new_generic_constr(predef::path_exn(), vec![]);
        let string_ty_for_exn = ctx.new_generic_constr(predef::path_string(), vec![]);
        let int_ty_for_exn = ctx.new_generic_constr(predef::path_int(), vec![]);

        let add_exception =
            |env: &mut Env, id: Ident, args: Vec<TypeExprRef>, exn_ty: TypeExprRef| {
                let path = Path::pident(id.clone());
                let warn_on_literal_pattern_attr = crate::types::decl::Attribute {
                    attr_name: crate::types::asttypes::Located::noloc(
                        "ocaml.warn_on_literal_pattern".to_string(),
                    ),
                    attr_payload: crate::types::decl::AttributePayload::Structure(vec![]),
                    attr_loc: Location::none(),
                };
                let cstr_desc = ConstructorDescription {
                    cstr_name: id.name().to_string(),
                    cstr_res: exn_ty,
                    cstr_existentials: vec![],
                    cstr_arity: args.len() as i32,
                    cstr_args: args,
                    cstr_tag: ConstructorTag::CstrExtension(path),
                    cstr_consts: -1,
                    cstr_nonconsts: -1,
                    cstr_generalized: false,
                    cstr_private: PrivateFlag::Public,
                    cstr_loc: Location::none(),
                    cstr_attributes: vec![warn_on_literal_pattern_attr],
                    cstr_inlined: None,
                };
                env.add_constructor(id, cstr_desc);
            };

        add_exception(&mut env, predef::ident_not_found(), vec![], exn_ty);
        add_exception(
            &mut env,
            predef::ident_invalid_argument(),
            vec![string_ty_for_exn],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_failure(),
            vec![string_ty_for_exn],
            exn_ty,
        );
        add_exception(&mut env, Ident::create_persistent("Exit"), vec![], exn_ty);
        add_exception(
            &mut env,
            predef::ident_match_failure(),
            vec![
                ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![
                    string_ty_for_exn,
                    int_ty_for_exn,
                    int_ty_for_exn,
                ])),
            ],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_assert_failure(),
            vec![
                ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![
                    string_ty_for_exn,
                    int_ty_for_exn,
                    int_ty_for_exn,
                ])),
            ],
            exn_ty,
        );
        add_exception(
            &mut env,
            Ident::create_persistent("Sys_error"),
            vec![string_ty_for_exn],
            exn_ty,
        );
        add_exception(&mut env, predef::ident_end_of_file(), vec![], exn_ty);
        add_exception(&mut env, predef::ident_division_by_zero(), vec![], exn_ty);
        add_exception(
            &mut env,
            Ident::create_persistent("Stack_overflow"),
            vec![],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_undefined_recursive_module(),
            vec![
                ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![
                    string_ty_for_exn,
                    int_ty_for_exn,
                    int_ty_for_exn,
                ])),
            ],
            exn_ty,
        );
        let unknown_ty_for_exn = ctx.new_generic_constr(predef::path_unknown(), vec![]);
        add_exception(
            &mut env,
            predef::ident_js_exn(),
            vec![unknown_ty_for_exn],
            exn_ty,
        );
    }

    // char = int (private manifest)
    add_type_with_constrs(
        &mut env,
        predef::ident_char(),
        TypeDeclaration {
            type_manifest: Some(ctx.new_generic_constr(predef::path_int(), vec![])),
            type_private: PrivateFlag::Private,
            ..decl_abstr(0, true)
        },
        ctx,
    );

    // OCaml's initial environment stops at predef types/exceptions
    // (compiler/ml/predef.ml:419-424). Pervasives values enter through
    // implicit opens (compiler/core/res_compmisc.ml:56-62,
    // compiler/ml/env.ml:1874-1877).
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_env() {
        let env = Env::empty();
        assert!(env.find_value("x").is_err());
        assert!(env.find_type("t").is_err());
    }

    #[test]
    fn test_add_and_find_value() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        };
        env.add_value(id.clone(), desc);

        assert!(env.find_value("x").is_ok());
        assert!(env.find_value("y").is_err());
    }

    #[test]
    fn test_add_and_find_type() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("t");
        let decl = TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: super::super::decl::TypeKind::TypeAbstract,
            type_private: super::super::asttypes::PrivateFlag::Public,
            type_manifest: None,
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: Location::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_unboxed: super::super::decl::UnboxedStatus::default(),
            type_inlined_types: vec![],
            type_path: None,
        };
        env.add_type(id.clone(), decl);

        assert!(env.find_type("t").is_ok());
        assert!(env.find_type("u").is_err());
    }

    #[test]
    fn test_shadowing() {
        let mut env = Env::empty();
        let id1 = Ident::create_local("x");
        let id2 = Ident::create_local("x");

        let desc1 = ValueDescription {
            val_type: TypeExprRef(1),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        };
        let desc2 = ValueDescription {
            val_type: TypeExprRef(2),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        };

        env.add_value(id1, desc1);
        env.add_value(id2, desc2);

        // Should find the most recent binding
        let found = env.find_value("x").unwrap();
        assert_eq!(found.val_type, TypeExprRef(2));
    }

    #[test]
    fn test_with_value() {
        let env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        };

        let env2 = env.with_value(id, desc);

        // Original env unchanged
        assert!(env.find_value("x").is_err());
        // New env has the binding
        assert!(env2.find_value("x").is_ok());
    }

    #[test]
    fn test_lookup_by_path() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: Location::none(),
            val_attributes: vec![],
            val_path: None,
        };
        env.add_value(id.clone(), desc);

        let path = Path::pident(id);
        assert!(env.lookup_value(&path).is_ok());
    }

    #[test]
    fn test_module_path_requires_env_scoped_cache_tracks_active_aliases() {
        use super::super::decl::{AliasPresence, ModuleDeclaration, ModuleType};

        let mut env = Env::empty();
        let target_id = Ident::create_local("Target");
        env.add_module(
            target_id.clone(),
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(vec![]),
                md_attributes: vec![],
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let alias_id = Ident::create_local("Alias");
        env.add_module(
            alias_id.clone(),
            ModuleDeclaration {
                md_type: ModuleType::MtyAlias(
                    AliasPresence::MtaPresent,
                    Path::pident(target_id.clone()),
                ),
                md_attributes: vec![],
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let target_child_path = Path::pdot(Path::pident(target_id.clone()), "Inner");
        assert!(env.module_path_requires_env_scoped_cache(&target_child_path));

        env.add_module(
            alias_id,
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(vec![]),
                md_attributes: vec![],
                md_loc: Location::none(),
                md_path: None,
            },
        );

        assert!(!env.module_path_requires_env_scoped_cache(&target_child_path));
    }
}
