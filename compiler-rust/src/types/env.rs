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
    LabelDescription, ModtypeDeclaration, ModuleDeclaration, ModuleType, PrimitiveDescription,
    SignatureItem, TypeDeclaration, TypeKind, ValueDescription, ValueKind,
};
use super::path::Path;
use super::type_expr::{TypeDesc, TypeExprRef};
use crate::ident::Ident;
use crate::location::Location;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Collect free type variables (Tvar nodes) from a type expression.
/// Matches OCaml's Datarepr.free_vars.
fn free_vars(ctx: &TypeContext<'_>, ty: TypeExprRef) -> HashSet<TypeExprRef> {
    let mut result = HashSet::new();
    let mut visited = HashSet::new();
    free_vars_rec(ctx, ty, &mut result, &mut visited);
    result
}

fn free_vars_rec(
    ctx: &TypeContext<'_>,
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
    ctx: &TypeContext<'_>,
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
            arg_vars
                .difference(&res_vars)
                .copied()
                .collect()
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

/// A table of bindings indexed by identifier.
/// Each entry tracks whether it was added locally (via `add`) or from an
/// opened module (via `add_opened`), matching OCaml's IdTbl which has separate
/// `current` (local) and `opened` structures.
#[derive(Debug, Clone)]
pub struct BindingTable<T> {
    /// Bindings indexed by name. The bool indicates whether the binding is
    /// local (true = from `add`, false = from `add_opened`).
    by_name: HashMap<String, Vec<(Ident, T, bool)>>,
    /// Bindings indexed by identifier stamp.
    by_stamp: HashMap<i32, T>,
}

impl<T: Clone> BindingTable<T> {
    /// Create a new empty binding table.
    pub fn new() -> Self {
        BindingTable {
            by_name: HashMap::new(),
            by_stamp: HashMap::new(),
        }
    }

    /// Add a binding (local). Goes at the end of the name vector,
    /// so it takes precedence over earlier bindings (including opened ones).
    pub fn add(&mut self, id: Ident, value: T) {
        let name = id.name().to_string();
        let stamp = id.stamp();

        self.by_stamp.insert(stamp, value.clone());

        self.by_name
            .entry(name)
            .or_default()
            .push((id, value, true));
    }

    /// Add a binding from an opened module. Goes at the end of the name
    /// vector, just like local bindings. Later opens shadow earlier ones.
    /// This matches OCaml's behavior where the most recent open takes precedence.
    pub fn add_opened(&mut self, id: Ident, value: T) {
        let name = id.name().to_string();
        let stamp = id.stamp();

        self.by_stamp.insert(stamp, value.clone());

        self.by_name
            .entry(name)
            .or_default()
            .push((id, value, false));
    }

    /// Find a binding by name.
    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        self.by_name
            .get(name)
            .and_then(|entries| entries.last())
            .map(|(_, v, _)| v)
    }

    /// Find a binding by name, returning both the identifier and value.
    pub fn find_by_name_with_id(&self, name: &str) -> Option<(&Ident, &T)> {
        self.by_name
            .get(name)
            .and_then(|entries| entries.last())
            .map(|(id, v, _)| (id, v))
    }

    /// Find a binding by name, returning the identifier, value, and whether
    /// it's a local binding. Matches OCaml's IdTbl.find_name which returns
    /// Pident for local bindings and Pdot for opened bindings.
    pub fn find_by_name_with_origin(&self, name: &str) -> Option<(&Ident, &T, bool)> {
        self.by_name
            .get(name)
            .and_then(|entries| entries.last())
            .map(|(id, v, is_local)| (id, v, *is_local))
    }

    /// Find a binding by identifier.
    /// Note: stamp=0 is shared by all persistent idents, so we skip
    /// by_stamp lookup for stamp=0 and fall through to by_name lookup.
    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        let stamp = id.stamp();
        if stamp == 0 {
            // All persistent idents share stamp=0, so by_stamp cannot
            // distinguish them. For persistent queries, prefer the most
            // recent persistent binding with that name; this mirrors OCaml's
            // `find_ident` behavior where persistent paths resolve through
            // persistent structures rather than opened/local shadowing.
            self.by_name.get(id.name()).and_then(|entries| {
                if id.is_persistent() {
                    return entries
                        .iter()
                        .rev()
                        .find(|(entry_id, _, _)| entry_id.is_persistent())
                        .map(|(_, value, _)| value);
                }
                entries.last().map(|(_, value, _)| value)
            })
        } else {
            self.by_stamp.get(&stamp)
        }
    }

    /// Get all bindings with a given name.
    pub fn find_all(&self, name: &str) -> Vec<&T> {
        self.by_name
            .get(name)
            .map(|entries| entries.iter().map(|(_, v, _)| v).collect())
            .unwrap_or_default()
    }

    /// Check if a binding exists.
    pub fn contains(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    /// Iterate over all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &T)> {
        self.by_name
            .values()
            .flat_map(|entries| entries.iter().map(|(id, v, _)| (id, v)))
    }
}

impl<T: Clone> Default for BindingTable<T> {
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
    values: BindingTable<Arc<ValueDescription>>,

    /// Type bindings.
    types: BindingTable<Arc<TypeDeclaration>>,

    /// Constructor bindings (for variant types).
    constrs: BindingTable<Arc<ConstructorDescription>>,

    /// Label bindings (for record fields).
    labels: BindingTable<Arc<LabelDescription>>,

    /// Module bindings.
    modules: BindingTable<Arc<ModuleDeclaration>>,

    /// Module type bindings.
    modtypes: BindingTable<Arc<ModtypeDeclaration>>,

    /// Summary of bindings.
    summary: Arc<EnvSummary>,

    /// Local constraints (for GADTs).
    local_constraints: HashMap<Path, Arc<TypeDeclaration>>,

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
            modtypes: self.modtypes.clone(),
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
            values: BindingTable::new(),
            types: BindingTable::new(),
            constrs: BindingTable::new(),
            labels: BindingTable::new(),
            modules: BindingTable::new(),
            modtypes: BindingTable::new(),
            summary: Arc::new(EnvSummary::Empty),
            local_constraints: HashMap::new(),
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
            modtypes: self.modtypes.clone(),
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

    // ========================================================================
    // Value Bindings
    // ========================================================================

    /// Add a value binding.
    pub fn add_value(&mut self, id: Ident, desc: ValueDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.values.add(id.clone(), desc.clone());
        self.summary = Arc::new(EnvSummary::Value(self.summary.clone(), id, desc));
    }

    /// Add a value binding from an opened module (lower priority than local bindings).
    pub fn add_opened_value(&mut self, id: Ident, desc: ValueDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.values.add_opened(id.clone(), desc.clone());
        self.summary = Arc::new(EnvSummary::Value(self.summary.clone(), id, desc));
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

    /// Iterate over visible value bindings.
    pub fn iter_values(&self) -> impl Iterator<Item = (&Ident, &ValueDescription)> {
        self.values.iter().map(|(id, v)| (id, v.as_ref()))
    }

    /// Update the visible value binding for `name` with a replacement type.
    /// This replaces the current binding in-place rather than adding a shadowing entry.
    pub fn update_value_type_by_name(&mut self, name: &str, new_type: TypeExprRef) -> bool {
        let Some(entries) = self.values.by_name.get_mut(name) else {
            return false;
        };
        let Some((id, desc, _is_local)) = entries.last_mut() else {
            return false;
        };

        let mut updated = (**desc).clone();
        updated.val_type = new_type;
        let updated = Arc::new(updated);
        *desc = updated.clone();

        // Persistent idents share stamp=0, and lookup for those already goes
        // through by_name. Keep by_stamp untouched for stamp=0.
        if id.stamp() != 0 {
            self.values.by_stamp.insert(id.stamp(), updated);
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
        self.types.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Type(self.summary.clone(), id, decl));
    }

    /// Add a type binding from an opened module (lower priority than local bindings).
    pub fn add_opened_type(&mut self, id: Ident, decl: TypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.types.add_opened(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Type(self.summary.clone(), id, decl));
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

    /// Find a type by name, also returning whether the binding is local.
    /// Local bindings (from `add_type`) return `is_local=true` and should
    /// use `Pident(id)` as their path. Opened bindings (from `add_opened_type`)
    /// return `is_local=false` and should use `decl.type_path`.
    /// This matches OCaml's IdTbl.find_name which returns Pident for
    /// current-table bindings and Pdot for opened-table bindings.
    pub fn find_type_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &TypeDeclaration, bool)> {
        self.types
            .find_by_name_with_origin(name)
            .map(|(id, decl, is_local)| (id, decl.as_ref(), is_local))
            .ok_or_else(|| EnvError::TypeNotFound(name.to_string()))
    }

    /// Find a type by path.
    pub fn lookup_type(&self, path: &Path) -> EnvResult<&TypeDeclaration> {
        match path {
            Path::Pident(id) => self
                .types
                .find_by_ident(id)
                .map(|t| t.as_ref())
                .ok_or_else(|| EnvError::TypeNotFound(id.name().to_string())),
            Path::Pdot(_, name, _) => self.find_type(name),
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

    /// Find all constructors with a given name.
    pub fn find_all_constructors(&self, name: &str) -> Vec<&ConstructorDescription> {
        self.constrs
            .find_all(name)
            .into_iter()
            .map(|c| c.as_ref())
            .collect()
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

    /// Find all labels with a given name.
    pub fn find_all_labels(&self, name: &str) -> Vec<&LabelDescription> {
        self.labels
            .find_all(name)
            .into_iter()
            .map(|l| l.as_ref())
            .collect()
    }

    // ========================================================================
    // Module Bindings
    // ========================================================================

    /// Add a module binding.
    pub fn add_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.modules.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Module(self.summary.clone(), id, decl));
    }

    /// Add a module binding from an opened module (lower priority than local bindings).
    pub fn add_opened_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.modules.add_opened(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Module(self.summary.clone(), id, decl));
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

    /// Find a module by name, returning the identifier, declaration, and
    /// whether the binding is local (from `add_module`) vs opened.
    pub fn find_module_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &ModuleDeclaration, bool)> {
        self.modules
            .find_by_name_with_origin(name)
            .map(|(id, decl, is_local)| (id, decl.as_ref(), is_local))
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Return current local module aliases in the environment.
    pub fn current_local_module_aliases(&self) -> Vec<(Ident, Path)> {
        let mut aliases = self
            .modules
            .by_name
            .values()
            .filter_map(|entries| entries.last())
            .filter_map(|(id, decl, is_local)| {
                if !*is_local {
                    return None;
                }
                match &decl.md_type {
                    ModuleType::MtyAlias(_, target) | ModuleType::MtyIdent(target) => {
                        Some((id.clone(), target.clone()))
                    }
                    _ => None,
                }
            })
            .collect::<Vec<_>>();

        aliases.sort_by(|(_, left_target), (_, right_target)| {
            right_target
                .name()
                .len()
                .cmp(&left_target.name().len())
                .then_with(|| left_target.name().cmp(&right_target.name()))
        });
        aliases
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
                Path::Pident(id) => env
                    .modules
                    .find_by_ident(id)
                    .map(|m| m.as_ref())
                    .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string())),
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
                    Path::Pdot(Box::new(normalized_prefix), name.clone(), *pos)
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
                    Path::Pdot(Box::new(p_norm), s.clone(), *pos)
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
        self.modtypes.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::ModType(self.summary.clone(), id, decl));
    }

    /// Add a module type binding from an opened module (lower priority than local bindings).
    pub fn add_opened_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.bump_id();
        let decl = Arc::new(decl);
        self.modtypes.add_opened(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::ModType(self.summary.clone(), id, decl));
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

    /// Find a module type by path.
    pub fn lookup_modtype(&self, path: &Path) -> EnvResult<&ModtypeDeclaration> {
        match path {
            Path::Pident(id) => self
                .modtypes
                .find_by_ident(id)
                .map(|m| m.as_ref())
                .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string())),
            Path::Pdot(_, name, _) => self.find_modtype(name),
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
pub fn initial_env(ctx: &TypeContext<'_>) -> Env {
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
    let cstr = |name: &str, args: Vec<TypeExprRef>| ConstructorDeclaration {
        cd_id: Ident::create_persistent(name),
        cd_args: ConstructorArguments::CstrTuple(args),
        cd_res: None,
        cd_loc: Location::none(),
        cd_attributes: vec![],
    };

    // Helper: add a type with its constructors to the environment
    // This matches OCaml's Env.store_type which calls Datarepr.constructors_of_type
    let add_type_with_constrs = |env: &mut Env,
                                 name: &str,
                                 decl: TypeDeclaration,
                                 ctx: &TypeContext<'_>| {
        let id = Ident::create_persistent(name);
        let type_path = Path::pident(id.clone());

        // Extract constructors/labels from predef declarations so they are
        // available for disambiguation just like OCaml's initial environment.
        match &decl.type_kind {
            TypeKind::TypeVariant(constrs) => {
                let num_consts = constrs.iter()
                    .filter(|c| matches!(c.cd_args, ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && c.cd_res.is_none())
                    .count() as i32;
                let num_nonconsts = constrs.len() as i32 - num_consts;
                let mut const_idx = 0i32;
                let mut nonconst_idx = 0i32;

                for cd in constrs {
                    let is_constant = matches!(cd.cd_args, ConstructorArguments::CstrTuple(ref args) if args.is_empty())
                        && cd.cd_res.is_none();

                    let cstr_tag = if is_constant {
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

    // ---- Abstract types ----
    add_type_with_constrs(&mut env, "int", decl_abstr(0, true), ctx);
    add_type_with_constrs(&mut env, "char", decl_abstr(0, true), ctx);
    add_type_with_constrs(&mut env, "float", decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, "bigint", decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, "string", decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, "extension_constructor", decl_abstr(0, false), ctx);
    add_type_with_constrs(
        &mut env,
        "array",
        TypeDeclaration {
            type_variance: vec![crate::types::variance::Variance::full()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        "promise",
        {
            let tvar = ctx.new_generic_var(None);
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            }
        },
        ctx,
    );

    // ---- Variant types (matching OCaml's Predef) ----

    // bool = false | true
    add_type_with_constrs(
        &mut env,
        "bool",
        TypeDeclaration {
            type_kind: TypeKind::TypeVariant(vec![cstr("false", vec![]), cstr("true", vec![])]),
            type_immediate: true,
            ..decl_abstr(0, true)
        },
        ctx,
    );

    // unit = ()
    add_type_with_constrs(
        &mut env,
        "unit",
        TypeDeclaration {
            type_kind: TypeKind::TypeVariant(vec![cstr("()", vec![])]),
            type_immediate: true,
            ..decl_abstr(0, true)
        },
        ctx,
    );

    // exn (type_open)
    add_type_with_constrs(
        &mut env,
        "exn",
        TypeDeclaration {
            type_kind: TypeKind::TypeOpen,
            ..decl_abstr(0, false)
        },
        ctx,
    );

    // Standard exception constructors (extension constructors of exn)
    {
        let exn_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("exn")), vec![]);
        let string_ty_for_exn =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("string")), vec![]);
        let int_ty_for_exn =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("int")), vec![]);

        let add_exception =
            |env: &mut Env, name: &str, args: Vec<TypeExprRef>, exn_ty: TypeExprRef| {
                let id = Ident::create_persistent(name);
                let path = Path::pident(id.clone());
                let cstr_desc = ConstructorDescription {
                    cstr_name: name.to_string(),
                    cstr_res: exn_ty,
                    cstr_existentials: vec![],
                    cstr_arity: args.len() as i32,
                    cstr_args: args,
                    cstr_tag: ConstructorTag::CstrExtension(path),
                    cstr_consts: 0,
                    cstr_nonconsts: 0,
                    cstr_generalized: false,
                    cstr_private: PrivateFlag::Public,
                    cstr_loc: Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: None,
                };
                env.add_constructor(id, cstr_desc);
            };

        add_exception(&mut env, "Not_found", vec![], exn_ty);
        add_exception(
            &mut env,
            "Invalid_argument",
            vec![string_ty_for_exn],
            exn_ty,
        );
        add_exception(&mut env, "Failure", vec![string_ty_for_exn], exn_ty);
        add_exception(&mut env, "Exit", vec![], exn_ty);
        add_exception(
            &mut env,
            "Match_failure",
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
            "Assert_failure",
            vec![
                ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![
                    string_ty_for_exn,
                    int_ty_for_exn,
                    int_ty_for_exn,
                ])),
            ],
            exn_ty,
        );
        add_exception(&mut env, "Sys_error", vec![string_ty_for_exn], exn_ty);
        add_exception(&mut env, "End_of_file", vec![], exn_ty);
        add_exception(&mut env, "Division_by_zero", vec![], exn_ty);
        add_exception(&mut env, "Stack_overflow", vec![], exn_ty);
        add_exception(
            &mut env,
            "Undefined_recursive_module",
            vec![
                ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![
                    string_ty_for_exn,
                    int_ty_for_exn,
                    int_ty_for_exn,
                ])),
            ],
            exn_ty,
        );
        // JsExn takes one argument of type `unknown`
        let unknown_ty_for_exn =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("unknown")), vec![]);
        add_exception(&mut env, "JsExn", vec![unknown_ty_for_exn], exn_ty);
    }

    // option('a) = None | Some('a)
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            "option",
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr("None", vec![]),
                    cstr("Some", vec![tvar]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }

    // ref('a) = { mutable contents: 'a }
    {
        let tvar = ctx.new_generic_var(None);
        let contents_label = crate::types::decl::LabelDeclaration {
            ld_id: Ident::create_persistent("contents"),
            ld_mutable: MutableFlag::Mutable,
            ld_optional: false,
            ld_type: tvar,
            ld_loc: Location::none(),
            ld_attributes: vec![],
        };
        add_type_with_constrs(
            &mut env,
            "ref",
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeRecord(
                    vec![contents_label],
                    crate::types::decl::RecordRepresentation::RecordRegular,
                ),
                type_variance: vec![crate::types::variance::Variance::invariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }

    // dict('a) = { dictValuesType?: option<'a> }
    // This mirrors OCaml Predef.decl_dict and powers dict pattern matching.
    {
        let tvar = ctx.new_generic_var(None);
        let option_t =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("option")), vec![tvar]);
        let dict_label = crate::types::decl::LabelDeclaration {
            ld_id: Ident::create_persistent("dictValuesType"),
            ld_mutable: MutableFlag::Immutable,
            ld_optional: true,
            ld_type: option_t,
            ld_loc: Location::none(),
            ld_attributes: vec![],
        };
        add_type_with_constrs(
            &mut env,
            "dict",
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

    // result('a, 'b) = Ok('a) | Error('b)
    {
        let tvar1 = ctx.new_generic_var(None);
        let tvar2 = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            "result",
            TypeDeclaration {
                type_params: vec![tvar1, tvar2],
                type_arity: 2,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr("Ok", vec![tvar1]),
                    cstr("Error", vec![tvar2]),
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

    // list('a) = [] | ::('a, list('a))
    {
        let tvar = ctx.new_generic_var(None);
        let list_ty =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("list")), vec![tvar]);
        add_type_with_constrs(
            &mut env,
            "list",
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: TypeKind::TypeVariant(vec![
                    cstr("[]", vec![]),
                    cstr("::", vec![tvar, list_ty]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }

    // unknown = Unknown('a) (GADT: Unknown returns unknown, not 'a)
    // Matches OCaml's Predef.decl_unknown
    {
        let tvar = ctx.new_generic_var(None);
        let type_unknown =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("unknown")), vec![]);
        add_type_with_constrs(
            &mut env,
            "unknown",
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: TypeKind::TypeVariant(vec![ConstructorDeclaration {
                    cd_id: Ident::create_persistent("Unknown"),
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

    // Create type references for primitives at generic level.
    // Using generic level ensures that instance() creates fresh copies
    // for each use site, matching OCaml's behavior where type schemes
    // from CMI files are at generic level.
    let int_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("int")), vec![]);
    let float_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("float")), vec![]);
    let bool_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("bool")), vec![]);
    let _string_ty =
        ctx.new_generic_constr(Path::pident(Ident::create_persistent("string")), vec![]);
    let unit_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("unit")), vec![]);

    // Add polymorphic arithmetic operators matching Pervasives.res:
    //   external "+": ('a, 'a) => 'a = "%add"
    // Each operator gets its own fresh 'a Tvar shared across all positions
    add_poly_binary_primitive(&mut env, ctx, "+", "%add");
    add_poly_binary_primitive(&mut env, ctx, "-", "%sub");
    add_poly_binary_primitive(&mut env, ctx, "*", "%mul");
    add_poly_binary_primitive(&mut env, ctx, "/", "%div");
    add_poly_binary_primitive(&mut env, ctx, "mod", "%mod");
    add_poly_binary_primitive(&mut env, ctx, "**", "%pow");
    add_poly_binary_primitive(&mut env, ctx, "%", "%mod");

    // Add monomorphic float operators matching Pervasives.res:
    //   external "+.": (float, float) => float = "%addfloat"
    // Each call creates fresh type nodes per position to match OCaml's CMI behavior
    // where each occurrence is a separate physical node.
    let float_path = Path::pident(Ident::create_persistent("float"));
    add_mono_binary_primitive(&mut env, ctx, "+.", "%addfloat", &float_path);
    add_mono_binary_primitive(&mut env, ctx, "-.", "%subfloat", &float_path);
    add_mono_binary_primitive(&mut env, ctx, "*.", "%mulfloat", &float_path);
    add_mono_binary_primitive(&mut env, ctx, "/.", "%divfloat", &float_path);

    // Add polymorphic comparison operators matching Pervasives.res:
    //   external "==": ('a, 'a) => bool = "%equal"
    add_poly_cmp_primitive(&mut env, ctx, "==", "%equal", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, "!=", "%notequal", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, "<", "%lessthan", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, ">", "%greaterthan", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, "<=", "%lessequal", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, ">=", "%greaterequal", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, "===", "%eq", bool_ty);
    add_poly_cmp_primitive(&mut env, ctx, "!==", "%noteq", bool_ty);

    // Add boolean operators (monomorphic)
    let bool_path = Path::pident(Ident::create_persistent("bool"));
    add_mono_binary_primitive(&mut env, ctx, "&&", "%sequand", &bool_path);
    add_mono_binary_primitive(&mut env, ctx, "||", "%sequor", &bool_path);
    add_mono_unary_primitive(&mut env, ctx, "not", "%boolnot", &bool_path);

    // Add polymorphic unary operators matching Pervasives.res:
    //   external "~-": 'a => 'a = "%neg"
    add_poly_unary_primitive(&mut env, ctx, "~-", "%neg");
    add_poly_unary_primitive(&mut env, ctx, "~+", "%plus");
    add_mono_unary_primitive(&mut env, ctx, "~-.", "%negfloat", &float_path);

    // Add string concatenation (monomorphic)
    let string_path = Path::pident(Ident::create_persistent("string"));
    add_mono_binary_primitive(&mut env, ctx, "++", "%string_concat", &string_path);

    // Add polymorphic bitwise operators matching Pervasives.res
    add_poly_binary_primitive(&mut env, ctx, "&&&", "%bitand");
    add_poly_binary_primitive(&mut env, ctx, "|||", "%bitor");
    add_poly_binary_primitive(&mut env, ctx, "^^^", "%bitxor");
    add_poly_binary_primitive(&mut env, ctx, "<<", "%lsl");
    add_poly_binary_primitive(&mut env, ctx, ">>", "%asr");
    add_poly_binary_primitive(&mut env, ctx, ">>>", "%lsr");
    add_poly_unary_primitive(&mut env, ctx, "~~~", "%bitnot");

    // Add polymorphic comparison/utility from Pervasives.res
    add_poly_cmp_primitive(&mut env, ctx, "compare", "%compare", int_ty);
    add_poly_binary_primitive(&mut env, ctx, "min", "%min");
    add_poly_binary_primitive(&mut env, ctx, "max", "%max");

    // Add ignore function (polymorphic)
    let alpha = ctx.new_generic_var(None);
    add_unary_primitive(&mut env, ctx, "ignore", "%ignore", alpha, unit_ty);

    // Add pair projections matching Pervasives.res
    //   external fst: (('a, 'b)) => 'a = "%field0"
    //   external snd: (('a, 'b)) => 'b = "%field1"
    {
        let alpha = ctx.new_generic_var(None);
        let beta = ctx.new_generic_var(None);
        let tuple_ty =
            ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![alpha, beta]));
        add_unary_primitive(&mut env, ctx, "fst", "%field0", tuple_ty, alpha);
    }
    {
        let alpha = ctx.new_generic_var(None);
        let beta = ctx.new_generic_var(None);
        let tuple_ty =
            ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(vec![alpha, beta]));
        add_unary_primitive(&mut env, ctx, "snd", "%field1", tuple_ty, beta);
    }

    // Add common numeric conversion helpers used from Pervasives.res
    add_unary_primitive(
        &mut env,
        ctx,
        "float_of_int",
        "%floatofint",
        int_ty,
        float_ty,
    );
    add_unary_primitive(
        &mut env,
        ctx,
        "int_of_float",
        "%intoffloat",
        float_ty,
        int_ty,
    );
    add_mono_unary_primitive(&mut env, ctx, "abs_float", "abs", &float_path);
    add_constant_value(&mut env, "min_int", int_ty);
    add_constant_value(&mut env, "max_int", int_ty);

    // Add ref primitives matching Pervasives.res
    //   external ref: 'a => ref<'a> = "%makeref"
    //   external "!" : ref<'a> => 'a = "%refget"
    //   external ":=": (ref<'a>, 'a) => unit = "%refset"
    {
        let alpha = ctx.new_generic_var(None);
        let ref_ty =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("ref")), vec![alpha]);
        add_unary_primitive(&mut env, ctx, "ref", "%makeref", alpha, ref_ty);
    }
    {
        let alpha = ctx.new_generic_var(None);
        let ref_ty =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("ref")), vec![alpha]);
        add_unary_primitive(&mut env, ctx, "!", "%refget", ref_ty, alpha);
    }
    {
        let alpha = ctx.new_generic_var(None);
        let ref_ty =
            ctx.new_generic_constr(Path::pident(Ident::create_persistent("ref")), vec![alpha]);
        add_binary_primitive(&mut env, ctx, ":=", "%refset", ref_ty, alpha, unit_ty);
    }

    env
}

/// Helper to add a binary primitive operator.
fn add_binary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
    arg1_ty: TypeExprRef,
    arg2_ty: TypeExprRef,
    ret_ty: TypeExprRef,
) {
    // Build at generic level so instance() creates fresh copies per use site
    let inner_ty = ctx.new_generic_arrow(crate::types::ArgLabel::Nolabel, arg2_ty, ret_ty, None);
    let func_ty =
        ctx.new_generic_arrow(crate::types::ArgLabel::Nolabel, arg1_ty, inner_ty, Some(2));
    let id = Ident::create_persistent(name);
    // Primitives come from Pervasives module
    let pervasives_id = Ident::create_persistent("Pervasives");
    let path = Path::pdot(Path::pident(pervasives_id), name.to_string());
    let desc = ValueDescription {
        val_type: func_ty,
        val_kind: ValueKind::ValPrim(PrimitiveDescription {
            prim_name: prim_name.to_string(),
            prim_arity: 2,
            prim_native_name: String::new(),
            prim_native_float: false,
        }),
        val_loc: Location::none(),
        val_attributes: vec![],
        val_path: Some(path),
    };
    env.add_value(id, desc);
}

/// Helper to add a unary primitive operator
fn add_unary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
    arg_ty: TypeExprRef,
    ret_ty: TypeExprRef,
) {
    // Build at generic level so instance() creates fresh copies per use site
    let func_ty = ctx.new_generic_arrow(crate::types::ArgLabel::Nolabel, arg_ty, ret_ty, Some(1));
    let id = Ident::create_persistent(name);
    // Primitives come from Pervasives module
    let pervasives_id = Ident::create_persistent("Pervasives");
    let path = Path::pdot(Path::pident(pervasives_id), name.to_string());
    let desc = ValueDescription {
        val_type: func_ty,
        val_kind: ValueKind::ValPrim(PrimitiveDescription {
            prim_name: prim_name.to_string(),
            prim_arity: 1,
            prim_native_name: String::new(),
            prim_native_float: false,
        }),
        val_loc: Location::none(),
        val_attributes: vec![],
        val_path: Some(path),
    };
    env.add_value(id, desc);
}

/// Helper to add a constant value from Pervasives with a known type.
fn add_constant_value(env: &mut Env, name: &str, ty: TypeExprRef) {
    let id = Ident::create_persistent(name);
    let pervasives_id = Ident::create_persistent("Pervasives");
    let path = Path::pdot(Path::pident(pervasives_id), name.to_string());
    let desc = ValueDescription {
        val_type: ty,
        val_kind: ValueKind::ValReg,
        val_loc: Location::none(),
        val_attributes: vec![],
        val_path: Some(path),
    };
    env.add_value(id, desc);
}

/// Helper to add a monomorphic binary operator where all positions use the same
/// nullary type constructor (e.g. float → float → float). Creates distinct type
/// nodes for each position to match OCaml's CMI behavior where each type
/// occurrence is a separate physical node.
fn add_mono_binary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
    ty_path: &Path,
) {
    let arg1 = ctx.new_generic_constr(ty_path.clone(), vec![]);
    let arg2 = ctx.new_generic_constr(ty_path.clone(), vec![]);
    let ret = ctx.new_generic_constr(ty_path.clone(), vec![]);
    add_binary_primitive(env, ctx, name, prim_name, arg1, arg2, ret);
}

/// Helper to add a monomorphic unary operator where both positions use the same
/// nullary type constructor. Creates distinct type nodes for each position.
fn add_mono_unary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
    ty_path: &Path,
) {
    let arg = ctx.new_generic_constr(ty_path.clone(), vec![]);
    let ret = ctx.new_generic_constr(ty_path.clone(), vec![]);
    add_unary_primitive(env, ctx, name, prim_name, arg, ret);
}

/// Helper to add a polymorphic binary operator: ('a, 'a) => 'a
/// Creates a single shared Tvar for all three positions, matching OCaml behavior
/// where Pervasives declares e.g. `external "+": ('a, 'a) => 'a = "%add"`
fn add_poly_binary_primitive(env: &mut Env, ctx: &TypeContext<'_>, name: &str, prim_name: &str) {
    // Create a SINGLE Tvar shared across all three positions
    let alpha = ctx.new_generic_var(None);
    add_binary_primitive(env, ctx, name, prim_name, alpha, alpha, alpha);
}

/// Helper to add a polymorphic comparison operator: ('a, 'a) => ret_ty
/// Creates a single shared Tvar for the two arg positions
fn add_poly_cmp_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
    ret_ty: TypeExprRef,
) {
    let alpha = ctx.new_generic_var(None);
    add_binary_primitive(env, ctx, name, prim_name, alpha, alpha, ret_ty);
}

/// Helper to add a polymorphic unary operator: 'a => 'a
fn add_poly_unary_primitive(env: &mut Env, ctx: &TypeContext<'_>, name: &str, prim_name: &str) {
    let alpha = ctx.new_generic_var(None);
    add_unary_primitive(env, ctx, name, prim_name, alpha, alpha);
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
}
