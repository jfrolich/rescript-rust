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

use super::context::TypeContext;
use super::asttypes::PrivateFlag;
use super::decl::{
    ConstructorArguments, ConstructorDeclaration, ConstructorDescription, ConstructorTag,
    LabelDescription, ModtypeDeclaration, ModuleDeclaration, PrimitiveDescription,
    TypeDeclaration, TypeKind, ValueDescription, ValueKind,
};
use super::path::Path;
use super::type_expr::TypeExprRef;
use crate::ident::Ident;
use crate::location::Location;
use std::collections::HashMap;
use std::sync::Arc;

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
#[derive(Debug, Clone)]
pub struct BindingTable<T> {
    /// Bindings indexed by name.
    by_name: HashMap<String, Vec<(Ident, T)>>,
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

    /// Add a binding.
    pub fn add(&mut self, id: Ident, value: T) {
        let name = id.name().to_string();
        let stamp = id.stamp();

        self.by_stamp.insert(stamp, value.clone());

        self.by_name.entry(name).or_default().push((id, value));
    }

    /// Find a binding by name.
    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        self.by_name
            .get(name)
            .and_then(|entries| entries.last())
            .map(|(_, v)| v)
    }

    /// Find a binding by name, returning both the identifier and value.
    pub fn find_by_name_with_id(&self, name: &str) -> Option<(&Ident, &T)> {
        self.by_name
            .get(name)
            .and_then(|entries| entries.last())
            .map(|(id, v)| (id, v))
    }

    /// Find a binding by identifier.
    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        self.by_stamp.get(&id.stamp())
    }

    /// Get all bindings with a given name.
    pub fn find_all(&self, name: &str) -> Vec<&T> {
        self.by_name
            .get(name)
            .map(|entries| entries.iter().map(|(_, v)| v).collect())
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
            .flat_map(|entries| entries.iter().map(|(id, v)| (id, v)))
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
#[derive(Debug, Clone)]
pub struct Env {
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

    /// Get the environment summary.
    pub fn summary(&self) -> &EnvSummary {
        &self.summary
    }

    // ========================================================================
    // Value Bindings
    // ========================================================================

    /// Add a value binding.
    pub fn add_value(&mut self, id: Ident, desc: ValueDescription) {
        let desc = Arc::new(desc);
        self.values.add(id.clone(), desc.clone());
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
        let decl = Arc::new(decl);
        self.types.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Type(self.summary.clone(), id, decl));
    }

    /// Find a type by name.
    pub fn find_type(&self, name: &str) -> EnvResult<&TypeDeclaration> {
        self.types
            .find_by_name(name)
            .map(|t| t.as_ref())
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
        let desc = Arc::new(desc);
        self.constrs.add(id, desc);
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
        let desc = Arc::new(desc);
        self.labels.add(id, desc);
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
        let decl = Arc::new(decl);
        self.modules.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::Module(self.summary.clone(), id, decl));
    }

    /// Find a module by name.
    pub fn find_module(&self, name: &str) -> EnvResult<&ModuleDeclaration> {
        self.modules
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
    }

    /// Find a module by path.
    pub fn lookup_module(&self, path: &Path) -> EnvResult<&ModuleDeclaration> {
        match path {
            Path::Pident(id) => self
                .modules
                .find_by_ident(id)
                .map(|m| m.as_ref())
                .ok_or_else(|| EnvError::ModuleNotFound(id.name().to_string())),
            Path::Pdot(_, name, _) => self.find_module(name),
            Path::Papply(_, _) => {
                // For functor application, would need to evaluate the application
                Err(EnvError::ModuleNotFound(
                    "(functor application)".to_string(),
                ))
            }
        }
    }

    // ========================================================================
    // Module Type Bindings
    // ========================================================================

    /// Add a module type binding.
    pub fn add_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        let decl = Arc::new(decl);
        self.modtypes.add(id.clone(), decl.clone());
        self.summary = Arc::new(EnvSummary::ModType(self.summary.clone(), id, decl));
    }

    /// Find a module type by name.
    pub fn find_modtype(&self, name: &str) -> EnvResult<&ModtypeDeclaration> {
        self.modtypes
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.to_string()))
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
        self.local_constraints.insert(path, Arc::new(decl));
    }

    /// Find a local constraint.
    pub fn find_local_constraint(&self, path: &Path) -> Option<&TypeDeclaration> {
        self.local_constraints.get(path).map(|d| d.as_ref())
    }

    /// Add a GADT instance level.
    pub fn add_gadt_instance_level(&mut self, level: i32, types: Vec<TypeExprRef>) {
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
    let add_type_with_constrs = |env: &mut Env, name: &str, decl: TypeDeclaration, ctx: &TypeContext<'_>| {
        let id = Ident::create_persistent(name);
        let type_path = Path::pident(id.clone());

        // Extract constructors from variant types
        if let TypeKind::TypeVariant(ref constrs) = decl.type_kind {
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

                let cstr_desc = ConstructorDescription {
                    cstr_name: cd.cd_id.name().to_string(),
                    cstr_res,
                    cstr_existentials: vec![],
                    cstr_args,
                    cstr_arity,
                    cstr_tag,
                    cstr_consts: num_consts,
                    cstr_nonconsts: num_nonconsts,
                    cstr_generalized: cd.cd_res.is_some(),
                    cstr_private: decl.type_private,
                    cstr_loc: Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: None,
                };

                env.add_constructor(cd.cd_id.clone(), cstr_desc);
            }
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
    add_type_with_constrs(&mut env, "array", decl_abstr(1, false), ctx);
    add_type_with_constrs(&mut env, "promise", {
        let tvar = ctx.new_generic_var(None);
        TypeDeclaration {
            type_params: vec![tvar],
            type_arity: 1,
            ..decl_abstr(1, false)
        }
    }, ctx);

    // ---- Variant types (matching OCaml's Predef) ----

    // bool = false | true
    add_type_with_constrs(&mut env, "bool", TypeDeclaration {
        type_kind: TypeKind::TypeVariant(vec![
            cstr("false", vec![]),
            cstr("true", vec![]),
        ]),
        type_immediate: true,
        ..decl_abstr(0, true)
    }, ctx);

    // unit = ()
    add_type_with_constrs(&mut env, "unit", TypeDeclaration {
        type_kind: TypeKind::TypeVariant(vec![
            cstr("()", vec![]),
        ]),
        type_immediate: true,
        ..decl_abstr(0, true)
    }, ctx);

    // exn (type_open)
    add_type_with_constrs(&mut env, "exn", TypeDeclaration {
        type_kind: TypeKind::TypeOpen,
        ..decl_abstr(0, false)
    }, ctx);

    // option('a) = None | Some('a)
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(&mut env, "option", TypeDeclaration {
            type_params: vec![tvar],
            type_arity: 1,
            type_kind: TypeKind::TypeVariant(vec![
                cstr("None", vec![]),
                cstr("Some", vec![tvar]),
            ]),
            ..decl_abstr(1, false)
        }, ctx);
    }

    // result('a, 'b) = Ok('a) | Error('b)
    {
        let tvar1 = ctx.new_generic_var(None);
        let tvar2 = ctx.new_generic_var(None);
        add_type_with_constrs(&mut env, "result", TypeDeclaration {
            type_params: vec![tvar1, tvar2],
            type_arity: 2,
            type_kind: TypeKind::TypeVariant(vec![
                cstr("Ok", vec![tvar1]),
                cstr("Error", vec![tvar2]),
            ]),
            ..decl_abstr(2, false)
        }, ctx);
    }

    // list('a) = [] | ::('a, list('a))
    {
        let tvar = ctx.new_generic_var(None);
        let list_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("list")), vec![tvar]);
        add_type_with_constrs(&mut env, "list", TypeDeclaration {
            type_params: vec![tvar],
            type_arity: 1,
            type_kind: TypeKind::TypeVariant(vec![
                cstr("[]", vec![]),
                cstr("::", vec![tvar, list_ty]),
            ]),
            ..decl_abstr(1, false)
        }, ctx);
    }

    // Create type references for primitives at generic level.
    // Using generic level ensures that instance() creates fresh copies
    // for each use site, matching OCaml's behavior where type schemes
    // from CMI files are at generic level.
    let int_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("int")), vec![]);
    let float_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("float")), vec![]);
    let bool_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("bool")), vec![]);
    let string_ty = ctx.new_generic_constr(Path::pident(Ident::create_persistent("string")), vec![]);
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
    add_binary_primitive(&mut env, ctx, "+.", "%addfloat", float_ty, float_ty, float_ty);
    add_binary_primitive(&mut env, ctx, "-.", "%subfloat", float_ty, float_ty, float_ty);
    add_binary_primitive(&mut env, ctx, "*.", "%mulfloat", float_ty, float_ty, float_ty);
    add_binary_primitive(&mut env, ctx, "/.", "%divfloat", float_ty, float_ty, float_ty);

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
    add_binary_primitive(&mut env, ctx, "&&", "%sequand", bool_ty, bool_ty, bool_ty);
    add_binary_primitive(&mut env, ctx, "||", "%sequor", bool_ty, bool_ty, bool_ty);
    add_unary_primitive(&mut env, ctx, "not", "%boolnot", bool_ty, bool_ty);

    // Add polymorphic unary operators matching Pervasives.res:
    //   external "~-": 'a => 'a = "%neg"
    add_poly_unary_primitive(&mut env, ctx, "~-", "%neg");
    add_poly_unary_primitive(&mut env, ctx, "~+", "%plus");
    add_unary_primitive(&mut env, ctx, "~-.", "%negfloat", float_ty, float_ty);

    // Add string concatenation (monomorphic)
    add_binary_primitive(&mut env, ctx, "++", "%string_concat", string_ty, string_ty, string_ty);

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

    env
}

/// Helper to add a binary primitive operator
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
    let func_ty = ctx.new_generic_arrow(crate::types::ArgLabel::Nolabel, arg1_ty, inner_ty, Some(2));
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

/// Helper to add a polymorphic binary operator: ('a, 'a) => 'a
/// Creates a single shared Tvar for all three positions, matching OCaml behavior
/// where Pervasives declares e.g. `external "+": ('a, 'a) => 'a = "%add"`
fn add_poly_binary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
) {
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
fn add_poly_unary_primitive(
    env: &mut Env,
    ctx: &TypeContext<'_>,
    name: &str,
    prim_name: &str,
) {
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
