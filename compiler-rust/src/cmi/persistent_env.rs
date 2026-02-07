//! Persistent environment for cached module loading.
//!
//! This module provides `PersistentEnv`, which caches loaded module interfaces
//! and provides lookup functions. It corresponds to OCaml's `persistent_structures`
//! hashtable in `env.ml`.
//!
//! # Load Path
//!
//! When a module is referenced (e.g., `Belt.Array`), the persistent environment
//! searches the load path for a corresponding `.cmi` file. The search is
//! case-insensitive on the first character (matching OCaml's `find_in_path_uncap`).

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::ident::Ident;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorDescription, ConstructorTag, LabelDescription, ModuleDeclaration, ModuleType,
    Signature, SignatureItem, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};

use super::cmi_format;
use super::sig_reader::SigReadContext;

/// A cached persistent module structure.
#[derive(Debug)]
pub struct PersStruct {
    /// Module name
    pub ps_name: String,
    /// Loaded signature
    pub ps_sig: Signature,
    /// Source filename
    pub ps_filename: String,
}

/// Persistent environment for module loading.
pub struct PersistentEnv {
    /// Cache of loaded modules: module_name -> PersStruct (or None if loading failed)
    cache: HashMap<String, Option<PersStruct>>,
    /// Load path: list of directories to search for .cmi files
    load_path: Vec<PathBuf>,
}

impl PersistentEnv {
    /// Create a new persistent environment with no load paths.
    pub fn new() -> Self {
        PersistentEnv {
            cache: HashMap::new(),
            load_path: Vec::new(),
        }
    }

    /// Set the load path (list of directories to search for .cmi files).
    pub fn set_load_path(&mut self, paths: Vec<PathBuf>) {
        self.load_path = paths;
    }

    /// Add a directory to the load path.
    pub fn add_load_path(&mut self, path: PathBuf) {
        if !self.load_path.contains(&path) {
            self.load_path.push(path);
        }
    }

    /// Find and load a module by name.
    /// Returns the cached signature, or None if the module cannot be found.
    pub fn find_pers_struct<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext<'a>,
    ) -> Option<&PersStruct> {
        // Check cache first
        if self.cache.contains_key(name) {
            return self.cache.get(name).and_then(|opt| opt.as_ref());
        }

        // Try to load from disk
        let result = self.load_module(name, ctx);
        self.cache.insert(name.to_string(), result);
        self.cache.get(name).and_then(|opt| opt.as_ref())
    }

    /// Load a module from a .cmi file.
    fn load_module<'a>(&self, name: &str, ctx: &'a TypeContext<'a>) -> Option<PersStruct> {
        // Search for the CMI file
        let cmi_filename = format!("{}.cmi", name);
        let full_path = self.find_in_path_uncap(&cmi_filename)?;

        // Read and parse the CMI file
        let cmi = match cmi_format::read_cmi(&full_path) {
            Ok(cmi) => cmi,
            Err(e) => {
                eprintln!("warning: failed to read CMI file {}: {}", full_path, e);
                return None;
            }
        };

        // Convert generic OCaml values to Rust type structures
        let mut sig_ctx = SigReadContext::new(ctx);
        let signature = sig_ctx.read_signature(&cmi.cmi_sign);

        // Register all type declarations in the global store for alias expansion
        let module_path = Path::Pident(Ident::create_persistent(name));
        register_sig_types_recursive(&signature, &module_path, ctx, &self.load_path);

        // Apply path substitution: rewrite Tconstr paths from internal
        // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
        // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
        substitute_type_paths_in_sig(&signature, &module_path, ctx);

        // Also recursively substitute paths in sub-module signatures
        substitute_submodule_paths(&signature, &module_path, ctx);

        Some(PersStruct {
            ps_name: cmi.cmi_name,
            ps_sig: signature,
            ps_filename: full_path,
        })
    }

    /// Search the load path for a file (case-insensitive on first char).
    /// Returns the full path if found.
    fn find_in_path_uncap(&self, filename: &str) -> Option<String> {
        for dir in &self.load_path {
            // Try exact case first
            let exact = dir.join(filename);
            if exact.exists() {
                return Some(exact.to_string_lossy().into_owned());
            }

            // Try uncapitalized
            if let Some(first_char) = filename.chars().next() {
                if first_char.is_ascii_uppercase() {
                    let uncap = format!(
                        "{}{}",
                        first_char.to_ascii_lowercase(),
                        &filename[1..]
                    );
                    let uncap_path = dir.join(&uncap);
                    if uncap_path.exists() {
                        return Some(uncap_path.to_string_lossy().into_owned());
                    }
                }
            }
        }
        None
    }

    /// Open a module's signature into the environment.
    /// This adds all the module's exported bindings to the environment.
    pub fn open_module<'a>(
        &mut self,
        name: &str,
        env: &mut Env,
        ctx: &'a TypeContext<'a>,
    ) -> bool {
        let ps = match self.find_pers_struct(name, ctx) {
            Some(ps) => ps,
            None => return false,
        };
        let module_path = Path::Pident(Ident::create_persistent(name));
        add_signature_to_env(&ps.ps_sig, &module_path, env, ctx, true);
        true
    }

    /// Get a module's declaration (for path resolution).
    pub fn get_module_declaration<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext<'a>,
    ) -> Option<ModuleDeclaration> {
        let ps = self.find_pers_struct(name, ctx)?;
        Some(ModuleDeclaration {
            md_type: ModuleType::MtySignature(ps.ps_sig.clone()),
            md_attributes: vec![],
            md_loc: crate::location::Location::none(),
        })
    }
}

/// Recursively register all type declarations from a signature
/// into the type context's global store for alias expansion.
///
/// `module_path` is the path to the module containing this signature
/// (e.g., `Pident(Js)` or `Pdot(Pident(Js), "Promise")`).
/// `load_path` is used to resolve module aliases by loading CMI files.
fn register_sig_types_recursive<'a>(
    sig: &Signature,
    module_path: &Path,
    ctx: &'a TypeContext<'a>,
    load_path: &[PathBuf],
) {
    for item in sig {
        match item {
            SignatureItem::SigType(id, decl, _) => {
                ctx.register_type_decl(id.name(), decl.clone());
                // Also register by stamp for precise lookup when name is ambiguous (e.g., "t")
                if id.stamp() != 0 {
                    ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
                }
                // Register by fully qualified path for Pdot lookup (e.g., "Js.Promise.t")
                let full_path = Path::pdot(module_path.clone(), id.name());
                ctx.register_type_decl_by_path(&full_path.name(), decl.clone());
            }
            SignatureItem::SigModule(id, md, _) => {
                let sub_path = Path::pdot(module_path.clone(), id.name());
                match &md.md_type {
                    ModuleType::MtySignature(sub_sig) => {
                        // Recurse into sub-module signatures with extended path
                        register_sig_types_recursive(sub_sig, &sub_path, ctx, load_path);
                    }
                    ModuleType::MtyAlias(_, alias_path) => {
                        // Module alias: resolve by loading the aliased module's CMI
                        let alias_module_name = match alias_path {
                            Path::Pident(alias_id) => Some(alias_id.name().to_string()),
                            // For Pdot paths like Js_promise.Make, use the root module
                            Path::Pdot(parent, _, _) => {
                                if let Path::Pident(alias_id) = parent.as_ref() {
                                    Some(alias_id.name().to_string())
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        };
                        if let Some(alias_name) = alias_module_name {
                            if let Some(alias_sig) = load_module_sig_for_alias(&alias_name, ctx, load_path) {
                                register_sig_types_recursive(&alias_sig, &sub_path, ctx, load_path);
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

/// Load a module's signature for resolving module aliases during type registration.
/// This is a lightweight version that doesn't use the persistent env cache.
fn load_module_sig_for_alias<'a>(
    name: &str,
    ctx: &'a TypeContext<'a>,
    load_path: &[PathBuf],
) -> Option<Signature> {
    let cmi_filename = format!("{}.cmi", name);

    // Search load path for the CMI file
    let full_path = find_in_path(load_path, &cmi_filename)?;

    // Read and parse the CMI file
    let cmi = cmi_format::read_cmi(&full_path).ok()?;

    // Convert to Rust type structures
    let mut sig_ctx = SigReadContext::new(ctx);
    let signature = sig_ctx.read_signature(&cmi.cmi_sign);

    Some(signature)
}

/// Search load paths for a file (case-insensitive on first character).
fn find_in_path(load_path: &[PathBuf], filename: &str) -> Option<String> {
    for dir in load_path {
        let exact = dir.join(filename);
        if exact.exists() {
            return Some(exact.to_string_lossy().into_owned());
        }
        if let Some(first_char) = filename.chars().next() {
            if first_char.is_ascii_uppercase() {
                let uncap = format!(
                    "{}{}",
                    first_char.to_ascii_lowercase(),
                    &filename[1..]
                );
                let uncap_path = dir.join(&uncap);
                if uncap_path.exists() {
                    return Some(uncap_path.to_string_lossy().into_owned());
                }
            }
        }
    }
    None
}

/// This is the core of `open_signature` from OCaml's `env.ml`.
/// For each signature item, we add the appropriate binding to the environment.
///
/// Uses "opened" add methods so that these bindings do NOT shadow existing
/// Recursively register all types from a module type (and sub-modules) by stamp.
/// This ensures that types referenced in function signatures can be expanded
/// during type unification, even when the type comes from a deeply nested module.
fn register_types_by_stamp_recursive(
    md_type: &ModuleType,
    ctx: &TypeContext<'_>,
) {
    if let ModuleType::MtySignature(sig) = md_type {
        for item in sig {
            match item {
                SignatureItem::SigType(id, decl, _) => {
                    if id.stamp() != 0 {
                        ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
                    }
                }
                SignatureItem::SigModule(_, md, _) => {
                    register_types_by_stamp_recursive(&md.md_type, ctx);
                }
                _ => {}
            }
        }
    }
}

/// Substitute type paths in type expressions.
///
/// This implements the equivalent of OCaml's `Subst.type_path` applied to type expressions.
/// When a module's signature is loaded, type identifiers internal to the module
/// (e.g., `Pident(ref)` inside Pervasives) need to be rewritten to qualified paths
/// (e.g., `Pdot(Pident "Pervasives") "ref"`).
///
/// The `stamp_map` maps type identifier stamps to their qualified paths.
/// The `name_map` maps type names (for persistent idents with stamp 0) to their qualified paths.
fn substitute_type_paths_in_sig(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    // Build substitution maps:
    // stamp -> qualified_path for stamped idents
    // name -> qualified_path for persistent idents (stamp 0)
    let mut stamp_map: HashMap<i32, Path> = HashMap::new();
    let mut name_map: HashMap<String, Path> = HashMap::new();

    for item in sig_items {
        if let SignatureItem::SigType(id, _decl, _) = item {
            let qualified_path = Path::pdot(module_path.clone(), id.name());
            if id.stamp() != 0 {
                stamp_map.insert(id.stamp(), qualified_path);
            } else {
                name_map.insert(id.name().to_string(), qualified_path);
            }
        }
    }

    if stamp_map.is_empty() && name_map.is_empty() {
        return;
    }

    // Now walk all type expressions referenced from the signature
    // and rewrite Tconstr paths that match our maps
    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(desc.val_type, &stamp_map, &name_map, ctx, &mut visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                // Substitute in type params
                for &param in &decl.type_params {
                    substitute_type_expr_path(param, &stamp_map, &name_map, ctx, &mut visited);
                }
                // Substitute in manifest
                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(manifest, &stamp_map, &name_map, ctx, &mut visited);
                }
                // Substitute in constructor/label types
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        substitute_type_expr_path(arg, &stamp_map, &name_map, ctx, &mut visited);
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        substitute_type_expr_path(lbl.ld_type, &stamp_map, &name_map, ctx, &mut visited);
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                substitute_type_expr_path(res, &stamp_map, &name_map, ctx, &mut visited);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, &stamp_map, &name_map, ctx, &mut visited);
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    substitute_type_expr_path(param, &stamp_map, &name_map, ctx, &mut visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            substitute_type_expr_path(arg, &stamp_map, &name_map, ctx, &mut visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, &stamp_map, &name_map, ctx, &mut visited);
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    substitute_type_expr_path(ret, &stamp_map, &name_map, ctx, &mut visited);
                }
            }
            _ => {}
        }
    }
}

/// Recursively walk a type expression and substitute Tconstr paths.
fn substitute_type_expr_path(
    ty_ref: TypeExprRef,
    stamp_map: &HashMap<i32, Path>,
    name_map: &HashMap<String, Path>,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.0) {
        return; // Already visited (cycle detection)
    }

    let ty = ctx.get_type(ty_ref);
    let desc = ty.desc().clone();

    match &desc {
        TypeDesc::Tconstr { path, args, .. } => {
            // Check if this path needs substitution
            if let Path::Pident(ident) = path {
                let new_path = if ident.stamp() != 0 {
                    stamp_map.get(&ident.stamp()).cloned()
                } else {
                    name_map.get(ident.name()).cloned()
                };

                if let Some(qualified_path) = new_path {
                    let mut desc_mut = ty.desc_mut();
                    if let TypeDesc::Tconstr { ref mut path, .. } = *desc_mut {
                        *path = qualified_path;
                    }
                }
            }

            // Recurse into type arguments
            for &arg in args {
                substitute_type_expr_path(arg, stamp_map, name_map, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            substitute_type_expr_path(arg.typ, stamp_map, name_map, ctx, visited);
            substitute_type_expr_path(*ret, stamp_map, name_map, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                substitute_type_expr_path(t, stamp_map, name_map, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) => {
            substitute_type_expr_path(*t, stamp_map, name_map, ctx, visited);
        }
        TypeDesc::Tsubst(t) => {
            substitute_type_expr_path(*t, stamp_map, name_map, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            substitute_type_expr_path(*body, stamp_map, name_map, ctx, visited);
            for &v in vars {
                substitute_type_expr_path(v, stamp_map, name_map, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            substitute_type_expr_path(*fields, stamp_map, name_map, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            substitute_type_expr_path(*typ, stamp_map, name_map, ctx, visited);
            substitute_type_expr_path(*rest, stamp_map, name_map, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            substitute_type_expr_path(row.row_more, stamp_map, name_map, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        substitute_type_expr_path(*t, stamp_map, name_map, ctx, visited);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            substitute_type_expr_path(t, stamp_map, name_map, ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for &arg in args {
                substitute_type_expr_path(arg, stamp_map, name_map, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// Rewrite type expression paths that reference an old module name to use a new path prefix.
/// For example, when accessing `Belt.Array` which is an alias for `Belt_Array`,
/// types with `Pident("Belt_Array")` or `Pdot(Pident("Belt_Array"), X)` need to be
/// rewritten to use `Pdot(Pident("Belt"), "Array")` as the prefix.
fn rewrite_type_expr_prefix(
    ty_ref: TypeExprRef,
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.0) {
        return; // Already visited (cycle detection)
    }

    let ty = ctx.get_type(ty_ref);
    let desc = ty.desc().clone();

    match &desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let rewritten = rewrite_path_prefix(path, old_name, new_prefix);
            if let Some(new_path) = rewritten {
                let mut desc_mut = ty.desc_mut();
                if let TypeDesc::Tconstr { ref mut path, .. } = *desc_mut {
                    *path = new_path;
                }
            }
            for &arg in args {
                rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_type_expr_prefix(arg.typ, old_name, new_prefix, ctx, visited);
            rewrite_type_expr_prefix(*ret, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                rewrite_type_expr_prefix(t, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) => {
            rewrite_type_expr_prefix(*t, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tsubst(t) => {
            rewrite_type_expr_prefix(*t, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_expr_prefix(*body, old_name, new_prefix, ctx, visited);
            for &v in vars {
                rewrite_type_expr_prefix(v, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_type_expr_prefix(*fields, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_type_expr_prefix(*typ, old_name, new_prefix, ctx, visited);
            rewrite_type_expr_prefix(*rest, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_type_expr_prefix(row.row_more, old_name, new_prefix, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_type_expr_prefix(*t, old_name, new_prefix, ctx, visited);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            rewrite_type_expr_prefix(t, old_name, new_prefix, ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { args, .. } => {
            for &arg in args {
                rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// Rewrite a path's module prefix from an old name to a new path.
/// Returns Some(new_path) if rewritten, None if unchanged.
fn rewrite_path_prefix(path: &Path, old_name: &str, new_prefix: &Path) -> Option<Path> {
    match path {
        // Pident("Belt_Array") → new_prefix (e.g., Pdot(Pident("Belt"), "Array"))
        Path::Pident(id) if id.name() == old_name => {
            Some(new_prefix.clone())
        }
        // Pdot(Pident("Belt_Array"), "t", pos) → Pdot(new_prefix, "t", pos)
        Path::Pdot(inner, name, pos) => {
            if let Path::Pident(id) = inner.as_ref() {
                if id.name() == old_name {
                    return Some(Path::Pdot(Box::new(new_prefix.clone()), name.clone(), *pos));
                }
            }
            // Recursively check deeper paths
            let rewritten_inner = rewrite_path_prefix(inner, old_name, new_prefix);
            rewritten_inner.map(|new_inner| Path::Pdot(Box::new(new_inner), name.clone(), *pos))
        }
        _ => None,
    }
}

/// Rewrite all type paths in a signature from one module prefix to another.
/// Used when resolving module aliases: e.g., Belt.Array is aliased to Belt_Array,
/// so types from Belt_Array.cmi need their paths rewritten from
/// Pdot(Pident("Belt_Array"), X) to Pdot(Pdot(Pident("Belt"), "Array"), X).
pub fn rewrite_module_prefix_in_sig(
    sig_items: &[SignatureItem],
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
) {
    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                rewrite_type_expr_prefix(desc.val_type, old_name, new_prefix, ctx, &mut visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_prefix(param, old_name, new_prefix, ctx, &mut visited);
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_prefix(manifest, old_name, new_prefix, ctx, &mut visited);
                }
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, &mut visited);
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_type_expr_prefix(lbl.ld_type, old_name, new_prefix, ctx, &mut visited);
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_prefix(res, old_name, new_prefix, ctx, &mut visited);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_type_expr_prefix(lbl.ld_type, old_name, new_prefix, ctx, &mut visited);
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    rewrite_type_expr_prefix(param, old_name, new_prefix, ctx, &mut visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, &mut visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            rewrite_type_expr_prefix(lbl.ld_type, old_name, new_prefix, ctx, &mut visited);
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    rewrite_type_expr_prefix(ret, old_name, new_prefix, ctx, &mut visited);
                }
            }
            _ => {}
        }
    }
}

/// Recursively substitute type paths in sub-module signatures.
/// For a module like Belt with sub-modules Array, Map, etc.,
/// the types in Belt.Array should have paths like Pdot(Pdot(Pident "Belt") "Array") "t"
/// instead of Pident "t".
fn substitute_submodule_paths(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            let sub_path = Path::pdot(module_path.clone(), id.name());
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                substitute_type_paths_in_sig(sub_sig, &sub_path, ctx);
                substitute_submodule_paths(sub_sig, &sub_path, ctx);
            }
        }
    }
}

/// local bindings. This matches OCaml's behavior where opened modules have
/// lower lookup priority than local bindings (e.g., Predef types like `int`
/// are not shadowed when Pervasives.cmi is opened).
///
/// When `as_opened` is true, items are added with lower priority (opened).
/// When `as_opened` is false, items are added with normal priority (for `include`).
pub fn add_signature_to_env(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext<'_>,
    as_opened: bool,
) {
    // Apply path substitution: rewrite Tconstr paths from internal
    // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
    // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
    substitute_type_paths_in_sig(sig_items, module_path, ctx);

    for item in sig_items {
        match item {
            SignatureItem::SigValue(id, desc) => {
                // Add value binding with qualified path
                let mut desc = desc.clone();
                desc.val_path = Some(Path::pdot(module_path.clone(), id.name()));
                if as_opened {
                    env.add_opened_value(id.clone(), desc);
                } else {
                    env.add_value(id.clone(), desc);
                }
            }
            SignatureItem::SigType(id, decl, _rec_status) => {
                // Add type binding with qualified path
                let mut decl = decl.clone();
                decl.type_path = Some(Path::pdot(module_path.clone(), id.name()));
                if as_opened {
                    env.add_opened_type(id.clone(), decl.clone());
                } else {
                    env.add_type(id.clone(), decl.clone());
                }

                // Also register in global type store for alias expansion
                ctx.register_type_decl(id.name(), decl.clone());
                // Register by stamp for types from CMI modules (non-zero stamp)
                if id.stamp() != 0 {
                    ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
                }

                // Also add constructors and labels from this type
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        let type_path = Path::pdot(module_path.clone(), id.name());
                        let num_consts = constrs
                            .iter()
                            .filter(|c| matches!(c.cd_args, crate::types::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty()) && c.cd_res.is_none())
                            .count() as i32;
                        let num_nonconsts = constrs.len() as i32 - num_consts;
                        let mut const_idx = 0i32;
                        let mut nonconst_idx = 0i32;

                        for cd in constrs {
                            let is_constant = matches!(cd.cd_args, crate::types::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty())
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

                            // Get argument types from constructor arguments
                            let (cstr_args, cstr_arity) = match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    (args.clone(), args.len() as i32)
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    let args: Vec<TypeExprRef> =
                                        labels.iter().map(|l| l.ld_type).collect();
                                    let arity = args.len() as i32;
                                    (args, arity)
                                }
                            };

                            // Create result type (the variant type itself)
                            let cstr_res = if let Some(res_ty) = cd.cd_res {
                                res_ty
                            } else {
                                // Default: the type constructor with its params
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
                                cstr_loc: crate::location::Location::none(),
                                cstr_attributes: vec![],
                                cstr_inlined: None,
                            };

                            if as_opened {
                                env.add_opened_constructor(cd.cd_id.clone(), cstr_desc);
                            } else {
                                env.add_constructor(cd.cd_id.clone(), cstr_desc);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, repr) => {
                        let type_path = Path::pdot(module_path.clone(), id.name());
                        let res_ty = ctx.new_generic_constr(type_path, decl.type_params.clone());

                        for (pos, ld) in labels.iter().enumerate() {
                            let label_desc = LabelDescription {
                                lbl_name: ld.ld_id.name().to_string(),
                                lbl_res: res_ty,
                                lbl_arg: ld.ld_type,
                                lbl_mut: ld.ld_mutable,
                                lbl_optional: ld.ld_optional,
                                lbl_pos: pos as i32,
                                lbl_all: crate::types::decl::LabelArrayRef(0), // placeholder
                                lbl_repres: repr.clone(),
                                lbl_private: decl.type_private,
                                lbl_loc: crate::location::Location::none(),
                                lbl_attributes: vec![],
                            };
                            if as_opened {
                                env.add_opened_label(ld.ld_id.clone(), label_desc);
                            } else {
                                env.add_label(ld.ld_id.clone(), label_desc);
                            }
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigModule(id, md, _rec_status) => {
                if as_opened {
                    env.add_opened_module(id.clone(), md.clone());
                } else {
                    env.add_module(id.clone(), md.clone());
                }
                // Recursively register types from sub-module signatures by stamp,
                // so that types referenced in function return types can be expanded
                register_types_by_stamp_recursive(&md.md_type, ctx);
            }
            SignatureItem::SigModtype(id, mtd) => {
                if as_opened {
                    env.add_opened_modtype(id.clone(), mtd.clone());
                } else {
                    env.add_modtype(id.clone(), mtd.clone());
                }
            }
            SignatureItem::SigTypext(id, ext, _status) => {
                // Add extension constructor
                let cstr_desc = ConstructorDescription {
                    cstr_name: id.name().to_string(),
                    cstr_res: ctx.new_generic_constr(ext.ext_type_path.clone(), ext.ext_type_params.clone()),
                    cstr_existentials: vec![],
                    cstr_args: match &ext.ext_args {
                        crate::types::decl::ConstructorArguments::CstrTuple(args) => args.clone(),
                        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                            labels.iter().map(|l| l.ld_type).collect()
                        }
                    },
                    cstr_arity: match &ext.ext_args {
                        crate::types::decl::ConstructorArguments::CstrTuple(args) => args.len() as i32,
                        crate::types::decl::ConstructorArguments::CstrRecord(labels) => labels.len() as i32,
                    },
                    cstr_tag: ConstructorTag::CstrExtension(
                        Path::pdot(module_path.clone(), id.name()),
                    ),
                    cstr_consts: 0,
                    cstr_nonconsts: 0,
                    cstr_generalized: ext.ext_ret_type.is_some(),
                    cstr_private: ext.ext_private,
                    cstr_loc: crate::location::Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: None,
                };
                if as_opened {
                    env.add_opened_constructor(id.clone(), cstr_desc);
                } else {
                    env.add_constructor(id.clone(), cstr_desc);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {
                // Skip class/class_type (not used in ReScript)
            }
        }
    }
}
