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
    /// Alias prefix rewrites: flattened_name -> qualified_path.
    /// Populated when loading a CMI that has MtyAlias submodules
    /// (e.g., Stdlib.cmi has module JSON = Stdlib_JSON, so we record
    /// "Stdlib_JSON" → Pdot(Pident("Stdlib"), "JSON")).
    alias_prefix_rewrites: HashMap<String, Path>,
}

impl PersistentEnv {
    /// Create a new persistent environment with no load paths.
    pub fn new() -> Self {
        PersistentEnv {
            cache: HashMap::new(),
            load_path: Vec::new(),
            alias_prefix_rewrites: HashMap::new(),
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

    /// Check if a directory is already in the load path.
    pub fn load_path_contains(&self, path: &PathBuf) -> bool {
        self.load_path.contains(path)
    }

    /// Return flattened module heads that are known aliases for `qualified_path`.
    /// Example: if cache has `"Stdlib_JSON" -> Stdlib.JSON`, returns `["Stdlib_JSON"]`
    /// when queried with `Stdlib.JSON`.
    pub fn flattened_alias_heads_for_path(&self, qualified_path: &Path) -> Vec<String> {
        self.alias_prefix_rewrites
            .iter()
            .filter_map(|(flat_head, qualified)| {
                if qualified.same(qualified_path) {
                    Some(flat_head.clone())
                } else {
                    None
                }
            })
            .collect()
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
    fn load_module<'a>(&mut self, name: &str, ctx: &'a TypeContext<'a>) -> Option<PersStruct> {
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

        let module_path = Path::Pident(Ident::create_persistent(name));

        // Apply path substitution: rewrite Tconstr paths from internal
        // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
        // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
        substitute_type_paths_in_sig(&signature, &module_path, ctx);

        // Also recursively substitute paths in sub-module signatures
        substitute_submodule_paths(&signature, &module_path, ctx);

        // If this module has a registered alias rewrite (e.g., "Stdlib_JSON" was
        // registered when loading Stdlib.cmi), apply depth-restricted prefix
        // rewriting: only rewrite Tconstr paths where the flattened name appears
        // at depth >= 2 (i.e., as a nested module prefix, not the direct parent).
        // This matches OCaml's behavior where:
        // - Pdot(Pident("Stdlib_JSON"), "t") stays as-is (direct type access)
        // - Pdot(Pdot(Pident("Stdlib_JSON"), "Classify"), "t") gets rewritten
        //   to Pdot(Pdot(Pdot(Pident("Stdlib"), "JSON"), "Classify"), "t")
        if let Some(qualified_path) = self.alias_prefix_rewrites.get(name).cloned() {
            rewrite_deep_prefix_in_sig(&signature, name, &qualified_path, ctx);
        }

        // Collect alias submodule mappings: when a module has submodules declared
        // as MtyAlias (e.g., Stdlib has module JSON = Stdlib_JSON), record the
        // mapping so that when Stdlib_JSON.cmi is later loaded, its type paths
        // get rewritten from Pident("Stdlib_JSON") to Pdot(Pident("Stdlib"), "JSON").
        // Use the qualified path (if available) so nested aliases produce fully
        // qualified paths. E.g., Stdlib_Intl's "NumberFormat" alias becomes
        // Pdot(Pdot(Pident("Stdlib"), "Intl"), "NumberFormat") not
        // Pdot(Pident("Stdlib_Intl"), "NumberFormat").
        let effective_module_path = self.alias_prefix_rewrites.get(name).cloned()
            .unwrap_or_else(|| module_path.clone());
        collect_alias_rewrites(&signature, &effective_module_path, &mut self.alias_prefix_rewrites);

        // Register type declarations after all signature rewrites so cached
        // declarations (especially record/variant field types) use the same
        // qualified paths seen during lookup from this signature.
        register_sig_types_recursive(&signature, &effective_module_path, ctx, &self.load_path);

        Some(PersStruct {
            ps_name: cmi.cmi_name,
            ps_sig: signature,
            ps_filename: full_path,
        })
    }

    /// Read a module's signature from CMI without applying path substitution.
    /// Used for interface constraint propagation (moregen) where we need raw
    /// Pident paths that match the implementation's local paths.
    /// In OCaml, ps_sig retains raw Pident paths; path substitution happens
    /// lazily in components_of_module_maker, not on ps_sig.
    pub fn read_raw_sig<'a>(&self, name: &str, ctx: &'a TypeContext<'a>) -> Option<Signature> {
        let cmi_filename = format!("{}.cmi", name);
        let full_path = self.find_in_path_uncap(&cmi_filename)?;
        let cmi = cmi_format::read_cmi(&full_path).ok()?;
        let mut sig_ctx = SigReadContext::new(ctx);
        Some(sig_ctx.read_signature(&cmi.cmi_sign))
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
                    let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &filename[1..]);
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
    pub fn open_module<'a>(&mut self, name: &str, env: &mut Env, ctx: &'a TypeContext<'a>) -> bool {
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
            md_path: None,
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
                            if let Some(alias_sig) =
                                load_module_sig_for_alias(&alias_name, ctx, load_path)
                            {
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
                let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &filename[1..]);
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
fn register_types_by_stamp_recursive(md_type: &ModuleType, ctx: &TypeContext<'_>) {
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
#[derive(Default, Clone)]
struct SubstMaps {
    type_stamp_map: HashMap<i32, Path>,
    type_name_map: HashMap<String, Path>,
    module_stamp_map: HashMap<i32, Path>,
    module_name_map: HashMap<String, Path>,
}

impl SubstMaps {
    fn is_empty(&self) -> bool {
        self.type_stamp_map.is_empty()
            && self.type_name_map.is_empty()
            && self.module_stamp_map.is_empty()
            && self.module_name_map.is_empty()
    }
}

fn build_subst_maps(sig_items: &[SignatureItem], module_path: &Path) -> SubstMaps {
    let mut maps = SubstMaps::default();

    for item in sig_items {
        match item {
            SignatureItem::SigType(id, _, _) | SignatureItem::SigModtype(id, _) => {
                let qualified_path = Path::pdot(module_path.clone(), id.name());
                if id.stamp() != 0 {
                    // OCaml Subst uses identifier identity for non-persistent ids.
                    maps.type_stamp_map.insert(id.stamp(), qualified_path);
                } else {
                    // Persistent ids (stamp=0) rewrite by name.
                    maps.type_name_map.insert(id.name().to_string(), qualified_path);
                }
            }
            SignatureItem::SigModule(id, _, _) => {
                let qualified_path = Path::pdot(module_path.clone(), id.name());
                if id.stamp() != 0 {
                    // OCaml Subst uses identifier identity for non-persistent ids.
                    maps.module_stamp_map.insert(id.stamp(), qualified_path);
                } else {
                    // Persistent ids (stamp=0) rewrite by name.
                    maps.module_name_map
                        .insert(id.name().to_string(), qualified_path);
                }
            }
            _ => {}
        }
    }

    maps
}

fn build_subst_maps_for_module(sig_items: &[SignatureItem], module_path: &Path) -> SubstMaps {
    let mut maps = build_subst_maps(sig_items, module_path);

    // Nested persistent modules are often materialized in CMIs with flattened
    // names (for example `Stdlib.JSON` appears as `Stdlib_JSON`). Add an
    // explicit mapping from that flattened head name back to the qualified
    // module access path so substitution can normalize those references.
    if let Ok((head, components)) = module_path.flatten() {
        if !components.is_empty() {
            let mut flat_name = head.name().to_string();
            for component in components {
                flat_name.push('_');
                flat_name.push_str(component);
            }
            maps.module_name_map
                .entry(flat_name)
                .or_insert_with(|| module_path.clone());
        }
    }

    maps
}

pub fn substitute_sig_path(path: &Path, sig_items: &[SignatureItem], module_path: &Path) -> Path {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    substitute_type_path(
        path,
        &maps.type_stamp_map,
        &maps.type_name_map,
        &maps.module_stamp_map,
        &maps.module_name_map,
    )
}

fn substitute_type_paths_in_sig_with_maps(
    sig_items: &[SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext<'_>,
) {
    if maps.is_empty() {
        return;
    }

    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(
                    desc.val_type,
                    &maps.type_stamp_map,
                    &maps.type_name_map,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    substitute_type_expr_path(
                        param,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        ctx,
                        &mut visited,
                    );
                }

                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(
                        manifest,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        ctx,
                        &mut visited,
                    );
                }

                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        substitute_type_expr_path(
                                            arg,
                                            &maps.type_stamp_map,
                                            &maps.type_name_map,
                                            &maps.module_stamp_map,
                                            &maps.module_name_map,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        substitute_type_expr_path(
                                            lbl.ld_type,
                                            &maps.type_stamp_map,
                                            &maps.type_name_map,
                                            &maps.module_stamp_map,
                                            &maps.module_name_map,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                substitute_type_expr_path(
                                    res,
                                    &maps.type_stamp_map,
                                    &maps.type_name_map,
                                    &maps.module_stamp_map,
                                    &maps.module_name_map,
                                    ctx,
                                    &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            substitute_type_expr_path(
                                lbl.ld_type,
                                &maps.type_stamp_map,
                                &maps.type_name_map,
                                &maps.module_stamp_map,
                                &maps.module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    substitute_type_expr_path(
                        param,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            substitute_type_expr_path(
                                arg,
                                &maps.type_stamp_map,
                                &maps.type_name_map,
                                &maps.module_stamp_map,
                                &maps.module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            substitute_type_expr_path(
                                lbl.ld_type,
                                &maps.type_stamp_map,
                                &maps.type_name_map,
                                &maps.module_stamp_map,
                                &maps.module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    substitute_type_expr_path(
                        ret,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
            }
            _ => {}
        }
    }
}

pub fn substitute_type_paths_in_sig(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    let type_stamp_map = &maps.type_stamp_map;
    let type_name_map = &maps.type_name_map;
    let module_stamp_map = &maps.module_stamp_map;
    let module_name_map = &maps.module_name_map;

    if type_stamp_map.is_empty()
        && type_name_map.is_empty()
        && module_stamp_map.is_empty()
        && module_name_map.is_empty()
    {
        return;
    }

    // Now walk all type expressions referenced from the signature
    // and rewrite Tconstr paths that match our maps
    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(
                    desc.val_type,
                    &type_stamp_map,
                    &type_name_map,
                    &module_stamp_map,
                    &module_name_map,
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                // Substitute in type params
                for &param in &decl.type_params {
                    substitute_type_expr_path(
                        param,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
                // Substitute in manifest
                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(
                        manifest,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
                // Substitute in constructor/label types
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        substitute_type_expr_path(
                                            arg,
                                            &type_stamp_map,
                                            &type_name_map,
                                            &module_stamp_map,
                                            &module_name_map,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        substitute_type_expr_path(
                                            lbl.ld_type,
                                            &type_stamp_map,
                                            &type_name_map,
                                            &module_stamp_map,
                                            &module_name_map,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                substitute_type_expr_path(
                                    res,
                                    &type_stamp_map,
                                    &type_name_map,
                                    &module_stamp_map,
                                    &module_name_map,
                                    ctx,
                                    &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            substitute_type_expr_path(
                                lbl.ld_type,
                                &type_stamp_map,
                                &type_name_map,
                                &module_stamp_map,
                                &module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    substitute_type_expr_path(
                        param,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            substitute_type_expr_path(
                                arg,
                                &type_stamp_map,
                                &type_name_map,
                                &module_stamp_map,
                                &module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            substitute_type_expr_path(
                                lbl.ld_type,
                                &type_stamp_map,
                                &type_name_map,
                                &module_stamp_map,
                                &module_name_map,
                                ctx,
                                &mut visited,
                            );
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    substitute_type_expr_path(
                        ret,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        ctx,
                        &mut visited,
                    );
                }
            }
            _ => {}
        }
    }
}

/// Recursively walk a type expression and substitute Tconstr paths.
fn substitute_type_expr_path(
    ty_ref: TypeExprRef,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &HashMap<i32, Path>,
    module_name_map: &HashMap<String, Path>,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.0) {
        return; // Already visited (cycle detection)
    }

    let desc = ctx.get_desc(ty_ref);

    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let new_path = substitute_type_path(
                path,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
            );
            if new_path != *path {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }

            // Recurse into type arguments
            for &arg in args {
                substitute_type_expr_path(
                    arg,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    ctx,
                    visited,
                );
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            substitute_type_expr_path(
                arg.typ,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
            substitute_type_expr_path(
                *ret,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                substitute_type_expr_path(
                    t,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    ctx,
                    visited,
                );
            }
        }
        TypeDesc::Tlink(t) => {
            substitute_type_expr_path(
                *t,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
        }
        TypeDesc::Tsubst(t) => {
            substitute_type_expr_path(
                *t,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
        }
        TypeDesc::Tpoly { body, vars } => {
            substitute_type_expr_path(
                *body,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
            for &v in vars {
                substitute_type_expr_path(
                    v,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    ctx,
                    visited,
                );
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            substitute_type_expr_path(
                *fields,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            substitute_type_expr_path(
                *typ,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
            substitute_type_expr_path(
                *rest,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
        }
        TypeDesc::Tvariant(row) => {
            substitute_type_expr_path(
                row.row_more,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
                ctx,
                visited,
            );
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        substitute_type_expr_path(
                            *t,
                            type_stamp_map,
                            type_name_map,
                            module_stamp_map,
                            module_name_map,
                            ctx,
                            visited,
                        );
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            substitute_type_expr_path(
                                t,
                                type_stamp_map,
                                type_name_map,
                                module_stamp_map,
                                module_name_map,
                                ctx,
                                visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, .. } => {
            // Package paths are module-type paths; OCaml substitutes these through
            // `Subst.modtype`, not just module substitution.
            let new_path = substitute_type_path(
                path,
                type_stamp_map,
                type_name_map,
                module_stamp_map,
                module_name_map,
            );
            if new_path != *path {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                substitute_type_expr_path(
                    arg,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    ctx,
                    visited,
                );
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

fn substitute_type_path(
    path: &Path,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &HashMap<i32, Path>,
    module_name_map: &HashMap<String, Path>,
) -> Path {
    match path {
        Path::Pident(ident) => {
            if ident.stamp() != 0 {
                type_stamp_map
                    .get(&ident.stamp())
                    .cloned()
                    .or_else(|| {
                        // Flattened CMI heads like Stdlib_JSON often carry
                        // non-zero stamps but still need name-based rewriting.
                        ident
                            .name()
                            .contains('_')
                            .then(|| type_name_map.get(ident.name()).cloned())
                            .flatten()
                    })
                    .unwrap_or_else(|| path.clone())
            } else {
                type_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| path.clone())
            }
        }
        Path::Pdot(prefix, name, pos) => {
            let rewritten_prefix =
                substitute_module_path(prefix, module_stamp_map, module_name_map);
            Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)
        }
        Path::Papply(left, right) => Path::Papply(
            Box::new(substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
            )),
            Box::new(substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
            )),
        ),
    }
}

fn substitute_module_path(
    path: &Path,
    module_stamp_map: &HashMap<i32, Path>,
    module_name_map: &HashMap<String, Path>,
) -> Path {
    match path {
        Path::Pident(ident) => {
            let debug_subst = std::env::var_os("RUST_DEBUG_SUBST_STDLIB_INTL").is_some()
                && (ident.name().contains("Stdlib_Intl") || ident.name().contains("NumberFormat"));
            if debug_subst {
                eprintln!(
                    "[subst-module] ident={} stamp={} has_stamp={} has_name={}",
                    ident.name(),
                    ident.stamp(),
                    module_stamp_map.contains_key(&ident.stamp()),
                    module_name_map.contains_key(ident.name())
                );
            }
            if ident.stamp() != 0 {
                module_stamp_map
                    .get(&ident.stamp())
                    .cloned()
                    .or_else(|| {
                        // Flattened module names (Stdlib_JSON, Stdlib_Intl_*)
                        // may appear with non-zero stamps; allow a targeted
                        // name fallback for those heads only.
                        ident
                            .name()
                            .contains('_')
                            .then(|| module_name_map.get(ident.name()).cloned())
                            .flatten()
                    })
                    .unwrap_or_else(|| path.clone())
            } else {
                module_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| path.clone())
            }
        }
        Path::Pdot(prefix, name, pos) => {
            let rewritten_prefix =
                substitute_module_path(prefix, module_stamp_map, module_name_map);
            Path::Pdot(Box::new(rewritten_prefix), name.clone(), *pos)
        }
        Path::Papply(left, right) => Path::Papply(
            Box::new(substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
            )),
            Box::new(substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
            )),
        ),
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

    let desc = ctx.get_desc(ty_ref);

    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let rewritten = rewrite_path_prefix(path, old_name, new_prefix);
            if let Some(new_path) = rewritten {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
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
        TypeDesc::Tpackage { path, args, .. } => {
            if let Some(new_path) = rewrite_path_prefix(path, old_name, new_prefix) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
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
        Path::Pident(id) if id.name() == old_name => Some(new_prefix.clone()),
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
                                        rewrite_type_expr_prefix(
                                            arg,
                                            old_name,
                                            new_prefix,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_type_expr_prefix(
                                            lbl.ld_type,
                                            old_name,
                                            new_prefix,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_prefix(
                                    res,
                                    old_name,
                                    new_prefix,
                                    ctx,
                                    &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_type_expr_prefix(
                                lbl.ld_type,
                                old_name,
                                new_prefix,
                                ctx,
                                &mut visited,
                            );
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
                            rewrite_type_expr_prefix(
                                lbl.ld_type,
                                old_name,
                                new_prefix,
                                ctx,
                                &mut visited,
                            );
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

/// Rewrite a path by replacing an old path prefix with a new one.
/// E.g., with old_prefix=Pdot(Pident("Js"),"Json") and new_prefix=Pident("J"):
///   Pdot(Pdot(Pident("Js"),"Json"),"Kind") → Pdot(Pident("J"),"Kind")
///   Pdot(Pdot(Pdot(Pident("Js"),"Json"),"Kind"),"t") → Pdot(Pdot(Pident("J"),"Kind"),"t")
fn rewrite_path_by_path_prefix(path: &Path, old_prefix: &Path, new_prefix: &Path) -> Option<Path> {
    if path.same(old_prefix) {
        return Some(new_prefix.clone());
    }
    match path {
        Path::Pdot(inner, name, pos) => {
            if inner.same(old_prefix) {
                return Some(Path::Pdot(Box::new(new_prefix.clone()), name.clone(), *pos));
            }
            rewrite_path_by_path_prefix(inner, old_prefix, new_prefix)
                .map(|new_inner| Path::Pdot(Box::new(new_inner), name.clone(), *pos))
        }
        _ => None,
    }
}

/// Walk a type expression tree and rewrite all Tconstr/Tpackage paths
/// that have `old_prefix` as a path prefix, replacing it with `new_prefix`.
/// Used for module alias resolution: `module J = Js.Json` rewrites
/// `Js.Json.Kind.t` → `J.Kind.t` in all types.
fn rewrite_type_expr_by_path_prefix(
    ty_ref: TypeExprRef,
    old_prefix: &Path,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.0) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if let Some(new_path) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_type_expr_by_path_prefix(arg, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_type_expr_by_path_prefix(arg.typ, old_prefix, new_prefix, ctx, visited);
            rewrite_type_expr_by_path_prefix(*ret, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                rewrite_type_expr_by_path_prefix(t, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) => {
            rewrite_type_expr_by_path_prefix(*t, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tsubst(t) => {
            rewrite_type_expr_by_path_prefix(*t, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_expr_by_path_prefix(*body, old_prefix, new_prefix, ctx, visited);
            for &v in vars {
                rewrite_type_expr_by_path_prefix(v, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_type_expr_by_path_prefix(*fields, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_type_expr_by_path_prefix(*typ, old_prefix, new_prefix, ctx, visited);
            rewrite_type_expr_by_path_prefix(*rest, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_type_expr_by_path_prefix(row.row_more, old_prefix, new_prefix, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_type_expr_by_path_prefix(*t, old_prefix, new_prefix, ctx, visited);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            rewrite_type_expr_by_path_prefix(
                                t, old_prefix, new_prefix, ctx, visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, .. } => {
            if let Some(new_path) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_type_expr_by_path_prefix(arg, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// Rewrite all type paths in a signature by replacing path prefix `old_prefix`
/// with `new_prefix`. Used when resolving module aliases like `module J = Js.Json`:
/// rewrites `Pdot(Pdot(Pident("Js"), "Json"), "Kind")` → `Pdot(Pident("J"), "Kind")`.
pub fn rewrite_sig_by_path_prefix(
    sig_items: &[SignatureItem],
    old_prefix: &Path,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
) {
    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                rewrite_type_expr_by_path_prefix(
                    desc.val_type, old_prefix, new_prefix, ctx, &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_by_path_prefix(
                        param, old_prefix, new_prefix, ctx, &mut visited,
                    );
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_by_path_prefix(
                        manifest, old_prefix, new_prefix, ctx, &mut visited,
                    );
                }
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        rewrite_type_expr_by_path_prefix(
                                            arg, old_prefix, new_prefix, ctx, &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_type_expr_by_path_prefix(
                                            lbl.ld_type, old_prefix, new_prefix, ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_by_path_prefix(
                                    res, old_prefix, new_prefix, ctx, &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_type_expr_by_path_prefix(
                                lbl.ld_type, old_prefix, new_prefix, ctx, &mut visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigModule(_id, md, _) => {
                if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    rewrite_sig_by_path_prefix(sub_sig, old_prefix, new_prefix, ctx);
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
    // Match OCaml `prefix_idents`/`Subst` behavior: when descending into a
    // submodule, keep parent substitutions visible so child signatures can
    // reference parent-defined types through qualified paths.
    let parent_maps = build_subst_maps(sig_items, module_path);

    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            let sub_path = Path::pdot(module_path.clone(), id.name());
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                substitute_type_paths_in_sig_with_maps(sub_sig, &parent_maps, ctx);
                substitute_type_paths_in_sig(sub_sig, &sub_path, ctx);
                substitute_submodule_paths(sub_sig, &sub_path, ctx);
            }
        }
    }
}

/// Collect alias rewrite mappings from MtyAlias submodules.
/// When a module has `module JSON = Stdlib_JSON` (MtyAlias), record
/// "Stdlib_JSON" → Pdot(Pident("Stdlib"), "JSON") so that when
/// Stdlib_JSON.cmi is later loaded, its types get rewritten.
fn collect_alias_rewrites(
    sig_items: &[SignatureItem],
    module_path: &Path,
    rewrites: &mut HashMap<String, Path>,
) {
    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            if let ModuleType::MtyAlias(_, alias_path) = &md.md_type {
                // The alias target is typically Pident("Stdlib_JSON") for
                // flattened submodules. Record the mapping.
                if let Path::Pident(alias_id) = alias_path {
                    let qualified = Path::pdot(module_path.clone(), id.name());
                    rewrites
                        .entry(alias_id.name().to_string())
                        .or_insert(qualified);
                }
            }
            // Also recurse into MtySignature submodules to find nested aliases
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                let sub_path = Path::pdot(module_path.clone(), id.name());
                collect_alias_rewrites(sub_sig, &sub_path, rewrites);
            }
        }
    }
}

/// Depth-restricted prefix rewriting for an entire signature.
/// Only rewrites Tconstr paths where old_name appears as a module prefix
/// at depth >= 2 (not as the direct parent of a type name).
fn rewrite_deep_prefix_in_sig(
    sig_items: &[SignatureItem],
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
) {
    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                rewrite_deep_prefix_expr(desc.val_type, old_name, new_prefix, ctx, &mut visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_deep_prefix_expr(param, old_name, new_prefix, ctx, &mut visited);
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_deep_prefix_expr(manifest, old_name, new_prefix, ctx, &mut visited);
                }
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        rewrite_deep_prefix_expr(
                                            arg, old_name, new_prefix, ctx, &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_deep_prefix_expr(
                                            lbl.ld_type, old_name, new_prefix, ctx, &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_deep_prefix_expr(
                                    res, old_name, new_prefix, ctx, &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_deep_prefix_expr(
                                lbl.ld_type, old_name, new_prefix, ctx, &mut visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    rewrite_deep_prefix_expr(param, old_name, new_prefix, ctx, &mut visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            rewrite_deep_prefix_expr(
                                arg, old_name, new_prefix, ctx, &mut visited,
                            );
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            rewrite_deep_prefix_expr(
                                lbl.ld_type, old_name, new_prefix, ctx, &mut visited,
                            );
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    rewrite_deep_prefix_expr(ret, old_name, new_prefix, ctx, &mut visited);
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                // Recurse into sub-module signatures
                if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    rewrite_deep_prefix_in_sig(sub_sig, old_name, new_prefix, ctx);
                }
            }
            _ => {}
        }
    }
}

/// Walk a type expression and rewrite Tconstr paths where old_name appears
/// at depth >= 2 as a module prefix. Depth 1 (direct parent) is preserved.
fn rewrite_deep_prefix_expr(
    ty_ref: TypeExprRef,
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.0) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);

    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            // Only rewrite if the path has depth >= 2 for the old_name prefix.
            // Pdot(Pident("old_name"), "t") -> depth 1, don't rewrite
            // Pdot(Pdot(Pident("old_name"), "Sub"), "t") -> depth 2, rewrite
            if let Some(new_path) = rewrite_path_deep(path, old_name, new_prefix) {

                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_deep_prefix_expr(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            rewrite_deep_prefix_expr(arg.typ, old_name, new_prefix, ctx, visited);
            rewrite_deep_prefix_expr(*ret, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                rewrite_deep_prefix_expr(t, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) => {
            rewrite_deep_prefix_expr(*t, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tsubst(t) => {
            rewrite_deep_prefix_expr(*t, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_deep_prefix_expr(*body, old_name, new_prefix, ctx, visited);
            for &v in vars {
                rewrite_deep_prefix_expr(v, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_deep_prefix_expr(*fields, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_deep_prefix_expr(*typ, old_name, new_prefix, ctx, visited);
            rewrite_deep_prefix_expr(*rest, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            rewrite_deep_prefix_expr(row.row_more, old_name, new_prefix, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_deep_prefix_expr(*t, old_name, new_prefix, ctx, visited);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            rewrite_deep_prefix_expr(t, old_name, new_prefix, ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, .. } => {
            if let Some(new_path) = rewrite_path_deep(path, old_name, new_prefix) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_deep_prefix_expr(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// Rewrite a path only when old_name appears at depth >= 2.
/// Pdot(Pident("old"), "t") -> None (depth 1, don't rewrite)
/// Pdot(Pdot(Pident("old"), "Sub"), "t") -> Some(Pdot(Pdot(new_prefix, "Sub"), "t"))
fn rewrite_path_deep(path: &Path, old_name: &str, new_prefix: &Path) -> Option<Path> {
    match path {
        // Pident("old_name") -> depth 0 as type path: don't rewrite
        Path::Pident(_) => None,
        Path::Pdot(inner, name, pos) => {
            match inner.as_ref() {
                // Pdot(Pident("old_name"), "t") -> depth 1: don't rewrite
                Path::Pident(id) if id.name() == old_name => None,
                // Pdot(Pdot(...), name) -> check if inner has a rewritable prefix
                _ => {
                    let rewritten_inner = rewrite_inner_prefix(inner, old_name, new_prefix)?;
                    Some(Path::Pdot(Box::new(rewritten_inner), name.clone(), *pos))
                }
            }
        }
        Path::Papply(_, _) => None,
    }
}

/// Rewrite old_name in a module path (at any depth).
/// Used for the inner part of a depth >= 2 path.
fn rewrite_inner_prefix(path: &Path, old_name: &str, new_prefix: &Path) -> Option<Path> {
    match path {
        Path::Pident(id) if id.name() == old_name => Some(new_prefix.clone()),
        Path::Pdot(inner, name, pos) => {
            let rewritten_inner = rewrite_inner_prefix(inner, old_name, new_prefix)?;
            Some(Path::Pdot(Box::new(rewritten_inner), name.clone(), *pos))
        }
        _ => None,
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
                            // Signature items may carry constructor argument nodes at
                            // non-generic levels. Rebuild a generic-level scheme so
                            // instance_constructor can instantiate per-use copies
                            // like OCaml's Env.add_signature/Datarepr flow.
                            let cstr_args: Vec<TypeExprRef> = cstr_args
                                .into_iter()
                                .map(|arg| crate::types::ctype::subst_identity_copy(ctx, arg))
                                .collect();

                            // Create result type (the variant type itself)
                            let cstr_res = if let Some(res_ty) = cd.cd_res {
                                crate::types::ctype::subst_identity_copy(ctx, res_ty)
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
                                lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                    ctx,
                                    ld.ld_type,
                                    &decl.type_params,
                                ),
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
                let mut md = md.clone();
                // Set the qualified path so that when this module is accessed
                // via Lident (e.g. "Console" from opened Stdlib), we produce
                // the correct Pdot path (e.g. Pdot(Pident("Stdlib"), "Console"))
                md.md_path = Some(Path::pdot(module_path.clone(), id.name()));
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
                let ext_type_path = substitute_sig_path(&ext.ext_type_path, sig_items, module_path);
                // Add extension constructor
                let cstr_desc = ConstructorDescription {
                    cstr_name: id.name().to_string(),
                    cstr_res: ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone()),
                    cstr_existentials: vec![],
                    cstr_args: match &ext.ext_args {
                        crate::types::decl::ConstructorArguments::CstrTuple(args) => args.clone(),
                        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                            labels.iter().map(|l| l.ld_type).collect()
                        }
                    },
                    cstr_arity: match &ext.ext_args {
                        crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                            args.len() as i32
                        }
                        crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                            labels.len() as i32
                        }
                    },
                    cstr_tag: ConstructorTag::CstrExtension(Path::pdot(
                        module_path.clone(),
                        id.name(),
                    )),
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
