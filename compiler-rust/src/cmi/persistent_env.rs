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
use std::fs;
use std::path::Path as FsPath;
use std::path::PathBuf;

use crate::driver::{jsx_version_for_structure, load_pervasives, normalize_signature_types, CompilerOptions};
use crate::ident::Ident;
use crate::parser::{jsx_ppx, module, Parser};
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorDescription, ConstructorTag, LabelDescription, ModuleDeclaration, ModuleType,
    Signature, SignatureItem, TypeKind,
};
use crate::types::env::{initial_env, Env};
use crate::types::path::Path;
use crate::types::typecore::TypeCheckContext;
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typedtree::{ModuleType as TypedModuleType, ModuleTypeDesc as TypedModuleTypeDesc};
use crate::types::typemod::{decl_module_type_from_typed, transl_signature, type_structure};

use super::cmi_format;
use super::sig_reader::SigReadContext;

/// A cached persistent module structure.
#[derive(Debug, Clone)]
pub struct PersStruct {
    /// Module name
    pub ps_name: String,
    /// Loaded signature
    pub ps_sig: Signature,
    /// Source filename
    pub ps_filename: String,
}

/// Persistent environment for module loading.
#[derive(Clone)]
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
    /// Additional modules opened implicitly from `-open` flags.
    open_modules: Vec<String>,
    /// Default JSX version from CLI flags, if any.
    jsx_version: Option<i32>,
}

impl PersistentEnv {
    /// Create a new persistent environment with no load paths.
    pub fn new() -> Self {
        PersistentEnv {
            cache: HashMap::new(),
            load_path: Vec::new(),
            alias_prefix_rewrites: HashMap::new(),
            open_modules: Vec::new(),
            jsx_version: None,
        }
    }

    /// Set the load path (list of directories to search for .cmi files).
    pub fn set_load_path(&mut self, paths: Vec<PathBuf>) {
        self.load_path = paths;
    }

    pub fn set_open_modules(&mut self, open_modules: Vec<String>) {
        self.open_modules = open_modules;
    }

    pub fn set_jsx_version(&mut self, jsx_version: Option<i32>) {
        self.jsx_version = jsx_version;
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

    pub fn qualified_alias_path_for_flattened_head(&self, flat_head: &str) -> Option<Path> {
        self.alias_prefix_rewrites.get(flat_head).cloned()
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

        // Insert a placeholder before loading so recursive lookups of the same
        // module fail cleanly instead of recursing indefinitely.
        self.cache.insert(name.to_string(), None);

        // Try to load from disk
        let result = self.load_module(name, ctx);
        self.cache.insert(name.to_string(), result);
        self.cache.get(name).and_then(|opt| opt.as_ref())
    }

    fn finalize_loaded_signature<'a>(
        &mut self,
        name: &str,
        ps_name: String,
        mut signature: Signature,
        ps_filename: String,
        ctx: &'a TypeContext<'a>,
    ) -> PersStruct {
        let module_path = Path::Pident(Ident::create_persistent(name));

        // Apply path substitution: rewrite Tconstr paths from internal
        // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
        substitute_type_paths_in_sig(&signature, &module_path, ctx);
        substitute_sig_decl_paths_in_place(&mut signature, &module_path);

        // Also recursively substitute paths in sub-module signatures.
        substitute_submodule_paths(&signature, &module_path, ctx);

        // Keep the existing deep-prefix rewrite for flattened alias heads.
        if let Some(qualified_path) = self.alias_prefix_rewrites.get(name).cloned() {
            if !name.contains('-') {
                rewrite_deep_prefix_in_sig(&signature, name, &qualified_path, ctx);
            }
        }

        let effective_module_path = self
            .alias_prefix_rewrites
            .get(name)
            .cloned()
            .unwrap_or_else(|| module_path.clone());
        collect_alias_rewrites(
            &signature,
            &effective_module_path,
            &mut self.alias_prefix_rewrites,
        );
        register_sig_types_recursive(&signature, &effective_module_path, ctx, &self.load_path);

        PersStruct {
            ps_name,
            ps_sig: signature,
            ps_filename,
        }
    }

    fn read_ast_source_path(ast_path: &FsPath) -> Option<PathBuf> {
        let content = fs::read(ast_path).ok()?;
        if content.len() < 5 {
            return None;
        }

        let dep_size =
            u32::from_be_bytes([content[0], content[1], content[2], content[3]]) as usize;
        let path_start = 4 + dep_size;
        if path_start >= content.len() {
            return None;
        }

        let path_end = content[path_start..]
            .iter()
            .position(|&b| b == b'\n')
            .map(|pos| path_start + pos)
            .unwrap_or(content.len());
        let path_bytes = &content[path_start..path_end];
        let path_str = String::from_utf8_lossy(path_bytes);
        if path_str.is_empty() {
            return None;
        }
        Some(PathBuf::from(path_str.into_owned()))
    }

    fn read_source_latin1(path: &FsPath) -> Option<String> {
        let bytes = fs::read(path).ok()?;
        Some(bytes.iter().map(|&b| b as char).collect())
    }

    fn typecheck_source_signature<'a>(
        &self,
        source_path: &FsPath,
        ctx: &'a TypeContext<'a>,
    ) -> Option<(Signature, PersistentEnv)> {
        let filename = source_path.to_string_lossy().into_owned();
        let source = Self::read_source_latin1(source_path)?;
        let mut fallback_pers = self.clone();
        let mut env = initial_env(ctx);
        let open_modules = fallback_pers.open_modules.clone();
        load_pervasives(&mut fallback_pers, &mut env, ctx, &open_modules);

        if source_path
            .extension()
            .and_then(|s| s.to_str())
            .is_some_and(|ext| ext == "resi" || ext == "mli")
        {
            let mut parser = Parser::new(&filename, &source);
            let signature = module::parse_signature(&mut parser);
            if parser.has_errors() {
                return None;
            }
            let signature = crate::binary_ast::ppx::rewrite_signature(&signature, parser.arena_mut()).ok()?;

            let mut tctx = TypeCheckContext::new(ctx, parser.arena());
            tctx.set_persistent_env(fallback_pers);
            let typed_signature = transl_signature(&mut tctx, &env, parser.arena(), &signature).ok()?;
            let fallback_pers = tctx.persistent_env.take()?;
            let typed_module_type = TypedModuleType {
                mty_desc: TypedModuleTypeDesc::Tmty_signature(typed_signature),
                mty_loc: crate::parse_arena::LocIdx(0),
                mty_attributes: crate::parser::ast::Attributes::new(),
            };
            let signature = match decl_module_type_from_typed(&typed_module_type)? {
                crate::types::decl::ModuleType::MtySignature(signature) => signature,
                _ => return None,
            };
            return Some((signature, fallback_pers));
        }

        let mut parser = Parser::new(&filename, &source);
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            return None;
        }

        let options = CompilerOptions {
            open_modules: self.open_modules.clone(),
            jsx_version: self.jsx_version,
            ..CompilerOptions::default()
        };
        let jsx_version = jsx_version_for_structure(&structure, &options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
        } else {
            structure
        };
        let structure = crate::binary_ast::ppx::expand_extensions(&structure, parser.arena_mut());
        let structure =
            crate::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut()).ok()?;

        let mut tctx = TypeCheckContext::new(ctx, parser.arena());
        tctx.set_persistent_env(fallback_pers);
        let (typed_structure, final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure).ok()?;

        let has_resi = source_path
            .extension()
            .and_then(|s| s.to_str())
            .is_some_and(|ext| ext == "res")
            && FsPath::new(&format!("{}i", filename)).exists();
        if !has_resi {
            normalize_signature_types(ctx, &typed_structure, &final_env);
        }

        let fallback_pers = tctx.persistent_env.take()?;
        Some((typed_structure.str_type.clone(), fallback_pers))
    }

    fn load_module_from_source_fallback<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext<'a>,
    ) -> Option<PersStruct> {
        let ast_filename = format!("{}.ast", name);
        let ast_path = self.find_in_path_uncap(&ast_filename)?;
        let source_path = Self::read_ast_source_path(FsPath::new(&ast_path))?;
        let interface_path = match source_path.extension().and_then(|s| s.to_str()) {
            Some("res") => {
                let resi = PathBuf::from(format!("{}i", source_path.to_string_lossy()));
                resi.exists().then_some(resi)
            }
            Some("ml") => {
                let mli = PathBuf::from(format!("{}i", source_path.to_string_lossy()));
                mli.exists().then_some(mli)
            }
            _ => None,
        };
        let preferred_path = interface_path.as_deref().unwrap_or(source_path.as_path());

        let debug_source_fallback = std::env::var_os("RUST_DEBUG_PERSISTENT_SOURCE_FALLBACK").is_some();
        if debug_source_fallback {
            eprintln!(
                "[persistent-source] module={} ast={} source={}",
                name,
                ast_path,
                preferred_path.display()
            );
        }

        let (signature, fallback_pers) = self.typecheck_source_signature(preferred_path, ctx)?;
        self.alias_prefix_rewrites
            .extend(fallback_pers.alias_prefix_rewrites.clone());
        for (module_name, loaded) in fallback_pers.cache {
            if module_name != name && loaded.is_some() && !self.cache.contains_key(&module_name) {
                self.cache.insert(module_name, loaded);
            }
        }

        Some(self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            preferred_path.to_string_lossy().into_owned(),
            ctx,
        ))
    }

    /// Load a module from a .cmi file, or fall back to the source path embedded
    /// in a sibling `.ast` when the module is implementation-only.
    fn load_module<'a>(&mut self, name: &str, ctx: &'a TypeContext<'a>) -> Option<PersStruct> {
        let cmi_filename = format!("{}.cmi", name);
        if let Some(full_path) = self.find_in_path_uncap(&cmi_filename) {
            let cmi = match cmi_format::read_cmi(&full_path) {
                Ok(cmi) => cmi,
                Err(e) => {
                    eprintln!("warning: failed to read CMI file {}: {}", full_path, e);
                    return None;
                }
            };

            let mut sig_ctx = SigReadContext::new(ctx);
            let signature = sig_ctx.read_signature(&cmi.cmi_sign);
            return Some(self.finalize_loaded_signature(
                name,
                cmi.cmi_name,
                signature,
                full_path,
                ctx,
            ));
        }

        self.load_module_from_source_fallback(name, ctx)
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

fn substitute_module_type_paths_with_maps(module_type: &mut ModuleType, maps: &SubstMaps) {
    match module_type {
        ModuleType::MtyIdent(path) | ModuleType::MtyAlias(_, path) => {
            *path = substitute_type_path(
                path,
                &maps.type_stamp_map,
                &maps.type_name_map,
                &maps.module_stamp_map,
                &maps.module_name_map,
            );
        }
        ModuleType::MtySignature(sig) => {
            substitute_sig_decl_paths_in_place_with_maps(sig, maps);
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                substitute_module_type_paths_with_maps(param_type, maps);
            }
            substitute_module_type_paths_with_maps(result, maps);
        }
    }
}

fn substitute_sig_decl_paths_in_place_with_maps(sig_items: &mut [SignatureItem], maps: &SubstMaps) {
    if maps.is_empty() {
        return;
    }

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    *path = substitute_type_path(
                        path,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                    );
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = decl.type_path.as_mut() {
                    *path = substitute_type_path(
                        path,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                    );
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                ext.ext_type_path = substitute_type_path(
                    &ext.ext_type_path,
                    &maps.type_stamp_map,
                    &maps.type_name_map,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                );
            }
            SignatureItem::SigModule(_, md, _) => {
                if let Some(path) = md.md_path.as_mut() {
                    *path = substitute_type_path(
                        path,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                    );
                }
                substitute_module_type_paths_with_maps(&mut md.md_type, maps);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    substitute_module_type_paths_with_maps(module_type, maps);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

pub fn substitute_sig_decl_paths_in_place(sig_items: &mut [SignatureItem], module_path: &Path) {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    substitute_sig_decl_paths_in_place_with_maps(sig_items, &maps);
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
            SignatureItem::SigModule(_id, md, _) => {
                if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    substitute_type_paths_in_sig_with_maps(sub_sig, maps, ctx);
                }
            }
            _ => {}
        }
    }
}

/// Apply parent-scope substitutions to a child signature.
///
/// This matches the first step performed by `substitute_submodule_paths`:
/// when entering a submodule, references to parent-defined types/modules
/// should be rewritten to qualified paths rooted at `parent_module_path`.
pub fn substitute_type_paths_in_child_sig(
    child_sig: &[SignatureItem],
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    let parent_maps = build_subst_maps(parent_sig, parent_module_path);
    substitute_type_paths_in_sig_with_maps(child_sig, &parent_maps, ctx);
}

/// Apply parent-scope substitutions to an entire child module type.
///
/// OCaml's `Subst.modtype` keeps parent-defined type/module paths visible when
/// descending into a nested module or functor result. A child module type can
/// therefore reference parent items using bare names (for example
/// `comparator<key>` inside `Comparable.Make`), and those names must be
/// rewritten through the enclosing parent module path.
pub fn substitute_type_paths_in_child_module_type(
    child_mty: &mut ModuleType,
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    match child_mty {
        ModuleType::MtySignature(sig) => {
            substitute_type_paths_in_child_sig(sig, parent_sig, parent_module_path, ctx);
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                substitute_type_paths_in_child_module_type(
                    param_type,
                    parent_sig,
                    parent_module_path,
                    ctx,
                );
            }
            substitute_type_paths_in_child_module_type(result, parent_sig, parent_module_path, ctx);
        }
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
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

fn rewrite_module_type_prefix_paths(
    module_type: &mut ModuleType,
    old_name: &str,
    new_prefix: &Path,
) {
    match module_type {
        ModuleType::MtyIdent(path) | ModuleType::MtyAlias(_, path) => {
            if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix) {
                *path = rewritten;
            }
        }
        ModuleType::MtySignature(sig) => {
            rewrite_module_prefix_paths_in_sig(sig, old_name, new_prefix);
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_module_type_prefix_paths(param_type, old_name, new_prefix);
            }
            rewrite_module_type_prefix_paths(result, old_name, new_prefix);
        }
    }
}

pub fn rewrite_module_prefix_paths_in_sig(
    sig_items: &mut [SignatureItem],
    old_name: &str,
    new_prefix: &Path,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix) {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = decl.type_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix) {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_prefix(&ext.ext_type_path, old_name, new_prefix)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                if let Some(path) = md.md_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix) {
                        *path = rewritten;
                    }
                }
                rewrite_module_type_prefix_paths(&mut md.md_type, old_name, new_prefix);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    rewrite_module_type_prefix_paths(module_type, old_name, new_prefix);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
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

fn rewrite_module_type_by_path_prefix(
    module_type: &mut ModuleType,
    old_prefix: &Path,
    new_prefix: &Path,
) {
    match module_type {
        ModuleType::MtyIdent(path) | ModuleType::MtyAlias(_, path) => {
            if let Some(rewritten) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix) {
                *path = rewritten;
            }
        }
        ModuleType::MtySignature(sig) => {
            rewrite_sig_paths_by_path_prefix(sig, old_prefix, new_prefix);
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_module_type_by_path_prefix(param_type, old_prefix, new_prefix);
            }
            rewrite_module_type_by_path_prefix(result, old_prefix, new_prefix);
        }
    }
}

pub fn rewrite_sig_paths_by_path_prefix(
    sig_items: &mut [SignatureItem],
    old_prefix: &Path,
    new_prefix: &Path,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
                    {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = decl.type_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
                    {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_by_path_prefix(&ext.ext_type_path, old_prefix, new_prefix)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                if let Some(path) = md.md_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
                    {
                        *path = rewritten;
                    }
                }
                rewrite_module_type_by_path_prefix(&mut md.md_type, old_prefix, new_prefix);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    rewrite_module_type_by_path_prefix(module_type, old_prefix, new_prefix);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
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

/// Public wrapper for substitute_submodule_paths.
pub fn substitute_submodule_paths_pub(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext<'_>,
) {
    substitute_submodule_paths(sig_items, module_path, ctx);
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

    fn collect_target_constr_nodes(
        ctx: &TypeContext<'_>,
        ty: TypeExprRef,
        out: &mut Vec<(TypeExprRef, String)>,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return;
        }
        let desc = ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let path_name = path.name();
                if path_name == "React.element"
                    || path_name == "Jsx.element"
                    || path.last() == "element"
                    || path.last() == "someElement"
                {
                    out.push((ty, path_name));
                }
                for arg in args {
                    collect_target_constr_nodes(ctx, *arg, out, seen);
                }
            }
            TypeDesc::Tarrow { arg, ret, .. } => {
                collect_target_constr_nodes(ctx, arg.typ, out, seen);
                collect_target_constr_nodes(ctx, *ret, out, seen);
            }
            TypeDesc::Ttuple(items) => {
                for item in items {
                    collect_target_constr_nodes(ctx, *item, out, seen);
                }
            }
            TypeDesc::Tobject { fields, name } => {
                collect_target_constr_nodes(ctx, *fields, out, seen);
                if let Some((_path, args)) = name {
                    for arg in args {
                        collect_target_constr_nodes(ctx, *arg, out, seen);
                    }
                }
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                collect_target_constr_nodes(ctx, *typ, out, seen);
                collect_target_constr_nodes(ctx, *rest, out, seen);
            }
            TypeDesc::Tpoly { body, vars } => {
                collect_target_constr_nodes(ctx, *body, out, seen);
                for var in vars {
                    collect_target_constr_nodes(ctx, *var, out, seen);
                }
            }
            TypeDesc::Tvariant(row) => {
                collect_target_constr_nodes(ctx, row.row_more, out, seen);
                for (_label, field) in &row.row_fields {
                    match field {
                        crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
                            collect_target_constr_nodes(ctx, *ty, out, seen);
                        }
                        crate::types::type_expr::RowField::Reither { types, .. } => {
                            for ty in types {
                                collect_target_constr_nodes(ctx, *ty, out, seen);
                            }
                        }
                        _ => {}
                    }
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for arg in args {
                    collect_target_constr_nodes(ctx, *arg, out, seen);
                }
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                collect_target_constr_nodes(ctx, *target, out, seen);
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }

    fn inline_record_type_params(
        ctx: &TypeContext<'_>,
        parent_type_params: &[TypeExprRef],
        labels: &[crate::types::LabelDeclaration],
    ) -> Vec<TypeExprRef> {
        parent_type_params
            .iter()
            .copied()
            .filter(|param| {
                labels
                    .iter()
                    .any(|label| crate::types::ctype::deep_occur(ctx, *param, label.ld_type))
            })
            .collect()
    }

    for (pos, item) in sig_items.iter().enumerate() {
        let slot_path = |name: &str| {
            Path::Pdot(Box::new(module_path.clone()), name.to_string(), pos as i32)
        };
        match item {
            SignatureItem::SigValue(id, desc) => {
                // Add value binding with qualified path
                let mut desc = desc.clone();
                desc.val_path = Some(slot_path(id.name()));
                if std::env::var_os("RUST_DEBUG_OPEN_SIG_VALUES").is_some()
                    && (id.name() == "someElement"
                        || id.name() == "element"
                        || id.name() == "stringToJson"
                        || id.name() == "stringFromJson"
                        || module_path.last() == "ReactDOM")
                {
                    let mut seen = HashSet::new();
                    let mut nodes = Vec::new();
                    collect_target_constr_nodes(ctx, desc.val_type, &mut nodes, &mut seen);
                    let refs = nodes
                        .iter()
                        .map(|(ty, path_name)| {
                            let repr = ctx.repr(*ty);
                            format!("{}#{}@{}", path_name, repr.0, ctx.get_level(repr))
                        })
                        .collect::<Vec<_>>();
                    eprintln!(
                        "[open-sig-value] module={} id={} val_type={} refs={}",
                        module_path.name(),
                        id.name(),
                        ctx.repr(desc.val_type).0,
                        refs.join(",")
                    );
                }
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

                            let inline_record = match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    let inline_params =
                                        inline_record_type_params(ctx, &decl.type_params, labels);
                                    let inline_path =
                                        Path::pdot(type_path.clone(), cd.cd_id.name());
                                    let inline_tag = match cstr_tag {
                                        ConstructorTag::CstrBlock(tag) => tag,
                                        _ => 0,
                                    };
                                    let inline_decl = crate::types::TypeDeclaration {
                                        type_params: inline_params.clone(),
                                        type_arity: inline_params.len() as i32,
                                        type_kind: crate::types::TypeKind::TypeRecord(
                                            labels.clone(),
                                            crate::types::RecordRepresentation::RecordInlined {
                                                tag: inline_tag,
                                                name: cd.cd_id.name().to_string(),
                                                num_nonconsts,
                                                attrs: cd.cd_attributes.clone(),
                                            },
                                        ),
                                        type_private: decl.type_private,
                                        type_manifest: None,
                                        type_variance: inline_params
                                            .iter()
                                            .map(|_| crate::types::variance::Variance::full())
                                            .collect(),
                                        type_newtype_level: None,
                                        type_loc: cd.cd_loc,
                                        type_attributes: vec![],
                                        type_immediate: false,
                                        type_unboxed: crate::types::UnboxedStatus::default(),
                                        type_inlined_types: vec![],
                                        type_path: None,
                                    };
                                    let inline_constr =
                                        ctx.new_generic_constr(inline_path, inline_params.clone());
                                    Some((vec![inline_constr], 1, Box::new(inline_decl)))
                                }
                                _ => None,
                            };

                            // Get argument types from constructor arguments
                            let (cstr_args, cstr_arity, cstr_inlined) = match inline_record {
                                Some((inline_args, inline_arity, inline_decl)) => {
                                    (inline_args, inline_arity, Some(inline_decl))
                                }
                                None => match &cd.cd_args {
                                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                        (args.clone(), args.len() as i32, None)
                                    }
                                    crate::types::decl::ConstructorArguments::CstrRecord(_) => {
                                        unreachable!("handled inline record constructor above")
                                    }
                                },
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
                                cstr_attributes:
                                    crate::types::decl::constructor_description_attrs_for_variant(
                                        constrs, cd,
                                    ),
                                cstr_inlined,
                            };

                            if let Some(ref inlined_decl) = cstr_desc.cstr_inlined {
                                if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) =
                                    inlined_decl.type_kind
                                {
                                    let inline_path =
                                        Path::pdot(type_path.clone(), cstr_desc.cstr_name.clone());
                                    let ty_res = ctx.new_constr(
                                        inline_path,
                                        inlined_decl.type_params.clone(),
                                    );
                                    for (pos, ld) in labels.iter().enumerate() {
                                        let label_desc = LabelDescription {
                                            lbl_name: ld.ld_id.name().to_string(),
                                            lbl_res: ty_res,
                                            lbl_arg: crate::types::ctype::remap_label_type_to_params(
                                                ctx,
                                                ld.ld_type,
                                                &inlined_decl.type_params,
                                            ),
                                            lbl_mut: ld.ld_mutable,
                                            lbl_optional: ld.ld_optional,
                                            lbl_pos: pos as i32,
                                            lbl_all: crate::types::decl::LabelArrayRef(0),
                                            lbl_repres: repres.clone(),
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
                            }

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
                let access_path = slot_path(id.name());
                md.md_path = Some(access_path.clone());
                // Rewrite module-type paths against the opened signature.
                // Some CMI signatures use hidden self-alias heads (e.g. `ArrayExt!`)
                // that are not directly resolvable from the current environment.
                // Normalize those to the qualified access path.
                let normalize_hidden_alias_path = |path: Path| -> Path {
                    fn go(path: Path, module_path: &Path, module_name: &str, access_path: &Path) -> Path {
                        match path {
                            Path::Pident(alias_id) => {
                                let clean = alias_id.name().trim_end_matches('!');
                                if clean == module_name {
                                    access_path.clone()
                                } else if clean == module_path.last() {
                                    module_path.clone()
                                } else {
                                    Path::Pident(alias_id)
                                }
                            }
                            Path::Pdot(prefix, name, pos) => Path::Pdot(
                                Box::new(go(*prefix, module_path, module_name, access_path)),
                                name,
                                pos,
                            ),
                            Path::Papply(functor, arg) => Path::Papply(
                                Box::new(go(*functor, module_path, module_name, access_path)),
                                Box::new(go(*arg, module_path, module_name, access_path)),
                            ),
                        }
                    }
                    go(path, module_path, id.name(), &access_path)
                };
                md.md_type = match md.md_type {
                    ModuleType::MtyAlias(alias_presence, alias_path) => {
                        let rewritten = substitute_sig_path(&alias_path, sig_items, module_path);
                        ModuleType::MtyAlias(alias_presence, normalize_hidden_alias_path(rewritten))
                    }
                    ModuleType::MtyIdent(path) => {
                        let rewritten = substitute_sig_path(&path, sig_items, module_path);
                        ModuleType::MtyIdent(normalize_hidden_alias_path(rewritten))
                    }
                    other => other,
                };
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
