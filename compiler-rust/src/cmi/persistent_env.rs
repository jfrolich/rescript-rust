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

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use std::fs;
use std::path::Path as FsPath;
use std::path::PathBuf;
use std::sync::Arc;

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::driver::{
    CompilerOptions, jsx_version_for_structure, load_pervasives, normalize_signature_types,
};
use crate::ident::Ident;
use crate::parser::{Parser, jsx_ppx, module};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, ConstructorDescription, ConstructorTag, LabelDescription, ModuleDeclaration,
    ModuleType, RecStatus, Signature, SignatureItem, TypeKind,
};
use crate::types::env::{Env, initial_env};
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typecore::TypeCheckContext;
use crate::types::typedtree::{
    ModuleType as TypedModuleType, ModuleTypeDesc as TypedModuleTypeDesc,
};
use crate::types::typemod::{decl_module_type_from_typed, transl_signature, type_structure};

use super::cmi_format;
use super::portable_types::{self, PortablePersStruct};
use super::sig_reader::SigReadContext;

fn first_char_case_variant(name: &str) -> Option<String> {
    let mut chars = name.chars();
    let first = chars.next()?;
    let rest = chars.as_str();
    if first.is_ascii_uppercase() {
        Some(format!("{}{}", first.to_ascii_lowercase(), rest))
    } else if first.is_ascii_lowercase() {
        Some(format!("{}{}", first.to_ascii_uppercase(), rest))
    } else {
        None
    }
}

fn resolve_first_char_case_key<V>(map: &HashMap<String, V>, name: &str) -> Option<String> {
    if map.contains_key(name) {
        return Some(name.to_string());
    }
    first_char_case_variant(name).filter(|variant| map.contains_key(variant))
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmjExportConstant {
    Bool(bool),
    Null,
    Undefined { is_unit: bool },
}

#[derive(Debug, Clone)]
pub struct CmjModuleMetadata {
    pub is_pure: bool,
    pub export_constants: HashMap<String, CmjExportConstant>,
}

/// In-memory module metadata for the `--in-process` build mode.
///
/// When a module is registered in the in-memory registry, these fields
/// replace the disk-based lookups that normally read `.ast` (source path),
/// `.cmj` (purity), and `.cmi` (interface).
#[derive(Debug, Clone)]
pub struct InMemoryModuleInfo {
    /// Source file path (replaces `.ast` source-path lookup)
    pub source_path: PathBuf,
    /// Whether the module is side-effect free (replaces `.cmj` purity lookup)
    pub is_pure: bool,
    /// Closed constant exports (replaces `.cmj` constant lookup)
    pub cmj_export_constants: HashMap<String, CmjExportConstant>,
    /// Whether this module belongs to `@rescript/runtime`
    pub is_runtime: bool,
}

/// Read-only module registry for `--in-process` builds.
///
/// Contains all previously-published module interfaces and metadata.
/// Shared (by reference) across parallel compilations within a wave.
/// Each worker creates a fresh `PersistentEnv` from this registry.
#[derive(Clone, Default)]
pub struct ModuleRegistry {
    /// Cached module structures in portable form (TypeExprRefs are self-contained
    /// indices into each entry's PortableTypeGraph, not arena refs).
    /// Values are shared so per-worker registry snapshots do not deep-clone
    /// published signatures and type graphs.
    /// Keyed by module name.
    pub cached_modules: HashMap<String, Arc<PortablePersStruct>>,
    /// Module metadata (source paths, purity, runtime status).
    pub module_info: HashMap<String, InMemoryModuleInfo>,
    /// Alias prefix rewrites (flattened_name -> qualified_path).
    pub alias_rewrites: HashMap<String, Path>,
    /// Source file paths for ALL modules, including those not yet compiled.
    /// Used for on-demand source-based type checking when a module is needed
    /// as an implicit dependency (e.g., via `-open Pervasives`) but hasn't
    /// been compiled yet in the current wave.
    pub source_fallback_paths: HashMap<String, PathBuf>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a namespace module's alias signature directly.
    /// This is the registry-level equivalent of `PersistentEnv::register_namespace_in_memory`.
    pub fn register_namespace(
        &mut self,
        namespace_name: &str,
        module_aliases: &[(String, String)],
    ) {
        let mut sig_items: Signature = Vec::with_capacity(module_aliases.len());
        for (short_name, internal_name) in module_aliases {
            sig_items.push(SignatureItem::SigModule(
                Ident::create_persistent(short_name.as_str()),
                ModuleDeclaration {
                    md_type: ModuleType::MtyAlias(
                        AliasPresence::MtaPresent,
                        Path::Pident(Ident::create_persistent(internal_name.as_str())),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ));
        }

        // Record alias rewrites
        let module_path = Path::Pident(Ident::create_persistent(namespace_name));
        collect_alias_rewrites(&sig_items, &module_path, &mut self.alias_rewrites);

        // Namespace signatures contain only MtyAlias entries (no TypeExprRefs),
        // so the portable type graph is empty.
        let fingerprint =
            portable_types::compute_type_graph_fingerprint_pub(&[], &sig_items);
        let portable = PortablePersStruct {
            ps_name: namespace_name.to_string(),
            ps_filename: format!("{}.mlmap", namespace_name),
            ps_sig: sig_items,
            cmi_longident_names: Vec::new(),
            type_graph: portable_types::PortableTypeGraph {
                entries: Vec::new(),
            },
            fingerprint,
        };
        self.cached_modules
            .insert(namespace_name.to_string(), Arc::new(portable));
    }

    /// Remove a module from the registry (for deleted/renamed modules).
    /// Purges cached signature, module info, source fallback, and any alias
    /// rewrites that reference this module.
    pub fn purge_module(&mut self, name: &str) {
        self.cached_modules.remove(name);
        self.module_info.remove(name);
        self.source_fallback_paths.remove(name);
        // Remove alias rewrites that point to this module
        self.alias_rewrites
            .retain(|key, _| key != name);
    }

    /// Store a compiled module's finalized PersStruct and metadata.
    pub fn register_module(
        &mut self,
        name: &str,
        portable: PortablePersStruct,
        info: InMemoryModuleInfo,
        new_alias_rewrites: HashMap<String, Path>,
    ) {
        self.cached_modules
            .insert(name.to_string(), Arc::new(portable));
        self.module_info.insert(name.to_string(), info);
        self.alias_rewrites.extend(new_alias_rewrites);
    }
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
    /// Whether the current compilation uses `-nopervasives`.
    nopervasives: bool,
    /// The module currently being compiled, used to skip self-opens.
    compiling_module: Option<String>,
    /// Cache of renamed signatures (matching OCaml's lazy Subst.signature).
    /// Each module's signature is renamed once and cached here.
    renamed_sig_cache: HashMap<String, Signature>,
    /// In-memory module registry for `--in-process` builds.
    /// When a module is registered here, its metadata (source path, purity)
    /// is resolved from memory instead of from `.ast`/`.cmj` files on disk.
    /// Wrapped in Arc for cheap cloning during source-fallback recursion.
    in_memory_modules: Arc<HashMap<String, InMemoryModuleInfo>>,
    /// When true, all module resolution uses the in-memory registry only.
    /// Disk fallbacks (`.ast`, `.cmj`, `.cmi` probes) are skipped entirely.
    in_process_mode: bool,
    /// Source file paths for on-demand lazy type checking in `--in-process` mode.
    /// When `find_pers_struct` can't find a module in the cache and this map
    /// has its source path, the module is type-checked from source on the fly.
    /// Wrapped in Arc for cheap cloning during source-fallback recursion.
    source_fallback_paths: Arc<HashMap<String, PathBuf>>,
    /// Current depth of source-fallback recursion. Each `typecheck_source_signature`
    /// call increments this. Used to prevent stack overflow from deep dependency chains.
    source_fallback_depth: usize,
    /// Portable module cache for `--in-process` builds. These contain self-contained
    /// type graphs that are internalized into the current TypeContext on first access
    /// via `find_pers_struct`. Populated by `from_registry()`.
    portable_cache: HashMap<String, Arc<PortablePersStruct>>,
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
            nopervasives: false,
            compiling_module: None,
            renamed_sig_cache: HashMap::new(),
            in_memory_modules: Arc::new(HashMap::new()),
            in_process_mode: false,
            source_fallback_paths: Arc::new(HashMap::new()),
            source_fallback_depth: 0,
            portable_cache: HashMap::new(),
        }
    }

    /// Create a PersistentEnv seeded from a ModuleRegistry.
    ///
    /// Each worker in a parallel wave gets its own PersistentEnv via this
    /// constructor. The registry's cached modules and metadata are cloned
    /// into the env so that `find_pers_struct` can resolve dependencies
    /// without disk I/O. The env is automatically in in-process mode.
    pub fn from_registry(registry: &ModuleRegistry) -> Self {
        // Store portable modules for lazy internalization. They will be
        // deserialized into the current TypeContext on first access via
        // find_pers_struct, which has a TypeContext parameter.
        let portable_cache = registry.cached_modules.clone();
        PersistentEnv {
            cache: HashMap::new(),
            load_path: Vec::new(),
            alias_prefix_rewrites: registry.alias_rewrites.clone(),
            open_modules: Vec::new(),
            jsx_version: None,
            nopervasives: false,
            compiling_module: None,
            renamed_sig_cache: HashMap::new(),
            in_memory_modules: Arc::new(registry.module_info.clone()),
            in_process_mode: true,
            source_fallback_paths: Arc::new(registry.source_fallback_paths.clone()),
            source_fallback_depth: 0,
            portable_cache,
        }
    }

    /// Extract the diff produced by this compilation: the newly-registered
    /// PersStruct and any new alias rewrites that weren't in the original
    /// registry. Used to update the shared ModuleRegistry after compilation.
    /// Extract the diff produced by this compilation: the newly-registered
    /// PersStruct (serialized to portable form) and any new alias rewrites.
    /// Must be called while the TypeContext is still alive so the type graph
    /// can be serialized.
    pub fn extract_module_update(
        &self,
        module_name: &str,
        original_alias_count: usize,
        ctx: &TypeContext<'_>,
    ) -> (Option<PortablePersStruct>, HashMap<String, Path>) {
        let portable = self
            .cache
            .get(module_name)
            .and_then(|opt| opt.as_ref())
            .map(|ps| portable_types::serialize_pers_struct(ps, ctx));
        // New alias rewrites are any beyond what was in the original registry
        let new_rewrites = if self.alias_prefix_rewrites.len() > original_alias_count {
            self.alias_prefix_rewrites.clone()
        } else {
            HashMap::new()
        };
        (portable, new_rewrites)
    }

    /// Extract all currently-cached modules as portable structs, plus the full
    /// alias-rewrite table. Used by the playground to hydrate the shared
    /// registry after a compile so subsequent compiles can reuse the typed
    /// stdlib instead of re-loading every dependency from source.
    pub fn extract_all_cached_modules(
        &self,
        ctx: &TypeContext<'_>,
    ) -> (HashMap<String, PortablePersStruct>, HashMap<String, Path>) {
        let portables: HashMap<String, PortablePersStruct> = self
            .cache
            .iter()
            .filter_map(|(name, opt)| {
                opt.as_ref()
                    .map(|ps| (name.clone(), portable_types::serialize_pers_struct(ps, ctx)))
            })
            .collect();
        (portables, self.alias_prefix_rewrites.clone())
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

    pub fn set_nopervasives(&mut self, nopervasives: bool) {
        self.nopervasives = nopervasives;
    }

    pub fn set_compiling_module(&mut self, module_name: Option<String>) {
        self.compiling_module = module_name;
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
        // Check cache first (already internalized)
        if let Some(cache_key) = resolve_first_char_case_key(&self.cache, name) {
            return self.cache.get(&cache_key).and_then(|opt| opt.as_ref());
        }

        // Check portable cache (from ModuleRegistry, needs internalization).
        // The portable PersStruct was already finalized (path substitution done)
        // before serialization. We only need to:
        // 1. Internalize types into the current TypeContext
        // 2. Collect alias rewrites
        // 3. Register types by stamp (without cascading alias resolution)
        if let Some(portable_key) = resolve_first_char_case_key(&self.portable_cache, name) {
            let portable = self.portable_cache.remove(&portable_key)?;
            let ps = portable_types::internalize_pers_struct(&portable, ctx);
            let module_path = Path::Pident(Ident::create_persistent(&portable_key));
            let effective_module_path = self
                .alias_prefix_rewrites
                .get(&portable_key)
                .cloned()
                .unwrap_or_else(|| module_path.clone());
            collect_alias_rewrites(
                &ps.ps_sig,
                &effective_module_path,
                &mut self.alias_prefix_rewrites,
            );
            register_types_by_stamp_recursive(
                &ModuleType::MtySignature(ps.ps_sig.clone()),
                ctx,
            );
            self.cache.insert(portable_key.clone(), Some(ps));
            return self.cache.get(&portable_key).and_then(|opt| opt.as_ref());
        }

        // Insert a placeholder before loading so recursive lookups of the same
        // module fail cleanly instead of recursing indefinitely.
        let load_name = resolve_first_char_case_key(&self.source_fallback_paths, name)
            .unwrap_or_else(|| name.to_string());
        self.cache.insert(load_name.clone(), None);

        // Try to load from disk
        let result = self.load_module(&load_name, ctx);
        self.cache.insert(load_name.clone(), result);
        self.cache.get(&load_name).and_then(|opt| opt.as_ref())
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

    /// Resolve a module name back to the source path recorded in its sibling
    /// binary AST when available. This mirrors the source-path lookup OCaml's
    /// backend uses indirectly through cmj/package metadata when computing JS
    /// import paths.
    pub fn resolve_module_source_path(&self, name: &str) -> Option<PathBuf> {
        // Check in-memory registry first (--in-process mode)
        if let Some(info_key) = resolve_first_char_case_key(&self.in_memory_modules, name)
            && let Some(info) = self.in_memory_modules.get(&info_key)
        {
            return Some(info.source_path.clone());
        }

        // In in-process mode, the registry is authoritative — no disk fallback.
        if self.in_process_mode {
            return None;
        }

        for ext in ["ast", "iast"] {
            let ast_filename = format!("{name}.{ext}");
            if let Some(ast_path) = self.find_in_path_uncap(&ast_filename) {
                if let Some(source_path) = Self::read_ast_source_path(FsPath::new(&ast_path)) {
                    return Some(source_path);
                }
            }
        }

        self.cache
            .get(name)
            .and_then(|loaded| loaded.as_ref())
            .and_then(|ps| {
                let path = PathBuf::from(&ps.ps_filename);
                match path.extension().and_then(|ext| ext.to_str()) {
                    Some("res" | "resi" | "ml" | "mli") => Some(path),
                    _ => None,
                }
            })
    }

    /// Resolve a module name to its companion `.cmj` path when present.
    pub fn resolve_module_cmj_path(&self, name: &str) -> Option<PathBuf> {
        let cmj_filename = format!("{name}.cmj");
        self.find_in_path_uncap(&cmj_filename).map(PathBuf::from)
    }

    /// Read the `pure` flag recorded in a module's `.cmj` metadata.
    /// In `--in-process` mode, returns the in-memory purity flag instead.
    pub fn module_cmj_is_pure(&self, name: &str) -> Option<bool> {
        // Check in-memory registry first (--in-process mode)
        if let Some(info_key) = resolve_first_char_case_key(&self.in_memory_modules, name)
            && let Some(info) = self.in_memory_modules.get(&info_key)
        {
            return Some(info.is_pure);
        }

        // In in-process mode, the registry is authoritative — no disk fallback.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        read_cmj_pure(&path)
    }

    /// Read closed constant exports recorded in a module's `.cmj` metadata.
    ///
    /// This matches OCaml's `Js_cmj_format.query_by_name` behavior under the
    /// default `cross_module_inline = false` mode, where only
    /// `null`/`undefined`/`true`/`false` closed lambdas are kept for
    /// cross-module inlining.
    pub fn module_cmj_export_constants(
        &self,
        name: &str,
    ) -> Option<HashMap<String, CmjExportConstant>> {
        // Check in-memory registry first (--in-process mode)
        if let Some(info_key) = resolve_first_char_case_key(&self.in_memory_modules, name)
            && let Some(info) = self.in_memory_modules.get(&info_key)
        {
            return Some(info.cmj_export_constants.clone());
        }

        // In in-process mode, the registry is authoritative — no disk fallback.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        read_cmj_export_constants(&path)
    }

    fn read_source_latin1(path: &FsPath) -> Option<String> {
        // On WASM, route through the virtual filesystem since there's no
        // real disk to read from. Fall back to fs::read for native targets.
        #[cfg(target_arch = "wasm32")]
        {
            if let Some(content) = crate::wasm_vfs::read_file(&path.to_string_lossy()) {
                return Some(content);
            }
        }
        let bytes = fs::read(path).ok()?;
        Some(bytes.iter().map(|&b| b as char).collect())
    }

    /// Maximum recursion depth for source-fallback type checking.
    /// Each level compiles a dependency from source. Deep chains indicate
    /// many transitive deps being loaded on demand.
    const MAX_SOURCE_FALLBACK_DEPTH: usize = 15;

    fn typecheck_source_signature<'a>(
        &self,
        source_path: &FsPath,
        ctx: &'a TypeContext<'a>,
    ) -> Option<(Signature, PersistentEnv)> {
        if self.source_fallback_depth >= Self::MAX_SOURCE_FALLBACK_DEPTH {
            return None;
        }

        let filename = source_path.to_string_lossy().into_owned();
        let source = Self::read_source_latin1(source_path)?;
        // Create a lightweight fallback env instead of cloning the entire PersistentEnv.
        // Share the read-only maps but start with an empty cache (deps loaded on demand).
        // Copy only the current cache placeholders (None entries that prevent infinite recursion).
        let placeholders: HashMap<String, Option<PersStruct>> = self
            .cache
            .iter()
            .filter(|(_, v)| v.is_none())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let mut fallback_pers = PersistentEnv {
            cache: placeholders,
            load_path: self.load_path.clone(),
            alias_prefix_rewrites: self.alias_prefix_rewrites.clone(),
            open_modules: self.open_modules.clone(),
            jsx_version: self.jsx_version,
            nopervasives: self.nopervasives,
            compiling_module: self.compiling_module.clone(),
            renamed_sig_cache: HashMap::new(),
            in_memory_modules: self.in_memory_modules.clone(),
            in_process_mode: self.in_process_mode,
            source_fallback_paths: self.source_fallback_paths.clone(),
            source_fallback_depth: self.source_fallback_depth + 1,
            portable_cache: self.portable_cache.clone(),
        };
        let mut env = initial_env(ctx);
        let open_modules = fallback_pers.open_modules.clone();
        let nopervasives = fallback_pers.nopervasives;
        let compiling_module = fallback_pers.compiling_module.clone();
        load_pervasives(
            &mut fallback_pers,
            &mut env,
            ctx,
            &open_modules,
            nopervasives,
            compiling_module.as_deref(),
        );

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
            let signature =
                crate::binary_ast::ppx::rewrite_signature(&signature, parser.arena_mut()).ok()?;

            let mut tctx = TypeCheckContext::new(ctx, parser.arena());
            tctx.set_persistent_env(fallback_pers);
            let typed_signature =
                transl_signature(&mut tctx, &env, parser.arena(), &signature).ok()?;
            let fallback_pers = tctx.persistent_env.take()?;
            let decl_signature =
                crate::types::typemod::decl_signature_from_typed_signature(&typed_signature, parser.arena());
            let typed_module_type = TypedModuleType {
                mty_desc: TypedModuleTypeDesc::Tmty_signature(typed_signature),
                mty_type: crate::types::decl::ModuleType::MtySignature(decl_signature),
                mty_env: crate::types::typedtree::EnvRef(0),
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
        let structure =
            crate::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut()).ok()?;

        let mut tctx = TypeCheckContext::new(ctx, parser.arena());
        tctx.set_persistent_env(fallback_pers);
        let (typed_structure, final_env) =
            type_structure(&mut tctx, &env, parser.arena(), &structure).ok()?;

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

        let debug_source_fallback =
            std::env::var_os("RUST_DEBUG_PERSISTENT_SOURCE_FALLBACK").is_some();
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
        // In in-process mode, the registry is the sole source of truth.
        // No CMI files, no source fallback. If a dependency isn't in the
        // registry, it means the build graph is wrong.
        // Exception: nopervasives modules (runtime bootstrap) may load from
        // CMI since they're being pre-compiled into the registry.
        if self.in_process_mode && !self.nopervasives {
            // When a source fallback path is registered, allow lazy loading
            // from source (used by the playground to compile stdlib on demand).
            // Otherwise, the registry is the sole source of truth — missing
            // dependencies indicate a dependency-graph bug in the build system.
            if let Some(source_key) = resolve_first_char_case_key(&self.source_fallback_paths, name) {
                return self.load_module_from_source_path_fallback(&source_key, ctx);
            }
            log::debug!(
                "in-process module '{}' not found in registry; alias rewrite: {:?}",
                name,
                self.alias_prefix_rewrites.get(name)
            );
            return None;
        }

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

    /// Load a module by type-checking its source file directly in `--in-process` mode.
    ///
    /// Unlike `load_module_from_source_fallback` (which reads `.ast` files),
    /// this reads the source `.res`/`.resi` file path from `source_fallback_paths`.
    fn load_module_from_source_path_fallback<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext<'a>,
    ) -> Option<PersStruct> {
        let source_path = self.source_fallback_paths.get(name)?.clone();

        // The source_fallback_paths already points to the preferred file
        // (.resi if it exists, .res otherwise), set by rewatch when
        // registering the paths.
        let (signature, fallback_pers) =
            self.typecheck_source_signature(&source_path, ctx)?;

        // Merge any modules the fallback discovered
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
            source_path.to_string_lossy().into_owned(),
            ctx,
        ))
    }

    /// Read a module's signature from CMI without applying path substitution.
    /// Used for interface constraint propagation (moregen) where we need raw
    /// Pident paths that match the implementation's local paths.
    /// In OCaml, ps_sig retains raw Pident paths; path substitution happens
    /// lazily in components_of_module_maker, not on ps_sig.
    pub fn read_raw_sig<'a>(&mut self, name: &str, ctx: &'a TypeContext<'a>) -> Option<Signature> {
        if self.in_process_mode {
            if let Some(loaded) = self.cache.get(name).and_then(|loaded| loaded.as_ref()) {
                return Some(loaded.ps_sig.clone());
            }

            let loaded = self.find_pers_struct(name, ctx)?;
            return Some(loaded.ps_sig.clone());
        }

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
    /// Get the renamed signature for a module, cached.
    /// Matches OCaml's `ps_sig = lazy (Subst.signature Subst.identity sign)`.
    /// In OCaml, accessing a module's components cascades into forcing ps_sig
    /// for all dependent modules (via components_of_module_maker → scrape_alias
    /// → find_module). We match this by triggering ALL registered module renames
    /// when any module is first accessed.
    pub fn get_renamed_sig<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext<'a>,
    ) -> Option<Signature> {
        // Check TypeContext cache first (populated by trigger_module_sig_rename)
        if let Some(cached) = ctx.renamed_module_sigs.borrow().get(name) {
            return Some(cached.clone());
        }
        // Check local cache
        if let Some(cached) = self.renamed_sig_cache.get(name) {
            return Some(cached.clone());
        }
        // Do the rename
        let ps = self.find_pers_struct(name, ctx)?;
        let renamed = rename_bound_idents_in_sig(&ps.ps_sig, ctx);
        self.renamed_sig_cache
            .insert(name.to_string(), renamed.clone());
        ctx.renamed_module_sigs
            .borrow_mut()
            .insert(name.to_string(), renamed.clone());
        Some(renamed)
    }

    pub fn open_module<'a>(&mut self, name: &str, env: &mut Env, ctx: &'a TypeContext<'a>) -> bool {
        // Don't rename at open time — OCaml's ps_sig is only forced later
        // when find_module is called from normalize_path during type expansion.
        let ps = match self.find_pers_struct(name, ctx) {
            Some(ps) => ps,
            None => return false,
        };
        let module_path = Path::Pident(Ident::create_persistent(name));
        add_signature_to_env_with_options(&ps.ps_sig, &module_path, env, ctx, true, false, true);
        true
    }

    /// Get a module's declaration using the raw (un-renamed) sig.
    /// Used during initial env setup where OCaml doesn't force ps_sig.
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

    /// Register a module's in-memory metadata for `--in-process` builds.
    ///
    /// This records the source path, purity, and runtime status so that
    /// `resolve_module_source_path`, `module_cmj_is_pure`, and runtime
    /// detection can resolve from memory instead of probing disk.
    pub fn register_in_memory_module(&mut self, name: &str, info: InMemoryModuleInfo) {
        Arc::make_mut(&mut self.in_memory_modules).insert(name.to_string(), info);
    }

    /// Register a module's signature directly into the cache for
    /// `--in-process` builds, bypassing `.cmi` loading from disk.
    ///
    /// `source_filename` is the source file path (e.g. `/path/to/Foo.res`),
    /// used as `ps_filename` for downstream lookups.
    pub fn register_in_memory_signature<'a>(
        &mut self,
        name: &str,
        signature: Signature,
        source_filename: &str,
        ctx: &'a TypeContext<'a>,
    ) {
        let ps = self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            source_filename.to_string(),
            ctx,
        );
        self.cache.insert(name.to_string(), Some(ps));
        // Invalidate any cached renamed sig so it gets re-derived
        self.renamed_sig_cache.remove(name);
    }

    /// Register a namespace module's alias signature directly into the cache
    /// for `--in-process` builds, without requiring a `TypeContext`.
    ///
    /// A namespace module is a synthetic module that re-exports submodules via
    /// aliases. For example, namespace `MyApp` with modules `Foo`, `Bar` produces:
    /// ```text
    /// module Foo = Foo-MyApp
    /// module Bar = Bar-MyApp
    /// ```
    ///
    /// `module_aliases` is a list of `(short_name, internal_name)` pairs, e.g.
    /// `[("Foo", "Foo-MyApp"), ("Bar", "Bar-MyApp")]`.
    ///
    /// This method bypasses `finalize_loaded_signature` since namespace alias
    /// signatures contain no type declarations—only `SigModule` items with
    /// `MtyAlias`—so type path substitution is a no-op.
    pub fn register_namespace_in_memory(
        &mut self,
        namespace_name: &str,
        module_aliases: &[(String, String)],
    ) {
        let mut sig_items: Signature = Vec::with_capacity(module_aliases.len());
        for (short_name, internal_name) in module_aliases {
            sig_items.push(SignatureItem::SigModule(
                Ident::create_persistent(short_name.as_str()),
                ModuleDeclaration {
                    md_type: ModuleType::MtyAlias(
                        AliasPresence::MtaPresent,
                        Path::Pident(Ident::create_persistent(internal_name.as_str())),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::location::Location::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ));
        }

        // Record alias rewrites (e.g., "Foo-MyApp" → Pdot(Pident("MyApp"), "Foo"))
        let module_path = Path::Pident(Ident::create_persistent(namespace_name));
        collect_alias_rewrites(&sig_items, &module_path, &mut self.alias_prefix_rewrites);

        let ps = PersStruct {
            ps_name: namespace_name.to_string(),
            ps_sig: sig_items,
            ps_filename: format!("{}.mlmap", namespace_name),
        };
        self.cache.insert(namespace_name.to_string(), Some(ps));
        self.renamed_sig_cache.remove(namespace_name);
    }

    /// Look up in-memory module info by name.
    pub fn get_in_memory_module(&self, name: &str) -> Option<&InMemoryModuleInfo> {
        self.in_memory_modules.get(name)
    }

    /// Check whether a module is registered in the in-memory registry.
    pub fn has_in_memory_module(&self, name: &str) -> bool {
        self.in_memory_modules.contains_key(name)
    }

    /// Enable in-process mode: all module resolution uses the in-memory
    /// registry only, with no disk fallbacks for `.ast`, `.cmj`, or `.cmi`.
    pub fn set_in_process_mode(&mut self, enabled: bool) {
        self.in_process_mode = enabled;
    }

    /// Whether in-process mode is active.
    pub fn is_in_process_mode(&self) -> bool {
        self.in_process_mode
    }
}

/// Recursively register all type declarations from a signature
/// into the type context's global store for alias expansion.
///
/// Rename all bound idents in a signature, matching OCaml's
/// `Subst.signature Subst.identity` which calls `rename_bound_idents`.
/// This gives each signature item a fresh stamp even with identity substitution.
fn rename_bound_idents_in_sig<'a>(sig_items: &Signature, ctx: &'a TypeContext<'a>) -> Signature {
    sig_items
        .iter()
        .map(|item| match item {
            SignatureItem::SigValue(id, desc) => {
                SignatureItem::SigValue(ctx.rename_ident(id), desc.clone())
            }
            SignatureItem::SigType(id, decl, rec_status) => {
                SignatureItem::SigType(ctx.rename_ident(id), decl.clone(), *rec_status)
            }
            SignatureItem::SigTypext(id, ext, ext_status) => {
                SignatureItem::SigTypext(ctx.rename_ident(id), ext.clone(), *ext_status)
            }
            SignatureItem::SigModule(id, md, rec_status) => {
                SignatureItem::SigModule(ctx.rename_ident(id), md.clone(), *rec_status)
            }
            SignatureItem::SigModtype(id, mtd) => {
                SignatureItem::SigModtype(ctx.rename_ident(id), mtd.clone())
            }
            SignatureItem::SigClass => SignatureItem::SigClass,
            SignatureItem::SigClassType => SignatureItem::SigClassType,
        })
        .collect()
}

/// `module_path` is the path to the module containing this signature
/// (e.g., `Pident(Js)` or `Pdot(Pident(Js), "Promise")`).
/// `load_path` is used to resolve module aliases by loading CMI files.
fn register_sig_types_recursive<'a>(
    sig: &Signature,
    module_path: &Path,
    ctx: &'a TypeContext<'a>,
    _load_path: &[PathBuf],
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
                        register_sig_types_recursive(sub_sig, &sub_path, ctx, _load_path);
                    }
                    // Match OCaml's lazy persistent-module behavior: don't eagerly
                    // load aliased CMIs here just to pre-register their nested types.
                    // Module-alias type lookup goes through module resolution later.
                    ModuleType::MtyAlias(_, _) => {}
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use tempfile::tempdir;

    #[test]
    fn in_process_ignores_bogus_cmi_on_load_path() {
        let tmp = tempdir().expect("failed to create tempdir");
        let load_path = tmp.path().join("lib").join("ocaml");
        std::fs::create_dir_all(&load_path).expect("failed to create load path");
        std::fs::write(load_path.join("Foo.cmi"), b"bogus cmi").expect("failed to write bogus cmi");

        let source_path = tmp.path().join("Foo.res");
        std::fs::write(&source_path, "let answer = 1\n").expect("failed to write source");

        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);

        let mut env = PersistentEnv::new();
        env.set_in_process_mode(true);
        env.set_nopervasives(true);
        env.add_load_path(load_path);
        Arc::make_mut(&mut env.source_fallback_paths).insert("Foo".to_string(), source_path);

        let loaded = env
            .find_pers_struct("Foo", &type_ctx)
            .expect("expected source fallback to load Foo");
        assert_eq!(loaded.ps_name, "Foo");

        let raw_sig = env
            .read_raw_sig("Foo", &type_ctx)
            .expect("expected raw signature from in-memory source load");
        assert!(!raw_sig.is_empty());
    }
}

fn read_marshaled_cmj(path: &FsPath) -> Option<OcamlValue> {
    const CMJ_DIGEST_LEN: usize = 16;

    let bytes = fs::read(path).ok()?;
    let marshaled = bytes.get(CMJ_DIGEST_LEN..)?;
    let mut reader = MarshalReader::new();
    reader.read_from_bytes(marshaled).ok()
}

pub fn read_cmj_module_metadata(path: &FsPath) -> Option<CmjModuleMetadata> {
    let value = read_marshaled_cmj(path)?;
    Some(CmjModuleMetadata {
        is_pure: decode_cmj_pure(&value)?,
        export_constants: decode_cmj_export_constants(&value)?,
    })
}

fn read_cmj_pure(path: &FsPath) -> Option<bool> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_pure(&value)
}

fn decode_cmj_pure(value: &OcamlValue) -> Option<bool> {
    let (_, fields) = value.as_block_opt()?;
    fields.get(1).map(|field| field.as_bool())
}

fn read_cmj_export_constants(path: &FsPath) -> Option<HashMap<String, CmjExportConstant>> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_export_constants(&value)
}

fn decode_cmj_export_constants(value: &OcamlValue) -> Option<HashMap<String, CmjExportConstant>> {
    let (_, fields) = value.as_block_opt()?;
    let values_field = fields.first()?;
    let (_, values) = values_field.as_block_opt()?;
    let mut exports = HashMap::new();

    for entry in values {
        let Some((_, entry_fields)) = entry.as_block_opt() else {
            continue;
        };
        if entry_fields.len() != 3 {
            continue;
        }
        let name = match &entry_fields[0] {
            OcamlValue::String(name) => name.clone(),
            _ => continue,
        };
        let Some(constant) = decode_cmj_persistent_closed_constant(&entry_fields[2]) else {
            continue;
        };
        exports.insert(name, constant);
    }

    Some(exports)
}

fn decode_cmj_persistent_closed_constant(value: &OcamlValue) -> Option<CmjExportConstant> {
    let lam = value.as_option()?;
    let (tag, fields) = lam.as_block_opt()?;
    if tag != 2 || fields.len() != 1 {
        return None;
    }
    decode_cmj_constant(&fields[0])
}

fn decode_cmj_constant(value: &OcamlValue) -> Option<CmjExportConstant> {
    match value {
        OcamlValue::Int(0) => Some(CmjExportConstant::Null),
        OcamlValue::Int(1) => Some(CmjExportConstant::Bool(true)),
        OcamlValue::Int(2) => Some(CmjExportConstant::Bool(false)),
        OcamlValue::Block(tag, fields) if *tag == 0 && fields.len() == 1 => Some(
            CmjExportConstant::Undefined {
                is_unit: fields[0].as_bool(),
            },
        ),
        _ => None,
    }
}

/// This is the core of `open_signature` from OCaml's `env.ml`.
/// For each signature item, we add the appropriate binding to the environment.
///
/// Uses "opened" add methods so that these bindings do NOT shadow existing
/// Recursively register all types from a module type (and sub-modules) by stamp.
/// This ensures that types referenced in function signatures can be expanded
/// during type unification, even when the type comes from a deeply nested module.
pub(crate) fn register_types_by_stamp_recursive(md_type: &ModuleType, ctx: &TypeContext<'_>) {
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
                    maps.type_name_map
                        .insert(id.name().to_string(), qualified_path);
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

fn insert_type_subst_path(maps: &mut SubstMaps, old_id: &Ident, new_id: &Ident) {
    let new_path = Path::pident(new_id.clone());
    if old_id.stamp() != 0 {
        maps.type_stamp_map.insert(old_id.stamp(), new_path);
    } else {
        maps.type_name_map
            .insert(old_id.name().to_string(), new_path);
    }
}

fn insert_module_subst_path(maps: &mut SubstMaps, old_id: &Ident, new_id: &Ident) {
    let new_path = Path::pident(new_id.clone());
    if old_id.stamp() != 0 {
        maps.module_stamp_map.insert(old_id.stamp(), new_path);
    } else {
        maps.module_name_map
            .insert(old_id.name().to_string(), new_path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_belt_map_string_empty_as_closed_undefined_constant_from_cmj() {
        let mut env = PersistentEnv::new();
        env.add_load_path(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("repo root")
                .join("packages")
                .join("@rescript")
                .join("runtime")
                .join("lib")
                .join("ocaml"),
        );

        let exports = env
            .module_cmj_export_constants("Belt_MapString")
            .expect("expected runtime cmj exports");

        assert_eq!(
            exports.get("empty"),
            Some(&CmjExportConstant::Undefined { is_unit: false })
        );
        assert!(!exports.contains_key("isEmpty"));
    }
}

fn merge_subst_maps(parent: &SubstMaps, child: &SubstMaps) -> SubstMaps {
    let mut merged = parent.clone();
    merged.type_stamp_map.extend(child.type_stamp_map.clone());
    merged.type_name_map.extend(child.type_name_map.clone());
    merged
        .module_stamp_map
        .extend(child.module_stamp_map.clone());
    merged.module_name_map.extend(child.module_name_map.clone());
    merged
}

fn freshen_module_type_bound_idents_with_maps(
    module_type: &mut ModuleType,
    maps: &SubstMaps,
    ctx: &TypeContext<'_>,
) {
    match module_type {
        ModuleType::MtyIdent(path) | ModuleType::MtyAlias(_, path) => {
            if !maps.is_empty() {
                *path = substitute_type_path(
                    path,
                    &maps.type_stamp_map,
                    &maps.type_name_map,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                );
            }
        }
        ModuleType::MtySignature(sig) => {
            freshen_signature_bound_idents_with_maps(sig, maps, ctx);
        }
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            if let Some(param_type) = param_type.as_mut() {
                freshen_module_type_bound_idents_with_maps(param_type, maps, ctx);
            }
            let old_param = param.clone();
            let new_param = ctx.rename_ident(&old_param);
            *param = new_param.clone();
            let mut param_maps = SubstMaps::default();
            insert_module_subst_path(&mut param_maps, &old_param, &new_param);
            let result_maps = merge_subst_maps(maps, &param_maps);
            freshen_module_type_bound_idents_with_maps(result, &result_maps, ctx);
        }
    }
}

fn freshen_signature_bound_idents_with_maps(
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext<'_>,
) {
    if !maps.is_empty() {
        substitute_type_paths_in_sig_with_maps(sig_items, maps, ctx);
        substitute_sig_decl_paths_in_place_with_maps(sig_items, maps);
    }

    let mut local_maps = SubstMaps::default();

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigTypext(id, _, _) => {
                *id = ctx.rename_ident(id);
            }
            SignatureItem::SigType(id, _, _) | SignatureItem::SigModtype(id, _) => {
                let old_id = id.clone();
                let new_id = ctx.rename_ident(&old_id);
                insert_type_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigModule(id, _, _) => {
                let old_id = id.clone();
                let new_id = ctx.rename_ident(&old_id);
                insert_module_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    if !local_maps.is_empty() {
        substitute_type_paths_in_sig_with_maps(sig_items, &local_maps, ctx);
        substitute_sig_decl_paths_in_place_with_maps(sig_items, &local_maps);
    }

    let combined_maps = merge_subst_maps(maps, &local_maps);

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                freshen_module_type_bound_idents_with_maps(&mut md.md_type, &combined_maps, ctx);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    freshen_module_type_bound_idents_with_maps(module_type, &combined_maps, ctx);
                }
            }
            _ => {}
        }
    }
}

pub(crate) fn freshen_signature_bound_idents(
    sig_items: &mut [SignatureItem],
    ctx: &TypeContext<'_>,
) {
    freshen_signature_bound_idents_with_maps(sig_items, &SubstMaps::default(), ctx);
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
    // Deep-copy the module type first to avoid modifying shared type expressions
    // in-place. OCaml's lazy `components_of_module_maker` + `Subst.type_declaration`
    // naturally deep-copies; we must do it explicitly.
    *child_mty = crate::types::typecore::copy_lookup_module_type_for_subst(child_mty, ctx);
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

/// Rewrite Tconstr paths in a signature using a direct stamp → path map.
/// Used to remap CMI idents to implementation idents before moregen linking.
pub fn substitute_type_paths_in_sig_with_stamp_map(
    sig_items: &[SignatureItem],
    stamp_map: &HashMap<i32, Path>,
    ctx: &TypeContext<'_>,
) {
    if stamp_map.is_empty() {
        return;
    }
    let empty: HashMap<String, Path> = HashMap::new();
    let mut visited = HashSet::new();
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(
                    desc.val_type,
                    stamp_map,
                    &empty,
                    &HashMap::new(),
                    &HashMap::new(),
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    substitute_type_expr_path(
                        param,
                        stamp_map,
                        &empty,
                        &HashMap::new(),
                        &HashMap::new(),
                        ctx,
                        &mut visited,
                    );
                }
                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(
                        manifest,
                        stamp_map,
                        &empty,
                        &HashMap::new(),
                        &HashMap::new(),
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
/// Public wrapper for substitute_type_expr_path.
pub fn substitute_type_expr_path_pub(
    ty_ref: TypeExprRef,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &HashMap<i32, Path>,
    module_name_map: &HashMap<String, Path>,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    substitute_type_expr_path(
        ty_ref,
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        ctx,
        visited,
    );
}

fn substitute_type_expr_path(
    initial_ty_ref: TypeExprRef,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &HashMap<i32, Path>,
    module_name_map: &HashMap<String, Path>,
    ctx: &TypeContext<'_>,
    visited: &mut HashSet<usize>,
) {
    // Use an explicit work stack instead of recursion to avoid stack overflow
    // on large type graphs (e.g., objects with hundreds of fields create deep
    // Tfield chains, and Tlink chains from unification can be thousands deep).
    let mut work_stack = vec![initial_ty_ref];

    while let Some(ty_ref) = work_stack.pop() {
        if !visited.insert(ty_ref.0) {
            continue; // Already visited (cycle detection)
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

                // Push type arguments onto work stack
                for &arg in args {
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tarrow { arg, ret, .. } => {
                work_stack.push(arg.typ);
                work_stack.push(*ret);
            }
            TypeDesc::Ttuple(types) => {
                for &t in types {
                    work_stack.push(t);
                }
            }
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => {
                work_stack.push(*t);
            }
            TypeDesc::Tpoly { body, vars } => {
                work_stack.push(*body);
                for &v in vars {
                    work_stack.push(v);
                }
            }
            TypeDesc::Tobject { fields, .. } => {
                work_stack.push(*fields);
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                work_stack.push(*typ);
                work_stack.push(*rest);
            }
            TypeDesc::Tvariant(row) => {
                work_stack.push(row.row_more);
                for field in &row.row_fields {
                    match &field.1 {
                        crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                            work_stack.push(*t);
                        }
                        crate::types::type_expr::RowField::Reither { types, .. } => {
                            for &t in types {
                                work_stack.push(t);
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
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
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

pub fn rewrite_type_expr_by_path_prefix_pub(
    ty_ref: TypeExprRef,
    old_prefix: &Path,
    new_prefix: &Path,
    ctx: &TypeContext<'_>,
) {
    let mut visited = HashSet::new();
    rewrite_type_expr_by_path_prefix(ty_ref, old_prefix, new_prefix, ctx, &mut visited);
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
                    desc.val_type,
                    old_prefix,
                    new_prefix,
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_by_path_prefix(
                        param,
                        old_prefix,
                        new_prefix,
                        ctx,
                        &mut visited,
                    );
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_by_path_prefix(
                        manifest,
                        old_prefix,
                        new_prefix,
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
                                        rewrite_type_expr_by_path_prefix(
                                            arg,
                                            old_prefix,
                                            new_prefix,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_type_expr_by_path_prefix(
                                            lbl.ld_type,
                                            old_prefix,
                                            new_prefix,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_by_path_prefix(
                                    res,
                                    old_prefix,
                                    new_prefix,
                                    ctx,
                                    &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_type_expr_by_path_prefix(
                                lbl.ld_type,
                                old_prefix,
                                new_prefix,
                                ctx,
                                &mut visited,
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
                                        rewrite_deep_prefix_expr(
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
                                rewrite_deep_prefix_expr(
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
                            rewrite_deep_prefix_expr(
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
                    rewrite_deep_prefix_expr(param, old_name, new_prefix, ctx, &mut visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            rewrite_deep_prefix_expr(arg, old_name, new_prefix, ctx, &mut visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            rewrite_deep_prefix_expr(
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
    add_signature_to_env_with_options(sig_items, module_path, env, ctx, as_opened, true, true);
}

fn add_signature_to_env_with_options(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext<'_>,
    as_opened: bool,
    apply_path_subst: bool,
    register_loaded_types: bool,
) {
    // Apply path substitution: rewrite Tconstr paths from internal
    // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
    // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
    if apply_path_subst {
        substitute_type_paths_in_sig(sig_items, module_path, ctx);
    }

    fn collect_target_constr_nodes(
        ctx: &TypeContext<'_>,
        initial_ty: TypeExprRef,
        out: &mut Vec<(TypeExprRef, String)>,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        // Use an explicit work stack to avoid stack overflow on large type
        // graphs (e.g., objects with hundreds of fields create deep Tfield chains).
        let mut work_stack = vec![initial_ty];

        while let Some(raw_ty) = work_stack.pop() {
            let ty = ctx.repr(raw_ty);
            if !seen.insert(ty) {
                continue;
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
                        work_stack.push(*arg);
                    }
                }
                TypeDesc::Tarrow { arg, ret, .. } => {
                    work_stack.push(arg.typ);
                    work_stack.push(*ret);
                }
                TypeDesc::Ttuple(items) => {
                    for item in items {
                        work_stack.push(*item);
                    }
                }
                TypeDesc::Tobject { fields, name } => {
                    work_stack.push(*fields);
                    if let Some((_path, args)) = name {
                        for arg in args {
                            work_stack.push(*arg);
                        }
                    }
                }
                TypeDesc::Tfield { typ, rest, .. } => {
                    work_stack.push(*typ);
                    work_stack.push(*rest);
                }
                TypeDesc::Tpoly { body, vars } => {
                    work_stack.push(*body);
                    for var in vars {
                        work_stack.push(*var);
                    }
                }
                TypeDesc::Tvariant(row) => {
                    work_stack.push(row.row_more);
                    for (_label, field) in &row.row_fields {
                        match field {
                            crate::types::type_expr::RowField::Rpresent(Some(ty)) => {
                                work_stack.push(*ty);
                            }
                            crate::types::type_expr::RowField::Reither { types, .. } => {
                                for ty in types {
                                    work_stack.push(*ty);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                TypeDesc::Tpackage { args, .. } => {
                    for arg in args {
                        work_stack.push(*arg);
                    }
                }
                TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                    work_stack.push(*target);
                }
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
            }
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

    // OCaml's components_of_module_maker uses a selective position counter:
    // only value-bearing items (non-primitive values, modules, extension constructors)
    // get runtime field positions. Types and module types are skipped.
    let mut pos: i32 = 0;
    for item in sig_items.iter() {
        let slot_path =
            |name: &str, p: i32| Path::Pdot(Box::new(module_path.clone()), name.to_string(), p);
        match item {
            SignatureItem::SigValue(id, desc) => {
                // Add value binding with qualified path
                let mut desc = desc.clone();
                desc.val_path = Some(slot_path(id.name(), pos));
                // OCaml: only increment pos for non-primitive values
                if !matches!(desc.val_kind, crate::types::decl::ValueKind::ValPrim(_)) {
                    pos += 1;
                }
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
                if register_loaded_types {
                    ctx.register_type_decl(id.name(), decl.clone());
                    // Register by stamp for types from CMI modules (non-zero stamp)
                    if id.stamp() != 0 {
                        ctx.register_type_decl_by_stamp(id.stamp(), decl.clone());
                    }
                }

                // Also add constructors and labels from this type
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs) => {
                        let type_path = Path::pdot(module_path.clone(), id.name());
                        let num_consts = constrs
                            .iter()
                            .filter(|c| matches!(c.cd_args, crate::types::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty()))
                            .count() as i32;
                        let num_nonconsts = constrs.len() as i32 - num_consts;
                        let mut const_idx = 0i32;
                        let mut nonconst_idx = 0i32;

                        for cd in constrs {
                            let is_constant = matches!(cd.cd_args, crate::types::decl::ConstructorArguments::CstrTuple(ref args) if args.is_empty());

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
                                    let ty_res = ctx
                                        .new_constr(inline_path, inlined_decl.type_params.clone());
                                    for (pos, ld) in labels.iter().enumerate() {
                                        let label_desc = LabelDescription {
                                            lbl_name: ld.ld_id.name().to_string(),
                                            lbl_res: ty_res,
                                            lbl_arg:
                                                crate::types::ctype::remap_label_type_to_params(
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
                                            lbl_loc: ld.ld_loc.clone(),
                                            lbl_attributes: ld.ld_attributes.clone(),
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
                                lbl_loc: ld.ld_loc.clone(),
                                lbl_attributes: ld.ld_attributes.clone(),
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
                let access_path = slot_path(id.name(), pos);
                pos += 1;
                md.md_path = Some(access_path.clone());
                // Rewrite module-type paths against the opened signature.
                // Some CMI signatures use hidden self-alias heads (e.g. `ArrayExt!`)
                // that are not directly resolvable from the current environment.
                // Normalize those to the qualified access path.
                let normalize_hidden_alias_path = |path: Path| -> Path {
                    fn go(
                        path: Path,
                        module_path: &Path,
                        module_name: &str,
                        access_path: &Path,
                    ) -> Path {
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
                if register_loaded_types {
                    register_types_by_stamp_recursive(&md.md_type, ctx);
                }
            }
            SignatureItem::SigModtype(id, mtd) => {
                if as_opened {
                    env.add_opened_modtype(id.clone(), mtd.clone());
                } else {
                    env.add_modtype(id.clone(), mtd.clone());
                }
            }
            SignatureItem::SigTypext(id, ext, _status) => {
                let ext_slot = pos;
                pos += 1; // Extension constructors occupy runtime slots
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
                    cstr_tag: ConstructorTag::CstrExtension(slot_path(id.name(), ext_slot)),
                    cstr_consts: -1,
                    cstr_nonconsts: -1,
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
