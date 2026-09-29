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
use std::sync::{Arc, Mutex, RwLock};

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::driver::{
    CompilerOptions, experimental_let_unwrap_for_structure, jsx_version_for_structure,
    load_pervasives, normalize_signature_types,
};
use crate::ident::Ident;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_constant::{Constant as LambdaConstant, PointerInfo, StringDelim};
use crate::lambda::lam_primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalFfiKind, ExternalFfiSpec, ExternalModuleName, ExternalReturnWrapper, ExternalSpec,
    Mutable, Primitive,
};
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda, PrimInfo,
    TagInfo,
};
use crate::location::Location;
use crate::parser::{Parser, jsx_ppx, module};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, ConstructorDescription, ConstructorKind, LabelDescription, ModtypeDeclaration,
    ModuleDeclaration, ModuleType, RecStatus, Signature, SignatureItem, TypeKind,
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
    let swapped = if first.is_ascii_uppercase() {
        first.to_ascii_lowercase()
    } else if first.is_ascii_lowercase() {
        first.to_ascii_uppercase()
    } else {
        return None;
    };
    let mut variant = String::with_capacity(name.len());
    variant.push(swapped);
    variant.push_str(rest);
    Some(variant)
}

fn resolve_first_char_case_key<'a, V>(map: &'a HashMap<String, V>, name: &str) -> Option<&'a str> {
    if let Some((key, _)) = map.get_key_value(name) {
        return Some(key.as_str());
    }
    let variant = first_char_case_variant(name)?;
    map.get_key_value(&variant).map(|(key, _)| key.as_str())
}

#[derive(Debug)]
struct SharedRegistryMap<V> {
    inner: Arc<RwLock<HashMap<String, V>>>,
}

impl<V> Clone for SharedRegistryMap<V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<V> Default for SharedRegistryMap<V> {
    fn default() -> Self {
        Self {
            inner: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl<V> SharedRegistryMap<V> {
    fn insert(&self, key: String, value: V) {
        self.inner.write().unwrap().insert(key, value);
    }

    fn remove(&self, key: &str) {
        self.inner.write().unwrap().remove(key);
    }

    fn retain(&self, mut keep: impl FnMut(&String, &mut V) -> bool) {
        self.inner
            .write()
            .unwrap()
            .retain(|key, value| keep(key, value));
    }

    fn replace(&self, values: HashMap<String, V>) {
        *self.inner.write().unwrap() = values;
    }

    fn len(&self) -> usize {
        self.inner.read().unwrap().len()
    }

    fn contains_key(&self, key: &str) -> bool {
        self.inner.read().unwrap().contains_key(key)
    }
}

impl<V: Clone> SharedRegistryMap<V> {
    fn get_cloned(&self, key: &str) -> Option<V> {
        self.inner.read().unwrap().get(key).cloned()
    }

    fn get_case_cloned(&self, name: &str) -> Option<(String, V)> {
        let map = self.inner.read().unwrap();
        if let Some((key, value)) = map.get_key_value(name) {
            return Some((key.clone(), value.clone()));
        }
        let variant = first_char_case_variant(name)?;
        map.get_key_value(&variant)
            .map(|(key, value)| (key.clone(), value.clone()))
    }

    fn extend(&self, values: HashMap<String, V>) {
        self.inner.write().unwrap().extend(values);
    }

    fn clone_map(&self) -> HashMap<String, V> {
        self.inner.read().unwrap().clone()
    }
}

impl<V> SharedRegistryMap<V> {
    fn get_case_with<R>(&self, name: &str, mut f: impl FnMut(&str, &V) -> R) -> Option<R> {
        let map = self.inner.read().unwrap();
        if let Some((key, value)) = map.get_key_value(name) {
            return Some(f(key, value));
        }
        let variant = first_char_case_variant(name)?;
        map.get_key_value(&variant)
            .map(|(key, value)| f(key, value))
    }

    fn for_each(&self, mut f: impl FnMut(&String, &V)) {
        let map = self.inner.read().unwrap();
        for (key, value) in map.iter() {
            f(key, value);
        }
    }
}

/// A cached persistent module structure.
#[derive(Debug, Clone)]
pub struct PersStruct {
    /// Module name
    pub ps_name: String,
    /// Loaded signature
    pub ps_sig: Arc<Signature>,
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
pub enum CmjExportArity {
    Single(Arity),
    Submodule(Vec<Arity>),
}

#[derive(Debug, Clone)]
pub struct CmjModuleMetadata {
    pub is_pure: bool,
    pub export_constants: HashMap<String, CmjExportConstant>,
    pub hoisted_exports: Vec<crate::lambda::HoistedExport>,
    pub package_spec: CmjPackageSpec,
    pub file_case: CmjFileCase,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CmjPackageName {
    Empty,
    Runtime,
    Normal(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmjPackageModuleSystem {
    CommonJs,
    EsModule,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CmjPackageInfo {
    pub module_system: CmjPackageModuleSystem,
    pub path: String,
    pub suffix: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CmjPackageSpec {
    pub name: CmjPackageName,
    pub module_systems: Vec<CmjPackageInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmjFileCase {
    Upper,
    Little,
}

#[derive(Debug, Clone)]
pub struct CmjModuleImportInfo {
    pub package_path: PathBuf,
    pub package_spec: CmjPackageSpec,
    pub file_case: CmjFileCase,
}

/// In-memory module metadata for the `--in-process` build mode.
///
/// When a module is registered in the in-memory registry, these fields
/// replace the disk-based lookups that normally read `.ast` (source path),
/// `.cmj` (purity), and `.cmi` (interface).
#[derive(Debug, Clone)]
pub struct InMemoryModuleInfo {
    /// Source file path (replaces `.ast` source-path lookup)
    pub source_path: Arc<PathBuf>,
    /// Whether the module is side-effect free (replaces `.cmj` purity lookup)
    pub is_pure: bool,
    /// Closed constant exports (replaces `.cmj` constant lookup)
    pub cmj_export_constants: Arc<HashMap<String, CmjExportConstant>>,
    /// Arity metadata for exports (replaces `.cmj` arity lookup)
    pub cmj_export_arities: Arc<HashMap<String, CmjExportArity>>,
    /// Flat hoisted-export path metadata (replaces `.cmj` lookup).
    pub cmj_hoisted_exports: Arc<Vec<crate::lambda::HoistedExport>>,
    /// Whether this module belongs to `@rescript/runtime`
    pub is_runtime: bool,
    /// Package name used by JS import rebasing in `--in-process` builds.
    pub package_name: Option<Arc<str>>,
    /// Package root used to turn a source path into a package-relative JS path.
    pub package_root: Option<Arc<PathBuf>>,
    /// JS suffix for this package's emitted output.
    pub js_output_suffix: Option<Arc<str>>,
}

impl InMemoryModuleInfo {
    pub fn new(
        source_path: PathBuf,
        is_pure: bool,
        cmj_export_constants: HashMap<String, CmjExportConstant>,
        is_runtime: bool,
    ) -> Self {
        Self {
            source_path: Arc::new(source_path),
            is_pure,
            cmj_export_constants: Arc::new(cmj_export_constants),
            cmj_export_arities: Arc::new(HashMap::new()),
            cmj_hoisted_exports: Arc::new(Vec::new()),
            is_runtime,
            package_name: None,
            package_root: None,
            js_output_suffix: None,
        }
    }

    pub fn with_cmj_export_arities(
        mut self,
        cmj_export_arities: HashMap<String, CmjExportArity>,
    ) -> Self {
        self.cmj_export_arities = Arc::new(cmj_export_arities);
        self
    }

    pub fn with_cmj_hoisted_exports(
        mut self,
        hoisted_exports: Vec<crate::lambda::HoistedExport>,
    ) -> Self {
        self.cmj_hoisted_exports = Arc::new(hoisted_exports);
        self
    }

    pub fn with_package(
        mut self,
        package_name: String,
        package_root: PathBuf,
        js_output_suffix: Option<String>,
    ) -> Self {
        self.package_name = Some(Arc::from(package_name.into_boxed_str()));
        self.package_root = Some(Arc::new(package_root));
        self.js_output_suffix = js_output_suffix.map(|suffix| Arc::from(suffix.into_boxed_str()));
        self
    }
}

#[derive(Clone)]
struct AliasPrefixRewrites {
    base: SharedRegistryMap<Path>,
    local: HashMap<String, Path>,
}

impl AliasPrefixRewrites {
    fn new() -> Self {
        Self {
            base: SharedRegistryMap::default(),
            local: HashMap::new(),
        }
    }

    fn from_base(base: SharedRegistryMap<Path>, local: HashMap<String, Path>) -> Self {
        Self { base, local }
    }

    fn get(&self, key: &str) -> Option<Path> {
        self.local
            .get(key)
            .cloned()
            .or_else(|| self.base.get_cloned(key))
    }

    fn insert_if_absent(&mut self, key: String, value: Path) {
        if !self.local.contains_key(&key) && !self.base.contains_key(&key) {
            self.local.insert(key, value);
        }
    }

    fn extend_missing(&mut self, rewrites: HashMap<String, Path>) {
        for (key, value) in rewrites {
            self.insert_if_absent(key, value);
        }
    }

    fn local_clone(&self) -> HashMap<String, Path> {
        self.local.clone()
    }

    fn to_hash_map(&self) -> HashMap<String, Path> {
        let mut rewrites = self.base.clone_map();
        rewrites.extend(self.local.clone());
        rewrites
    }

    fn flattened_alias_heads_for_path(&self, qualified_path: &Path) -> Vec<String> {
        let mut heads = Vec::new();
        self.base.for_each(|flat_head, qualified| {
            if !self.local.contains_key(flat_head) && qualified.same(qualified_path) {
                heads.push(flat_head.clone());
            }
        });
        for (flat_head, qualified) in self.local.iter() {
            if qualified.same(qualified_path) {
                heads.push(flat_head.clone());
            }
        }
        heads
    }
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
    cached_modules: SharedRegistryMap<Arc<PortablePersStruct>>,
    /// Module metadata (source paths, purity, runtime status).
    module_info: SharedRegistryMap<InMemoryModuleInfo>,
    /// Alias prefix rewrites (flattened_name -> qualified_path).
    alias_rewrites: SharedRegistryMap<Path>,
    /// Source file paths for ALL modules, including those not yet compiled.
    /// Used for on-demand source-based type checking when a module is needed
    /// as an implicit dependency (e.g., via `-open Pervasives`) but hasn't
    /// been compiled yet in the current wave.
    source_fallback_paths: SharedRegistryMap<PathBuf>,
    local_cached_modules: HashMap<String, Arc<PortablePersStruct>>,
    local_module_info: HashMap<String, InMemoryModuleInfo>,
    local_alias_rewrites: HashMap<String, Path>,
    local_source_fallback_paths: HashMap<String, PathBuf>,
    write_to_local: bool,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn for_worker_snapshot(&self) -> Self {
        if crate::perf_counters::enabled() {
            let shared_entries = self.cached_modules.len()
                + self.module_info.len()
                + self.alias_rewrites.len()
                + self.source_fallback_paths.len();
            crate::perf_counters::record_module_registry_snapshot(
                shared_entries,
                self.local_cached_modules.len(),
                self.local_module_info.len(),
                self.local_alias_rewrites.len(),
                self.local_source_fallback_paths.len(),
            );
        }
        let mut snapshot = self.clone();
        snapshot.write_to_local = true;
        snapshot
    }

    pub fn alias_rewrite_len(&self) -> usize {
        self.alias_rewrites.len() + self.local_alias_rewrites.len()
    }

    pub fn has_cached_module(&self, name: &str) -> bool {
        self.local_cached_modules.contains_key(name) || self.cached_modules.contains_key(name)
    }

    pub fn is_empty(&self) -> bool {
        self.local_cached_modules.is_empty() && self.cached_modules.len() == 0
    }

    pub fn module_info_is_runtime(&self, name: &str) -> bool {
        self.local_module_info
            .get(name)
            .map(|info| info.is_runtime)
            .or_else(|| {
                self.module_info
                    .get_cloned(name)
                    .map(|info| info.is_runtime)
            })
            .unwrap_or(false)
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
        let mut new_alias_rewrites = HashMap::new();
        collect_alias_rewrites(&sig_items, &module_path, &mut new_alias_rewrites);
        self.extend_alias_rewrites(new_alias_rewrites);

        // Namespace signatures contain only MtyAlias entries (no TypeExprRefs),
        // so the portable type graph is empty.
        let fingerprint = portable_types::compute_type_graph_fingerprint_pub(&[], &sig_items);
        let portable = PortablePersStruct {
            ps_name: namespace_name.to_string(),
            ps_filename: format!("{}.mlmap", namespace_name),
            ps_sig: sig_items,
            raw_ps_sig: None,
            cmi_longident_names: Vec::new(),
            type_graph: portable_types::PortableTypeGraph {
                entries: Vec::new(),
                variant_layouts: Vec::new(),
            },
            raw_type_graph: None,
            fingerprint,
        };
        self.insert_cached_module(namespace_name.to_string(), Arc::new(portable));
    }

    /// Remove a module from the registry (for deleted/renamed modules).
    /// Purges cached signature, module info, source fallback, and any alias
    /// rewrites that reference this module.
    pub fn purge_module(&mut self, name: &str) {
        self.cached_modules.remove(name);
        self.local_cached_modules.remove(name);
        self.module_info.remove(name);
        self.local_module_info.remove(name);
        self.source_fallback_paths.remove(name);
        self.local_source_fallback_paths.remove(name);
        // Remove alias rewrites that point to this module
        self.alias_rewrites.retain(|key, _| key != name);
        self.local_alias_rewrites.retain(|key, _| key != name);
    }

    /// Store a compiled module's finalized PersStruct and metadata.
    pub fn register_module(
        &mut self,
        name: &str,
        portable: PortablePersStruct,
        info: InMemoryModuleInfo,
        new_alias_rewrites: HashMap<String, Path>,
    ) {
        self.register_module_arc(name, Arc::new(portable), info, new_alias_rewrites);
    }

    /// Store a compiled module's finalized PersStruct and metadata from an
    /// already shared portable signature.
    pub fn register_module_arc(
        &mut self,
        name: &str,
        portable: Arc<PortablePersStruct>,
        info: InMemoryModuleInfo,
        new_alias_rewrites: HashMap<String, Path>,
    ) {
        self.insert_cached_module(name.to_string(), portable);
        self.insert_module_info(name.to_string(), info);
        self.extend_alias_rewrites(new_alias_rewrites);
    }

    fn insert_cached_module(&mut self, name: String, portable: Arc<PortablePersStruct>) {
        if self.write_to_local {
            self.local_cached_modules.insert(name, portable);
        } else {
            self.cached_modules.insert(name, portable);
        }
    }

    pub fn insert_module_info(&mut self, name: String, info: InMemoryModuleInfo) {
        if self.write_to_local {
            self.local_module_info.insert(name, info);
        } else {
            self.module_info.insert(name, info);
        }
    }

    pub fn extend_alias_rewrites(&mut self, new_alias_rewrites: HashMap<String, Path>) {
        if self.write_to_local {
            self.local_alias_rewrites.extend(new_alias_rewrites);
        } else {
            self.alias_rewrites.extend(new_alias_rewrites);
        }
    }

    pub fn insert_source_fallback_path(&mut self, name: String, path: PathBuf) {
        if self.write_to_local {
            self.local_source_fallback_paths.insert(name, path);
        } else {
            self.source_fallback_paths.insert(name, path);
        }
    }

    pub fn set_source_fallback_paths(&mut self, paths: HashMap<String, PathBuf>) {
        if self.write_to_local {
            self.local_source_fallback_paths = paths;
        } else {
            self.source_fallback_paths.replace(paths);
            self.local_source_fallback_paths.clear();
        }
    }
}

/// Private loader-view state. A PersistentEnv clone shares this coarse snapshot
/// until its first write; mutable overrides and alias preparation never leak to
/// sibling views. Type graphs and the existing shared registry caches are not
/// copied here. This is container ownership, not a new component/force cache.
#[derive(Clone)]
struct ResolutionView {
    /// Alias prefix rewrites: flattened_name -> qualified_path.
    /// Populated when loading a CMI that has MtyAlias submodules
    /// (e.g., Stdlib.cmi has module JSON = Stdlib_JSON, so we record
    /// "Stdlib_JSON" → Pdot(Pident("Stdlib"), "JSON")).
    alias_prefix_rewrites: AliasPrefixRewrites,
    /// The module currently being compiled, used to skip self-opens.
    compiling_module: Option<String>,
    in_memory_module_overrides: HashMap<String, InMemoryModuleInfo>,
    source_fallback_path_overrides: HashMap<String, PathBuf>,
    portable_cache_overrides: HashMap<String, Arc<PortablePersStruct>>,
    /// Modules hidden from this worker environment. Used when the current
    /// module's transient signature must be removed before raw/JS compilation
    /// without copy-on-writing the shared in-process registry maps.
    hidden_modules: HashSet<String>,
    /// Cache entries whose alias-rewrite side effects have already been
    /// applied to this PersistentEnv. OCaml's persistent structures keep lazy
    /// module components in the environment table (`compiler/ml/env.ml:711-746,
    /// 1516-1605`); Rust shares loaded structures across env clones, so each
    /// env still has to rebuild its local flattened-alias table when it first
    /// observes a cached signature.
    prepared_cached_alias_rewrites: HashSet<String>,
}

/// Persistent environment for module loading.
#[derive(Clone)]
pub struct PersistentEnv {
    /// Cache of loaded modules: module_name -> PersStruct (or None if loading failed).
    /// OCaml keeps persistent structures in a mutable table
    /// (`compiler/ml/env.ml:711-746`); make PersistentEnv clones share this
    /// table so TypeContext lookups do not re-internalize and re-copy
    /// signatures on every persistent-module access.
    cache: Arc<Mutex<HashMap<String, Option<Arc<PersStruct>>>>>,
    /// Load path: list of directories to search for .cmi files
    load_path: Arc<Vec<PathBuf>>,
    /// Display spelling for each load-path entry.
    /// OCaml stores `ps.ps_filename` through `Consistbl.check` at
    /// compiler/ml/env.ml:630-638 and prints it at compiler/ml/env.ml:2110-2119.
    /// Keep lookup paths normalized while preserving the load-path spelling
    /// that should appear in diagnostics.
    load_path_display: Arc<Vec<PathBuf>>,
    /// Additional modules opened implicitly from `-open` flags.
    open_modules: Arc<Vec<String>>,
    /// Default JSX version from CLI flags, if any.
    jsx_version: Option<i32>,
    /// Whether the current compilation uses `-nopervasives`.
    nopervasives: bool,
    /// Cache of renamed signatures (matching OCaml's lazy Subst.signature).
    /// Each module's signature is renamed once and cached here.
    renamed_sig_cache: Arc<HashMap<String, Arc<crate::types::context::DeferredRenamedSig>>>,
    /// In-memory module registry for `--in-process` builds.
    /// When a module is registered here, its metadata (source path, purity)
    /// is resolved from memory instead of from `.ast`/`.cmj` files on disk.
    /// Shared through the build registry so worker snapshots do not clone it.
    in_memory_modules: SharedRegistryMap<InMemoryModuleInfo>,
    /// When true, all module resolution uses the in-memory registry only.
    /// Disk fallbacks (`.ast`, `.cmj`, `.cmi` probes) are skipped entirely.
    in_process_mode: bool,
    /// Source file paths for on-demand lazy type checking in `--in-process` mode.
    /// When `find_pers_struct` can't find a module in the cache and this map
    /// has its source path, the module is type-checked from source on the fly.
    /// Shared through the build registry so worker snapshots do not clone it.
    source_fallback_paths: SharedRegistryMap<PathBuf>,
    /// Current depth of source-fallback recursion. Each `typecheck_source_signature`
    /// call increments this. Used to prevent stack overflow from deep dependency chains.
    source_fallback_depth: usize,
    /// Portable module cache for `--in-process` builds. These contain self-contained
    /// type graphs that are internalized into the current TypeContext on first access
    /// via `find_pers_struct`. Populated by `from_registry()`.
    portable_cache: SharedRegistryMap<Arc<PortablePersStruct>>,
    /// First persistent-loader error observed through any clone of this env.
    last_error: Arc<Mutex<Option<PersistentEnvError>>>,
    /// Consistency table for imported CMI digests, matching OCaml `Consistbl`.
    crc_units: Arc<Mutex<HashMap<String, (Vec<u8>, String)>>>,
    view: Arc<ResolutionView>,
}

/// Errors reported by OCaml's `Env` persistent interface loader.
#[derive(Debug, Clone)]
pub enum PersistentEnvError {
    /// A discovered compiled interface could not be decoded.
    InterfaceRead {
        /// User-facing CMI reader message, with the display path retained.
        message: String,
    },
    /// The file found for one module contains a different compiled unit.
    IllegalRenaming {
        /// Module name requested by the lookup.
        expected: String,
        /// Unit name stored inside the loaded `.cmi`.
        actual: String,
        /// Path to the mismatched `.cmi`.
        filename: String,
    },
    /// Two loaded CMIs disagree on the digest for an imported interface.
    InconsistentImport {
        /// Interface whose digest assumptions differ.
        name: String,
        /// File that made the first assumption.
        source1: String,
        /// File that made the conflicting assumption.
        source2: String,
    },
}

fn should_register_lazy_raw_sig(name: &str, alias_rewrites: &AliasPrefixRewrites) -> bool {
    // OCaml compiler/ml/env.ml:1516-1518 reaches alias backing signatures only
    // through `scrape_alias` and the component tables built by env.ml:1530-1578.
    // Rust keeps raw signatures for the same known backing unit heads. Ordinary
    // same-name aliases already resolve through their component table and do
    // not need to be added to the ps_sig rename set.
    alias_rewrites
        .get(name)
        .is_some_and(|qualified_path| qualified_path.head_name() != name)
}

impl PersistentEnv {
    fn view_mut(&mut self) -> &mut ResolutionView {
        Arc::make_mut(&mut self.view)
    }

    /// Create a new persistent environment with no load paths.
    pub fn new() -> Self {
        PersistentEnv {
            cache: Arc::new(Mutex::new(HashMap::new())),
            load_path: Arc::new(Vec::new()),
            load_path_display: Arc::new(Vec::new()),
            open_modules: Arc::new(Vec::new()),
            jsx_version: None,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: SharedRegistryMap::default(),
            in_process_mode: false,
            source_fallback_paths: SharedRegistryMap::default(),
            source_fallback_depth: 0,
            portable_cache: SharedRegistryMap::default(),
            last_error: Arc::new(Mutex::new(None)),
            crc_units: Arc::new(Mutex::new(HashMap::new())),
            view: Arc::new(ResolutionView {
                alias_prefix_rewrites: AliasPrefixRewrites::new(),
                compiling_module: None,
                in_memory_module_overrides: HashMap::new(),
                source_fallback_path_overrides: HashMap::new(),
                portable_cache_overrides: HashMap::new(),
                hidden_modules: HashSet::new(),
                prepared_cached_alias_rewrites: HashSet::new(),
            }),
        }
    }

    /// Create a PersistentEnv seeded from a ModuleRegistry with a fresh
    /// internalization cache.
    pub fn from_registry(registry: &ModuleRegistry) -> Self {
        PersistentEnv {
            cache: Arc::new(Mutex::new(HashMap::new())),
            load_path: Arc::new(Vec::new()),
            load_path_display: Arc::new(Vec::new()),
            open_modules: Arc::new(Vec::new()),
            jsx_version: None,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: registry.module_info.clone(),
            in_process_mode: true,
            source_fallback_paths: registry.source_fallback_paths.clone(),
            source_fallback_depth: 0,
            portable_cache: registry.cached_modules.clone(),
            last_error: Arc::new(Mutex::new(None)),
            crc_units: Arc::new(Mutex::new(HashMap::new())),
            view: Arc::new(ResolutionView {
                alias_prefix_rewrites: AliasPrefixRewrites::from_base(
                    registry.alias_rewrites.clone(),
                    registry.local_alias_rewrites.clone(),
                ),
                compiling_module: None,
                in_memory_module_overrides: registry.local_module_info.clone(),
                source_fallback_path_overrides: registry.local_source_fallback_paths.clone(),
                portable_cache_overrides: registry.local_cached_modules.clone(),
                hidden_modules: HashSet::new(),
                prepared_cached_alias_rewrites: HashSet::new(),
            }),
        }
    }

    fn record_error(&self, error: PersistentEnvError) {
        let mut last_error = self.last_error.lock().unwrap();
        if last_error.is_none() {
            *last_error = Some(error);
        }
    }

    pub fn last_error(&self) -> Option<PersistentEnvError> {
        self.last_error.lock().unwrap().clone()
    }

    fn validate_cmi_name(&self, expected: &str, actual: &str, filename: &str) -> bool {
        if actual == expected {
            true
        } else {
            self.record_error(PersistentEnvError::IllegalRenaming {
                expected: expected.to_string(),
                actual: actual.to_string(),
                filename: filename.to_string(),
            });
            false
        }
    }

    fn check_cmi_consistency(
        &self,
        crcs: &[(String, Option<Vec<u8>>)],
        unit_name: &str,
        filename: &str,
    ) -> bool {
        let mut crc_units = self.crc_units.lock().unwrap();
        for (name, crc) in crcs {
            if name == unit_name {
                continue;
            }
            let Some(crc) = crc else {
                continue;
            };
            match crc_units.get(name) {
                Some((old_crc, old_source)) if old_crc != crc => {
                    self.record_error(PersistentEnvError::InconsistentImport {
                        name: name.clone(),
                        source1: old_source.clone(),
                        source2: filename.to_string(),
                    });
                    return false;
                }
                Some(_) => {}
                None => {
                    crc_units.insert(name.clone(), (crc.clone(), filename.to_string()));
                }
            }
        }
        true
    }

    fn cache_lookup(&self, name: &str) -> Option<Option<Arc<PersStruct>>> {
        self.cache_lookup_entry(name).map(|(_, value)| value)
    }

    fn cache_lookup_entry(&self, name: &str) -> Option<(String, Option<Arc<PersStruct>>)> {
        if self.view.hidden_modules.contains(name) {
            return Some((name.to_string(), None));
        }
        let cache = self.cache.lock().unwrap();
        let cache_key = resolve_first_char_case_key(&cache, name)?;
        cache
            .get(cache_key)
            .cloned()
            .map(|value| (cache_key.to_string(), value))
    }

    fn cache_contains_key(&self, name: &str) -> bool {
        let cache = self.cache.lock().unwrap();
        resolve_first_char_case_key(&cache, name).is_some()
    }

    fn cache_insert(&self, name: String, value: Option<Arc<PersStruct>>) {
        self.cache.lock().unwrap().insert(name, value);
    }

    fn cache_remove(&self, name: &str) {
        self.cache.lock().unwrap().remove(name);
    }

    fn in_memory_info(&self, name: &str) -> Option<InMemoryModuleInfo> {
        if let Some(key) = resolve_first_char_case_key(&self.view.in_memory_module_overrides, name)
        {
            if self.view.hidden_modules.contains(key) {
                return None;
            }
            return self.view.in_memory_module_overrides.get(key).cloned();
        }
        let (key, info) = self.in_memory_modules.get_case_cloned(name)?;
        if self.view.hidden_modules.contains(&key) {
            return None;
        }
        Some(info)
    }

    fn in_memory_info_with<R>(
        &self,
        name: &str,
        mut f: impl FnMut(&InMemoryModuleInfo) -> R,
    ) -> Option<R> {
        if let Some(key) = resolve_first_char_case_key(&self.view.in_memory_module_overrides, name)
        {
            if self.view.hidden_modules.contains(key) {
                return None;
            }
            return self
                .view
                .in_memory_module_overrides
                .get(key)
                .map(|info| f(info));
        }
        self.in_memory_modules
            .get_case_with(name, |key, info| {
                if self.view.hidden_modules.contains(key) {
                    None
                } else {
                    Some(f(info))
                }
            })
            .flatten()
    }

    fn portable_cache_entry(&self, name: &str) -> Option<(String, Arc<PortablePersStruct>)> {
        if let Some(key) = resolve_first_char_case_key(&self.view.portable_cache_overrides, name) {
            return self
                .view
                .portable_cache_overrides
                .get(key)
                .cloned()
                .map(|portable| (key.to_string(), portable));
        }
        self.portable_cache.get_case_cloned(name)
    }

    fn source_fallback_path_entry(&self, name: &str) -> Option<(String, PathBuf)> {
        if let Some(key) =
            resolve_first_char_case_key(&self.view.source_fallback_path_overrides, name)
        {
            return self
                .view
                .source_fallback_path_overrides
                .get(key)
                .cloned()
                .map(|path| (key.to_string(), path));
        }
        self.source_fallback_paths.get_case_cloned(name)
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
        _original_alias_count: usize,
        ctx: &TypeContext,
        arena: Option<&crate::parse_arena::ParseArena>,
    ) -> (Option<PortablePersStruct>, HashMap<String, Path>) {
        let portable = self
            .cache_lookup(module_name)
            .and_then(|opt| opt)
            .map(|ps| portable_types::serialize_pers_struct(ps.as_ref(), ctx, arena));
        (portable, self.view.alias_prefix_rewrites.local_clone())
    }

    /// Extract all currently-cached modules as portable structs, plus the full
    /// alias-rewrite table. Used by the playground to hydrate the shared
    /// registry after a compile so subsequent compiles can reuse the typed
    /// stdlib instead of re-loading every dependency from source.
    pub fn extract_all_cached_modules(
        &self,
        ctx: &TypeContext,
        arena: Option<&crate::parse_arena::ParseArena>,
    ) -> (HashMap<String, PortablePersStruct>, HashMap<String, Path>) {
        let portables: HashMap<String, PortablePersStruct> = self
            .cache
            .lock()
            .unwrap()
            .iter()
            .filter_map(|(name, opt)| {
                opt.as_ref().map(|ps| {
                    (
                        name.clone(),
                        portable_types::serialize_pers_struct(ps, ctx, arena),
                    )
                })
            })
            .collect();
        (portables, self.view.alias_prefix_rewrites.to_hash_map())
    }

    /// Set the load path (list of directories to search for .cmi files).
    pub fn set_load_path(&mut self, paths: Vec<PathBuf>) {
        self.set_load_path_with_display(paths.clone(), paths);
    }

    /// Set the load path from lists shared with other compilations.
    pub fn set_load_path_shared(&mut self, paths: Arc<Vec<PathBuf>>, display_paths: Arc<Vec<PathBuf>>) {
        debug_assert_eq!(paths.len(), display_paths.len());
        self.load_path = paths;
        self.load_path_display = display_paths;
    }

    pub fn set_load_path_with_display(&mut self, paths: Vec<PathBuf>, display_paths: Vec<PathBuf>) {
        debug_assert_eq!(paths.len(), display_paths.len());
        self.load_path = Arc::new(paths);
        self.load_path_display = Arc::new(display_paths);
    }

    pub fn set_open_modules(&mut self, open_modules: Vec<String>) {
        self.open_modules = Arc::new(open_modules);
    }

    pub fn set_jsx_version(&mut self, jsx_version: Option<i32>) {
        self.jsx_version = jsx_version;
    }

    pub fn set_nopervasives(&mut self, nopervasives: bool) {
        self.nopervasives = nopervasives;
    }

    pub fn set_compiling_module(&mut self, module_name: Option<String>) {
        self.view_mut().compiling_module = module_name;
    }

    pub fn is_compiling_module(&self, module_name: &str) -> bool {
        self.view
            .compiling_module
            .as_deref()
            .is_some_and(|compiling| compiling == module_name)
    }

    /// Add a directory to the load path.
    pub fn add_load_path(&mut self, path: PathBuf) {
        if !self.load_path.contains(&path) {
            Arc::make_mut(&mut self.load_path).push(path);
            Arc::make_mut(&mut self.load_path_display)
                .push(self.load_path.last().cloned().unwrap_or_default());
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
        self.view
            .alias_prefix_rewrites
            .flattened_alias_heads_for_path(qualified_path)
    }

    pub fn qualified_alias_path_for_flattened_head(&self, flat_head: &str) -> Option<Path> {
        self.view.alias_prefix_rewrites.get(flat_head)
    }

    pub fn has_known_module_without_loading(&self, name: &str) -> bool {
        // OCaml compiler/ml/env.ml:1058-1062 checks a persistent unit without
        // forcing its signature when `lookup_module ~load:false` only needs to
        // know that the unit exists. Keep this as an availability probe so
        // namespace alias resolution can avoid consuming `Subst.signature`
        // stamps just to test a flattened compile-unit name.
        self.cache_contains_key(name)
            || self.portable_cache.contains_key(name)
            || self.in_memory_modules.contains_key(name)
            || self.source_fallback_paths.contains_key(name)
            || (!self.in_process_mode && self.find_in_path_uncap(&format!("{name}.cmi")).is_some())
    }

    /// Find and load a module by name.
    /// Returns the cached signature, or None if the module cannot be found.
    pub fn find_pers_struct<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext,
    ) -> Option<Arc<PersStruct>> {
        if ctx.in_store_build() {
            // Preparing a module is an effect on this compilation; later users
            // of the shared data replay it (`StoreEffect::PreparePers`).
            ctx.record_store_effect(crate::types::context::StoreEffect::PreparePers(name.into()));
            return ctx.suspend_store_build(|| self.find_pers_struct(name, ctx));
        }
        let debug_pers = crate::debug_flags::debug_pers_struct();
        if debug_pers {
            eprintln!("[pers] find {name}");
        }
        // Check cache first (already internalized)
        if let Some((cache_key, cached)) = self.cache_lookup_entry(name) {
            if debug_pers {
                eprintln!(
                    "[pers] cache {name} key={cache_key} hit={}",
                    cached.is_some()
                );
            }
            if let Some(ps) = cached.as_ref() {
                self.prepare_cached_pers_struct(&cache_key, ps, ctx);
            } else if self.in_process_mode
                && !self.view.hidden_modules.contains(&cache_key)
                && (self.portable_cache_entry(name).is_some()
                    || self.in_memory_info(name).is_some())
            {
                // OCaml overwrites the persistent table with `Some ps` when a
                // unit is saved/loaded (`compiler/ml/env.ml:642-645,
                // 687-688, 707-709, 1960-1977`). A shared in-process worker
                // cache can still hold an earlier miss placeholder while the
                // ModuleRegistry has since published the module, so discard
                // the stale negative entry and fall through to the registry.
                self.cache_remove(&cache_key);
            } else {
                return cached;
            }
            if cached.is_some() {
                return cached;
            }
        }

        // Check portable cache (from ModuleRegistry, needs internalization).
        // The portable PersStruct was already finalized (path substitution done)
        // before serialization. We only need to:
        // 1. Internalize types into the current TypeContext
        // 2. Collect alias rewrites
        // 3. Register types by stamp (without cascading alias resolution)
        if let Some((portable_key, portable)) = self.portable_cache_entry(name) {
            if debug_pers {
                eprintln!("[pers] portable {name} key={portable_key}");
            }
            if self.view.hidden_modules.contains(&portable_key) {
                return None;
            }
            ctx.poison_store_build_for("find_pers_struct:load");
            let ps = portable_types::internalize_pers_struct(portable, ctx);
            let module_path = Path::Pident(Ident::create_persistent(&portable_key));
            let effective_module_path = self
                .view
                .alias_prefix_rewrites
                .get(&portable_key)
                .unwrap_or_else(|| module_path.clone());
            collect_alias_rewrites(
                &ps.ps_sig,
                &effective_module_path,
                &mut self.view_mut().alias_prefix_rewrites,
            );
            let shared = ctx.thread_store().owns_signature(&ps.ps_sig);
            register_sig_types_recursive(&ps.ps_sig, &effective_module_path, ctx, shared);
            if !effective_module_path.same(&module_path) {
                register_sig_types_recursive(&ps.ps_sig, &module_path, ctx, shared);
            }
            register_types_by_stamp_in_signature_recursive(&ps.ps_sig, ctx, shared);
            if should_register_lazy_raw_sig(&portable_key, &self.view.alias_prefix_rewrites)
                && !ctx.has_raw_module_sig(&portable_key)
            {
                ctx.register_raw_module_sig(&portable_key, ps.ps_sig.clone());
            }
            self.view_mut()
                .prepared_cached_alias_rewrites
                .insert(portable_key.clone());
            self.cache_insert(portable_key, Some(ps.clone()));
            return Some(ps);
        }

        // OCaml compiler/core/res_compmisc.ml:48-66 filters the current unit
        // from implicit opens, and compiler/ml/typemod.ml:1732-1788 only saves
        // an implementation's inferred signature after type-checking it. In
        // --in-process source fallback, do not recursively type-check the current
        // implementation as if a persistent `.cmi` already existed; if an
        // interface was published above, the portable-cache branch has already
        // returned it.
        if self
            .view
            .compiling_module
            .as_deref()
            .is_some_and(|compiling| compiling == name)
        {
            return None;
        }

        // Insert a placeholder before loading so recursive lookups of the same
        // module fail cleanly instead of recursing indefinitely.
        let load_name = self
            .source_fallback_path_entry(name)
            .map(|(key, _)| key)
            .unwrap_or_else(|| name.to_string());
        if debug_pers {
            eprintln!("[pers] load {name} as {load_name}");
        }
        ctx.poison_store_build_for("find_pers_struct:disk");
        self.cache_insert(load_name.clone(), None);

        // Try to load from disk
        let result = self.load_module(&load_name, ctx).map(Arc::new);
        if let Some(ps) = result.as_ref() {
            self.view_mut()
                .prepared_cached_alias_rewrites
                .insert(load_name.clone());
            if should_register_lazy_raw_sig(&load_name, &self.view.alias_prefix_rewrites)
                && !ctx.has_raw_module_sig(&load_name)
            {
                ctx.register_raw_module_sig(&load_name, ps.ps_sig.clone());
            }
        }
        self.cache_insert(load_name, result.clone());
        result
    }

    fn prepare_cached_pers_struct(&mut self, cache_key: &str, ps: &PersStruct, ctx: &TypeContext) {
        if !self.view.prepared_cached_alias_rewrites.contains(cache_key) {
            ctx.poison_store_build_for("find_pers_struct:prepare");
            self.view_mut()
                .prepared_cached_alias_rewrites
                .insert(cache_key.to_string());
            let module_path = Path::Pident(Ident::create_persistent(cache_key));
            let effective_module_path = self
                .view
                .alias_prefix_rewrites
                .get(cache_key)
                .unwrap_or_else(|| module_path.clone());
            collect_alias_rewrites(
                &ps.ps_sig,
                &effective_module_path,
                &mut self.view_mut().alias_prefix_rewrites,
            );
            // Reusing a worker `TypeContext` clears short-name and stamp-keyed
            // declaration tables at unit boundaries because OCaml resets local
            // stamps per unit (`compiler/ml/predef.ml:447`). A cache hit still
            // has to re-install this module's declarations for the current unit;
            // OCaml exposes the same ps_sig through the persistent table
            // (`compiler/ml/env.ml:711-746`) without re-reading the CMI.
            let shared = ctx.thread_store().owns_signature(&ps.ps_sig);
            register_sig_types_recursive(&ps.ps_sig, &effective_module_path, ctx, shared);
            if !effective_module_path.same(&module_path) {
                register_sig_types_recursive(&ps.ps_sig, &module_path, ctx, shared);
            }
            register_types_by_stamp_in_signature_recursive(&ps.ps_sig, ctx, shared);
        }

        if should_register_lazy_raw_sig(cache_key, &self.view.alias_prefix_rewrites)
            && !ctx.has_raw_module_sig(cache_key)
        {
            ctx.register_raw_module_sig(cache_key, ps.ps_sig.clone());
        }
    }

    fn finalize_loaded_signature<'a>(
        &mut self,
        name: &str,
        ps_name: String,
        mut signature: Signature,
        ps_filename: String,
        ctx: &'a TypeContext,
    ) -> PersStruct {
        let module_path = Path::Pident(Ident::create_persistent(name));

        // Apply path substitution: rewrite Tconstr paths from internal
        // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
        substitute_type_paths_in_sig(&signature, &module_path, ctx);
        substitute_sig_decl_paths_in_place(&mut signature, &module_path);

        // Also recursively substitute paths in sub-module signatures.
        substitute_submodule_paths(&signature, &module_path, ctx);

        // OCaml compiler/ml/env.ml:677 and env.ml:1970 store `ps_sig` as
        // `Subst.signature Subst.identity sign`. Alias path rewriting is applied
        // lazily when env.ml:1513-1530 builds module components, not by rewriting
        // the cached persistent unit signature during load.

        let effective_module_path = self
            .view
            .alias_prefix_rewrites
            .get(name)
            .unwrap_or_else(|| module_path.clone());
        collect_alias_rewrites(
            &signature,
            &effective_module_path,
            &mut self.view_mut().alias_prefix_rewrites,
        );
        register_sig_types_recursive(&signature, &effective_module_path, ctx, false);
        let signature = Arc::new(signature);
        if should_register_lazy_raw_sig(name, &self.view.alias_prefix_rewrites) {
            ctx.register_raw_module_sig(name, signature.clone());
        }

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
        if let Some(source_path) =
            self.in_memory_info_with(name, |info| (*info.source_path).clone())
        {
            return Some(source_path);
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

        self.cache_lookup(name).and_then(|loaded| {
            loaded.and_then(|ps| {
                let path = PathBuf::from(&ps.ps_filename);
                match path.extension().and_then(|ext| ext.to_str()) {
                    Some("res" | "resi" | "ml" | "mli") => Some(path),
                    _ => None,
                }
            })
        })
    }

    /// Return in-memory package metadata for JS import rebasing.
    pub fn module_js_package_info(
        &self,
        name: &str,
    ) -> Option<(Arc<str>, Arc<PathBuf>, Option<Arc<str>>)> {
        self.in_memory_info_with(name, |info| {
            Some((
                info.package_name.clone()?,
                info.package_root.clone()?,
                info.js_output_suffix.clone(),
            ))
        })?
    }

    /// Return package metadata recorded in a dependency `.cmj`, matching
    /// `Lam_compile_env.get_package_path_from_cmj`.
    pub fn module_cmj_import_info(&self, name: &str) -> Option<CmjModuleImportInfo> {
        if let Some(info) = self.in_memory_info(name) {
            if info.package_name.is_some() {
                return None;
            }
            return Some(CmjModuleImportInfo {
                package_path: PathBuf::new(),
                package_spec: CmjPackageSpec {
                    name: CmjPackageName::Empty,
                    module_systems: Vec::new(),
                },
                file_case: CmjFileCase::Upper,
            });
        }

        let path = self.resolve_module_cmj_path(name)?;
        let metadata = read_cmj_module_metadata(&path)?;
        let package_path = path.parent()?.parent()?.parent()?.to_path_buf();
        Some(CmjModuleImportInfo {
            package_path,
            package_spec: metadata.package_spec,
            file_case: metadata.file_case,
        })
    }

    pub fn module_has_in_memory_info(&self, name: &str) -> bool {
        self.in_memory_info_with(name, |_| ()).is_some()
    }

    pub fn file_exists_in_load_path_uncap(&self, filename: &str) -> bool {
        self.find_in_path_uncap(filename).is_some()
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
        if let Some(is_pure) = self.in_memory_info_with(name, |info| info.is_pure) {
            return Some(is_pure);
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
    ) -> Option<Arc<HashMap<String, CmjExportConstant>>> {
        // Check in-memory registry first (--in-process mode)
        if let Some(constants) =
            self.in_memory_info_with(name, |info| info.cmj_export_constants.clone())
        {
            return Some(constants);
        }

        // In in-process mode, the registry is authoritative — no disk fallback.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        read_cmj_export_constants(&path).map(Arc::new)
    }

    /// Read arity metadata recorded in a module's companion `.cmj`.
    ///
    /// OCaml keeps `arity` even when `compiler/core/js_cmj_format.ml:113-121`
    /// strips non-constant `persistent_closed_lambda` with cross-module
    /// inlining off.
    pub fn module_cmj_export_arities(
        &self,
        name: &str,
    ) -> Option<Arc<HashMap<String, CmjExportArity>>> {
        if let Some(arities) =
            self.in_memory_info_with(name, |info| info.cmj_export_arities.clone())
        {
            return Some(arities);
        }

        // In in-process mode, the registry is authoritative — no disk fallback.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        read_cmj_export_arities(&path).map(Arc::new)
    }

    /// Resolve a nested source path to its flat hoisted JS export.
    pub fn module_cmj_hoisted_export(&self, name: &str, path: &[String]) -> Option<String> {
        if let Some(exports) =
            self.in_memory_info_with(name, |info| info.cmj_hoisted_exports.clone())
        {
            return exports
                .iter()
                .find(|entry| entry.path == path)
                .map(|entry| entry.export_name.clone());
        }
        if self.in_process_mode {
            return None;
        }
        let cmj_path = self.resolve_module_cmj_path(name)?;
        read_cmj_hoisted_exports(&cmj_path)?
            .into_iter()
            .find(|entry| entry.path == path)
            .map(|entry| entry.export_name)
    }

    /// Read closed lambda exports recorded in a module's `.cmj` metadata.
    ///
    /// This mirrors the `cross_module_inline = true` arm of OCaml
    /// `js_cmj_format.ml:112-121`, where non-constant
    /// `persistent_closed_lambda` values are preserved for backend inlining.
    pub fn module_cmj_export_lambdas(&self, name: &str) -> Option<Arc<HashMap<String, Lambda>>> {
        // In in-process mode the registry is authoritative; do not fall back to
        // disk `.cmj` files behind the scheduler's back.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        read_cmj_export_lambdas(&path).map(Arc::new)
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
        Some(crate::source_text::latin1_bytes_to_string(bytes))
    }

    /// Maximum recursion depth for source-fallback type checking.
    /// Each level compiles a dependency from source. Deep chains indicate
    /// many transitive deps being loaded on demand.
    const MAX_SOURCE_FALLBACK_DEPTH: usize = 15;

    fn typecheck_source_signature<'a>(
        &self,
        source_path: &FsPath,
        ctx: &'a TypeContext,
    ) -> Option<(Signature, PersistentEnv)> {
        if self.source_fallback_depth >= Self::MAX_SOURCE_FALLBACK_DEPTH {
            return None;
        }

        let filename = source_path.to_string_lossy().into_owned();
        let source = Self::read_source_latin1(source_path)?;
        // Create a lightweight fallback env instead of cloning the entire PersistentEnv.
        // Share the read-only maps but start with an empty cache (deps loaded on demand).
        // Copy only the current cache placeholders (None entries that prevent infinite recursion).
        let placeholders: HashMap<String, Option<Arc<PersStruct>>> = self
            .cache
            .lock()
            .unwrap()
            .iter()
            .filter(|(_, v)| v.is_none())
            .map(|(k, _)| (k.clone(), None))
            .collect();
        let mut fallback_pers = PersistentEnv {
            cache: Arc::new(Mutex::new(placeholders)),
            load_path: self.load_path.clone(),
            load_path_display: self.load_path_display.clone(),
            open_modules: self.open_modules.clone(),
            jsx_version: self.jsx_version,
            nopervasives: self.nopervasives,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: self.in_memory_modules.clone(),
            in_process_mode: self.in_process_mode,
            source_fallback_paths: self.source_fallback_paths.clone(),
            source_fallback_depth: self.source_fallback_depth + 1,
            portable_cache: self.portable_cache.clone(),
            last_error: self.last_error.clone(),
            crc_units: self.crc_units.clone(),
            view: Arc::new(ResolutionView {
                alias_prefix_rewrites: self.view.alias_prefix_rewrites.clone(),
                compiling_module: self.view.compiling_module.clone(),
                in_memory_module_overrides: self.view.in_memory_module_overrides.clone(),
                source_fallback_path_overrides: self.view.source_fallback_path_overrides.clone(),
                portable_cache_overrides: self.view.portable_cache_overrides.clone(),
                hidden_modules: self.view.hidden_modules.clone(),
                prepared_cached_alias_rewrites: HashSet::new(),
            }),
        };
        let mut env = initial_env(ctx);
        let open_modules = fallback_pers.open_modules.clone();
        let nopervasives = fallback_pers.nopervasives;
        let compiling_module = fallback_pers.view.compiling_module.clone();
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

            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let mut tctx = TypeCheckContext::new(ctx, parser.arena());
            tctx.set_persistent_env(fallback_pers);
            let typed_signature =
                transl_signature(&mut tctx, &env, parser.arena(), &signature).ok()?;
            let fallback_pers = tctx.persistent_env.take()?;
            let decl_signature = crate::types::typemod::decl_signature_from_typed_signature(
                &typed_signature,
                parser.arena(),
            );
            let typed_module_type = TypedModuleType {
                mty_desc: TypedModuleTypeDesc::Tmty_signature(typed_signature),
                mty_type: crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(decl_signature)),
                mty_env: crate::types::typedtree::EnvRef(0),
                mty_loc: crate::parse_arena::LocIdx(0),
                mty_attributes: crate::parser::ast::Attributes::new(),
            };
            let signature = match decl_module_type_from_typed(&typed_module_type)? {
                crate::types::decl::ModuleType::MtySignature(signature) => {
                    std::sync::Arc::unwrap_or_clone(signature)
                }
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
            open_modules: self.open_modules.as_ref().clone(),
            jsx_version: self.jsx_version,
            ..CompilerOptions::default()
        };
        let experimental_let_unwrap =
            experimental_let_unwrap_for_structure(&structure, &options, parser.arena());
        let jsx_version = jsx_version_for_structure(&structure, &options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            jsx_ppx::transform_structure_result(structure, jsx_version, parser.arena_mut()).ok()?
        } else {
            structure
        };
        let structure =
            crate::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut()).ok()?;

        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let mut tctx = TypeCheckContext::new(ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        tctx.set_persistent_env(fallback_pers);
        let (typed_structure, final_env) =
            type_structure(&mut tctx, &env, parser.arena(), &structure).ok()?;

        let has_resi = source_path
            .extension()
            .and_then(|s| s.to_str())
            .is_some_and(|ext| ext == "res")
            && !self.in_process_mode
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
        ctx: &'a TypeContext,
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
            crate::debug_flags::debug_persistent_source_fallback();
        if debug_source_fallback {
            eprintln!(
                "[persistent-source] module={} ast={} source={}",
                name,
                ast_path,
                preferred_path.display()
            );
        }

        let (signature, fallback_pers) = self.typecheck_source_signature(preferred_path, ctx)?;
        self.view_mut()
            .alias_prefix_rewrites
            .extend_missing(fallback_pers.view.alias_prefix_rewrites.local_clone());
        let fallback_entries = fallback_pers
            .cache
            .lock()
            .unwrap()
            .iter()
            .filter(|(module_name, loaded)| module_name.as_str() != name && loaded.is_some())
            .map(|(module_name, loaded)| (module_name.clone(), loaded.clone()))
            .collect::<Vec<_>>();
        for (module_name, loaded) in fallback_entries {
            if !self.cache_contains_key(&module_name) {
                self.cache_insert(module_name, loaded);
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
    fn load_module<'a>(&mut self, name: &str, ctx: &'a TypeContext) -> Option<PersStruct> {
        // In in-process mode, never fall through to .cmi loading. The registry
        // is authoritative for normal project modules. Runtime/bootstrap code
        // may register source fallback paths, which are also source-only.
        if self.in_process_mode {
            if let Some((source_key, _)) = self.source_fallback_path_entry(name) {
                return self.load_module_from_source_path_fallback(&source_key, ctx);
            }
            log::debug!(
                "in-process module '{}' not found in registry; alias rewrite: {:?}",
                name,
                self.view.alias_prefix_rewrites.get(name)
            );
            return None;
        }

        let cmi_filename = format!("{}.cmi", name);
        if let Some((full_path, display_path)) = self.find_in_path_uncap_entry(&cmi_filename) {
            let cmi = match cmi_format::read_cmi(&full_path) {
                Ok(cmi) => cmi,
                Err(error) => {
                    // OCaml Env.find_pers_struct propagates Cmi_format.Error as
                    // a fatal persistent-environment diagnostic. Preserve the
                    // load-path spelling rather than leaking the canonical I/O
                    // path used to open the file.
                    let message = error.to_string().replacen(&full_path, &display_path, 1);
                    self.record_error(PersistentEnvError::InterfaceRead { message });
                    return None;
                }
            };

            if !self.validate_cmi_name(name, &cmi.cmi_name, &display_path) {
                return None;
            }
            if !self.check_cmi_consistency(&cmi.cmi_crcs, &cmi.cmi_name, &display_path) {
                return None;
            }

            let mut sig_ctx = SigReadContext::new(ctx);
            let signature = sig_ctx.read_signature(&cmi.cmi_sign);
            return Some(self.finalize_loaded_signature(
                name,
                name.to_string(),
                signature,
                display_path,
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
        ctx: &'a TypeContext,
    ) -> Option<PersStruct> {
        let source_path = self.source_fallback_path_entry(name)?.1;

        // The source_fallback_paths already points to the preferred file
        // (.resi if it exists, .res otherwise), set by rewatch when
        // registering the paths.
        let (signature, fallback_pers) = self.typecheck_source_signature(&source_path, ctx)?;

        // Merge any modules the fallback discovered
        self.view_mut()
            .alias_prefix_rewrites
            .extend_missing(fallback_pers.view.alias_prefix_rewrites.local_clone());
        let fallback_entries = fallback_pers
            .cache
            .lock()
            .unwrap()
            .iter()
            .filter(|(module_name, loaded)| module_name.as_str() != name && loaded.is_some())
            .map(|(module_name, loaded)| (module_name.clone(), loaded.clone()))
            .collect::<Vec<_>>();
        for (module_name, loaded) in fallback_entries {
            if !self.cache_contains_key(&module_name) {
                self.cache_insert(module_name, loaded);
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
    pub fn read_raw_sig_shared<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext,
    ) -> Option<Arc<Signature>> {
        if self.in_process_mode {
            if let Some(cached) = self.cache_lookup(name) {
                return cached.map(|loaded| loaded.ps_sig.clone());
            }

            let loaded = self.find_pers_struct(name, ctx)?;
            return Some(loaded.ps_sig.clone());
        }

        let cmi_filename = format!("{}.cmi", name);
        let (full_path, display_path) = self.find_in_path_uncap_entry(&cmi_filename)?;
        let cmi = match cmi_format::read_cmi(&full_path) {
            Ok(cmi) => cmi,
            Err(error) => {
                let message = error.to_string().replacen(&full_path, &display_path, 1);
                self.record_error(PersistentEnvError::InterfaceRead { message });
                return None;
            }
        };
        if !self.validate_cmi_name(name, &cmi.cmi_name, &display_path) {
            return None;
        }
        if !self.check_cmi_consistency(&cmi.cmi_crcs, &cmi.cmi_name, &display_path) {
            return None;
        }
        let mut sig_ctx = SigReadContext::new(ctx);
        Some(Arc::new(sig_ctx.read_signature(&cmi.cmi_sign)))
    }

    /// Read a module's signature from CMI without applying path substitution.
    /// Used for interface constraint propagation (moregen) where we need raw
    /// Pident paths that match the implementation's local paths.
    /// In OCaml, ps_sig retains raw Pident paths; path substitution happens
    /// lazily in components_of_module_maker, not on ps_sig.
    pub fn read_raw_sig<'a>(&mut self, name: &str, ctx: &'a TypeContext) -> Option<Signature> {
        self.read_raw_sig_shared(name, ctx)
            .map(|sig| (*sig).clone())
    }

    /// Search the load path for a file (case-insensitive on first char).
    /// Returns the full path if found.
    fn find_in_path_uncap(&self, filename: &str) -> Option<String> {
        self.find_in_path_uncap_entry(filename)
            .map(|(lookup_path, _)| lookup_path)
    }

    fn find_in_path_uncap_entry(&self, filename: &str) -> Option<(String, String)> {
        for (index, dir) in self.load_path.iter().enumerate() {
            let display_dir = self.load_path_display.get(index).unwrap_or(dir);
            if let Some(first_char) = filename.chars().next() {
                if first_char.is_ascii_uppercase() {
                    let uncap = format!("{}{}", first_char.to_ascii_lowercase(), &filename[1..]);
                    let uncap_path = dir.join(&uncap);
                    if uncap_path.exists() {
                        return Some((
                            uncap_path.to_string_lossy().into_owned(),
                            display_dir.join(uncap).to_string_lossy().into_owned(),
                        ));
                    }
                }
            }

            let exact = dir.join(filename);
            if exact.exists() {
                return Some((
                    exact.to_string_lossy().into_owned(),
                    display_dir.join(filename).to_string_lossy().into_owned(),
                ));
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
    pub fn get_renamed_sig_shared<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext,
    ) -> Option<Arc<Signature>> {
        // Check TypeContext cache first (populated by trigger_module_sig_rename)
        if let Some(renamed) = ctx.renamed_module_sig(name) {
            return Some(renamed);
        }
        // Check local cache
        if let Some(cached) = self.renamed_sig_cache.get(name).cloned() {
            return Some(ctx.materialize_renamed_sig(&cached));
        }
        self.force_lazy_signature_rename(name, ctx)?;
        ctx.renamed_module_sig(name).or_else(|| {
            let cached = self.renamed_sig_cache.get(name).cloned()?;
            Some(ctx.materialize_renamed_sig(&cached))
        })
    }

    pub fn get_renamed_sig<'a>(&mut self, name: &str, ctx: &'a TypeContext) -> Option<Signature> {
        self.get_renamed_sig_shared(name, ctx)
            .map(|sig| sig.as_ref().clone())
    }

    /// Force the lazy `Subst.signature Subst.identity` side effect for a
    /// persistent module without requiring the caller to use the renamed
    /// signature. OCaml allocates fresh identifiers the first time `ps_sig` is
    /// forced; in-process type lookups still often need the raw signature shape.
    pub(crate) fn force_lazy_signature_rename<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext,
    ) -> Option<()> {
        if ctx.renamed_module_sigs.borrow().contains_key(name)
            || self.renamed_sig_cache.contains_key(name)
        {
            return Some(());
        }

        // OCaml's `ps_sig` lazy is `Subst.signature Subst.identity sign`
        // (compiler/ml/subst.ml:358-364): one copied signature pass plus bound
        // identifier freshening. Do not pre-clone/pre-copy the persistent
        // signature here; the helper below owns that single OCaml-equivalent
        // copy.
        let ps = self.find_pers_struct(name, ctx)?;
        let renamed = ctx.defer_renamed_sig("persistent_env_lazy_rename", ps.ps_sig.clone());
        Arc::make_mut(&mut self.renamed_sig_cache).insert(name.to_string(), renamed.clone());
        ctx.renamed_module_sigs
            .borrow_mut()
            .insert(name.to_string(), renamed);
        Some(())
    }

    pub fn open_module<'a>(&mut self, name: &str, env: &mut Env, ctx: &'a TypeContext) -> bool {
        // Don't rename at open time — OCaml's ps_sig is only forced later
        // when find_module is called from normalize_path during type expansion.
        let ps = match self.find_pers_struct(name, ctx) {
            Some(ps) => ps,
            None => return false,
        };
        let module_path = Path::Pident(Ident::create_persistent(name));
        let components_key = crate::types::context::QualifiedModuleComponentsCacheKey::new(
            module_path.clone(),
            None,
        );
        // OCaml compiler/ml/env.ml:669-678 stores persistent module components
        // in one `ps_comps` lazy table, and env.ml:1874-1877 forces that same
        // table when opening the module. Reuse an already forced component view
        // here so `prefix_idents` and `Subst.modtype_declaration` side effects
        // are not repeated.
        let alias_source = self.qualified_alias_path_for_flattened_head(name);
        let components = ctx
            .with_qualified_module_components(&components_key, |components| {
                Arc::new(components.clone())
            })
            .unwrap_or_else(|| {
                // The view of a unit loaded into the worker store is the same
                // for every compilation (OCaml builds `ps_comps` once per
                // process), so it is built as a store build and shared.
                let shareable = alias_source.is_none()
                    && self.in_process_mode
                    && ctx.thread_store().owns_signature(&ps.ps_sig)
                    && crate::types::typecore::shared_components_enabled();
                if shareable
                    && let Some((components, piece)) =
                        ctx.thread_store().shared_components(&components_key)
                {
                    ctx.touch_store_piece(&piece);
                    ctx.register_qualified_module_components_arc(
                        components_key.clone(),
                        components.clone(),
                    );
                    return components;
                }
                // OCaml compiler/ml/env.ml:1513-1519 builds the component
                // table after `scrape_alias`, and env.ml:1581-1585 stores the
                // substituted modtypes in that table. When ReScript's
                // persistent registry knows this opened unit is the flattened
                // backing head for a selected alias path, share the same
                // component modtype force with that alias path.
                let build = || {
                    crate::types::env_lazy::QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix(
                        module_path.clone(),
                        ps.ps_sig.clone(),
                        ahash::AHashMap::new(),
                        alias_source.clone(),
                        ctx,
                    )
                };
                let (components, piece) = if shareable {
                    ctx.build_in_store(build)
                } else {
                    (build(), None)
                };
                let components = Arc::new(components);
                if shareable {
                    match piece {
                        Some(piece) => ctx.thread_store().publish_shared_components(
                            components_key.clone(),
                            components.clone(),
                            piece,
                        ),
                        None => components.make_private(),
                    }
                }
                ctx.register_qualified_module_components_arc(components_key, components.clone());
                components
            });
        open_components_into_env(&components, env, ctx);
        true
    }

    /// Get a module's declaration using the raw (un-renamed) sig.
    /// Used during initial env setup where OCaml doesn't force ps_sig.
    pub fn get_module_declaration<'a>(
        &mut self,
        name: &str,
        ctx: &'a TypeContext,
    ) -> Option<ModuleDeclaration> {
        let ps = self.find_pers_struct(name, ctx)?;
        Some(ModuleDeclaration {
            md_type: ModuleType::MtySignature(std::sync::Arc::new(ps.ps_sig.as_ref().clone())),
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
        self.view_mut().hidden_modules.remove(name);
        self.view_mut()
            .in_memory_module_overrides
            .insert(name.to_string(), info);
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
        ctx: &'a TypeContext,
    ) {
        let ps = self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            source_filename.to_string(),
            ctx,
        );
        self.view_mut().hidden_modules.remove(name);
        self.cache_insert(name.to_string(), Some(Arc::new(ps)));
        // Invalidate any cached renamed sig so it gets re-derived
        Arc::make_mut(&mut self.renamed_sig_cache).remove(name);
    }

    /// Remove a transient in-memory signature from this worker's local cache.
    ///
    /// The in-process no-interface implementation path keeps the current
    /// signature visible through Lambda lowering, matching OCaml's
    /// save-before-translation order (compiler/ml/typemod.ml:1779-1788). JS
    /// finishing then uses this helper to hide the current module from later
    /// module-path probing.
    pub fn unregister_in_memory_signature(&mut self, name: &str) {
        self.cache_remove(name);
        Arc::make_mut(&mut self.renamed_sig_cache).remove(name);
        self.view_mut().hidden_modules.insert(name.to_string());
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
        collect_alias_rewrites(
            &sig_items,
            &module_path,
            &mut self.view_mut().alias_prefix_rewrites,
        );

        let ps = PersStruct {
            ps_name: namespace_name.to_string(),
            ps_sig: Arc::new(sig_items),
            ps_filename: format!("{}.mlmap", namespace_name),
        };
        self.view_mut().hidden_modules.remove(namespace_name);
        self.cache_insert(namespace_name.to_string(), Some(Arc::new(ps)));
        Arc::make_mut(&mut self.renamed_sig_cache).remove(namespace_name);
    }

    /// Look up in-memory module info by name.
    pub fn get_in_memory_module(&self, name: &str) -> Option<InMemoryModuleInfo> {
        self.in_memory_info(name)
    }

    /// Check whether a module is registered in the in-memory registry.
    pub fn has_in_memory_module(&self, name: &str) -> bool {
        self.in_memory_info(name).is_some()
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

    pub fn module_is_runtime(&self, name: &str) -> bool {
        self.in_memory_info_with(name, |info| info.is_runtime)
            .unwrap_or(false)
    }
}

/// `module_path` is the path to the module containing this signature
/// (e.g., `Pident(Js)` or `Pdot(Pident(Js), "Promise")`).
/// `load_path` is used to resolve module aliases by loading CMI files.
/// Install the type declarations of a loaded signature in this unit's
/// registries. `shared` says the signature is owned by the worker store, so
/// the `Arc` handles can be shared across compilations instead of cloned.
fn register_sig_types_recursive<'a>(
    sig: &Signature,
    module_path: &Path,
    ctx: &'a TypeContext,
    shared: bool,
) {
    if shared {
        let store = ctx.thread_store();
        let registrations = store.sig_type_registrations(sig, module_path, || {
            let mut registrations = Vec::new();
            collect_sig_type_registrations(sig, module_path, ctx, &mut registrations);
            registrations
        });
        ctx.register_sig_type_registrations(&registrations);
        return;
    }
    for item in sig {
        match item {
            SignatureItem::SigType(id, decl, _) => {
                let decl = if shared {
                    ctx.thread_store().shared_type_decl(decl)
                } else {
                    decl.clone()
                };
                ctx.register_shared_type_decl(id.name(), decl.clone());
                // Also register by stamp for precise lookup when name is ambiguous (e.g., "t")
                if id.stamp() != 0 {
                    ctx.register_shared_type_decl_by_stamp(id.stamp(), decl.clone());
                }
                // Register by fully qualified path for Pdot lookup (e.g., "Js.Promise.t")
                let full_path = Path::pdot(module_path.clone(), id.name());
                ctx.register_shared_type_decl_by_path(&full_path.name(), decl.clone());
                ctx.register_shared_type_decl_by_exact_path(full_path, decl);
            }
            SignatureItem::SigModule(id, md, _) => {
                let sub_path = Path::pdot(module_path.clone(), id.name());
                match &md.md_type {
                    ModuleType::MtySignature(sub_sig) => {
                        // Recurse into sub-module signatures with extended path
                        register_sig_types_recursive(sub_sig, &sub_path, ctx, shared);
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

/// The registrations `register_sig_types_recursive` installs for a
/// store-owned signature, in installation order.
fn collect_sig_type_registrations(
    sig: &Signature,
    module_path: &Path,
    ctx: &TypeContext,
    out: &mut Vec<crate::types::thread_store::SigTypeRegistration>,
) {
    for item in sig {
        match item {
            SignatureItem::SigType(id, decl, _) => {
                let decl = ctx.thread_store().shared_type_decl(decl);
                let qualified_path = Path::pdot(module_path.clone(), id.name());
                out.push(crate::types::thread_store::SigTypeRegistration {
                    name: smol_str::SmolStr::new_static(id.name()),
                    stamp: id.stamp(),
                    qualified_name: smol_str::SmolStr::new(qualified_path.name()),
                    qualified_path,
                    decl,
                });
            }
            SignatureItem::SigModule(id, md, _) => {
                if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    let sub_path = Path::pdot(module_path.clone(), id.name());
                    collect_sig_type_registrations(sub_sig, &sub_path, ctx, out);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod cmj_export_tests {
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
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let mut env = PersistentEnv::new();
        env.set_in_process_mode(true);
        env.set_nopervasives(true);
        env.add_load_path(load_path);
        env.view_mut()
            .source_fallback_path_overrides
            .insert("Foo".to_string(), source_path);

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
        hoisted_exports: decode_cmj_hoisted_exports(&value)?,
        package_spec: decode_cmj_package_spec(&value)?,
        file_case: decode_cmj_file_case(&value)?,
    })
}

fn read_cmj_pure(path: &FsPath) -> Option<bool> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_pure(&value)
}

fn decode_cmj_pure(value: &OcamlValue) -> Option<bool> {
    let (_, fields) = value.as_block_opt()?;
    fields.get(2).map(|field| field.as_bool())
}

fn read_cmj_hoisted_exports(path: &FsPath) -> Option<Vec<crate::lambda::HoistedExport>> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_hoisted_exports(&value)
}

fn decode_cmj_hoisted_exports(value: &OcamlValue) -> Option<Vec<crate::lambda::HoistedExport>> {
    let (_, fields) = value.as_block_opt()?;
    let (_, entries) = fields.get(1)?.as_block_opt()?;
    entries
        .iter()
        .map(|entry| {
            let (_, fields) = entry.as_block_opt()?;
            Some(crate::lambda::HoistedExport {
                path: decode_cmj_string_list(fields.first()?)?,
                export_name: fields.get(1)?.as_string().to_string(),
            })
        })
        .collect()
}

fn read_cmj_export_constants(path: &FsPath) -> Option<HashMap<String, CmjExportConstant>> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_export_constants(&value)
}

fn read_cmj_export_arities(path: &FsPath) -> Option<HashMap<String, CmjExportArity>> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_export_arities(&value)
}

fn read_cmj_export_lambdas(path: &FsPath) -> Option<HashMap<String, Lambda>> {
    let value = read_marshaled_cmj(path)?;
    decode_cmj_export_lambdas(&value)
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

fn decode_cmj_export_arities(value: &OcamlValue) -> Option<HashMap<String, CmjExportArity>> {
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
        let Some(arity) = decode_cmj_export_arity(&entry_fields[1]) else {
            continue;
        };
        exports.insert(name, arity);
    }

    Some(exports)
}

fn decode_cmj_export_arity(value: &OcamlValue) -> Option<CmjExportArity> {
    match value {
        // compiler/core/js_cmj_format.ml:27: `Single of Lam_arity.t`.
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(CmjExportArity::Single(decode_cmj_lam_arity(&fields[0])?))
        }
        // compiler/core/js_cmj_format.ml:27: `Submodule of Lam_arity.t array`.
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            let (_, items) = fields[0].as_block_opt()?;
            let mut arities = Vec::with_capacity(items.len());
            for item in items {
                arities.push(decode_cmj_lam_arity(item)?);
            }
            Some(CmjExportArity::Submodule(arities))
        }
        _ => None,
    }
}

fn decode_cmj_lam_arity(value: &OcamlValue) -> Option<Arity> {
    match value {
        // compiler/core/lam_arity.ml:27-34: `Arity_na`.
        OcamlValue::Int(0) => Some(Arity::na()),
        // compiler/core/lam_arity.ml:27-34: `Arity_info of int list * bool`.
        OcamlValue::Block(0, fields) if fields.len() == 2 => Some(Arity::info(
            decode_cmj_list(&fields[0], |item| Some(item.as_int() as i32))?,
            fields[1].as_bool(),
        )),
        _ => None,
    }
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
        OcamlValue::Block(tag, fields) if *tag == 0 && fields.len() == 1 => {
            Some(CmjExportConstant::Undefined {
                is_unit: fields[0].as_bool(),
            })
        }
        _ => None,
    }
}

fn decode_cmj_export_lambdas(value: &OcamlValue) -> Option<HashMap<String, Lambda>> {
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
        let Some(lambda) = decode_cmj_persistent_closed_lambda(&entry_fields[2]) else {
            continue;
        };
        exports.insert(name, lambda);
    }

    Some(exports)
}

fn decode_cmj_persistent_closed_lambda(value: &OcamlValue) -> Option<Lambda> {
    let lam = value.as_option()?;
    decode_cmj_lambda(lam)
}

fn decode_cmj_package_spec(value: &OcamlValue) -> Option<CmjPackageSpec> {
    let (_, fields) = value.as_block_opt()?;
    let package_field = fields.get(3)?;
    let (_, package_fields) = package_field.as_block_opt()?;
    if package_fields.len() != 2 {
        return None;
    }

    Some(CmjPackageSpec {
        name: decode_cmj_package_name(&package_fields[0])?,
        module_systems: decode_cmj_list(&package_fields[1], decode_cmj_package_info)?,
    })
}

fn decode_cmj_package_name(value: &OcamlValue) -> Option<CmjPackageName> {
    match value {
        // compiler/core/js_packages_info.ml:39: Pkg_empty.
        OcamlValue::Int(0) => Some(CmjPackageName::Empty),
        // compiler/core/js_packages_info.ml:39: Pkg_runtime.
        OcamlValue::Int(1) => Some(CmjPackageName::Runtime),
        // compiler/core/js_packages_info.ml:39: Pkg_normal of string.
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(CmjPackageName::Normal(fields[0].as_string().to_string()))
        }
        _ => None,
    }
}

fn decode_cmj_package_info(value: &OcamlValue) -> Option<CmjPackageInfo> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() != 3 {
        return None;
    }

    Some(CmjPackageInfo {
        module_system: decode_cmj_package_module_system(&fields[0])?,
        path: fields[1].as_string().to_string(),
        suffix: fields[2].as_string().to_string(),
    })
}

fn decode_cmj_package_module_system(value: &OcamlValue) -> Option<CmjPackageModuleSystem> {
    match value.as_int() {
        // compiler/ext/ext_module_system.ml:1: Commonjs | Esmodule.
        0 => Some(CmjPackageModuleSystem::CommonJs),
        1 => Some(CmjPackageModuleSystem::EsModule),
        _ => None,
    }
}

fn decode_cmj_file_case(value: &OcamlValue) -> Option<CmjFileCase> {
    let (_, fields) = value.as_block_opt()?;
    match fields.get(4)?.as_int() {
        // compiler/ext/ext_js_file_kind.ml:24: Upper | Little.
        0 => Some(CmjFileCase::Upper),
        1 => Some(CmjFileCase::Little),
        _ => None,
    }
}

fn decode_cmj_lambda(value: &OcamlValue) -> Option<Lambda> {
    match value {
        // OCaml Lam.t constructor order is defined in compiler/core/lam.ml:91-113.
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(Lambda::Lvar(decode_cmj_ident(&fields[0])?))
        }
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(Lambda::LglobalModule(
            decode_cmj_ident(&fields[0])?,
            fields[1].as_bool(),
        )),
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(Lambda::Lconst(decode_cmj_lambda_constant(&fields[0])?))
        }
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            let apply = decode_cmj_apply(&fields[0])?;
            Some(Lambda::Lapply(apply))
        }
        OcamlValue::Block(4, fields) if fields.len() == 1 => {
            Some(Lambda::Lfunction(decode_cmj_lfunction(&fields[0])?))
        }
        OcamlValue::Block(7, fields) if fields.len() == 1 => {
            let prim = decode_cmj_prim_info(&fields[0])?;
            Some(Lambda::Lprim(prim))
        }
        OcamlValue::Block(13, fields) if fields.len() == 3 => Some(Lambda::if_(
            decode_cmj_lambda(&fields[0])?,
            decode_cmj_lambda(&fields[1])?,
            decode_cmj_lambda(&fields[2])?,
        )),
        OcamlValue::Block(14, fields) if fields.len() == 2 => Some(Lambda::seq(
            decode_cmj_lambda(&fields[0])?,
            decode_cmj_lambda(&fields[1])?,
        )),
        _ => None,
    }
}

fn decode_cmj_ident(value: &OcamlValue) -> Option<Ident> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 3 {
        return None;
    }
    let stamp = fields[0].as_int() as i32;
    let name = fields[1].as_string();
    let flags = fields[2].as_int() as u8;

    Some(if stamp == 0 {
        let id = Ident::create_persistent(name);
        if flags & 1 != 0 { id.with_global() } else { id }
    } else if stamp < 1000 {
        crate::types::predef::find_predef_ident(name).unwrap_or_else(|| {
            Ident::new(
                name,
                stamp,
                crate::ident::IdentFlags::from_bits_truncate(flags),
            )
        })
    } else {
        Ident::new(
            name,
            stamp,
            crate::ident::IdentFlags::from_bits_truncate(flags),
        )
    })
}

fn decode_cmj_lfunction(value: &OcamlValue) -> Option<LFunction> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 4 {
        return None;
    }
    Some(LFunction {
        arity: fields[0].as_int() as i32,
        params: decode_cmj_list(&fields[1], decode_cmj_ident)?,
        body: Box::new(decode_cmj_lambda(&fields[2])?),
        attr: decode_cmj_function_attribute(&fields[3])?,
    })
}

fn decode_cmj_function_attribute(value: &OcamlValue) -> Option<FunctionAttribute> {
    let (_, fields) = value.as_block_opt()?;
    Some(FunctionAttribute {
        inline: fields
            .first()
            .and_then(decode_cmj_inline_attribute)
            .unwrap_or_default(),
        is_a_functor: fields.get(1).is_some_and(OcamlValue::as_bool),
        return_unit: fields.get(2).is_some_and(OcamlValue::as_bool),
        async_: fields.get(3).is_some_and(OcamlValue::as_bool),
        directive: fields
            .get(4)
            .and_then(|field| field.as_option().map(|value| value.as_string().to_string())),
        one_unit_arg: fields.get(5).is_some_and(OcamlValue::as_bool),
    })
}

fn decode_cmj_inline_attribute(value: &OcamlValue) -> Option<InlineAttribute> {
    match value.as_int() {
        0 => Some(InlineAttribute::Always),
        1 => Some(InlineAttribute::Never),
        2 => Some(InlineAttribute::Default),
        _ => None,
    }
}

fn decode_cmj_apply(value: &OcamlValue) -> Option<Apply> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 4 {
        return None;
    }
    Some(Apply {
        ap_func: Box::new(decode_cmj_lambda(&fields[0])?),
        ap_args: decode_cmj_list(&fields[1], decode_cmj_lambda)?,
        ap_info: decode_cmj_ap_info(&fields[2])?,
        ap_transformed_jsx: fields[3].as_bool(),
    })
}

fn decode_cmj_ap_info(value: &OcamlValue) -> Option<ApInfo> {
    let (_, fields) = value.as_block_opt()?;
    Some(ApInfo {
        loc: Location::none(),
        inlined: fields
            .get(1)
            .and_then(decode_cmj_inline_attribute)
            .unwrap_or_default(),
        status: fields
            .get(2)
            .and_then(decode_cmj_apply_status)
            .unwrap_or(ApplyStatus::Na),
    })
}

fn decode_cmj_apply_status(value: &OcamlValue) -> Option<ApplyStatus> {
    match value.as_int() {
        0 => Some(ApplyStatus::Na),
        1 => Some(ApplyStatus::InferFull),
        2 => Some(ApplyStatus::Uncurry),
        _ => None,
    }
}

fn decode_cmj_prim_info(value: &OcamlValue) -> Option<PrimInfo> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 2 {
        return None;
    }
    Some(PrimInfo {
        primitive: decode_cmj_primitive(&fields[0])?,
        args: decode_cmj_list(&fields[1], decode_cmj_lambda)?,
        loc: Location::none(),
    })
}

fn decode_cmj_lambda_constant(value: &OcamlValue) -> Option<LambdaConstant> {
    // OCaml Lam_constant.t constructor order is in compiler/frontend/lam_constant.ml:33-50.
    match value {
        OcamlValue::Int(0) => Some(LambdaConstant::JsNull),
        OcamlValue::Int(1) => Some(LambdaConstant::JsTrue),
        OcamlValue::Int(2) => Some(LambdaConstant::JsFalse),
        OcamlValue::Int(3) => Some(LambdaConstant::ModuleAlias),
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(LambdaConstant::JsUndefined {
            is_unit: fields[0].as_bool(),
        }),
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(LambdaConstant::Int {
            i: fields[0].as_int() as i32,
            comment: decode_cmj_pointer_info(&fields[1])?,
        }),
        OcamlValue::Block(2, fields) if fields.len() == 1 => Some(LambdaConstant::Constructor(
            decode_cmj_variant_tag(&fields[0])?,
        )),
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Char(fields[0].as_int() as i32))
        }
        OcamlValue::Block(4, fields) if fields.len() == 2 => Some(LambdaConstant::String {
            s: fields[0].as_string().to_string(),
            delim: decode_cmj_external_delim_option(&fields[1])?,
        }),
        OcamlValue::Block(5, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Float(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(6, fields) if fields.len() == 2 => Some(LambdaConstant::BigInt {
            negative: fields[0].as_bool(),
            value: fields[1].as_string().to_string(),
        }),
        OcamlValue::Block(7, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Pointer(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(8, fields) if fields.len() == 2 => Some(LambdaConstant::Block {
            tag_info: decode_cmj_tag_info(&fields[0])?,
            elements: decode_cmj_list(&fields[1], decode_cmj_lambda_constant)?,
        }),
        OcamlValue::Block(9, fields) if fields.len() == 1 => Some(LambdaConstant::Some(Box::new(
            decode_cmj_lambda_constant(&fields[0])?,
        ))),
        _ => None,
    }
}

fn decode_cmj_pointer_info(value: &OcamlValue) -> Option<Option<PointerInfo>> {
    match value {
        OcamlValue::Int(0) => Some(None),
        OcamlValue::Int(1) => Some(Some(PointerInfo::AssertFalse)),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(Some(PointerInfo::Some(fields[0].as_string().to_string())))
        }
        _ => None,
    }
}

fn decode_cmj_variant_tag(value: &OcamlValue) -> Option<crate::types::VariantTag> {
    let (0, fields) = value.as_block_opt()? else {
        return None;
    };
    if fields.len() != 2 {
        return None;
    }
    Some(crate::types::VariantTag {
        name: fields[0].as_string().to_string(),
        tag_type: decode_cmj_variant_tag_type_option(&fields[1])?,
    })
}

fn decode_cmj_variant_tag_type_option(
    value: &OcamlValue,
) -> Option<Option<crate::types::VariantTagType>> {
    match value {
        OcamlValue::Int(0) => Some(None),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(Some(decode_cmj_variant_tag_type(&fields[0])?))
        }
        _ => None,
    }
}

fn decode_cmj_variant_tag_type(value: &OcamlValue) -> Option<crate::types::VariantTagType> {
    use crate::types::VariantTagType as T;
    match value {
        OcamlValue::Int(0) => Some(T::Null),
        OcamlValue::Int(1) => Some(T::Undefined),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(T::String(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            Some(T::Int(fields[0].as_int() as i32))
        }
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(T::Float(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            Some(T::BigInt(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(4, fields) if fields.len() == 1 => Some(T::Bool(fields[0].as_bool())),
        OcamlValue::Block(5, fields) if fields.len() == 1 => {
            Some(T::Untagged(decode_cmj_variant_block_type(&fields[0])?))
        }
        _ => None,
    }
}

fn decode_cmj_variant_block_type(value: &OcamlValue) -> Option<crate::types::VariantBlockType> {
    use crate::types::{VariantBlockType as T, VariantInstance as I};
    match value {
        OcamlValue::Int(0) => Some(T::Int),
        OcamlValue::Int(1) => Some(T::String),
        OcamlValue::Int(2) => Some(T::Float),
        OcamlValue::Int(3) => Some(T::Bigint),
        OcamlValue::Int(4) => Some(T::Boolean),
        OcamlValue::Int(5) => Some(T::Function),
        OcamlValue::Int(6) => Some(T::Object),
        OcamlValue::Int(7) => Some(T::Unknown),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(T::Instance(match fields[0].as_int() {
                0 => I::Array,
                1 => I::ArrayBuffer,
                2 => I::BigInt64Array,
                3 => I::BigUint64Array,
                4 => I::Blob,
                5 => I::DataView,
                6 => I::Date,
                7 => I::File,
                8 => I::Float32Array,
                9 => I::Float64Array,
                10 => I::Int16Array,
                11 => I::Int32Array,
                12 => I::Int8Array,
                13 => I::Promise,
                14 => I::RegExp,
                15 => I::Uint16Array,
                16 => I::Uint32Array,
                17 => I::Uint8Array,
                18 => I::Uint8ClampedArray,
                19 => I::Set,
                20 => I::Map,
                21 => I::WeakSet,
                22 => I::WeakMap,
                _ => return None,
            }))
        }
        _ => None,
    }
}

fn decode_cmj_tag_info(value: &OcamlValue) -> Option<TagInfo> {
    fn mutable_flag(value: &OcamlValue) -> Option<crate::parser::ast::MutableFlag> {
        match value.as_int() {
            0 => Some(crate::parser::ast::MutableFlag::Immutable),
            1 => Some(crate::parser::ast::MutableFlag::Mutable),
            _ => None,
        }
    }

    fn block_runtime(value: &OcamlValue) -> Option<crate::types::BlockRuntime> {
        let (_, fields) = value.as_block_opt()?;
        Some(crate::types::BlockRuntime {
            tag: decode_cmj_variant_tag(fields.first()?)?,
            tag_name: fields
                .get(1)?
                .as_option()
                .map(|name| name.as_string().to_string()),
            untagged: fields.get(2)?.as_bool(),
        })
    }

    fn record_fields(value: &OcamlValue) -> Option<Vec<(String, bool)>> {
        if matches!(value, OcamlValue::Int(0)) {
            return Some(Vec::new());
        }
        let (_, fields) = value.as_block_opt()?;
        fields
            .iter()
            .map(|field| {
                let (_, pair) = field.as_block_opt()?;
                Some((
                    pair.first()?.as_string().to_string(),
                    pair.get(1)?.as_bool(),
                ))
            })
            .collect()
    }

    fn string_array(value: &OcamlValue) -> Option<Vec<String>> {
        if matches!(value, OcamlValue::Int(0)) {
            return Some(Vec::new());
        }
        let (_, fields) = value.as_block_opt()?;
        Some(
            fields
                .iter()
                .map(|field| field.as_string().to_string())
                .collect(),
        )
    }

    match value {
        OcamlValue::Int(0) => Some(TagInfo::Tuple),
        OcamlValue::Int(1) => Some(TagInfo::Extension),
        OcamlValue::Int(2) => Some(TagInfo::Some),
        OcamlValue::Int(3) => Some(TagInfo::SomeNotNested),
        OcamlValue::Block(0, fields) if fields.len() == 3 => Some(TagInfo::Constructor {
            name: fields[0].as_string().to_string(),
            num_nonconst: fields[1].as_int() as i32,
            runtime: Box::new(block_runtime(&fields[2])?),
        }),
        OcamlValue::Block(1, fields) if fields.len() == 5 => Some(TagInfo::RecordInlined {
            name: fields[0].as_string().to_string(),
            num_nonconst: fields[1].as_int() as i32,
            fields: record_fields(&fields[2])?,
            logical_field_count: None,
            mutable_flag: mutable_flag(&fields[3])?,
            runtime: Box::new(block_runtime(&fields[4])?),
        }),
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(TagInfo::PolyVar(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(3, fields) if fields.len() == 2 => Some(TagInfo::Record {
            fields: record_fields(&fields[0])?,
            logical_field_count: None,
            mutable_flag: mutable_flag(&fields[1])?,
        }),
        OcamlValue::Block(4, fields) if fields.len() == 1 => {
            Some(TagInfo::Module(decode_cmj_string_list(&fields[0])?))
        }
        OcamlValue::Block(5, fields) if fields.len() == 1 => Some(TagInfo::ModuleExport(
            decode_cmj_list(&fields[0], decode_cmj_ident)?,
        )),
        OcamlValue::Block(6, fields) if fields.len() == 2 => Some(TagInfo::RecordExt {
            fields: string_array(&fields[0])?,
            mutable_flag: mutable_flag(&fields[1])?,
        }),
        _ => None,
    }
}

fn decode_cmj_primitive(value: &OcamlValue) -> Option<Primitive> {
    match value {
        // OCaml Lam_primitive.t nullary constructor indexes follow
        // compiler/core/lam_primitive.ml:36-184, excluding payload variants.
        OcamlValue::Int(1) => Some(Primitive::Praise),
        OcamlValue::Int(6) => Some(Primitive::Pobjsize),
        OcamlValue::Int(7) => Some(Primitive::Psequand),
        OcamlValue::Int(8) => Some(Primitive::Psequor),
        OcamlValue::Int(9) => Some(Primitive::Pnot),
        OcamlValue::Int(13) => Some(Primitive::Pisint),
        OcamlValue::Int(14) => Some(Primitive::Pnegint),
        OcamlValue::Int(15) => Some(Primitive::Paddint),
        OcamlValue::Int(16) => Some(Primitive::Psubint),
        OcamlValue::Int(17) => Some(Primitive::Pmulint),
        OcamlValue::Int(18) => Some(Primitive::Pdivint),
        OcamlValue::Int(19) => Some(Primitive::Pmodint),
        OcamlValue::Int(21) => Some(Primitive::Pandint),
        OcamlValue::Int(22) => Some(Primitive::Porint),
        OcamlValue::Int(23) => Some(Primitive::Pxorint),
        OcamlValue::Int(25) => Some(Primitive::Plslint),
        OcamlValue::Int(26) => Some(Primitive::Plsrint),
        OcamlValue::Int(27) => Some(Primitive::Pasrint),
        OcamlValue::Int(59) => Some(Primitive::Pstringlength),
        OcamlValue::Int(66) => Some(Primitive::Pmakearray),
        OcamlValue::Int(67) => Some(Primitive::Parraylength),
        OcamlValue::Int(68) => Some(Primitive::Parrayrefu),
        OcamlValue::Int(69) => Some(Primitive::Parraysetu),
        OcamlValue::Int(77) => Some(Primitive::PjsApply),
        OcamlValue::Int(91) => Some(Primitive::PfnArity),
        OcamlValue::Int(93) => Some(Primitive::PisNotNone),
        OcamlValue::Int(94) => Some(Primitive::PvalFromOption),
        OcamlValue::Int(95) => Some(Primitive::PvalFromOptionNotNest),
        OcamlValue::Int(96) => Some(Primitive::Psome),
        OcamlValue::Int(97) => Some(Primitive::PsomeNotNest),
        OcamlValue::Block(0, fields) if fields.len() == 2 => Some(Primitive::Pmakeblock(
            decode_cmj_tag_info(&fields[0])?,
            match fields[1].as_int() {
                0 => Mutable::Immutable,
                1 => Mutable::Mutable,
                _ => return None,
            },
        )),
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(Primitive::Pfield(
            fields[0].as_int() as i32,
            decode_cmj_field_dbg_info(&fields[1])?,
        )),
        OcamlValue::Block(4, fields) if fields.len() == 5 => Some(Primitive::PjsCall {
            prim_name: fields[0].as_string().to_string(),
            arg_types: decode_cmj_list(&fields[1], decode_cmj_external_arg_spec)?,
            ffi: Box::new(decode_cmj_external_ffi_spec(&fields[2])?),
            dynamic_import: fields[3].as_bool(),
            transformed_jsx: fields[4].as_bool(),
        }),
        OcamlValue::Block(6, fields) if fields.len() == 1 => {
            Some(Primitive::Pobjcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(7, fields) if fields.len() == 1 => {
            Some(Primitive::Pboolcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(10, fields) if fields.len() == 1 => {
            Some(Primitive::Pintcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(11, fields) if fields.len() == 1 => {
            Some(Primitive::Pfloatcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(13, fields) if fields.len() == 1 => {
            Some(Primitive::Pstringcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(15, fields) if fields.len() == 1 => {
            Some(Primitive::Pjscomp(decode_cmj_comparison(&fields[0])?))
        }
        _ => None,
    }
}

fn decode_cmj_comparison(value: &OcamlValue) -> Option<Comparison> {
    match value.as_int() {
        0 => Some(Comparison::Eq),
        1 => Some(Comparison::Neq),
        2 => Some(Comparison::Lt),
        3 => Some(Comparison::Gt),
        4 => Some(Comparison::Le),
        5 => Some(Comparison::Ge),
        _ => None,
    }
}

fn decode_cmj_field_dbg_info(value: &OcamlValue) -> Option<FieldDbgInfo> {
    match value {
        // compiler/core/lam_compat.ml:65-75.
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(FieldDbgInfo::Record {
            name: fields[0].as_string().to_string(),
        }),
        OcamlValue::Block(1, fields) if fields.len() == 1 => Some(FieldDbgInfo::Module {
            name: fields[0].as_string().to_string(),
        }),
        OcamlValue::Int(0) => Some(FieldDbgInfo::Tuple),
        OcamlValue::Int(5) => Some(FieldDbgInfo::Cons),
        _ => None,
    }
}

fn decode_cmj_external_arg_spec(value: &OcamlValue) -> Option<ExternalArgSpec> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 2 {
        return None;
    }
    Some(ExternalArgSpec {
        arg_type: decode_cmj_external_arg_attr(&fields[0])?,
        arg_label: decode_cmj_external_arg_label(&fields[1])?,
    })
}

fn decode_cmj_external_arg_attr(value: &OcamlValue) -> Option<ExternalArgAttr> {
    // compiler/frontend/external_arg_spec.ml:41-61.
    match value {
        OcamlValue::Int(0) => Some(ExternalArgAttr::ExternUnit),
        OcamlValue::Int(1) => Some(ExternalArgAttr::Nothing),
        OcamlValue::Int(2) => Some(ExternalArgAttr::Ignore),
        OcamlValue::Int(3) => Some(ExternalArgAttr::Unwrap),
        OcamlValue::Block(3, fields) if fields.len() == 1 => Some(ExternalArgAttr::ArgCst(
            decode_cmj_external_arg_const(&fields[0])?,
        )),
        _ => None,
    }
}

fn decode_cmj_external_arg_label(value: &OcamlValue) -> Option<ExternalArgLabel> {
    match value.as_int() {
        0 => Some(ExternalArgLabel::Label),
        1 => Some(ExternalArgLabel::Empty),
        2 => Some(ExternalArgLabel::Optional),
        _ => None,
    }
}

fn decode_cmj_external_arg_const(value: &OcamlValue) -> Option<ExternalArgConst> {
    match value {
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(ExternalArgConst::IntLit(fields[0].as_int()))
        }
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(ExternalArgConst::StringLit(
            fields[0].as_string().to_string(),
            decode_cmj_external_arg_delim(&fields[1])?,
        )),
        _ => None,
    }
}

fn decode_cmj_external_arg_delim(value: &OcamlValue) -> Option<ExternalArgDelim> {
    match value.as_int() {
        0 => Some(ExternalArgDelim::None),
        1 => Some(ExternalArgDelim::StarJ),
        2 => Some(ExternalArgDelim::NoQuotes),
        3 => Some(ExternalArgDelim::BackQuotes),
        _ => None,
    }
}

fn decode_cmj_external_delim_option(value: &OcamlValue) -> Option<Option<StringDelim>> {
    match value {
        OcamlValue::Int(0) => Some(None),
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(Some(match fields[0].as_int() {
            0 => StringDelim::Plain,
            1 => StringDelim::StarJ,
            2 => StringDelim::NoQuotes,
            3 => StringDelim::Backtick,
            _ => return None,
        })),
        _ => None,
    }
}

fn decode_cmj_external_ffi_spec(value: &OcamlValue) -> Option<ExternalFfiSpec> {
    Some(ExternalFfiSpec {
        kind: ExternalFfiKind::Default,
        spec: Some(decode_cmj_external_spec(value)?),
        obj_params: None,
        return_wrapper: ExternalReturnWrapper::Identity,
        inline_constant: None,
    })
}

fn decode_cmj_external_spec(value: &OcamlValue) -> Option<ExternalSpec> {
    // compiler/frontend/external_ffi_types.ml:45-75.
    match value {
        OcamlValue::Block(4, fields) if fields.len() >= 4 => Some(ExternalSpec::JsCall {
            name: fields[0].as_string().to_string(),
            external_module_name: decode_cmj_external_module_name_option(&fields[1])?,
            splice: fields[2].as_bool(),
            scopes: decode_cmj_string_list(&fields[3])?,
        }),
        OcamlValue::Block(6, fields) if fields.len() >= 4 => Some(ExternalSpec::JsNew {
            name: fields[0].as_string().to_string(),
            external_module_name: decode_cmj_external_module_name_option(&fields[1])?,
            splice: fields[2].as_bool(),
            scopes: decode_cmj_string_list(&fields[3])?,
        }),
        _ => None,
    }
}

fn decode_cmj_external_module_name_option(
    value: &OcamlValue,
) -> Option<Option<ExternalModuleName>> {
    match value {
        OcamlValue::Int(0) => Some(None),
        _ => Some(Some(decode_cmj_external_module_name(value.as_option()?)?)),
    }
}

fn decode_cmj_external_module_name(value: &OcamlValue) -> Option<ExternalModuleName> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 2 {
        return None;
    }
    Some(ExternalModuleName {
        bundle: fields[0].as_string().to_string(),
        module_bind_name: crate::lambda::lam_primitive::ExternalModuleBindName::Nothing,
        import_attributes: None,
    })
}

fn decode_cmj_string_list(value: &OcamlValue) -> Option<Vec<String>> {
    decode_cmj_list(value, |item| Some(item.as_string().to_string()))
}

fn decode_cmj_list<T>(
    value: &OcamlValue,
    mut decode: impl FnMut(&OcamlValue) -> Option<T>,
) -> Option<Vec<T>> {
    let mut out = Vec::new();
    let mut cursor = value;
    loop {
        match cursor {
            OcamlValue::Int(0) => break,
            OcamlValue::Block(0, fields) if fields.len() == 2 => {
                out.push(decode(&fields[0])?);
                cursor = &fields[1];
            }
            _ => return None,
        }
    }
    Some(out)
}

/// This is the core of `open_signature` from OCaml's `env.ml`.
/// For each signature item, we add the appropriate binding to the environment.
///
/// Uses "opened" add methods so that these bindings do NOT shadow existing
/// Recursively register all types from a module type (and sub-modules) by stamp.
/// This ensures that types referenced in function signatures can be expanded
/// during type unification, even when the type comes from a deeply nested module.
pub(crate) fn register_types_by_stamp_recursive(md_type: &ModuleType, ctx: &TypeContext) {
    if let ModuleType::MtySignature(sig) = md_type {
        register_types_by_stamp_in_signature_recursive(sig, ctx, false);
    }
}

fn register_types_by_stamp_in_signature_recursive(
    sig: &Signature,
    ctx: &TypeContext,
    shared: bool,
) {
    for item in sig {
        match item {
            SignatureItem::SigType(id, decl, _) => {
                if id.stamp() != 0 {
                    let decl = if shared {
                        ctx.thread_store().shared_type_decl(decl)
                    } else {
                        decl.clone()
                    };
                    ctx.register_shared_type_decl_by_stamp(id.stamp(), decl);
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    register_types_by_stamp_in_signature_recursive(sub_sig, ctx, shared);
                }
            }
            _ => {}
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
/// Module stamp substitution protects the current local access-path head because
/// in-process compilation stores signatures produced by independent compiler
/// contexts whose local stamp counters can overlap.
/// The `name_map` maps type names (for persistent idents with stamp 0) to their qualified paths.
type ModuleStampSubstMap = HashMap<i32, (String, Path)>;

fn insert_module_stamp_subst(map: &mut ModuleStampSubstMap, id: &Ident, path: Path) {
    map.insert(id.stamp(), (id.name().to_string(), path));
}

fn nonpersistent_path_head(path: &Path) -> Option<(i32, String)> {
    match path {
        Path::Pident(id) => (id.stamp() != 0).then(|| (id.stamp(), id.name().to_string())),
        Path::Pdot(prefix, _, _) => nonpersistent_path_head(prefix),
        Path::Papply(left, right) => {
            nonpersistent_path_head(left).or_else(|| nonpersistent_path_head(right))
        }
    }
}

#[derive(Default, Clone, Debug)]
struct SubstMaps {
    type_stamp_map: HashMap<i32, Path>,
    type_name_map: HashMap<String, Path>,
    module_stamp_map: ModuleStampSubstMap,
    module_name_map: HashMap<String, Path>,
    protected_module_head: Option<(i32, String)>,
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
    maps.protected_module_head = nonpersistent_path_head(module_path);

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
                    insert_module_stamp_subst(&mut maps.module_stamp_map, id, qualified_path);
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
        insert_module_stamp_subst(&mut maps.module_stamp_map, old_id, new_path);
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
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        std::fs::write(
            temp_dir.path().join("Belt_MapString.cmj"),
            include_bytes!("../../tests/fixtures/Belt_MapString.cmj"),
        )
        .expect("CMJ fixture should be written");

        let mut env = PersistentEnv::new();
        env.add_load_path(temp_dir.path().to_path_buf());
        let exports = env
            .module_cmj_export_constants("Belt_MapString")
            .expect("expected decoded cmj exports");

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
    if merged.protected_module_head.is_none() {
        merged.protected_module_head = child.protected_module_head.clone();
    }
    merged
}

fn freshen_module_type_bound_idents_with_maps(
    module_type: &mut ModuleType,
    maps: &SubstMaps,
    ctx: &TypeContext,
) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            if !maps.is_empty() {
                // OCaml compiler/ml/subst.ml:345-348 handles `Mty_ident`
                // through the modtype substitution table; Rust shares the
                // type/modtype id map here, with dotted prefixes still going
                // through `module_path` like compiler/ml/subst.ml:78-84.
                *path = substitute_type_path(
                    path,
                    &maps.type_stamp_map,
                    &maps.type_name_map,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                    maps.protected_module_head.as_ref(),
                );
            }
        }
        ModuleType::MtyAlias(_, path) => {
            if !maps.is_empty() {
                // OCaml compiler/ml/subst.ml:358-364 applies
                // `module_path` to `Mty_alias` targets. Using the type path
                // map here leaves freshly included sibling aliases pointing at
                // stale module identifiers instead of the renamed module id.
                *path = substitute_module_path(
                    path,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                    maps.protected_module_head.as_ref(),
                );
            }
        }
        ModuleType::MtySignature(sig) => {
            freshen_signature_bound_idents_with_maps(crate::types::decl::signature_mut(sig), maps, ctx);
        }
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let old_param = param.clone();
            // OCaml compiler/ml/subst.ml:352-355 renames the functor
            // parameter, then observes `Mty_functor` argument evaluation by
            // freshening the result before the argument module type. This
            // stamp order is observable in strict typedtree identifiers.
            let new_param = ctx.rename_ident(&old_param);
            *param = new_param.clone();
            let mut param_maps = SubstMaps::default();
            insert_module_subst_path(&mut param_maps, &old_param, &new_param);
            let result_maps = merge_subst_maps(maps, &param_maps);
            freshen_module_type_bound_idents_with_maps(result, &result_maps, ctx);
            if let Some(param_type) = param_type.as_mut() {
                freshen_module_type_bound_idents_with_maps(param_type, maps, ctx);
            }
        }
    }
}

fn freshen_signature_bound_idents_with_maps(
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext,
) {
    let mut local_maps = SubstMaps::default();
    let mut has_nested_module_types = false;

    if !maps.is_empty() {
        substitute_type_paths_in_sig_with_maps(sig_items, maps, ctx);
        substitute_sig_decl_paths_in_place_with_maps(sig_items, maps);
    }

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigTypext(id, _, _) => {
                *id = ctx.rename_ident(id);
            }
            SignatureItem::SigType(id, _, _) => {
                let old_id = id.clone();
                let new_id = ctx.rename_ident(&old_id);
                insert_type_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigModtype(id, mtd) => {
                has_nested_module_types |= mtd.mtd_type.is_some();
                let old_id = id.clone();
                let new_id = ctx.rename_ident(&old_id);
                insert_type_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigModule(id, _, _) => {
                has_nested_module_types = true;
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

    if !has_nested_module_types {
        return;
    }

    let owned_combined_maps = if local_maps.is_empty() {
        None
    } else if maps.is_empty() && maps.protected_module_head.is_none() {
        None
    } else {
        Some(merge_subst_maps(maps, &local_maps))
    };
    let combined_maps = match owned_combined_maps.as_ref() {
        Some(combined_maps) => combined_maps,
        None if local_maps.is_empty() => maps,
        None => &local_maps,
    };

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                freshen_module_type_bound_idents_with_maps(&mut md.md_type, combined_maps, ctx);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    freshen_module_type_bound_idents_with_maps(module_type, combined_maps, ctx);
                }
            }
            _ => {}
        }
    }
}

fn freshened_signature_ident_plan(
    sig_items: &[SignatureItem],
    ctx: &TypeContext,
) -> (Vec<Option<Ident>>, SubstMaps, bool) {
    let mut local_maps = SubstMaps::default();
    let mut new_idents = Vec::with_capacity(sig_items.len());
    let mut has_nested_module_types = false;

    for item in sig_items {
        match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigTypext(id, _, _) => {
                new_idents.push(Some(ctx.rename_ident(id)));
            }
            SignatureItem::SigType(id, _, _) => {
                let new_id = ctx.rename_ident(id);
                insert_type_subst_path(&mut local_maps, id, &new_id);
                new_idents.push(Some(new_id));
            }
            SignatureItem::SigModtype(id, mtd) => {
                has_nested_module_types |= mtd.mtd_type.is_some();
                let new_id = ctx.rename_ident(id);
                insert_type_subst_path(&mut local_maps, id, &new_id);
                new_idents.push(Some(new_id));
            }
            SignatureItem::SigModule(id, _, _) => {
                has_nested_module_types = true;
                let new_id = ctx.rename_ident(id);
                insert_module_subst_path(&mut local_maps, id, &new_id);
                new_idents.push(Some(new_id));
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {
                new_idents.push(None);
            }
        }
    }

    (new_idents, local_maps, has_nested_module_types)
}

/// Number of binder stamps `freshened_signature_bound_idents_from_kind`
/// allocates for `sig_items`: one per top-level binder
/// (`freshened_signature_ident_plan`), then the nested module-type binders
/// renamed by `freshen_nested_signature_module_types`.
pub(crate) fn signature_freshen_stamp_count(sig_items: &[SignatureItem]) -> i32 {
    fn module_type_count(module_type: &ModuleType) -> i32 {
        match module_type {
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => 0,
            ModuleType::MtySignature(sig) => signature_freshen_stamp_count(sig),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                1 + module_type_count(result)
                    + param_type.as_ref().map_or(0, |param| module_type_count(param))
            }
        }
    }
    sig_items
        .iter()
        .map(|item| match item {
            SignatureItem::SigValue(..) | SignatureItem::SigTypext(..) | SignatureItem::SigType(..) => 1,
            SignatureItem::SigModtype(_, mtd) => {
                1 + mtd.mtd_type.as_ref().map_or(0, module_type_count)
            }
            SignatureItem::SigModule(_, md, _) => 1 + module_type_count(&md.md_type),
            SignatureItem::SigClass | SignatureItem::SigClassType => 0,
        })
        .sum()
}

fn freshen_nested_signature_module_types(sig_items: &mut [SignatureItem], ctx: &TypeContext) {
    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                freshen_module_type_bound_idents_with_maps(
                    &mut md.md_type,
                    &SubstMaps::default(),
                    ctx,
                );
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    freshen_module_type_bound_idents_with_maps(
                        module_type,
                        &SubstMaps::default(),
                        ctx,
                    );
                }
            }
            _ => {}
        }
    }
}

pub(crate) fn freshened_signature_bound_idents_from_kind(
    kind: &'static str,
    sig_items: &[SignatureItem],
    ctx: &TypeContext,
) -> Signature {
    // Mirrors OCaml `Subst.signature` (compiler/ml/subst.ml:358-364):
    // first build the global binder substitution, then copy each component
    // through that substitution with its renamed binder.
    if ctx.compiler_counters_enabled() {
        crate::perf_counters::record_signature_freshen(kind, sig_items.len());
    }
    let (new_idents, local_maps, has_nested_module_types) =
        freshened_signature_ident_plan(sig_items, ctx);
    let maps_empty = local_maps.is_empty();
    let rewrite_type_path = |path: &Path| {
        if maps_empty {
            path.clone()
        } else {
            substitute_type_path(
                path,
                &local_maps.type_stamp_map,
                &local_maps.type_name_map,
                &local_maps.module_stamp_map,
                &local_maps.module_name_map,
                local_maps.protected_module_head.as_ref(),
            )
        }
    };
    let rewrite_module_path = |path: &Path| {
        if maps_empty {
            path.clone()
        } else {
            substitute_module_path(
                path,
                &local_maps.module_stamp_map,
                &local_maps.module_name_map,
                local_maps.protected_module_head.as_ref(),
            )
        }
    };
    let mut copied = crate::types::typecore::copy_lookup_signature_for_subst_with_paths_and_idents(
        sig_items,
        ctx,
        &rewrite_type_path,
        &rewrite_module_path,
        new_idents,
    );
    if has_nested_module_types {
        freshen_nested_signature_module_types(&mut copied, ctx);
    }
    copied
}

pub(crate) fn freshen_module_type_bound_idents(module_type: &mut ModuleType, ctx: &TypeContext) {
    // OCaml compiler/ml/subst.ml:365-376 implements `Subst.modtype` by
    // returning a fresh module type; for signatures it reaches subst.ml:378-400,
    // where component types are copied before binder substitutions are applied.
    *module_type = crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
    freshen_module_type_bound_idents_with_maps(module_type, &SubstMaps::default(), ctx);
}

pub(crate) fn substitute_functor_result_module_path(
    module_type: &ModuleType,
    old_param: &Ident,
    arg_path: &Path,
    ctx: &TypeContext,
) -> ModuleType {
    // OCaml compiler/ml/typemod.ml:1321-1325 applies
    // `Subst.modtype (Subst.add_module param path ...) mty_res`.
    // compiler/ml/subst.ml:351-364 handles `Mty_signature` by first
    // renaming every signature binder and then applying the combined module
    // substitution. Do both together here; a plain path rewrite skips the
    // binder renames and creates later local identifiers too early.
    let mut copied = crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
    let mut maps = SubstMaps::default();
    if old_param.stamp() != 0 {
        insert_module_stamp_subst(&mut maps.module_stamp_map, old_param, arg_path.clone());
    } else {
        maps.module_name_map
            .insert(old_param.name().to_string(), arg_path.clone());
    }
    freshen_module_type_bound_idents_with_maps(&mut copied, &maps, ctx);
    copied
}

pub(crate) fn substitute_module_type_with_module_path_subst(
    module_type: &ModuleType,
    module_paths: &[(Ident, Path)],
    ctx: &TypeContext,
) -> ModuleType {
    // Mirrors the `Subst.modtype (Subst.add_module ...)` shape used by
    // compiler/ml/typemod.ml:1056-1120 for recursive-module inclusion. The
    // module type is copied first, then bound signature/functor ids are
    // freshened while module paths are rewritten through the same substitution.
    let mut copied = crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
    let mut maps = SubstMaps::default();
    for (id, path) in module_paths {
        if id.stamp() != 0 {
            insert_module_stamp_subst(&mut maps.module_stamp_map, id, path.clone());
        } else {
            maps.module_name_map
                .insert(id.name().to_string(), path.clone());
        }
    }
    freshen_module_type_bound_idents_with_maps(&mut copied, &maps, ctx);
    copied
}

pub(crate) fn freshen_functor_component_module_type(
    module_type: &ModuleType,
    parent_context: Option<(&Path, &[SignatureItem])>,
    ctx: &TypeContext,
) -> ModuleType {
    // OCaml compiler/ml/env.ml:1595-1602 builds `Functor_comps` by applying
    // `Subst.modtype sub` to the functor argument/result module types, without
    // applying `Subst.modtype` to the outer `Mty_functor` itself. That means
    // the result signature binders are freshened here, while the functor
    // parameter binder is not renamed until a full module declaration thunk is
    // forced through env.ml:865-882.
    let mut copied = crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
    let maps = parent_context
        .map(|(parent_module_path, parent_sig)| build_subst_maps(parent_sig, parent_module_path))
        .unwrap_or_default();
    freshen_module_type_bound_idents_with_maps(&mut copied, &maps, ctx);
    copied
}

pub(crate) fn freshen_component_modtype_declaration_bound_idents(
    mtd: &mut ModtypeDeclaration,
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
    ctx: &TypeContext,
) {
    if let Some(module_type) = mtd.mtd_type.as_mut() {
        // OCaml compiler/ml/env.ml:1530 builds the component substitution with
        // `prefix_idents`, then env.ml:1581-1585 stores
        // `Subst.modtype_declaration sub decl` in the component modtype table.
        // Rebuild and substitute with the parent signature maps here so outer
        // references inside module types (for example Belt_Id.cmp) are rooted
        // at the component access path before lookup observes them.
        *module_type = crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
        let maps = build_subst_maps(parent_sig, parent_module_path);
        freshen_module_type_bound_idents_with_maps(module_type, &maps, ctx);
    }
}

pub(crate) fn freshen_component_module_declaration_bound_idents(
    md: &mut ModuleDeclaration,
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
    ctx: &TypeContext,
) {
    // OCaml compiler/ml/env.ml:1568 stores child module declarations as
    // EnvLazy thunks. Forcing them through env.ml:475 runs
    // `Subst.modtype sub md.md_type`, with `sub` built by env.ml:1530.
    // Subst.modtype freshens signature binders at compiler/ml/subst.ml:352-364.
    md.md_type = crate::types::typecore::copy_lookup_module_type_for_subst(&md.md_type, ctx);
    let maps = build_subst_maps(parent_sig, parent_module_path);
    freshen_module_type_bound_idents_with_maps(&mut md.md_type, &maps, ctx);
}

fn build_subst_maps_for_module(sig_items: &[SignatureItem], module_path: &Path) -> SubstMaps {
    // OCaml compiler/ml/env.ml:1530-1538 builds substitution maps from the
    // component signature with `prefix_idents`, and compiler/ml/subst.ml:69-95
    // rewrites module paths only through those explicit maps.
    build_subst_maps(sig_items, module_path)
}

pub fn substitute_sig_path(path: &Path, sig_items: &[SignatureItem], module_path: &Path) -> Path {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    substitute_type_path(
        path,
        &maps.type_stamp_map,
        &maps.type_name_map,
        &maps.module_stamp_map,
        &maps.module_name_map,
        maps.protected_module_head.as_ref(),
    )
}

fn substitute_module_type_paths_with_maps(module_type: &mut ModuleType, maps: &SubstMaps) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            *path = substitute_type_path(
                path,
                &maps.type_stamp_map,
                &maps.type_name_map,
                &maps.module_stamp_map,
                &maps.module_name_map,
                maps.protected_module_head.as_ref(),
            );
        }
        ModuleType::MtyAlias(_, path) => {
            *path = substitute_module_path(
                path,
                &maps.module_stamp_map,
                &maps.module_name_map,
                maps.protected_module_head.as_ref(),
            );
        }
        ModuleType::MtySignature(sig) => {
            substitute_sig_decl_paths_in_place_with_maps(crate::types::decl::signature_mut(sig), maps);
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
                        maps.protected_module_head.as_ref(),
                    );
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut() {
                    *path = substitute_type_path(
                        path,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        maps.protected_module_head.as_ref(),
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
                    maps.protected_module_head.as_ref(),
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
                        maps.protected_module_head.as_ref(),
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
    ctx: &TypeContext,
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
                    maps.protected_module_head.as_ref(),
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
                        maps.protected_module_head.as_ref(),
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
                        maps.protected_module_head.as_ref(),
                        ctx,
                        &mut visited,
                    );
                }

                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
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
                                            maps.protected_module_head.as_ref(),
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
                                            maps.protected_module_head.as_ref(),
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
                                    maps.protected_module_head.as_ref(),
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
                                maps.protected_module_head.as_ref(),
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
                        maps.protected_module_head.as_ref(),
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
                                maps.protected_module_head.as_ref(),
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
                                maps.protected_module_head.as_ref(),
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
                        maps.protected_module_head.as_ref(),
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
            SignatureItem::SigModtype(..)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
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
    ctx: &TypeContext,
) {
    let parent_maps = build_subst_maps(parent_sig, parent_module_path);
    substitute_type_paths_in_sig_with_maps(child_sig, &parent_maps, ctx);
    // OCaml compiler/ml/env.ml:1454-1486 builds `prefix_idents` from the real
    // signature binders, and compiler/ml/subst.ml:69-95 rewrites module paths
    // only through those explicit bindings. Do not synthesize extra flattened
    // backing-head substitutions here: a scraped alias value type such as
    // `Crypto-NodeJs.KeyObject.t` is not a path to the parent `KeyObject`
    // binder, so OCaml leaves it unchanged while building child components at
    // compiler/ml/env.ml:1516-1578.
    restore_child_self_manifests_from_parent_scope(child_sig, parent_sig, parent_module_path, ctx);
}

fn restore_child_self_manifests_from_parent_scope(
    child_sig: &[SignatureItem],
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
    ctx: &TypeContext,
) {
    for child_item in child_sig {
        let SignatureItem::SigType(child_id, child_decl, _) = child_item else {
            continue;
        };
        let Some(manifest) = child_decl.type_manifest else {
            continue;
        };
        let manifest = ctx.repr(manifest);
        let desc = ctx.get_desc(manifest).clone();
        let TypeDesc::Tconstr { path, args, abbrev } = desc else {
            continue;
        };
        let Path::Pident(manifest_id) = &path else {
            continue;
        };
        if !manifest_id.same(child_id) {
            continue;
        }
        let has_parent_type = parent_sig.iter().any(|parent_item| {
            matches!(
                parent_item,
                SignatureItem::SigType(parent_id, parent_decl, _)
                    if parent_id.name() == child_id.name()
                        && !parent_id.same(child_id)
                        && parent_decl.type_params.len() == args.len()
            )
        });
        if !has_parent_type {
            continue;
        }

        // OCaml's `Subst.signature` first carries the incoming parent
        // substitution into nested signatures, then renames the child binders
        // by identifier identity only (compiler/ml/subst.ml:358-364,
        // compiler/ml/subst.ml:327-339, compiler/ml/subst.ml:87-95). If Rust
        // sees a direct child self-manifest here, it came from a non-recursive
        // alias that originally resolved to the parent scope; restore that
        // parent path before child-local qualification can preserve the wrong
        // self alias.
        ctx.set_desc(
            manifest,
            TypeDesc::Tconstr {
                path: Path::pdot(parent_module_path.clone(), child_id.name()),
                args,
                abbrev,
            },
        );
    }
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
    ctx: &TypeContext,
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
    ctx: &TypeContext,
) {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    let type_stamp_map = &maps.type_stamp_map;
    // OCaml compiler/ml/env.ml:1530-1538 builds a component substitution with
    // `prefix_idents`, then compiler/ml/subst.ml:87-95 and subst.ml:303-309
    // apply it to value/type descriptions. Rust in-process saved signatures can
    // contain stamp-0 `Pident(type_name)` self references after portable
    // serialization, so keep the direct signature binder names available for
    // this non-recursive component-root substitution.
    let mut direct_type_name_map = maps.type_name_map.clone();
    for item in sig_items {
        match item {
            SignatureItem::SigType(id, _, _) | SignatureItem::SigModtype(id, _) => {
                direct_type_name_map
                    .entry(id.name().to_string())
                    .or_insert_with(|| Path::pdot(module_path.clone(), id.name()));
            }
            _ => {}
        }
    }
    let type_name_map = direct_type_name_map;
    let module_stamp_map = &maps.module_stamp_map;
    let module_name_map = &maps.module_name_map;
    let protected_module_head = maps.protected_module_head.as_ref();

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
                    protected_module_head,
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(id, decl, _) => {
                // Substitute in type params
                for &param in &decl.type_params {
                    substitute_type_expr_path(
                        param,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        protected_module_head,
                        ctx,
                        &mut visited,
                    );
                }
                // Substitute in manifest
                if let Some(manifest) = decl.type_manifest {
                    // OCaml `Subst` rewrites by `Ident` identity, not by a
                    // bare name. If anchoring would turn a direct manifest into
                    // this type's own qualified path, keep the manifest as-is;
                    // parent-scope substitution handles outer aliases when a
                    // child module is later viewed through its enclosing path
                    // (compiler/ml/subst.ml:129, compiler/ml/ctype.ml:4389-4407).
                    if !direct_manifest_substitution_would_self_alias(
                        ctx,
                        id,
                        manifest,
                        module_path,
                        &type_stamp_map,
                        &type_name_map,
                        &module_stamp_map,
                        &module_name_map,
                        protected_module_head,
                    ) {
                        substitute_type_expr_path(
                            manifest,
                            &type_stamp_map,
                            &type_name_map,
                            &module_stamp_map,
                            &module_name_map,
                            protected_module_head,
                            ctx,
                            &mut visited,
                        );
                    }
                }
                // Substitute in constructor/label types
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
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
                                            protected_module_head,
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
                                            protected_module_head,
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
                                    protected_module_head,
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
                                protected_module_head,
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
                        protected_module_head,
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
                                protected_module_head,
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
                                protected_module_head,
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
                        protected_module_head,
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
pub(crate) fn substitute_type_paths_in_sig_with_stamp_map(
    sig_items: &[SignatureItem],
    stamp_map: &HashMap<i32, Path>,
    ctx: &TypeContext,
) {
    if stamp_map.is_empty() {
        return;
    }
    let empty: HashMap<String, Path> = HashMap::new();
    let empty_module_stamp: ModuleStampSubstMap = HashMap::new();
    let mut visited = HashSet::new();
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(
                    desc.val_type,
                    stamp_map,
                    &empty,
                    &empty_module_stamp,
                    &HashMap::new(),
                    None,
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
                        &empty_module_stamp,
                        &HashMap::new(),
                        None,
                        ctx,
                        &mut visited,
                    );
                }
                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(
                        manifest,
                        stamp_map,
                        &empty,
                        &empty_module_stamp,
                        &HashMap::new(),
                        None,
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
pub(crate) fn substitute_type_expr_path_pub(
    ty_ref: TypeExprRef,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    substitute_type_expr_path(
        ty_ref,
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
        ctx,
        visited,
    );
}

fn substitute_type_expr_path(
    initial_ty_ref: TypeExprRef,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    // Use an explicit work stack instead of recursion to avoid stack overflow
    // on large type graphs (e.g., objects with hundreds of fields create deep
    // Tfield chains, and Tlink chains from unification can be thousands deep).
    let mut work_stack = vec![initial_ty_ref];

    while let Some(ty_ref) = work_stack.pop() {
        if !visited.insert(ty_ref.key()) {
            continue; // Already visited (cycle detection)
        }

        let desc = ctx.borrow_desc(ty_ref);
        let mut replacement = None;

        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let new_path = substitute_type_path(
                    path,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    protected_module_head,
                );
                if new_path != *path {
                    let mut new_desc = (*desc).clone();
                    if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                        *path = new_path;
                    }
                    replacement = Some(new_desc);
                }

                // Push type arguments onto work stack
                for &arg in args {
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tarrow { args, ret } => {
                work_stack.extend(args.iter().map(|arg| arg.typ));
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
                // OCaml compiler/ml/subst.ml:226-235 rewrites
                // polymorphic-variant row_name paths while copying the row.
                if let Some((path, _)) = &row.row_name {
                    let new_path = substitute_type_path(
                        path,
                        type_stamp_map,
                        type_name_map,
                        module_stamp_map,
                        module_name_map,
                        protected_module_head,
                    );
                    if new_path != *path {
                        let mut new_desc = (*desc).clone();
                        if let TypeDesc::Tvariant(ref mut row) = new_desc
                            && let Some((ref mut path, _)) = row.row_name
                        {
                            *path = new_path;
                        }
                        replacement = Some(new_desc);
                    }
                }
                if let Some((_, args)) = &row.row_name {
                    for &arg in args {
                        work_stack.push(arg);
                    }
                }
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
                    protected_module_head,
                );
                if new_path != *path {
                    let mut new_desc = (*desc).clone();
                    if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                        *path = new_path;
                    }
                    replacement = Some(new_desc);
                }
                for &arg in args {
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
        drop(desc);
        if let Some(new_desc) = replacement {
            ctx.set_desc(ty_ref, new_desc);
        }
    }
}

/// Component substitution used by `substitute_type_paths_in_value_from_sig`.
/// It depends only on the component signature and access path, so component
/// tables can build it once and reuse it for every value lookup.
#[derive(Debug)]
pub struct ValueSubstMaps {
    maps: SubstMaps,
    direct_type_name_map: HashMap<String, Path>,
}

pub fn build_value_subst_maps(sig_items: &[SignatureItem], module_path: &Path) -> ValueSubstMaps {
    let maps = build_subst_maps_for_module(sig_items, module_path);
    // OCaml compiler/ml/env.ml:1530-1538 builds component substitutions with
    // `prefix_idents`, then compiler/ml/subst.ml:303-309 applies
    // `Subst.value_description`. In-process persistent signatures can preserve
    // raw stamp-0 `Pident(type_name)` refs for component-local types, so keep the
    // same direct binder-name fallback used by `substitute_type_paths_in_sig`.
    let mut direct_type_name_map = maps.type_name_map.clone();
    for item in sig_items {
        match item {
            SignatureItem::SigType(id, _, _) | SignatureItem::SigModtype(id, _) => {
                direct_type_name_map
                    .entry(id.name().to_string())
                    .or_insert_with(|| Path::pdot(module_path.clone(), id.name()));
            }
            _ => {}
        }
    }
    ValueSubstMaps {
        maps,
        direct_type_name_map,
    }
}

pub fn substitute_type_paths_in_value_from_sig(
    desc: &mut crate::types::decl::ValueDescription,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let value_maps = build_value_subst_maps(sig_items, module_path);
    substitute_type_paths_in_value_with_maps(desc, &value_maps, sig_items, module_path, ctx);
}

pub fn substitute_type_paths_in_value_with_maps(
    desc: &mut crate::types::decl::ValueDescription,
    value_maps: &ValueSubstMaps,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let maps = &value_maps.maps;
    let direct_type_name_map = &value_maps.direct_type_name_map;
    let type_stamp_map = &maps.type_stamp_map;
    let type_name_map = direct_type_name_map;
    let module_stamp_map = &maps.module_stamp_map;
    let module_name_map = &maps.module_name_map;
    let protected_module_head = maps.protected_module_head.as_ref();

    if type_stamp_map.is_empty()
        && type_name_map.is_empty()
        && module_stamp_map.is_empty()
        && module_name_map.is_empty()
    {
        return;
    }

    let mut visited = HashSet::new();
    substitute_type_expr_path(
        desc.val_type,
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
        ctx,
        &mut visited,
    );

    for alias_source in ctx.alias_sources_for_component_path(module_path) {
        for item in sig_items {
            let SignatureItem::SigType(id, _, _) = item else {
                continue;
            };
            let old_path = Path::pdot(alias_source.clone(), id.name());
            let new_path = Path::pdot(module_path.clone(), id.name());
            if old_path.same(&new_path) {
                continue;
            }
            // OCaml compiler/ml/env.ml:1454-1481 `prefix_idents`
            // creates a selected component type path for each `Sig_type`,
            // and env.ml:1530-1538 applies compiler/ml/subst.ml:303-309
            // `Subst.value_description` before typecore.ml:2421-2457
            // instances the selected value. Rust CMI type graphs can still
            // contain the flattened persistent backing path for that same
            // component type, so rewrite only the current component's direct
            // type binders at the Env substitution boundary.
            rewrite_type_expr_by_path_prefix_pub(desc.val_type, &old_path, &new_path, ctx);
        }
    }
}

fn direct_manifest_substitution_would_self_alias(
    ctx: &TypeContext,
    id: &Ident,
    manifest: TypeExprRef,
    module_path: &Path,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
) -> bool {
    let manifest = ctx.repr(manifest);
    let desc = ctx.get_desc(manifest);
    let TypeDesc::Tconstr { path, args, .. } = &*desc else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }

    let substituted = substitute_type_path(
        path,
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
    );
    substituted.same(&Path::pdot(module_path.clone(), id.name()))
}

fn substitute_type_path(
    path: &Path,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
) -> Path {
    match path {
        Path::Pident(ident) => {
            if ident.stamp() != 0 {
                // OCaml compiler/ml/subst.ml:87-100 `type_path` rewrites
                // non-persistent ids through Ident.find_same only. It does not
                // fall back to declaration names or flattened path spelling.
                type_stamp_map
                    .get(&ident.stamp())
                    .cloned()
                    .unwrap_or_else(|| path.clone())
            } else {
                type_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| path.clone())
            }
        }
        Path::Pdot(prefix, name, pos) => {
            let rewritten_prefix = substitute_module_path(
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            );
            Path::Pdot(std::sync::Arc::new(rewritten_prefix), name.clone(), *pos)
        }
        Path::Papply(left, right) => Path::Papply(
            std::sync::Arc::new(substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            )),
            std::sync::Arc::new(substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            )),
        ),
    }
}

fn substitute_module_path(
    path: &Path,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
) -> Path {
    match path {
        Path::Pident(ident) => {
            if ident.stamp() != 0 {
                let protected = protected_module_head
                    .is_some_and(|(stamp, name)| *stamp == ident.stamp() && name == ident.name());
                // OCaml compiler/ml/subst.ml:69-76 `module_path` rewrites
                // non-persistent ids through Ident.find_same only. It does not
                // fall back to declaration names or flattened path spelling.
                module_stamp_map
                    .get(&ident.stamp())
                    .and_then(|(_, path)| (!protected).then(|| path.clone()))
                    .unwrap_or_else(|| path.clone())
            } else {
                module_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| path.clone())
            }
        }
        Path::Pdot(prefix, name, pos) => {
            let rewritten_prefix = substitute_module_path(
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            );
            Path::Pdot(std::sync::Arc::new(rewritten_prefix), name.clone(), *pos)
        }
        Path::Papply(left, right) => Path::Papply(
            std::sync::Arc::new(substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            )),
            std::sync::Arc::new(substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
                protected_module_head,
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
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.key()) {
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
        TypeDesc::Tarrow { args, ret } => {
            for arg in args {
                rewrite_type_expr_prefix(arg.typ, old_name, new_prefix, ctx, visited);
            }
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
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_prefix(path, old_name, new_prefix)
            {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tvariant(ref mut row) = new_desc
                    && let Some((ref mut path, _)) = row.row_name
                {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            if let Some((_, args)) = &row.row_name {
                for &arg in args {
                    rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
                }
            }
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
                    return Some(Path::Pdot(
                        std::sync::Arc::new(new_prefix.clone()),
                        name.clone(),
                        *pos,
                    ));
                }
            }
            // Recursively check deeper paths
            let rewritten_inner = rewrite_path_prefix(inner, old_name, new_prefix);
            rewritten_inner
                .map(|new_inner| Path::Pdot(std::sync::Arc::new(new_inner), name.clone(), *pos))
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
            rewrite_module_prefix_paths_in_sig(crate::types::decl::signature_mut(sig), old_name, new_prefix);
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
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut() {
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

// OCaml compiler/ml/env.ml:1530-1578 builds one component-table level at a
// time; child module declarations remain lazy component thunks at env.ml:1568
// and env.ml:1573. This path-metadata rewrite therefore intentionally stops at
// the current signature level instead of descending into child modules.
pub fn rewrite_module_prefix_paths_in_sig_shallow(
    sig_items: &mut [SignatureItem],
    old_name: &str,
    new_prefix: &Path,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut()
                    && let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut()
                    && let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_prefix(&ext.ext_type_path, old_name, new_prefix)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, _, _)
            | SignatureItem::SigModtype(_, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
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
    ctx: &TypeContext,
) {
    let mut visited = HashSet::new();
    rewrite_module_prefix_in_sig_with_visited(sig_items, old_name, new_prefix, ctx, &mut visited);
}

// OCaml compiler/ml/env.ml:1530-1578 applies prefix_idents substitution only to
// the component table currently being built. Child module bodies are represented
// by env.ml:1568/env.ml:1573 lazy thunks, so their type expressions are rewritten
// only when those component thunks are forced.
pub fn rewrite_module_prefix_in_sig_shallow(
    sig_items: &[SignatureItem],
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext,
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
                    TypeKind::TypeVariant(constrs, _) => {
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
            SignatureItem::SigModule(_, _, _)
            | SignatureItem::SigModtype(_, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
        }
    }
}

fn rewrite_module_type_prefix_in_module_type(
    module_type: &ModuleType,
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    match module_type {
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        ModuleType::MtySignature(sig) => {
            rewrite_module_prefix_in_sig_with_visited(sig, old_name, new_prefix, ctx, visited);
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_ref() {
                rewrite_module_type_prefix_in_module_type(
                    param_type, old_name, new_prefix, ctx, visited,
                );
            }
            rewrite_module_type_prefix_in_module_type(result, old_name, new_prefix, ctx, visited);
        }
    }
}

fn rewrite_module_prefix_in_sig_with_visited(
    sig_items: &[SignatureItem],
    old_name: &str,
    new_prefix: &Path,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                rewrite_type_expr_prefix(desc.val_type, old_name, new_prefix, ctx, visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_prefix(param, old_name, new_prefix, ctx, visited);
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_prefix(manifest, old_name, new_prefix, ctx, visited);
                }
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        rewrite_type_expr_prefix(
                                            arg, old_name, new_prefix, ctx, visited,
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
                                            visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_prefix(res, old_name, new_prefix, ctx, visited);
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
                                visited,
                            );
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    rewrite_type_expr_prefix(param, old_name, new_prefix, ctx, visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            rewrite_type_expr_prefix(
                                lbl.ld_type,
                                old_name,
                                new_prefix,
                                ctx,
                                visited,
                            );
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    rewrite_type_expr_prefix(ret, old_name, new_prefix, ctx, visited);
                }
            }
            SignatureItem::SigModule(_id, md, _) => {
                // OCaml compiler/ml/env.ml:1530-1538 `prefix_idents`
                // substitution walks the full component signature. Nested module
                // type expressions are reachable through Mty_signature items, so
                // descend into them here as the mutable path rewriter already does
                // in rewrite_module_type_prefix_paths.
                rewrite_module_type_prefix_in_module_type(
                    &md.md_type,
                    old_name,
                    new_prefix,
                    ctx,
                    visited,
                );
            }
            SignatureItem::SigModtype(_id, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_ref() {
                    rewrite_module_type_prefix_in_module_type(
                        module_type,
                        old_name,
                        new_prefix,
                        ctx,
                        visited,
                    );
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
                return Some(Path::Pdot(
                    std::sync::Arc::new(new_prefix.clone()),
                    name.clone(),
                    *pos,
                ));
            }
            rewrite_path_by_path_prefix(inner, old_prefix, new_prefix)
                .map(|new_inner| Path::Pdot(std::sync::Arc::new(new_inner), name.clone(), *pos))
        }
        _ => None,
    }
}

/// Prefix rewrites `(old, new)` tried in order, with an index from each old
/// prefix (compared with `Path::same`) to its first position.
struct PathPrefixes<'a> {
    pairs: &'a [(Path, Path)],
    index: Option<ahash::AHashMap<crate::types::context::SamePathKey, usize>>,
}

impl<'a> PathPrefixes<'a> {
    fn new(pairs: &'a [(Path, Path)]) -> Self {
        // A short list is cheaper to scan than to hash every ancestor.
        let index = (pairs.len() > 4).then(|| {
            let mut index = ahash::AHashMap::with_capacity(pairs.len());
            for (position, (old_prefix, _)) in pairs.iter().enumerate() {
                index
                    .entry(crate::types::context::SamePathKey::new(old_prefix.clone()))
                    .or_insert(position);
            }
            index
        });
        PathPrefixes { pairs, index }
    }
}

fn rewrite_path_by_path_prefixes(path: &Path, prefixes: &PathPrefixes<'_>) -> Option<Path> {
    let Some(index) = &prefixes.index else {
        for (old_prefix, new_prefix) in prefixes.pairs {
            if let Some(rewritten) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix) {
                return Some(rewritten);
            }
        }
        return None;
    };
    // The scan above returns the first prefix, in list order, equal to the
    // path or one of its `Pdot` ancestors. Find that prefix through the index,
    // then rewrite with it exactly as the scan would.
    let mut first: Option<usize> = None;
    let mut ancestor = path;
    loop {
        if let Some(&position) =
            index.get(&crate::types::context::SamePathKey::new(ancestor.clone()))
        {
            first = Some(first.map_or(position, |found| found.min(position)));
        }
        match ancestor {
            Path::Pdot(inner, _, _) => ancestor = inner,
            _ => break,
        }
    }
    let (old_prefix, new_prefix) = &prefixes.pairs[first?];
    rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
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
            rewrite_sig_paths_by_path_prefix(crate::types::decl::signature_mut(sig), old_prefix, new_prefix);
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
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut() {
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

// OCaml compiler/ml/env.ml:1530-1578 exposes selected component paths for the
// current table, while mtype.ml:98-102 keeps child modules strengthened as
// aliases to the scraped target. Keep this rewrite shallow so child module
// aliases are left for their env.ml:1568/env.ml:1573 component thunks.
pub fn rewrite_sig_paths_by_path_prefix_shallow(
    sig_items: &mut [SignatureItem],
    old_prefix: &Path,
    new_prefix: &Path,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut()
                    && let Some(rewritten) =
                        rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut()
                    && let Some(rewritten) =
                        rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_by_path_prefix(&ext.ext_type_path, old_prefix, new_prefix)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, _, _)
            | SignatureItem::SigModtype(_, _)
            | SignatureItem::SigClass
            | SignatureItem::SigClassType => {}
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
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.key()) {
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
        TypeDesc::Tarrow { args, ret } => {
            for arg in args {
                rewrite_type_expr_by_path_prefix(arg.typ, old_prefix, new_prefix, ctx, visited);
            }
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
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
            {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tvariant(ref mut row) = new_desc
                    && let Some((ref mut path, _)) = row.row_name
                {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            if let Some((_, args)) = &row.row_name {
                for &arg in args {
                    rewrite_type_expr_by_path_prefix(arg, old_prefix, new_prefix, ctx, visited);
                }
            }
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
    ctx: &TypeContext,
) {
    let mut visited = HashSet::new();
    rewrite_type_expr_by_path_prefix(ty_ref, old_prefix, new_prefix, ctx, &mut visited);
}

fn rewrite_type_expr_by_path_prefixes(
    ty_ref: TypeExprRef,
    prefixes: &PathPrefixes<'_>,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    if !visited.insert(ty_ref.key()) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_type_expr_by_path_prefixes(arg, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in args {
                rewrite_type_expr_by_path_prefixes(arg.typ, prefixes, ctx, visited);
            }
            rewrite_type_expr_by_path_prefixes(*ret, prefixes, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for &t in types {
                rewrite_type_expr_by_path_prefixes(t, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => {
            rewrite_type_expr_by_path_prefixes(*t, prefixes, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_expr_by_path_prefixes(*body, prefixes, ctx, visited);
            for &v in vars {
                rewrite_type_expr_by_path_prefixes(v, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_type_expr_by_path_prefixes(*fields, prefixes, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_type_expr_by_path_prefixes(*typ, prefixes, ctx, visited);
            rewrite_type_expr_by_path_prefixes(*rest, prefixes, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes)
            {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tvariant(ref mut row) = new_desc
                    && let Some((ref mut path, _)) = row.row_name
                {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            if let Some((_, args)) = &row.row_name {
                for &arg in args {
                    rewrite_type_expr_by_path_prefixes(arg, prefixes, ctx, visited);
                }
            }
            rewrite_type_expr_by_path_prefixes(row.row_more, prefixes, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_type_expr_by_path_prefixes(*t, prefixes, ctx, visited);
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            rewrite_type_expr_by_path_prefixes(t, prefixes, ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
        }
        TypeDesc::Tpackage { path, args, .. } => {
            if let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes) {
                let mut new_desc = (*desc).clone();
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for &arg in args {
                rewrite_type_expr_by_path_prefixes(arg, prefixes, ctx, visited);
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
    ctx: &TypeContext,
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
                    TypeKind::TypeVariant(constrs, _) => {
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

/// Rewrite all type paths in a signature using a batch of sibling path-prefix
/// substitutions. This mirrors OCaml `Subst` maps: one signature traversal can
/// apply all child component substitutions for a table.
pub fn rewrite_sig_by_path_prefixes(
    sig_items: &[SignatureItem],
    prefixes: &[(Path, Path)],
    ctx: &TypeContext,
) {
    if prefixes.is_empty() {
        return;
    }
    rewrite_sig_by_path_prefix_index(sig_items, &PathPrefixes::new(prefixes), ctx);
}

fn rewrite_sig_by_path_prefix_index(
    sig_items: &[SignatureItem],
    prefixes: &PathPrefixes<'_>,
    ctx: &TypeContext,
) {

    let mut visited = HashSet::new();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                rewrite_type_expr_by_path_prefixes(desc.val_type, prefixes, ctx, &mut visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_by_path_prefixes(param, prefixes, ctx, &mut visited);
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_by_path_prefixes(manifest, prefixes, ctx, &mut visited);
                }
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        rewrite_type_expr_by_path_prefixes(
                                            arg,
                                            prefixes,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        rewrite_type_expr_by_path_prefixes(
                                            lbl.ld_type,
                                            prefixes,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                rewrite_type_expr_by_path_prefixes(
                                    res,
                                    prefixes,
                                    ctx,
                                    &mut visited,
                                );
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            rewrite_type_expr_by_path_prefixes(
                                lbl.ld_type,
                                prefixes,
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
                    rewrite_sig_by_path_prefix_index(sub_sig, prefixes, ctx);
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
    ctx: &TypeContext,
) {
    substitute_submodule_paths(sig_items, module_path, ctx);
}

/// Recursively substitute type paths in sub-module signatures.
/// For a module like Belt with sub-modules Array, Map, etc.,
/// the types in Belt.Array should have paths like Pdot(Pdot(Pident "Belt") "Array") "t"
/// instead of Pident "t".
fn substitute_submodule_paths(sig_items: &[SignatureItem], module_path: &Path, ctx: &TypeContext) {
    // Match OCaml `prefix_idents`/`Subst` behavior: when descending into a
    // submodule, keep parent substitutions visible so child signatures can
    // reference parent-defined types through qualified paths.
    let parent_maps = build_subst_maps(sig_items, module_path);

    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            let sub_path = Path::pdot(module_path.clone(), id.name());
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                substitute_type_paths_in_sig_with_maps(sub_sig, &parent_maps, ctx);
                restore_child_self_manifests_from_parent_scope(
                    sub_sig,
                    sig_items,
                    module_path,
                    ctx,
                );
                substitute_type_paths_in_sig(sub_sig, &sub_path, ctx);
                substitute_submodule_paths(sub_sig, &sub_path, ctx);
            }
        }
    }
}

trait AliasRewriteSink {
    fn has_alias_rewrite(&self, key: &str) -> bool;
    fn insert_alias_rewrite_if_absent(&mut self, key: String, value: Path);
}

impl AliasRewriteSink for HashMap<String, Path> {
    fn has_alias_rewrite(&self, key: &str) -> bool {
        self.contains_key(key)
    }

    fn insert_alias_rewrite_if_absent(&mut self, key: String, value: Path) {
        self.entry(key).or_insert(value);
    }
}

impl AliasRewriteSink for AliasPrefixRewrites {
    fn has_alias_rewrite(&self, key: &str) -> bool {
        self.local.contains_key(key) || self.base.contains_key(key)
    }

    fn insert_alias_rewrite_if_absent(&mut self, key: String, value: Path) {
        self.insert_if_absent(key, value);
    }
}

/// Collect alias rewrite mappings from alias-shaped submodules.
/// When a module has `module JSON = Stdlib_JSON` (MtyAlias/MtyIdent), record
/// "Stdlib_JSON" → Pdot(Pident("Stdlib"), "JSON") so that when
/// Stdlib_JSON.cmi is later loaded, its types get rewritten.
fn collect_alias_rewrites<S: AliasRewriteSink>(
    sig_items: &[SignatureItem],
    module_path: &Path,
    rewrites: &mut S,
) {
    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            if let ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) =
                &md.md_type
            {
                // OCaml compiler/ml/env.ml:1517 scrapes aliases before
                // env.ml:1530-1538 prefixes component identifiers. Rust can store
                // that alias-shaped module as either MtyAlias or MtyIdent after CMI
                // loading, so record both forms for flattened namespace units such
                // as `Webapi__Fetch`.
                // Only the first mapping for a name is kept; skip building
                // the key and path for names already mapped.
                if let Path::Pident(alias_id) = alias_path
                    && !rewrites.has_alias_rewrite(alias_id.name())
                {
                    let qualified = Path::pdot(module_path.clone(), id.name_atom());
                    rewrites.insert_alias_rewrite_if_absent(alias_id.name().to_string(), qualified);
                }
            }
            // Also recurse into MtySignature submodules to find nested aliases
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                let sub_path = Path::pdot(module_path.clone(), id.name_atom());
                collect_alias_rewrites(sub_sig, &sub_path, rewrites);
            }
        }
    }
}

/// local bindings. This matches OCaml's behavior where opened modules have
/// lower lookup priority than local bindings (e.g., Predef types like `int`
/// are not shadowed when Pervasives.cmi is opened).
///
/// Add an already-built module component signature with opened-binding priority.
pub fn open_signature_components_into_env(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext,
) {
    // OCaml compiler/ml/env.ml:1874-1877 implements `open_signature` by
    // forcing `find_module_descr root` and passing the already-built component
    // table to `add_components`. The component table was built by
    // env.ml:1513-1588, including the env.ml:1530 `prefix_idents` substitution,
    // so an `open` must not apply a second signature-wide substitution here.
    add_signature_to_env_with_options(sig_items, module_path, env, ctx, true, false, true, None);
}

pub(crate) fn open_module_components_into_env(
    components: &crate::types::env_lazy::QualifiedModuleComponents,
    env: &mut Env,
    ctx: &TypeContext,
) {
    // OCaml compiler/ml/env.ml:1874-1877 calls `get_components
    // (find_module_descr root)` and compiler/ml/env.ml:1841-1860 installs that
    // same component table into the opened environment. Reuse the component view
    // that module lookup already forced so opened `comp_modules` and
    // `comp_components` share the same lazy state.
    open_components_into_env(components, env, ctx);
}

fn add_signature_to_env_with_options(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext,
    as_opened: bool,
    apply_path_subst: bool,
    register_loaded_types: bool,
    precomputed_components: Option<&crate::types::env_lazy::QualifiedModuleComponents>,
) {
    if as_opened {
        let layers = build_opened_layers(
            sig_items,
            module_path,
            ctx,
            apply_path_subst,
            register_loaded_types,
            precomputed_components,
        );
        env.add_prebuilt_open_layers(module_path.clone(), &layers);
        return;
    }
    add_signature_to_env_with_options_inner(
        sig_items,
        module_path,
        env,
        ctx,
        false,
        apply_path_subst,
        register_loaded_types,
        precomputed_components,
        None,
    );
}

/// The layer tables that opening `sig_items` under `module_path` adds.
fn build_opened_layers(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
    apply_path_subst: bool,
    register_loaded_types: bool,
    precomputed_components: Option<&crate::types::env_lazy::QualifiedModuleComponents>,
) -> crate::types::env::OpenedLayers {
    let mut out = None;
    add_signature_to_env_with_options_inner(
        sig_items,
        module_path,
        &mut Env::empty(),
        ctx,
        true,
        apply_path_subst,
        register_loaded_types,
        precomputed_components,
        Some(&mut out),
    );
    out.expect("opened layers built")
}

/// Open the component view `components` into `env`, reusing the view's
/// layer tables when another Env already opened it.
fn open_components_into_env(
    components: &crate::types::env_lazy::QualifiedModuleComponents,
    env: &mut Env,
    ctx: &TypeContext,
) {
    let layers = components.opened_layers(ctx, || {
        build_opened_layers(
            components.signature(),
            components.access_path(),
            ctx,
            false,
            true,
            Some(components),
        )
    });
    env.add_prebuilt_open_layers(components.access_path().clone(), &layers);
}

#[allow(clippy::too_many_arguments)]
fn add_signature_to_env_with_options_inner(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext,
    as_opened: bool,
    apply_path_subst: bool,
    register_loaded_types: bool,
    precomputed_components: Option<&crate::types::env_lazy::QualifiedModuleComponents>,
    opened_out: Option<&mut Option<crate::types::env::OpenedLayers>>,
) {
    // Apply path substitution: rewrite Tconstr paths from internal
    // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
    // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
    if apply_path_subst {
        substitute_type_paths_in_sig(sig_items, module_path, ctx);
    }

    fn collect_target_constr_nodes(
        ctx: &TypeContext,
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
                TypeDesc::Tarrow { args, ret } => {
                    work_stack.extend(args.iter().map(|arg| arg.typ));
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
                    if let Some((_, args)) = &row.row_name {
                        for arg in args {
                            work_stack.push(*arg);
                        }
                    }
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
        ctx: &TypeContext,
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
    let mut opened_values = Vec::new();
    let mut opened_types = Vec::new();
    let mut opened_constructors = Vec::new();
    let mut opened_labels = Vec::new();
    let mut opened_modules = Vec::new();
    let mut opened_module_components = Vec::new();
    let mut opened_modtypes = Vec::new();
    // `substitute_sig_path` rebuilds the component substitution for the whole
    // signature on every call; build it once for this open instead of once per
    // alias/extension item.
    let mut sig_subst_maps: Option<SubstMaps> = None;
    let mut substitute_path = |path: &Path| {
        let maps = sig_subst_maps
            .get_or_insert_with(|| build_subst_maps_for_module(sig_items, module_path));
        substitute_type_path(
            path,
            &maps.type_stamp_map,
            &maps.type_name_map,
            &maps.module_stamp_map,
            &maps.module_name_map,
            maps.protected_module_head.as_ref(),
        )
    };
    for item in sig_items.iter() {
        let slot_path = |name: &str, p: i32| {
            Path::Pdot(
                std::sync::Arc::new(module_path.clone()),
                name.to_string().into(),
                p,
            )
        };
        match item {
            SignatureItem::SigValue(id, desc) => {
                // Add value binding with qualified path
                let mut desc = desc.clone();
                let value_pos = pos;
                desc.val_path = Some(slot_path(id.name(), value_pos));
                // OCaml: only increment pos for non-primitive values
                if !matches!(desc.val_kind, crate::types::decl::ValueKind::ValPrim(_)) {
                    pos += 1;
                }
                if crate::debug_flags::debug_open_sig_values()
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
                    opened_values.push((id.clone(), desc, value_pos));
                } else {
                    env.add_value(id.clone(), desc);
                }
            }
            SignatureItem::SigType(id, decl, _rec_status) => {
                // Add type binding with qualified path
                let mut decl = (**decl).clone();
                decl.type_path = Some(Path::pdot(module_path.clone(), id.name()));
                let decl = Arc::new(decl);
                if as_opened {
                    opened_types.push((id.clone(), decl.clone()));
                } else {
                    env.add_type(id.clone(), decl.clone());
                }

                // Also register in global type store for alias expansion
                if register_loaded_types {
                    ctx.register_shared_type_decl(id.name(), decl.clone());
                    // Register by stamp for types from CMI modules (non-zero stamp)
                    if id.stamp() != 0 {
                        ctx.register_shared_type_decl_by_stamp(id.stamp(), decl.clone());
                    }
                }

                // Also add constructors and labels from this type
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, layout) => {
                        let type_path = Path::pdot(module_path.clone(), id.name());
                        for (position, cd) in constrs.iter().enumerate() {
                            let inline_record = match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    let inline_params =
                                        inline_record_type_params(ctx, &decl.type_params, labels);
                                    let inline_path =
                                        Path::pdot(type_path.clone(), cd.cd_id.name());
                                    let inline_decl = crate::types::TypeDeclaration {
                                        type_params: inline_params.clone(),
                                        type_arity: inline_params.len() as i32,
                                        type_kind: crate::types::TypeKind::TypeRecord(
                                            crate::types::decl::SharedVec::from(labels.clone()),
                                            crate::types::RecordRepresentation::RecordInlined {
                                                name: cd.cd_id.name().to_string(),
                                                representation:
                                                    crate::types::ConstructorReference {
                                                        variant: *layout,
                                                        position,
                                                    },
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
                                        type_representation:
                                            crate::types::TypeRepresentation::Boxed,
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
                                cstr_kind: ConstructorKind::Ordinary(
                                    crate::types::ConstructorReference {
                                        variant: *layout,
                                        position,
                                    },
                                ),
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
                                            opened_labels.push((ld.ld_id.clone(), label_desc));
                                        } else {
                                            env.add_label(ld.ld_id.clone(), label_desc);
                                        }
                                    }
                                }
                            }

                            if as_opened {
                                opened_constructors.push((cd.cd_id.clone(), cstr_desc));
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
                                opened_labels.push((ld.ld_id.clone(), label_desc));
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
                let module_pos = pos;
                let access_path = slot_path(id.name(), module_pos);
                pos += 1;
                md.md_path = Some(access_path.clone());
                // Rewrite module-type paths against the opened signature.
                // Persistent identifiers in debug output carry `!` (e.g.
                // `ArrayExt!`). Keep those top-level alias targets distinct so
                // they resolve through the persistent registry rather than the
                // opened binding currently being installed.
                let normalize_hidden_alias_path = |path: Path| -> Path {
                    fn go(
                        path: Path,
                        module_path: &Path,
                        module_name: &str,
                        access_path: &Path,
                    ) -> Path {
                        match path {
                            Path::Pident(alias_id) => {
                                if alias_id.is_persistent() {
                                    return Path::Pident(alias_id);
                                }
                                let clean = alias_id.name();
                                if clean == module_name {
                                    access_path.clone()
                                } else if clean == module_path.last() {
                                    module_path.clone()
                                } else {
                                    Path::Pident(alias_id)
                                }
                            }
                            Path::Pdot(prefix, name, pos) => Path::Pdot(
                                std::sync::Arc::new(go(
                                    prefix.as_ref().clone(),
                                    module_path,
                                    module_name,
                                    access_path,
                                )),
                                name,
                                pos,
                            ),
                            Path::Papply(functor, arg) => Path::Papply(
                                std::sync::Arc::new(go(
                                    functor.as_ref().clone(),
                                    module_path,
                                    module_name,
                                    access_path,
                                )),
                                std::sync::Arc::new(go(
                                    arg.as_ref().clone(),
                                    module_path,
                                    module_name,
                                    access_path,
                                )),
                            ),
                        }
                    }
                    go(path, module_path, id.name(), &access_path)
                };
                md.md_type = match md.md_type {
                    ModuleType::MtyAlias(alias_presence, alias_path) => {
                        let rewritten = substitute_path(&alias_path);
                        ModuleType::MtyAlias(alias_presence, normalize_hidden_alias_path(rewritten))
                    }
                    ModuleType::MtyIdent(path) => {
                        let rewritten = substitute_path(&path);
                        ModuleType::MtyIdent(normalize_hidden_alias_path(rewritten))
                    }
                    other => other,
                };
                if as_opened {
                    let direct_persistent_alias = matches!(
                        &md.md_type,
                        ModuleType::MtyAlias(_, Path::Pident(alias_id))
                            | ModuleType::MtyIdent(Path::Pident(alias_id))
                            if alias_id.is_persistent()
                    );
                    if direct_persistent_alias && precomputed_components.is_some() {
                        // OCaml compiler/ml/env.ml:1516-1518 scrapes a
                        // direct persistent child alias through env.ml:865-875
                        // `find_module`, so the child component table does not
                        // need the parent component environment. Avoid forcing
                        // the parent's `comp_components` just to open an
                        // equivalent persistent-alias thunk.
                        let stored = Arc::new(crate::types::env_lazy::StoredModuleComponents::new(
                            Env::empty(),
                            access_path.clone(),
                            md.clone(),
                        ));
                        opened_module_components.push((id.clone(), stored, module_pos));
                        opened_modules.push((id.clone(), md.clone(), module_pos));
                    } else if let Some((_, stored)) = precomputed_components
                        .and_then(|components| components.lookup_child_components(id.name(), ctx))
                    {
                        // OCaml compiler/ml/env.ml:1841-1877 opens the
                        // already-built `comp_components` table alongside
                        // `comp_modules`. Reuse that child component thunk so
                        // opened-module source lookup follows env.ml:1000-1013
                        // without forcing the parent module declaration.
                        opened_module_components.push((id.clone(), stored, module_pos));
                        opened_modules.push((id.clone(), md.clone(), module_pos));
                    } else {
                        opened_modules.push((id.clone(), md.clone(), module_pos));
                    }
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
                let mtd = precomputed_components
                    .and_then(|components| {
                        // OCaml compiler/ml/env.ml:1853-1855 opens
                        // `comp_modtypes`, whose entries were built at
                        // env.ml:1581-1584 via `Subst.modtype_declaration`.
                        components
                            .lookup_modtype(id.name(), ctx)
                            .map(|(_, component_mtd)| component_mtd.clone())
                    })
                    .unwrap_or_else(|| mtd.clone());
                if as_opened {
                    opened_modtypes.push((id.clone(), mtd));
                } else {
                    env.add_modtype(id.clone(), mtd);
                }
            }
            SignatureItem::SigTypext(id, ext, _status) => {
                let ext_slot = pos;
                pos += 1; // Extension constructors occupy runtime slots
                let ext_type_path = substitute_path(&ext.ext_type_path);
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
                    cstr_kind: ConstructorKind::Extension(slot_path(id.name(), ext_slot)),
                    cstr_generalized: ext.ext_ret_type.is_some(),
                    cstr_private: ext.ext_private,
                    cstr_loc: crate::location::Location::none(),
                    cstr_attributes: vec![],
                    cstr_inlined: None,
                };
                if as_opened {
                    opened_constructors.push((id.clone(), cstr_desc));
                } else {
                    env.add_constructor(id.clone(), cstr_desc);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {
                // Skip class/class_type (not used in ReScript)
            }
        }
    }
    if as_opened {
        let layers = crate::types::env::OpenedLayers::build(
            opened_values,
            opened_types,
            opened_constructors,
            opened_labels,
            opened_modules,
            opened_module_components,
            opened_modtypes,
        );
        match opened_out {
            Some(out) => *out = Some(layers),
            None => env.add_prebuilt_open_layers(module_path.clone(), &layers),
        }
    }
}

#[cfg(test)]
mod resolution_view_tests {
    use super::*;
    use crate::context::IdGenerator;

    #[test]
    fn cloned_views_share_reads_but_isolate_every_owned_overlay() {
        let mut original = PersistentEnv::new();
        original.set_compiling_module(Some("Original".to_string()));
        original.register_in_memory_module(
            "Original",
            InMemoryModuleInfo::new(PathBuf::from("original.res"), true, HashMap::new(), false),
        );
        original
            .view_mut()
            .source_fallback_path_overrides
            .insert("Source".to_string(), PathBuf::from("source.res"));
        original
            .view_mut()
            .hidden_modules
            .insert("Hidden".to_string());
        original
            .view_mut()
            .prepared_cached_alias_rewrites
            .insert("Prepared".to_string());
        original.view_mut().alias_prefix_rewrites.insert_if_absent(
            "Backing".to_string(),
            Path::pident(Ident::create_persistent("Selected")),
        );
        let mut query = original.clone();
        assert!(Arc::ptr_eq(&original.view, &query.view));
        assert!(query.is_compiling_module("Original"));
        assert!(Arc::ptr_eq(&original.view, &query.view));

        query.set_compiling_module(Some("Query".to_string()));
        query.view_mut().source_fallback_path_overrides.clear();
        query.view_mut().in_memory_module_overrides.clear();
        query.view_mut().hidden_modules.clear();
        query.view_mut().prepared_cached_alias_rewrites.clear();
        query.view_mut().alias_prefix_rewrites.local.clear();
        assert!(!Arc::ptr_eq(&original.view, &query.view));
        assert!(original.is_compiling_module("Original"));
        assert_eq!(original.view.source_fallback_path_overrides.len(), 1);
        assert_eq!(original.view.in_memory_module_overrides.len(), 1);
        assert!(original.view.hidden_modules.contains("Hidden"));
        assert!(
            original
                .view
                .prepared_cached_alias_rewrites
                .contains("Prepared")
        );
        assert!(original.view.alias_prefix_rewrites.get("Backing").is_some());
        // Existing persistent cache, diagnostics and CRC identities stay shared.
        assert!(Arc::ptr_eq(&original.cache, &query.cache));
        assert!(Arc::ptr_eq(&original.last_error, &query.last_error));
        assert!(Arc::ptr_eq(&original.crc_units, &query.crc_units));
    }

    #[test]
    fn warm_preparation_keeps_view_shared_and_cold_preparation_stays_private() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut original = PersistentEnv::new();
        original.register_in_memory_signature("M", vec![], "M.res", &ctx);
        let ps = original
            .find_pers_struct("M", &ctx)
            .expect("registered module");
        let mut warm = original.clone();
        warm.prepare_cached_pers_struct("M", &ps, &ctx);
        assert!(Arc::ptr_eq(&original.view, &warm.view));
        let mut cold = original.clone();
        cold.prepare_cached_pers_struct("Other", &ps, &ctx);
        assert!(!Arc::ptr_eq(&original.view, &cold.view));
        assert!(
            !original
                .view
                .prepared_cached_alias_rewrites
                .contains("Other")
        );
        assert!(cold.view.prepared_cached_alias_rewrites.contains("Other"));
    }

    #[test]
    fn registration_and_hiding_detach_on_their_first_write() {
        let mut original = PersistentEnv::new();
        original.register_in_memory_module(
            "M",
            InMemoryModuleInfo::new(PathBuf::from("M.res"), true, HashMap::new(), false),
        );
        let mut registered = original.clone();
        registered.register_in_memory_module(
            "N",
            InMemoryModuleInfo::new(PathBuf::from("N.res"), false, HashMap::new(), false),
        );
        assert!(!Arc::ptr_eq(&original.view, &registered.view));
        assert!(original.in_memory_info("N").is_none());
        assert!(registered.in_memory_info("N").is_some());
        let mut hidden = original.clone();
        hidden.unregister_in_memory_signature("M");
        assert!(!Arc::ptr_eq(&original.view, &hidden.view));
        assert!(original.in_memory_info("M").is_some());
        assert!(hidden.in_memory_info("M").is_none());
        assert!(Arc::ptr_eq(&original.cache, &hidden.cache));
        assert!(Arc::ptr_eq(&original.last_error, &registered.last_error));
        assert!(Arc::ptr_eq(&original.crc_units, &registered.crc_units));
    }

    #[test]
    fn portable_override_first_write_keeps_backing_graph_shared() {
        let portable = Arc::new(PortablePersStruct {
            ps_name: "Portable".to_string(),
            ps_filename: "Portable.res".to_string(),
            ps_sig: vec![],
            raw_ps_sig: None,
            cmi_longident_names: vec![],
            type_graph: portable_types::PortableTypeGraph {
                entries: vec![],
                variant_layouts: vec![],
            },
            raw_type_graph: None,
            fingerprint: 0,
        });
        let mut original = PersistentEnv::new();
        original
            .view_mut()
            .portable_cache_overrides
            .insert("Portable".to_string(), portable.clone());
        let mut query = original.clone();
        query
            .view_mut()
            .portable_cache_overrides
            .insert("Other".to_string(), portable.clone());
        assert!(!Arc::ptr_eq(&original.view, &query.view));
        assert!(!original.view.portable_cache_overrides.contains_key("Other"));
        assert!(Arc::ptr_eq(
            &original.view.portable_cache_overrides["Portable"],
            &query.view.portable_cache_overrides["Portable"]
        ));
        assert!(Arc::ptr_eq(
            &portable,
            &query.view.portable_cache_overrides["Other"]
        ));
    }

    #[test]
    fn source_fallback_resets_private_preparation_and_merges_real_aliases() {
        let dir = tempfile::tempdir().expect("fixture directory");
        let leaf = dir.path().join("Leaf.res");
        let backing = dir.path().join("Backing.res");
        let unit = dir.path().join("AliasUnit.res");
        std::fs::write(&leaf, "let value = 1\n").unwrap();
        std::fs::write(&backing, "module Child = Leaf\n").unwrap();
        std::fs::write(
            &unit,
            "module Alias = Backing.Child\nlet value = Alias.value\n",
        )
        .unwrap();
        let mut original = PersistentEnv::new();
        original.set_in_process_mode(true);
        original.set_nopervasives(true);
        for (name, path) in [
            ("Leaf", leaf),
            ("Backing", backing),
            ("AliasUnit", unit.clone()),
        ] {
            original
                .view_mut()
                .source_fallback_path_overrides
                .insert(name.to_string(), path);
        }
        original
            .view_mut()
            .prepared_cached_alias_rewrites
            .insert("AlreadyPrepared".to_string());
        original.cache_insert("Cycle".to_string(), None);
        let first = original.clone();
        let second = original.clone();
        let ctx1 = TypeContext::new(Arc::new(IdGenerator::new()));
        let ctx2 = TypeContext::new(Arc::new(IdGenerator::new()));
        let (sig1, fallback1) = first
            .typecheck_source_signature(&unit, &ctx1)
            .expect("first fallback");
        let (sig2, fallback2) = second
            .typecheck_source_signature(&unit, &ctx2)
            .expect("second fallback");
        assert_eq!(sig1.len(), sig2.len());
        assert!(
            sig1.iter()
                .any(|item| matches!(item,SignatureItem::SigModule(id,_,_) if id.name()=="Alias"))
        );
        assert!(!Arc::ptr_eq(&first.cache, &fallback1.cache));
        assert!(!Arc::ptr_eq(&fallback1.cache, &fallback2.cache));
        for fallback in [&fallback1, &fallback2] {
            assert_eq!(
                fallback.source_fallback_depth,
                original.source_fallback_depth + 1
            );
            {
                let cache = fallback.cache.lock().unwrap();
                assert!(matches!(cache.get("Cycle"), Some(None)));
            }
            assert!(
                !fallback
                    .view
                    .prepared_cached_alias_rewrites
                    .contains("AlreadyPrepared")
            );
        }
        assert!(
            original
                .view
                .prepared_cached_alias_rewrites
                .contains("AlreadyPrepared")
        );
        assert!(fallback1.view.alias_prefix_rewrites.get("Leaf").is_some());
        assert!(fallback2.view.alias_prefix_rewrites.get("Leaf").is_some());
        assert!(original.view.alias_prefix_rewrites.get("Leaf").is_none());
        assert!(!original.cache_contains_key("Leaf"));
        assert!(Arc::ptr_eq(&original.view, &first.view));
        assert!(Arc::ptr_eq(&original.view, &second.view));

        // Neither direct fallback populated the parent cache with type nodes.
        // The merge uses a third context only while that cache is still empty
        // apart from its cycle placeholder; no cross-context handles are read.
        {
            let cache = original.cache.lock().unwrap();
            assert_eq!(cache.len(), 1);
            assert!(matches!(cache.get("Cycle"), Some(None)));
        }
        let ctx3 = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut merged = original.clone();
        let loaded = merged
            .load_module_from_source_path_fallback("AliasUnit", &ctx3)
            .expect("merge fallback");
        assert_eq!(loaded.ps_name, "AliasUnit");
        assert!(merged.view.alias_prefix_rewrites.get("Leaf").is_some());
        assert!(original.view.alias_prefix_rewrites.get("Leaf").is_none());
        assert!(Arc::ptr_eq(&original.cache, &merged.cache));
        assert!(original.cache_contains_key("Leaf"));
        assert!(Arc::ptr_eq(&original.last_error, &merged.last_error));
        assert!(Arc::ptr_eq(&original.crc_units, &merged.crc_units));
    }
}
