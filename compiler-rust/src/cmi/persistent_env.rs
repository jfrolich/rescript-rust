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

use crate::types::path::PathView;
use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use std::fs;
use std::path::Path as FsPath;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::driver::{
    CompilerOptions, experimental_let_unwrap_for_structure, jsx_module_name,
    jsx_version_for_structure, load_pervasives, normalize_signature,
};
use crate::ident::Ident;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_constant::{Constant as LambdaConstant, PointerInfo};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda, PrimInfo,
    TagInfo,
};
use crate::location::Location;
use crate::name::Name;
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
    /// Stored modules registered without decoding their signature and JS
    /// metadata (see [`ModuleRegistry::register_stored_lazily`]): a lookup
    /// that misses decodes the module's entry first.
    lazy: Option<Arc<LazyStoredModules>>,
}

impl<V> Clone for SharedRegistryMap<V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            lazy: self.lazy.clone(),
        }
    }
}

impl<V> Default for SharedRegistryMap<V> {
    fn default() -> Self {
        Self {
            inner: Arc::new(RwLock::new(HashMap::new())),
            lazy: None,
        }
    }
}

/// The stored modules of a registry whose signature and JS metadata are not
/// decoded yet, with the registry maps that decoding one fills. An entry is
/// decoded once, by the first lookup of its name; until then the module
/// costs only its encoded bytes.
pub struct LazyStoredModules {
    pending: Mutex<HashMap<String, Arc<Mutex<Option<PendingCore>>>>>,
    cached_modules: Arc<RwLock<HashMap<String, Arc<PortablePersStruct>>>>,
    module_info: Arc<RwLock<HashMap<String, InMemoryModuleInfo>>>,
}

impl std::fmt::Debug for LazyStoredModules {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LazyStoredModules").finish_non_exhaustive()
    }
}

/// Reads the encoded core (see [`super::stored_module`]) of a stored module
/// by name, `None` when it cannot.
pub type CoreFetcher = Arc<dyn Fn(&str) -> Option<Vec<u8>> + Send + Sync>;

/// The not yet decoded core of a stored module: its bytes, or how to read
/// them, so a module the build never looks up is never read either.
pub enum PendingCore {
    /// The encoded core, borrowed when it is part of the executable (see
    /// [`ModuleRegistry::register_stored_static`]).
    Bytes(std::borrow::Cow<'static, [u8]>),
    /// Reads the encoded core when the module is first looked up.
    Fetch(CoreFetcher),
}

impl LazyStoredModules {
    /// Decode the pending entry of `name`, or of its first-character case
    /// variant, into the registry maps. Returns whether there was one.
    fn materialize_case(&self, name: &str) -> bool {
        self.materialize(name)
            || first_char_case_variant(name).is_some_and(|variant| self.materialize(&variant))
    }

    fn materialize(&self, name: &str) -> bool {
        self.materialize_with(name, None)
    }

    /// [`Self::materialize`], from `bytes` when given (read ahead by the
    /// caller) instead of the entry's own.
    fn materialize_with(&self, name: &str, bytes: Option<Vec<u8>>) -> bool {
        let Some(entry) = self.pending.lock().unwrap().get(name).cloned() else {
            return false;
        };
        // Concurrent lookups of the same module wait here for the first to
        // fill the maps.
        let mut pending = entry.lock().unwrap();
        let Some(core) = pending.take() else {
            return true;
        };
        let data: Option<std::borrow::Cow<'static, [u8]>> = match (bytes, core) {
            (Some(bytes), _) => Some(bytes.into()),
            (None, PendingCore::Bytes(bytes)) => Some(bytes),
            (None, PendingCore::Fetch(fetch)) => fetch(name).map(Into::into),
        };
        if let Some(core) = data.as_deref().and_then(super::stored_module::decode_core) {
            if let Some(pers) = core.pers_struct {
                self.cached_modules
                    .write()
                    .unwrap()
                    .insert(name.to_string(), Arc::new(pers));
            }
            self.module_info
                .write()
                .unwrap()
                .insert(name.to_string(), core.info);
        }
        drop(pending);
        self.pending.lock().unwrap().remove(name);
        true
    }

    fn remove(&self, name: &str) {
        self.pending.lock().unwrap().remove(name);
    }
}

impl<V> SharedRegistryMap<V> {
    /// Decode `name`'s pending stored module, if any; whether there was one.
    fn materialize_case(&self, name: &str) -> bool {
        self.lazy
            .as_ref()
            .is_some_and(|lazy| lazy.materialize_case(name))
    }

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
        if self.inner.read().unwrap().contains_key(key) {
            return true;
        }
        self.lazy.as_ref().is_some_and(|lazy| lazy.materialize(key))
            && self.inner.read().unwrap().contains_key(key)
    }
}

impl<V> SharedRegistryMap<V> {
    /// `f` of the value for `key`, read in place under the map's read lock:
    /// `f` must not look up this map again.
    fn with_value<R>(&self, key: &str, f: impl FnOnce(&V) -> R) -> Option<R> {
        {
            let inner = self.inner.read().unwrap();
            if let Some(value) = inner.get(key) {
                return Some(f(value));
            }
        }
        if !self.lazy.as_ref().is_some_and(|lazy| lazy.materialize(key)) {
            return None;
        }
        self.inner.read().unwrap().get(key).map(f)
    }
}

impl<V: Clone> SharedRegistryMap<V> {
    fn get_cloned(&self, key: &str) -> Option<V> {
        if let Some(value) = self.inner.read().unwrap().get(key).cloned() {
            return Some(value);
        }
        if !self.lazy.as_ref().is_some_and(|lazy| lazy.materialize(key)) {
            return None;
        }
        self.inner.read().unwrap().get(key).cloned()
    }

    fn get_case_cloned(&self, name: &str) -> Option<(String, V)> {
        let found = self.get_case_cloned_now(name);
        if found.is_some() || !self.materialize_case(name) {
            return found;
        }
        self.get_case_cloned_now(name)
    }

    fn get_case_cloned_now(&self, name: &str) -> Option<(String, V)> {
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
        let found = self.get_case_with_now(name, &mut f);
        if found.is_some() || !self.materialize_case(name) {
            return found;
        }
        self.get_case_with_now(name, &mut f)
    }

    fn get_case_with_now<R>(&self, name: &str, mut f: impl FnMut(&str, &V) -> R) -> Option<R> {
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
    /// The `Deprecated` persistence flag (`cmi_flags`, env.ml:663-668),
    /// reported when the unit is looked up (env.ml:1044-1048).
    pub ps_deprecated: Option<String>,
    /// `ps_crcs` (env.ml:669-678): the unit's `.cmi` CRC list, itself first.
    pub ps_crcs: Vec<(String, Option<[u8; 16]>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CmjExportConstant {
    Bool(bool),
    Null,
    Undefined { is_unit: bool },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CmjPackageModuleSystem {
    CommonJs,
    EsModule,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

/// Serialize a map in key order, so that equal maps encode identically.
fn serialize_sorted<V: serde::Serialize, S: serde::Serializer>(
    map: &Arc<HashMap<String, V>>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let mut entries: Vec<(&String, &V)> = map.iter().collect();
    entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
    serializer.collect_map(entries)
}

/// In-memory module metadata for the `--in-process` build mode.
///
/// When a module is registered in the in-memory registry, these fields
/// replace the disk-based lookups that normally read `.ast` (source path),
/// `.cmj` (purity), and `.cmi` (interface).
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct InMemoryModuleInfo {
    /// Source file path (replaces `.ast` source-path lookup)
    pub source_path: Arc<PathBuf>,
    /// Whether the module is side-effect free (replaces `.cmj` purity lookup)
    pub is_pure: bool,
    /// Closed constant exports (replaces `.cmj` constant lookup)
    #[serde(serialize_with = "serialize_sorted")]
    pub cmj_export_constants: Arc<HashMap<String, CmjExportConstant>>,
    /// Arity metadata for exports (replaces `.cmj` arity lookup)
    #[serde(serialize_with = "serialize_sorted")]
    pub cmj_export_arities: Arc<HashMap<String, CmjExportArity>>,
    /// Non-constant `persistent_closed_lambda` exports (replaces the `.cmj`
    /// lookup used for cross-module inlining, js_cmj_format.ml:112-121).
    pub cmj_export_lambdas: Arc<crate::lambda::CmjExportLambdas>,
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
    /// Where the module's JavaScript goes, per module system, as its `.cmj`
    /// records it (`Js_packages_info`, from `-bs-package-output`): the output
    /// directory relative to the package root and the suffix.
    pub package_outputs: Arc<Vec<CmjPackageInfo>>,
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
            cmj_export_lambdas: Arc::new(crate::lambda::CmjExportLambdas::default()),
            cmj_hoisted_exports: Arc::new(Vec::new()),
            is_runtime,
            package_name: None,
            package_root: None,
            js_output_suffix: None,
            package_outputs: Arc::new(Vec::new()),
        }
    }

    pub fn with_package_outputs(mut self, package_outputs: Vec<CmjPackageInfo>) -> Self {
        self.package_outputs = Arc::new(package_outputs);
        self
    }

    pub fn with_cmj_export_lambdas(
        mut self,
        cmj_export_lambdas: crate::lambda::CmjExportLambdas,
    ) -> Self {
        self.cmj_export_lambdas = Arc::new(cmj_export_lambdas);
        self
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
    /// Clean one-shot modules with validated typed artifacts on disk.
    disk_modules: SharedRegistryMap<bool>,
    /// Module metadata (source paths, purity, runtime status).
    module_info: SharedRegistryMap<InMemoryModuleInfo>,
    /// Alias prefix rewrites (flattened_name -> qualified_path) of the
    /// registered namespace modules. A compiled or stored module's aliases are
    /// not shared: a compilation collects them when it loads the module.
    alias_rewrites: SharedRegistryMap<Path>,
    /// Source file paths for ALL modules, including those not yet compiled.
    /// Used for on-demand source-based type checking when a module is needed
    /// as an implicit dependency (e.g., via `-open Pervasives`) but hasn't
    /// been compiled yet in the current wave.
    source_fallback_paths: SharedRegistryMap<PathBuf>,
    /// Package roots of registered modules that carry no `InMemoryModuleInfo`
    /// (namespace units), for load-path visibility.
    module_package_roots: SharedRegistryMap<PathBuf>,
    local_cached_modules: HashMap<String, Arc<PortablePersStruct>>,
    local_module_info: HashMap<String, InMemoryModuleInfo>,
    local_alias_rewrites: HashMap<String, Path>,
    local_source_fallback_paths: HashMap<String, PathBuf>,
    write_to_local: bool,
    /// Item references of registered signatures (see `resolve_reads`),
    /// shared by every snapshot. Keyed by the signature's identity, so a
    /// module registered again gets fresh entries.
    /// Keyed by unit, signature identity and fingerprint, and the identity
    /// of the JS metadata whose inlinable bodies the references follow
    /// (`usize::MAX` for references without them).
    item_refs_cache:
        Arc<RwLock<HashMap<(Name, usize, u64, usize), Arc<super::item_deps::UnitRefs>>>>,
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

    pub fn has_cached_module(&self, name: &str) -> bool {
        self.local_cached_modules.contains_key(name) || self.cached_modules.contains_key(name)
    }

    /// A digest of everything another module's compile can read about
    /// `name`: its published signature and its JS metadata (purity,
    /// constants, arities, inlinable lambdas, hoisted exports, package).
    /// Equal digests mean a dependent compiles to the same output. `None`
    /// when the module is not registered.
    /// The digest of the module's whole interface: of all its item digests
    /// (see [`super::item_deps::item_digests`]), so it changes exactly when
    /// what dependents compile against changes.
    pub fn interface_digest(&self, name: &str) -> Option<u64> {
        Some(self.item_digests(name)?[super::item_deps::WHOLE])
    }

    fn registered(
        &self,
        name: &str,
    ) -> (Option<Arc<PortablePersStruct>>, Option<InMemoryModuleInfo>) {
        let pers = self
            .local_cached_modules
            .get(name)
            .cloned()
            .or_else(|| self.cached_modules.get_cloned(name));
        let info = self
            .local_module_info
            .get(name)
            .cloned()
            .or_else(|| self.module_info.get_cloned(name));
        (pers, info)
    }

    /// `f` of the JS metadata of a registered module, read in place. `f`
    /// must not look up module metadata again.
    fn with_info<R>(&self, name: &str, f: impl FnOnce(&InMemoryModuleInfo) -> R) -> Option<R> {
        match self.local_module_info.get(name) {
            Some(info) => Some(f(info)),
            None => self.module_info.with_value(name, f),
        }
    }

    /// The per-item digests of a registered module
    /// (see [`super::item_deps::item_digests`]), `None` when it is not
    /// registered.
    pub fn item_digests(&self, name: &str) -> Option<std::collections::BTreeMap<String, u64>> {
        let (pers, info) = self.registered(name);
        if pers.is_none() && info.is_none() {
            return None;
        }
        Some(super::item_deps::item_digests(
            pers.as_deref(),
            info.as_ref(),
        ))
    }

    /// Resolve the reads of a compile against the registered modules' signatures
    /// (see [`super::item_deps::resolve_reads`]), leaving out what inlinable
    /// bodies refer to: a dependency publishes those with its JS metadata,
    /// possibly after this compile, while the signatures every reached unit
    /// is read through are final. [`Self::lambda_reads`] adds the rest once
    /// all metadata is final. Runtime modules are not recorded.
    pub fn resolve_signature_reads(
        &self,
        reads: Vec<super::item_deps::UnitRead>,
    ) -> super::item_deps::ResolvedReads {
        super::item_deps::resolve_reads(
            reads,
            &RegistryUnitSource {
                registry: self,
                lambdas: false,
            },
        )
    }

    /// What the inlinable bodies of the values and modules in `resolved`
    /// (reads from [`Self::resolve_signature_reads`]) refer to, closed over
    /// everything those units' items refer to.
    pub fn lambda_reads(
        &self,
        resolved: &super::item_deps::ResolvedReads,
    ) -> super::item_deps::ResolvedReads {
        use super::item_deps::{ItemKey, Kind, Segs, UnitRead};
        let source = RegistryUnitSource {
            registry: self,
            lambdas: true,
        };
        let mut seeds = Vec::new();
        for (unit, keys) in resolved {
            self.with_info(unit, |info| {
                let lambdas = &info.cmj_export_lambdas;
                if lambdas.is_empty() {
                    return;
                }
                let mut push = |name: &str| {
                    for lambda_unit in lambda_units_of(lambdas, name) {
                        seeds.push(UnitRead {
                            unit: lambda_unit,
                            segs: Segs::new(),
                            kind: Kind::Module,
                        });
                    }
                };
                if keys.contains(&ItemKey::Whole) {
                    lambdas.keys().for_each(|name| push(name));
                } else {
                    for key in keys {
                        if let ItemKey::Item(Kind::Value | Kind::Module, name) = key {
                            push(name.as_str());
                        }
                    }
                }
            });
        }
        if seeds.is_empty() {
            return super::item_deps::ResolvedReads::default();
        }
        super::item_deps::resolve_reads(seeds, &source)
    }

    /// The module's published interface encoded for storage (see
    /// [`super::stored_module`]), `None` when it is not registered.
    pub fn encode_stored_module(&self, name: &str) -> Option<Vec<u8>> {
        let (pers, info) = self.registered(name);
        let info = info?;
        let gentype_declarations = crate::gentype::main::type_declarations_of_module(name);
        Some(super::stored_module::encode(
            &super::stored_module::StoredModuleRef {
                pers_struct: pers.as_deref(),
                info: &info,
                gentype_declarations: &gentype_declarations,
            },
        ))
    }

    /// [`Self::encode_stored_module`] as its extras, `None` when it has none,
    /// and core (see [`super::stored_module::encode_parts`]).
    pub fn encode_stored_module_parts(&self, name: &str) -> Option<(Option<Vec<u8>>, Vec<u8>)> {
        let (pers, info) = self.registered(name);
        let info = info?;
        let gentype_declarations = crate::gentype::main::type_declarations_of_module(name);
        Some(super::stored_module::encode_parts(
            &super::stored_module::StoredModuleRef {
                pers_struct: pers.as_deref(),
                info: &info,
                gentype_declarations: &gentype_declarations,
            },
        ))
    }

    /// Register a stored module's interface (see
    /// [`super::stored_module::encode`]), as compiling it would. Its GenType
    /// declarations are registered now; its signature and JS metadata are
    /// decoded by the first lookup of the module, so a build that registers
    /// many stored modules pays only for those its compiles read. Returns
    /// `None`, registering nothing, when the data does not decode.
    pub fn register_stored_lazily(&mut self, name: &str, data: &[u8]) -> Option<()> {
        let (extras, core) = super::stored_module::split(data)?;
        self.register_stored_parts(name, Some(extras), PendingCore::Bytes(core.to_vec().into()))
    }

    /// [`Self::register_stored_lazily`] for data that lives as long as the
    /// process (compiled into the executable), which the registry borrows
    /// instead of copying.
    pub fn register_stored_static(
        &mut self,
        name: &str,
        data: &'static [u8],
    ) -> Option<()> {
        let (extras, core) = super::stored_module::split(data)?;
        self.register_stored_parts(name, Some(extras), PendingCore::Bytes(core.into()))
    }

    /// [`Self::register_stored_lazily`] for a module stored as its encoded
    /// extras (`None` for none) and core (see
    /// [`super::stored_module::encode_parts`]), the core possibly still to be
    /// read.
    pub fn register_stored_parts(
        &mut self,
        name: &str,
        extras: Option<&[u8]>,
        core: PendingCore,
    ) -> Option<()> {
        assert!(
            !self.write_to_local,
            "stored modules are registered in the shared registry"
        );
        let extras = match extras {
            Some(extras) => super::stored_module::decode_extras(extras)?,
            None => super::stored_module::StoredExtras::default(),
        };
        let lazy = self.lazy_stored_modules();
        crate::gentype::main::restore_type_declarations(name, extras.gentype_declarations);
        lazy.pending
            .lock()
            .unwrap()
            .insert(name.to_string(), Arc::new(Mutex::new(Some(core))));
        Some(())
    }

    /// Decode `name`'s stored module now if it is registered with
    /// [`Self::register_stored_lazily`] and not decoded yet, so a build can
    /// decode the modules it knows its compiles will read in parallel. With
    /// `core`, from those bytes (read ahead) instead of the entry's own.
    pub fn decode_stored(&self, name: &str, core: Option<Vec<u8>>) {
        if let Some(lazy) = &self.cached_modules.lazy {
            lazy.materialize_with(name, core);
        }
    }

    /// Whether `name` is a stored module registered with
    /// [`Self::register_stored_lazily`] and not decoded yet.
    pub fn is_pending_stored(&self, name: &str) -> bool {
        self.cached_modules
            .lazy
            .as_ref()
            .is_some_and(|lazy| lazy.pending.lock().unwrap().contains_key(name))
    }

    /// The registry's pending stored modules, created on first use and
    /// attached to the maps decoding fills, so every later snapshot and
    /// `PersistentEnv` of the registry decodes on lookup.
    fn lazy_stored_modules(&mut self) -> Arc<LazyStoredModules> {
        if let Some(lazy) = &self.cached_modules.lazy {
            return lazy.clone();
        }
        let lazy = Arc::new(LazyStoredModules {
            pending: Mutex::new(HashMap::new()),
            cached_modules: self.cached_modules.inner.clone(),
            module_info: self.module_info.inner.clone(),
        });
        self.cached_modules.lazy = Some(lazy.clone());
        self.module_info.lazy = Some(lazy.clone());
        lazy
    }

    pub fn register_disk_module(&mut self, name: &str, info: InMemoryModuleInfo) {
        self.disk_modules.insert(name.to_string(), true);
        self.insert_module_info(name.to_string(), info);
    }

    pub fn is_empty(&self) -> bool {
        self.local_cached_modules.is_empty()
            && self.cached_modules.len() == 0
            && self.disk_modules.len() == 0
            && self
                .cached_modules
                .lazy
                .as_ref()
                .is_none_or(|lazy| lazy.pending.lock().unwrap().is_empty())
    }

    pub fn module_info_is_runtime(&self, name: &str) -> bool {
        self.with_info(name, |info| info.is_runtime)
            .unwrap_or(false)
    }

    /// Register a namespace module's alias signature directly.
    /// This is the registry-level equivalent of `PersistentEnv::register_namespace_in_memory`.
    pub fn register_namespace(
        &mut self,
        namespace_name: &str,
        module_aliases: &[(String, String)],
    ) {
        self.register_namespace_for_package(namespace_name, module_aliases, None, Vec::new());
    }

    /// [`Self::register_namespace`] for a namespace owned by the package at
    /// `package_root` (its `.mlmap` is only on that package's load path).
    pub fn register_namespace_for_package(
        &mut self,
        namespace_name: &str,
        module_aliases: &[(String, String)],
        package_root: Option<PathBuf>,
        ps_crcs: Vec<(String, Option<[u8; 16]>)>,
    ) {
        if let Some(root) = package_root {
            self.module_package_roots
                .insert(namespace_name.to_string(), root);
        }
        let mut sig_items: Signature = Vec::with_capacity(module_aliases.len());
        for (short_name, internal_name) in module_aliases {
            sig_items.push(SignatureItem::SigModule(
                Ident::create_persistent(short_name.as_str()),
                ModuleDeclaration {
                    // As saved in the namespace `.cmi`: an alias typed by
                    // `type_module_aux` is `Mty_alias (Mta_absent, path)`.
                    md_type: ModuleType::MtyAlias(
                        AliasPresence::MtaAbsent,
                        Path::pident(Ident::create_persistent(internal_name.as_str())),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ));
        }

        // Record alias rewrites
        let module_path = Path::pident(Ident::create_persistent(namespace_name));
        let mut new_alias_rewrites = HashMap::new();
        collect_alias_rewrites(&sig_items, &module_path, &mut new_alias_rewrites);
        self.extend_alias_rewrites(new_alias_rewrites);

        // Namespace signatures contain only MtyAlias entries (no TypeExprRefs),
        // so the portable type graph is empty.
        let fingerprint = portable_types::compute_type_graph_fingerprint(
            &portable_types::HashGraph {
                entries: &[],
                layouts: &[],
                mutabilities: &[],
            },
            &sig_items,
        );
        let portable = PortablePersStruct::new(
            namespace_name.to_string(),
            format!("{}.mlmap", namespace_name),
            None,
            // The saved `.cmi`'s CRC list, recorded by importers like any
            // loaded unit's (env.ml:627-638, 1924-1930).
            ps_crcs,
            portable_types::PortableSignature {
                ps_sig: sig_items,
                cmi_longident_names: Vec::new(),
                type_graph: portable_types::PortableTypeGraph {
                    entries: Vec::new(),
                    variant_layouts: Vec::new(),
                    mutabilities: Vec::new(),
                },
                locations: Default::default(),
            },
            None,
            fingerprint,
        );
        self.insert_cached_module(namespace_name.to_string(), Arc::new(portable));
    }

    /// Remove a module from the registry (for deleted/renamed modules).
    /// Purges cached signature, module info, source fallback, and any alias
    /// rewrites that reference this module.
    pub fn purge_module(&mut self, name: &str) {
        if let Some(lazy) = &self.cached_modules.lazy {
            lazy.remove(name);
        }
        self.cached_modules.remove(name);
        self.local_cached_modules.remove(name);
        self.disk_modules.remove(name);
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
    ) {
        self.register_module_arc(name, Arc::new(portable), info);
    }

    /// Store a compiled module's finalized PersStruct and metadata from an
    /// already shared portable signature.
    pub fn register_module_arc(
        &mut self,
        name: &str,
        portable: Arc<PortablePersStruct>,
        info: InMemoryModuleInfo,
    ) {
        self.insert_cached_module(name.to_string(), portable);
        self.insert_module_info(name.to_string(), info);
    }

    fn insert_cached_module(&mut self, name: String, portable: Arc<PortablePersStruct>) {
        if self.write_to_local {
            self.local_cached_modules.insert(name, portable);
        } else {
            // A compiled module replaces a stored one not decoded yet.
            if let Some(lazy) = &self.cached_modules.lazy {
                lazy.remove(&name);
            }
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
    jsx_module: Option<String>,
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
    disk_modules: SharedRegistryMap<bool>,
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
    /// Package roots of registered units without module info (namespaces).
    module_package_roots: SharedRegistryMap<PathBuf>,
    /// Package roots whose units are on this compilation's load path. OCaml
    /// only finds units through `-I` directories (the package itself, its
    /// dependencies, dev dependencies for dev sources and the runtime);
    /// `None` makes every registered unit visible.
    visible_package_roots: Option<Arc<Vec<PathBuf>>>,
    /// `outside_load_path` answers for `visible_package_roots`, by unit name.
    outside_load_path_memo: OutsideLoadPathMemo,
    /// First persistent-loader error observed through any clone of this env.
    last_error: Arc<Mutex<Option<PersistentEnvError>>>,
    /// Consistency table for imported CMI digests, matching OCaml `Consistbl`.
    crc_units: Arc<Mutex<HashMap<String, (Vec<u8>, String)>>>,
    /// `imported_units` with their recorded CRCs (env.ml:612-646): the
    /// units this compilation found and the units their CRC lists name.
    imported_units: Arc<Mutex<ImportedUnits>>,
    /// Decoded `.cmj` files by path, so the per-kind disk queries
    /// (`module_cmj_*`) read and unmarshal each file once per compilation.
    cmj_values: Arc<Mutex<HashMap<PathBuf, Option<OcamlValue>>>>,
    view: Arc<ResolutionView>,
}

/// Per-environment memo of `outside_load_path`. Each clone starts empty:
/// clones are per compilation, and sharing one lock across workers made it
/// contended.
#[derive(Default)]
struct OutsideLoadPathMemo(std::cell::RefCell<crate::fast_hash::AHashMap<String, bool>>);

impl Clone for OutsideLoadPathMemo {
    fn clone(&self) -> Self {
        Self::default()
    }
}

/// `imported_units` plus the units whose CRC lists were already merged, so
/// repeated lookups of a loaded unit skip re-recording its imports.
#[derive(Debug, Default)]
struct ImportedUnits {
    units: std::collections::BTreeMap<String, Option<[u8; 16]>>,
    recorded: crate::fast_hash::AHashSet<String>,
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
            jsx_module: None,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: SharedRegistryMap::default(),
            in_process_mode: false,
            disk_modules: SharedRegistryMap::default(),
            source_fallback_paths: SharedRegistryMap::default(),
            source_fallback_depth: 0,
            portable_cache: SharedRegistryMap::default(),
            module_package_roots: SharedRegistryMap::default(),
            visible_package_roots: None,
            outside_load_path_memo: OutsideLoadPathMemo::default(),
            last_error: Arc::new(Mutex::new(None)),
            crc_units: Arc::new(Mutex::new(HashMap::new())),
            imported_units: Arc::default(),
            cmj_values: Arc::default(),
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
            jsx_module: None,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: registry.module_info.clone(),
            in_process_mode: true,
            disk_modules: registry.disk_modules.clone(),
            source_fallback_paths: registry.source_fallback_paths.clone(),
            source_fallback_depth: 0,
            portable_cache: registry.cached_modules.clone(),
            module_package_roots: registry.module_package_roots.clone(),
            visible_package_roots: None,
            outside_load_path_memo: OutsideLoadPathMemo::default(),
            last_error: Arc::new(Mutex::new(None)),
            crc_units: Arc::new(Mutex::new(HashMap::new())),
            imported_units: Arc::default(),
            cmj_values: Arc::default(),
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
        if self.view.hidden_modules.contains(name) || self.outside_load_path(name) {
            return Some((name.to_string(), None));
        }
        let cache = self.cache.lock().unwrap();
        let cache_key = resolve_first_char_case_key(&cache, name)?;
        cache
            .get(cache_key)
            .cloned()
            .map(|value| (cache_key.to_string(), value))
    }

    /// The already-loaded persistent structure of `name`, without loading it.
    pub(crate) fn loaded_pers_struct(&self, name: &str) -> Option<Arc<PersStruct>> {
        self.cache_lookup_entry(name).and_then(|(_, loaded)| loaded)
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
        if self.outside_load_path(name) {
            return None;
        }
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
            return self.view.in_memory_module_overrides.get(key).map(&mut f);
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
        if self.outside_load_path(name) {
            return None;
        }
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
    /// PersStruct, serialized to portable form. Must be called while the
    /// TypeContext is still alive so the type graph can be serialized. Used
    /// to update the shared ModuleRegistry after compilation.
    ///
    /// The alias rewrites the compilation collected stay with it: a
    /// compilation that reads this module collects them from its signature
    /// when it loads it (`find_pers_struct`), as OCaml scrapes the aliases of
    /// the units a compilation reads (`compiler/ml/env.ml:1513-1538`), so what
    /// a compilation sees does not depend on which other modules compiled
    /// before it.
    pub fn extract_module_update(
        &self,
        module_name: &str,
        ctx: &TypeContext,
        arena: Option<&crate::parse_arena::ParseArena>,
    ) -> Option<PortablePersStruct> {
        self.cache_lookup(module_name)
            .and_then(|opt| opt)
            .map(|ps| portable_types::serialize_pers_struct(ps.as_ref(), ctx, arena))
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
    pub fn set_load_path_shared(
        &mut self,
        paths: Arc<Vec<PathBuf>>,
        display_paths: Arc<Vec<PathBuf>>,
    ) {
        debug_assert_eq!(paths.len(), display_paths.len());
        self.load_path = paths;
        self.load_path_display = display_paths;
    }

    pub fn set_load_path_with_display(&mut self, paths: Vec<PathBuf>, display_paths: Vec<PathBuf>) {
        debug_assert_eq!(paths.len(), display_paths.len());
        self.load_path = Arc::new(paths);
        self.load_path_display = Arc::new(display_paths);
    }

    /// Restrict registered units to those of the given packages (see
    /// `visible_package_roots`).
    pub fn set_visible_package_roots(&mut self, roots: Option<Vec<PathBuf>>) {
        self.visible_package_roots = roots.map(Arc::new);
        self.outside_load_path_memo = OutsideLoadPathMemo::default();
    }

    /// Whether this compilation can see the persistent unit `name`: it is
    /// neither hidden nor in a package outside its load path (OCaml finds a
    /// unit only through the compilation's load path, env.ml:669-678).
    pub(crate) fn unit_visible(&self, name: &str) -> bool {
        !self.view.hidden_modules.contains(name) && !self.outside_load_path(name)
    }

    fn outside_load_path(&self, name: &str) -> bool {
        let Some(visible) = self.visible_package_roots.as_deref() else {
            return false;
        };
        if let Some(&outside) = self.outside_load_path_memo.0.borrow().get(name) {
            return outside;
        }
        let visible_root = |root: &FsPath| visible.iter().any(|v| v == root);
        let outside = self
            .in_memory_info_with(name, |info| {
                !info.is_runtime
                    && info
                        .package_root
                        .as_deref()
                        .is_some_and(|root| !visible_root(root))
            })
            .or_else(|| {
                self.module_package_roots
                    .get_case_cloned(name)
                    .map(|(_, root)| !visible_root(&root))
            });
        // An unknown unit may still be registered later; only memoize answers
        // from its registry entry.
        let Some(outside) = outside else {
            return false;
        };
        self.outside_load_path_memo
            .0
            .borrow_mut()
            .insert(name.to_string(), outside);
        outside
    }

    pub fn set_open_modules(&mut self, open_modules: Vec<String>) {
        self.open_modules = Arc::new(open_modules);
    }

    pub fn set_jsx_module(&mut self, jsx_module: Option<String>) {
        self.jsx_module = jsx_module;
    }

    pub fn set_jsx_version(&mut self, jsx_version: Option<i32>) {
        self.jsx_version = jsx_version;
    }

    pub fn set_nopervasives(&mut self, nopervasives: bool) {
        self.nopervasives = nopervasives;
    }

    pub fn compiling_module_name(&self) -> Option<&str> {
        self.view.compiling_module.as_deref()
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
        if self.outside_load_path(name) {
            return false;
        }
        self.cache_contains_key(name)
            || self.portable_cache.contains_key(name)
            || self.in_memory_modules.contains_key(name)
            || self.source_fallback_paths.contains_key(name)
            || ((!self.in_process_mode || self.disk_modules.contains_key(name))
                && self.find_in_path_uncap(&format!("{name}.cmi")).is_some())
    }

    /// Find and load a module by name.
    /// Returns the cached signature, or None if the module cannot be found.
    /// `Env.find_pers_struct` (env.ml:711-731): a found unit is an import
    /// (`add_import`), and so is every unit its CRC list names, with that
    /// CRC (`check_consistency`, env.ml:627-638).
    pub fn find_pers_struct(&mut self, name: &str, ctx: &TypeContext) -> Option<Arc<PersStruct>> {
        if ctx.in_store_build() {
            // Preparing a module is an effect on this compilation; later users
            // of the shared data replay it (`StoreEffect::PreparePers`).
            ctx.record_store_effect(crate::types::context::StoreEffect::PreparePers(name.into()));
            return ctx.suspend_store_build(|| self.find_pers_struct(name, ctx));
        }
        let ps = self.find_pers_struct_unrecorded(name, ctx)?;
        self.record_import(&ps);
        Some(ps)
    }

    /// `Env.check_pers_struct` (env.ml:741-748): under `-no-alias-deps`, a
    /// module looked up without loading is still recorded as a (weak) import,
    /// with no CRC unless a loaded unit's CRC list supplies one.
    pub fn check_pers_struct(&self, name: &str) {
        self.imported_units
            .lock()
            .unwrap()
            .units
            .entry(name.to_string())
            .or_insert(None);
    }

    /// The units whose interface this compilation read, sorted.
    pub fn loaded_units(&self) -> Vec<String> {
        let mut units: Vec<String> = self
            .imported_units
            .lock()
            .unwrap()
            .recorded
            .iter()
            .cloned()
            .collect();
        units.sort();
        units
    }

    /// Replay of `find_pers_struct(name)` for `StoreEffect::PreparePers`:
    /// apply its lasting effects on the compilation (loading the unit into
    /// the shared cache, the raw signature registration and `record_import`)
    /// without copying the resolution view. The unit's alias rewrites would
    /// only be collected into a throwaway copy of the view, and they cannot
    /// change the registration decision for the unit itself. Returns `false`
    /// in the other cases (hidden, missing, or loaded from disk), so the
    /// caller runs the full lookup.
    pub(crate) fn replay_cached_pers_struct(&self, name: &str, ctx: &TypeContext) -> bool {
        let (cache_key, ps) = match self.cache_lookup_entry(name) {
            Some((cache_key, Some(ps))) => (cache_key, ps),
            Some((_, None)) => return false,
            None => {
                // Not loaded by this compilation yet: internalize the
                // registry's portable unit as `find_pers_struct_unrecorded`
                // does. Its alias rewrites are collected when this compilation
                // first looks the unit up itself (`prepare_cached_pers_struct`).
                let Some((portable_key, portable)) = self.portable_cache_entry(name) else {
                    return false;
                };
                if self.view.hidden_modules.contains(&portable_key) {
                    return false;
                }
                let ps = portable_types::internalize_pers_struct(portable, ctx);
                self.cache_insert(portable_key.clone(), Some(ps.clone()));
                (portable_key, ps)
            }
        };
        if should_register_lazy_raw_sig(&cache_key, &self.view.alias_prefix_rewrites)
            && !ctx.has_raw_module_sig(&cache_key)
        {
            ctx.register_raw_module_sig(&cache_key, ps.ps_sig.clone());
        }
        self.record_import(&ps);
        true
    }

    fn record_import(&self, ps: &PersStruct) {
        let mut imported = self.imported_units.lock().unwrap();
        if imported.recorded.contains(ps.ps_name.as_str()) {
            return;
        }
        imported.recorded.insert(ps.ps_name.clone());
        imported.units.entry(ps.ps_name.clone()).or_insert(None);
        for (unit, crc) in &ps.ps_crcs {
            if let Some(crc) = crc {
                let slot = imported.units.entry(unit.clone()).or_insert(None);
                if slot.is_none() {
                    *slot = Some(*crc);
                }
            }
        }
    }

    /// `Env.imports ()` (env.ml:1873-1882, consistbl.ml:36-44): the imported
    /// units in decreasing name order, without `dont_record_crc_unit`.
    pub fn imports(&self, dont_record_crc_unit: Option<&str>) -> Vec<(String, Option<[u8; 16]>)> {
        let imported = self.imported_units.lock().unwrap();
        imported
            .units
            .iter()
            .rev()
            .filter(|(name, _)| Some(name.as_str()) != dont_record_crc_unit)
            .map(|(name, crc)| (name.clone(), *crc))
            .collect()
    }

    fn find_pers_struct_unrecorded(
        &mut self,
        name: &str,
        ctx: &TypeContext,
    ) -> Option<Arc<PersStruct>> {
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
        if let Some((portable_key, portable)) = self.portable_cache_entry(name) {
            if debug_pers {
                eprintln!("[pers] portable {name} key={portable_key}");
            }
            if self.view.hidden_modules.contains(&portable_key) {
                return None;
            }
            ctx.poison_store_build_for("find_pers_struct:load");
            let ps = portable_types::internalize_pers_struct(portable, ctx);
            let module_path = Path::pident(Ident::create_persistent(&portable_key));
            let effective_module_path = self
                .view
                .alias_prefix_rewrites
                .get(&portable_key)
                .unwrap_or_else(|| module_path);
            collect_alias_rewrites(
                &ps.ps_sig,
                &effective_module_path,
                &mut self.view_mut().alias_prefix_rewrites,
            );
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
            let module_path = Path::pident(Ident::create_persistent(cache_key));
            let effective_module_path = self
                .view
                .alias_prefix_rewrites
                .get(cache_key)
                .unwrap_or_else(|| module_path);
            collect_alias_rewrites(
                &ps.ps_sig,
                &effective_module_path,
                &mut self.view_mut().alias_prefix_rewrites,
            );
        }

        if should_register_lazy_raw_sig(cache_key, &self.view.alias_prefix_rewrites)
            && !ctx.has_raw_module_sig(cache_key)
        {
            ctx.register_raw_module_sig(cache_key, ps.ps_sig.clone());
        }
    }

    fn finalize_loaded_signature(
        &mut self,
        name: &str,
        ps_name: String,
        mut signature: Signature,
        ps_filename: String,
        ps_deprecated: Option<String>,
        ps_crcs: Vec<(String, Option<[u8; 16]>)>,
        ctx: &TypeContext,
    ) -> PersStruct {
        let module_path = Path::pident(Ident::create_persistent(name));

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
            .unwrap_or_else(|| module_path);
        collect_alias_rewrites(
            &signature,
            &effective_module_path,
            &mut self.view_mut().alias_prefix_rewrites,
        );
        let signature = Arc::new(signature);
        if should_register_lazy_raw_sig(name, &self.view.alias_prefix_rewrites) {
            ctx.register_raw_module_sig(name, signature.clone());
        }

        PersStruct {
            ps_name,
            ps_sig: signature,
            ps_filename,
            ps_deprecated,
            ps_crcs,
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
            if let Some(package_name) = &info.package_name {
                // The package info the module's `.cmj` would hold
                // (`Js_cmj_format.package_spec`, `case`).
                let lowercase = info
                    .source_path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .and_then(|name| name.chars().next())
                    .is_some_and(|c| c.is_ascii_lowercase());
                return Some(CmjModuleImportInfo {
                    package_path: info.package_root.as_deref().cloned().unwrap_or_default(),
                    package_spec: CmjPackageSpec {
                        name: CmjPackageName::Normal(package_name.to_string()),
                        module_systems: info.package_outputs.as_ref().clone(),
                    },
                    file_case: if lowercase {
                        CmjFileCase::Little
                    } else {
                        CmjFileCase::Upper
                    },
                });
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
        let metadata = decode_cmj_module_metadata(&self.cmj_value(&path)?)?;
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

    /// `Config_util.find_opt`: the load-path file, trying the uncapitalized
    /// name first.
    pub fn find_in_load_path_uncap(&self, filename: &str) -> Option<String> {
        self.find_in_path_uncap(filename)
    }

    pub fn file_exists_in_load_path_uncap(&self, filename: &str) -> bool {
        self.find_in_path_uncap(filename).is_some()
    }

    /// The decoded `.cmj` at `path`, read from disk on first use.
    fn cmj_value(&self, path: &FsPath) -> Option<OcamlValue> {
        if let Some(value) = self.cmj_values.lock().unwrap().get(path) {
            return value.clone();
        }
        let value = read_marshaled_cmj(path);
        self.cmj_values
            .lock()
            .unwrap()
            .insert(path.to_path_buf(), value.clone());
        value
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
        decode_cmj_pure(&self.cmj_value(&path)?)
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
        decode_cmj_export_constants(&self.cmj_value(&path)?).map(Arc::new)
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
        decode_cmj_export_arities(&self.cmj_value(&path)?).map(Arc::new)
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
        decode_cmj_hoisted_exports(&self.cmj_value(&cmj_path)?)?
            .into_iter()
            .find(|entry| entry.path == path)
            .map(|entry| entry.export_name)
    }

    /// Read closed lambda exports recorded in a module's `.cmj` metadata.
    ///
    /// This mirrors the `cross_module_inline = true` arm of OCaml
    /// `js_cmj_format.ml:112-121`, where non-constant
    /// `persistent_closed_lambda` values are preserved for backend inlining.
    pub fn module_cmj_export_lambdas(
        &self,
        name: &str,
    ) -> Option<Arc<crate::lambda::CmjExportLambdas>> {
        if let Some(lambdas) =
            self.in_memory_info_with(name, |info| info.cmj_export_lambdas.clone())
        {
            return Some(lambdas);
        }
        // In in-process mode the registry is authoritative; do not fall back to
        // disk `.cmj` files behind the scheduler's back.
        if self.in_process_mode {
            return None;
        }

        let path = self.resolve_module_cmj_path(name)?;
        // The disk decoder keeps no locations (`decode_cmj_lambda`).
        decode_cmj_export_lambdas(&self.cmj_value(&path)?)
            .map(|lambdas| Arc::new(crate::lambda::CmjExportLambdas::without_locations(lambdas)))
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

    fn typecheck_source_signature(
        &self,
        source_path: &FsPath,
        ctx: &TypeContext,
    ) -> Option<(Signature, PersistentEnv, Option<String>)> {
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
            jsx_module: self.jsx_module.clone(),
            nopervasives: self.nopervasives,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: self.in_memory_modules.clone(),
            in_process_mode: self.in_process_mode,
            disk_modules: self.disk_modules.clone(),
            source_fallback_paths: self.source_fallback_paths.clone(),
            source_fallback_depth: self.source_fallback_depth + 1,
            portable_cache: self.portable_cache.clone(),
            module_package_roots: self.module_package_roots.clone(),
            visible_package_roots: self.visible_package_roots.clone(),
            outside_load_path_memo: self.outside_load_path_memo.clone(),
            last_error: self.last_error.clone(),
            crc_units: self.crc_units.clone(),
            // A unit compiled from source has its own imports.
            imported_units: Arc::default(),
            cmj_values: self.cmj_values.clone(),
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
            let deprecated = crate::types::typemod::deprecated_of_sig(parser.arena(), &signature);

            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let mut tctx = TypeCheckContext::new(ctx, parser.arena());
            tctx.set_persistent_env(fallback_pers);
            let typed_signature =
                transl_signature(&mut tctx, &env, parser.arena(), &signature).ok()?;
            let fallback_pers = tctx.persistent_env.take()?;
            let decl_signature = crate::types::typemod::decl_signature_from_typed_signature(
                &tctx.typed,
                &typed_signature,
                parser.arena(),
                ctx,
            );
            let typed_module_type = TypedModuleType {
                mty_desc: TypedModuleTypeDesc::Tmty_signature(typed_signature),
                mty_type: crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(
                    decl_signature,
                )),
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
            return Some((signature, fallback_pers, deprecated));
        }

        let mut parser = Parser::new(&filename, &source);
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            return None;
        }

        let options = CompilerOptions {
            open_modules: self.open_modules.as_ref().clone(),
            jsx_version: self.jsx_version,
            jsx_module: self.jsx_module.clone(),
            ..CompilerOptions::default()
        };
        let experimental_let_unwrap =
            experimental_let_unwrap_for_structure(&structure, &options, parser.arena());
        let jsx_version = jsx_version_for_structure(&structure, &options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            jsx_ppx::transform_structure_result(
                structure,
                jsx_version,
                jsx_module_name(&options, None),
                parser.arena_mut(),
            )
            .ok()?
        } else {
            structure
        };
        let structure =
            crate::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut()).ok()?;
        let deprecated = crate::types::typemod::deprecated_of_str(parser.arena(), &structure);

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
            normalize_signature(
                ctx,
                &final_env,
                &crate::types::includemod::simplify_signature(&typed_structure.str_type),
            );
        }

        let fallback_pers = tctx.persistent_env.take()?;
        Some((typed_structure.str_type.clone(), fallback_pers, deprecated))
    }

    fn load_module_from_source_fallback(
        &mut self,
        name: &str,
        ctx: &TypeContext,
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

        let debug_source_fallback = crate::debug_flags::debug_persistent_source_fallback();
        if debug_source_fallback {
            eprintln!(
                "[persistent-source] module={} ast={} source={}",
                name,
                ast_path,
                preferred_path.display()
            );
        }

        let (signature, fallback_pers, deprecated) =
            self.typecheck_source_signature(preferred_path, ctx)?;
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

        // OCaml reads this unit's `.cmi`; report the CRCs saved beside the
        // source it was typed from.
        let crcs =
            cmi_format::read_cmi_crcs(&preferred_path.with_extension("cmi").to_string_lossy())
                .unwrap_or_default();
        Some(self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            preferred_path.to_string_lossy().into_owned(),
            deprecated,
            crcs,
            ctx,
        ))
    }

    /// Load a module from a .cmi file, or fall back to the source path embedded
    /// in a sibling `.ast` when the module is implementation-only.
    fn load_module(&mut self, name: &str, ctx: &TypeContext) -> Option<PersStruct> {
        // In in-process mode, never fall through to .cmi loading. The registry
        // is authoritative for normal project modules. Runtime/bootstrap code
        // may register source fallback paths, which are also source-only.
        if self.in_process_mode && !self.disk_modules.contains_key(name) {
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
            // env.ml:663-668: the unit's `Deprecated` persistence flag.
            let deprecated = cmi.cmi_flags.iter().fold(None, |_, flag| match flag {
                crate::cmi::cmi_format::PersFlags::Deprecated(s) => Some(s.clone()),
            });
            let crcs = cmi
                .cmi_crcs
                .iter()
                .map(|(unit, crc)| {
                    (
                        unit.clone(),
                        crc.as_deref()
                            .and_then(|crc| <[u8; 16]>::try_from(crc).ok()),
                    )
                })
                .collect();
            return Some(self.finalize_loaded_signature(
                name,
                name.to_string(),
                signature,
                display_path,
                deprecated,
                crcs,
                ctx,
            ));
        }

        self.load_module_from_source_fallback(name, ctx)
    }

    /// Load a module by type-checking its source file directly in `--in-process` mode.
    ///
    /// Unlike `load_module_from_source_fallback` (which reads `.ast` files),
    /// this reads the source `.res`/`.resi` file path from `source_fallback_paths`.
    fn load_module_from_source_path_fallback(
        &mut self,
        name: &str,
        ctx: &TypeContext,
    ) -> Option<PersStruct> {
        let source_path = self.source_fallback_path_entry(name)?.1;

        // The source_fallback_paths already points to the preferred file
        // (.resi if it exists, .res otherwise), set by rewatch when
        // registering the paths.
        let (signature, fallback_pers, deprecated) =
            self.typecheck_source_signature(&source_path, ctx)?;

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

        // OCaml reads this unit's `.cmi`; report the CRCs saved beside the
        // source it was typed from.
        let crcs = cmi_format::read_cmi_crcs(&source_path.with_extension("cmi").to_string_lossy())
            .unwrap_or_default();
        Some(self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            source_path.to_string_lossy().into_owned(),
            deprecated,
            crcs,
            ctx,
        ))
    }

    /// Read a module's signature from CMI without applying path substitution.
    /// Used for interface constraint propagation (moregen) where we need raw
    /// Pident paths that match the implementation's local paths.
    /// In OCaml, ps_sig retains raw Pident paths; path substitution happens
    /// lazily in components_of_module_maker, not on ps_sig.
    pub fn read_raw_sig_shared(&mut self, name: &str, ctx: &TypeContext) -> Option<Arc<Signature>> {
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

    /// Owned copy of [`Self::read_raw_sig_shared`].
    pub fn read_raw_sig(&mut self, name: &str, ctx: &TypeContext) -> Option<Signature> {
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
        let uncap = filename
            .chars()
            .next()
            .filter(char::is_ascii_uppercase)
            .map(|first_char| format!("{}{}", first_char.to_ascii_lowercase(), &filename[1..]));
        for (index, dir) in self.load_path.iter().enumerate() {
            let display_dir = self.load_path_display.get(index).unwrap_or(dir);
            if let Some(uncap) = &uncap {
                let uncap_path = dir.join(uncap);
                if uncap_path.exists() {
                    return Some((
                        uncap_path.to_string_lossy().into_owned(),
                        display_dir.join(uncap).to_string_lossy().into_owned(),
                    ));
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

    /// Get the renamed signature for a module, cached.
    /// Matches OCaml's `ps_sig = lazy (Subst.signature Subst.identity sign)`.
    /// In OCaml, accessing a module's components cascades into forcing ps_sig
    /// for all dependent modules (via components_of_module_maker → scrape_alias
    /// → find_module). We match this by triggering ALL registered module renames
    /// when any module is first accessed.
    pub fn get_renamed_sig_shared(
        &mut self,
        name: &str,
        ctx: &TypeContext,
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

    pub fn get_renamed_sig(&mut self, name: &str, ctx: &TypeContext) -> Option<Signature> {
        self.get_renamed_sig_shared(name, ctx)
            .map(|sig| sig.as_ref().clone())
    }

    /// Force the lazy `Subst.signature Subst.identity` side effect for a
    /// persistent module without requiring the caller to use the renamed
    /// signature. OCaml allocates fresh identifiers the first time `ps_sig` is
    /// forced; in-process type lookups still often need the raw signature shape.
    pub(crate) fn force_lazy_signature_rename(
        &mut self,
        name: &str,
        ctx: &TypeContext,
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

    pub fn open_module(&mut self, name: &str, env: &mut Env, ctx: &TypeContext) -> bool {
        // Don't rename at open time — OCaml's ps_sig is only forced later
        // when find_module is called from normalize_path during type expansion.
        let ps = match self.find_pers_struct(name, ctx) {
            Some(ps) => ps,
            None => return false,
        };
        let module_path = Path::pident(Ident::create_persistent(name));
        let components_key = crate::types::context::QualifiedModuleComponentsCacheKey::new(
            module_path,
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
                        module_path,
                        ps.ps_sig.clone(),
                        crate::fast_hash::AHashMap::new(),
                        alias_source,
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
    pub fn get_module_declaration(
        &mut self,
        name: &str,
        ctx: &TypeContext,
    ) -> Option<ModuleDeclaration> {
        let ps = self.find_pers_struct(name, ctx)?;
        Some(ModuleDeclaration {
            md_type: ModuleType::MtySignature(std::sync::Arc::new(ps.ps_sig.as_ref().clone())),
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
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
    pub fn register_in_memory_signature(
        &mut self,
        name: &str,
        signature: Signature,
        source_filename: &str,
        deprecated: Option<String>,
        crcs: Vec<(String, Option<[u8; 16]>)>,
        ctx: &TypeContext,
    ) {
        let ps = self.finalize_loaded_signature(
            name,
            name.to_string(),
            signature,
            source_filename.to_string(),
            deprecated,
            crcs,
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
                    // As saved in the namespace `.cmi`: an alias typed by
                    // `type_module_aux` is `Mty_alias (Mta_absent, path)`.
                    md_type: ModuleType::MtyAlias(
                        AliasPresence::MtaAbsent,
                        Path::pident(Ident::create_persistent(internal_name.as_str())),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            ));
        }

        // Record alias rewrites (e.g., "Foo-MyApp" → Pdot(Pident("MyApp"), "Foo"))
        let module_path = Path::pident(Ident::create_persistent(namespace_name));
        collect_alias_rewrites(
            &sig_items,
            &module_path,
            &mut self.view_mut().alias_prefix_rewrites,
        );

        let ps = PersStruct {
            ps_name: namespace_name.to_string(),
            ps_sig: Arc::new(sig_items),
            ps_filename: format!("{}.mlmap", namespace_name),
            ps_deprecated: None,
            ps_crcs: Vec::new(),
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

fn decode_cmj_module_metadata(value: &OcamlValue) -> Option<CmjModuleMetadata> {
    Some(CmjModuleMetadata {
        is_pure: decode_cmj_pure(value)?,
        export_constants: decode_cmj_export_constants(value)?,
        hoisted_exports: decode_cmj_hoisted_exports(value)?,
        package_spec: decode_cmj_package_spec(value)?,
        file_case: decode_cmj_file_case(value)?,
    })
}

fn decode_cmj_pure(value: &OcamlValue) -> Option<bool> {
    let (_, fields) = value.as_block_opt()?;
    fields.get(2).map(|field| field.as_bool())
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
    // `Lambda.structured_constant` (compiler/ml/lambda.mli): constant
    // constructors Const_assertfalse, Const_module_alias, Const_js_false,
    // Const_js_true, Const_js_null; Const_js_undefined is block tag 9.
    match value {
        OcamlValue::Int(4) => Some(CmjExportConstant::Null),
        OcamlValue::Int(3) => Some(CmjExportConstant::Bool(true)),
        OcamlValue::Int(2) => Some(CmjExportConstant::Bool(false)),
        OcamlValue::Block(tag, fields) if *tag == 9 && fields.len() == 1 => {
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
        // `Lambda.t` constructor order is defined in compiler/ml/lambda.mli.
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(Lambda::Lvar(decode_cmj_ident(&fields[0])?))
        }
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            Some(Lambda::LglobalModule(decode_cmj_ident(&fields[0])?))
        }
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(Lambda::Lconst(decode_cmj_lambda_constant(&fields[0])?))
        }
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            let apply = decode_cmj_apply(&fields[0])?;
            Some(Lambda::Lapply(Box::new(apply)))
        }
        OcamlValue::Block(4, fields) if fields.len() == 1 => Some(Lambda::Lfunction(Box::new(
            decode_cmj_lfunction(&fields[0])?,
        ))),
        OcamlValue::Block(7, fields) if fields.len() == 1 => {
            let prim = decode_cmj_prim_info(&fields[0])?;
            Some(Lambda::Lprim(Box::new(prim)))
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
    // `Lambda.lfunction = {params; body; attr; loc}`; the arity is the
    // parameter count.
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 3 {
        return None;
    }
    let params = decode_cmj_list(&fields[0], decode_cmj_ident)?;
    Some(LFunction {
        arity: params.len() as i32,
        params,
        body: Box::new(decode_cmj_lambda(&fields[1])?),
        attr: decode_cmj_function_attribute(&fields[2])?,
        // Locations of decoded `.cmj` lambdas are not kept (as for
        // applications and primitives above).
        loc: crate::lambda::LamLoc::NONE,
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
    // `Lambda.ap_info = {ap_loc; ap_inlined}`.
    let (_, fields) = value.as_block_opt()?;
    Some(ApInfo {
        loc: crate::lambda::LamLoc::NONE,
        inlined: fields
            .get(1)
            .and_then(decode_cmj_inline_attribute)
            .unwrap_or_default(),
        status: ApplyStatus::Na,
    })
}

fn decode_cmj_prim_info(value: &OcamlValue) -> Option<PrimInfo> {
    let (_, fields) = value.as_block_opt()?;
    if fields.len() < 2 {
        return None;
    }
    Some(PrimInfo {
        primitive: decode_cmj_primitive(&fields[0])?,
        args: decode_cmj_list(&fields[1], decode_cmj_lambda)?,
        loc: crate::lambda::LamLoc::NONE,
    })
}

fn decode_cmj_lambda_constant(value: &OcamlValue) -> Option<LambdaConstant> {
    // `Lambda.structured_constant` constructor order is in compiler/ml/lambda.mli.
    match value {
        OcamlValue::Int(0) => Some(LambdaConstant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::AssertFalse)),
        }),
        OcamlValue::Int(1) => Some(LambdaConstant::ModuleAlias),
        OcamlValue::Int(2) => Some(LambdaConstant::JsFalse),
        OcamlValue::Int(3) => Some(LambdaConstant::JsTrue),
        OcamlValue::Int(4) => Some(LambdaConstant::JsNull),
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(LambdaConstant::Int {
            i: fields[0].as_int() as i32,
            comment: None,
        }),
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Char(fields[0].as_int() as i32))
        }
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(LambdaConstant::String(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Float(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(4, fields) if fields.len() == 2 => Some(LambdaConstant::BigInt {
            negative: fields[0].as_bool(),
            value: fields[1].as_string().to_string(),
        }),
        OcamlValue::Block(5, fields) if fields.len() == 2 => Some(LambdaConstant::Block {
            tag_info: Box::new(decode_cmj_tag_info(&fields[0])?),
            elements: decode_cmj_list(&fields[1], decode_cmj_lambda_constant)?,
        }),
        OcamlValue::Block(6, fields) if fields.len() == 1 => Some(LambdaConstant::Constructor(
            decode_cmj_variant_tag(&fields[0])?,
        )),
        // Tagless polymorphic variant; numeric-looking names are Const_int.
        OcamlValue::Block(7, fields) if fields.len() == 1 => {
            Some(LambdaConstant::Pointer(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(8, fields) if fields.len() == 1 => Some(LambdaConstant::Some(Box::new(
            decode_cmj_lambda_constant(&fields[0])?,
        ))),
        OcamlValue::Block(9, fields) if fields.len() == 1 => Some(LambdaConstant::JsUndefined {
            is_unit: fields[0].as_bool(),
        }),
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
        literal: decode_cmj_variant_literal_tag_option(&fields[1])?,
    })
}

fn decode_cmj_variant_literal_tag_option(
    value: &OcamlValue,
) -> Option<Option<crate::types::VariantLiteralTag>> {
    match value {
        OcamlValue::Int(0) => Some(None),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(Some(decode_cmj_variant_literal_tag(&fields[0])?))
        }
        _ => None,
    }
}

/// `Variant_runtime.literal_tag`.
fn decode_cmj_variant_literal_tag(value: &OcamlValue) -> Option<crate::types::VariantLiteralTag> {
    use crate::types::VariantLiteralTag as T;
    match value {
        OcamlValue::Int(0) => Some(T::Null),
        OcamlValue::Int(1) => Some(T::Undefined),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            Some(T::String(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(1, fields) if fields.len() == 1 => Some(T::Int(fields[0].as_int())),
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(T::Float(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            Some(T::BigInt(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(4, fields) if fields.len() == 1 => Some(T::Bool(fields[0].as_bool())),
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

    /// `Variant_runtime.tagged_block`.
    fn tagged_block(value: &OcamlValue) -> Option<crate::types::TaggedBlock> {
        let (_, fields) = value.as_block_opt()?;
        Some(crate::types::TaggedBlock {
            tag: decode_cmj_variant_tag(fields.first()?)?,
            tag_name: fields
                .get(1)?
                .as_option()
                .map(|name| name.as_string().to_string()),
        })
    }

    /// `Variant_runtime.block`: `Tagged of tagged_block` or the inline
    /// record `Untagged of {tag; block_type}`.
    fn block(value: &OcamlValue) -> Option<crate::types::VariantBlock> {
        match value.as_block_opt()? {
            (0, fields) => Some(crate::types::VariantBlock::Tagged(tagged_block(
                fields.first()?,
            )?)),
            (1, fields) => Some(crate::types::VariantBlock::Untagged {
                tag: decode_cmj_variant_tag(fields.first()?)?,
                block_type: crate::cmi::sig_reader::decode_variant_block_type(fields.get(1)?),
            }),
            _ => None,
        }
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

    // `Lambda.tag_info` constructor order is in compiler/ml/lambda.mli.
    match value {
        OcamlValue::Int(0) => Some(TagInfo::Tuple),
        OcamlValue::Int(1) => Some(TagInfo::PolyVar(String::new())),
        OcamlValue::Int(2) => Some(TagInfo::Extension),
        OcamlValue::Block(0, fields) if fields.len() == 3 => Some(TagInfo::Constructor(Box::new(
            crate::lambda::lam_tag_info::ConstructorTag {
                name: fields[0].as_string().to_string(),
                num_nonconst: fields[1].as_int() as i32,
                runtime: Box::new(tagged_block(&fields[2])?),
            },
        ))),
        OcamlValue::Block(1, fields) if fields.len() == 5 => Some(TagInfo::RecordInlined(
            Box::new(crate::lambda::lam_tag_info::RecordInlinedTag {
                name: fields[0].as_string().to_string(),
                num_nonconst: fields[1].as_int() as i32,
                fields: record_fields(&fields[2])?,
                logical_field_count: None,
                mutable_flag: mutable_flag(&fields[3])?,
                runtime: Box::new(block(&fields[4])?),
            }),
        )),
        OcamlValue::Block(2, fields) if fields.len() == 2 => Some(TagInfo::Record(Box::new(
            crate::lambda::lam_tag_info::RecordTag {
                fields: record_fields(&fields[0])?,
                logical_field_count: None,
                mutable_flag: mutable_flag(&fields[1])?,
            },
        ))),
        OcamlValue::Block(3, fields) if fields.len() == 1 => {
            Some(TagInfo::Module(decode_cmj_string_list(&fields[0])?))
        }
        OcamlValue::Block(4, fields) if fields.len() == 1 => Some(TagInfo::ModuleExport(
            decode_cmj_list(&fields[0], decode_cmj_ident)?,
        )),
        OcamlValue::Block(5, fields) if fields.len() == 2 => Some(TagInfo::RecordExt {
            fields: string_array(&fields[0])?,
            mutable_flag: mutable_flag(&fields[1])?,
        }),
        _ => None,
    }
}

fn decode_cmj_primitive(value: &OcamlValue) -> Option<Primitive> {
    // `Lambda.primitive` constructor order is in compiler/ml/lambda.mli.
    match value {
        OcamlValue::Int(0) => Some(Primitive::Pdebugger),
        OcamlValue::Int(1) => Some(Primitive::Ptypeof),
        OcamlValue::Int(2) => Some(Primitive::Psome),
        OcamlValue::Int(3) => Some(Primitive::PsomeNotNest),
        OcamlValue::Int(4) => Some(Primitive::Pduprecord),
        OcamlValue::Int(5) => Some(Primitive::Praise),
        OcamlValue::Int(6) => Some(Primitive::Pobjorder),
        OcamlValue::Int(7) => Some(Primitive::Pobjmin),
        OcamlValue::Int(8) => Some(Primitive::Pobjmax),
        OcamlValue::Int(9) => Some(Primitive::Pobjtag),
        OcamlValue::Int(10) => Some(Primitive::Pobjsize),
        OcamlValue::Int(11) => Some(Primitive::Psequand),
        OcamlValue::Int(12) => Some(Primitive::Psequor),
        OcamlValue::Int(13) => Some(Primitive::Pnot),
        OcamlValue::Int(14) => Some(Primitive::Pboolorder),
        OcamlValue::Int(15) => Some(Primitive::Pboolmin),
        OcamlValue::Int(16) => Some(Primitive::Pboolmax),
        OcamlValue::Int(17) => Some(Primitive::Pnegint),
        OcamlValue::Int(18) => Some(Primitive::Paddint),
        OcamlValue::Int(19) => Some(Primitive::Psubint),
        OcamlValue::Int(20) => Some(Primitive::Pmulint),
        OcamlValue::Int(21) => Some(Primitive::Pdivint),
        OcamlValue::Int(22) => Some(Primitive::Pmodint),
        OcamlValue::Int(23) => Some(Primitive::Ppowint),
        OcamlValue::Int(24) => Some(Primitive::Pandint),
        OcamlValue::Int(25) => Some(Primitive::Porint),
        OcamlValue::Int(26) => Some(Primitive::Pxorint),
        OcamlValue::Int(27) => Some(Primitive::Pnotint),
        OcamlValue::Int(28) => Some(Primitive::Plslint),
        OcamlValue::Int(29) => Some(Primitive::Plsrint),
        OcamlValue::Int(30) => Some(Primitive::Pasrint),
        OcamlValue::Int(31) => Some(Primitive::Pintorder),
        OcamlValue::Int(32) => Some(Primitive::Pintmin),
        OcamlValue::Int(33) => Some(Primitive::Pintmax),
        OcamlValue::Int(34) => Some(Primitive::Pintoffloat),
        OcamlValue::Int(35) => Some(Primitive::Pfloatofint),
        OcamlValue::Int(36) => Some(Primitive::Pnegfloat),
        OcamlValue::Int(37) => Some(Primitive::Pmodfloat),
        OcamlValue::Int(38) => Some(Primitive::Paddfloat),
        OcamlValue::Int(39) => Some(Primitive::Psubfloat),
        OcamlValue::Int(40) => Some(Primitive::Pmulfloat),
        OcamlValue::Int(41) => Some(Primitive::Pdivfloat),
        OcamlValue::Int(42) => Some(Primitive::Ppowfloat),
        OcamlValue::Int(43) => Some(Primitive::Pfloatorder),
        OcamlValue::Int(44) => Some(Primitive::Pfloatmin),
        OcamlValue::Int(45) => Some(Primitive::Pfloatmax),
        OcamlValue::Int(46) => Some(Primitive::Pnegbigint),
        OcamlValue::Int(47) => Some(Primitive::Paddbigint),
        OcamlValue::Int(48) => Some(Primitive::Psubbigint),
        OcamlValue::Int(49) => Some(Primitive::Ppowbigint),
        OcamlValue::Int(50) => Some(Primitive::Pmulbigint),
        OcamlValue::Int(51) => Some(Primitive::Pdivbigint),
        OcamlValue::Int(52) => Some(Primitive::Pmodbigint),
        OcamlValue::Int(53) => Some(Primitive::Pandbigint),
        OcamlValue::Int(54) => Some(Primitive::Porbigint),
        OcamlValue::Int(55) => Some(Primitive::Pxorbigint),
        OcamlValue::Int(56) => Some(Primitive::Pnotbigint),
        OcamlValue::Int(57) => Some(Primitive::Plslbigint),
        OcamlValue::Int(58) => Some(Primitive::Pasrbigint),
        OcamlValue::Int(59) => Some(Primitive::Pbigintorder),
        OcamlValue::Int(60) => Some(Primitive::Pbigintmin),
        OcamlValue::Int(61) => Some(Primitive::Pbigintmax),
        OcamlValue::Int(62) => Some(Primitive::Pstringlength),
        OcamlValue::Int(63) => Some(Primitive::Pstringrefu),
        OcamlValue::Int(64) => Some(Primitive::Pstringrefs),
        OcamlValue::Int(65) => Some(Primitive::Pstringorder),
        OcamlValue::Int(66) => Some(Primitive::Pstringmin),
        OcamlValue::Int(67) => Some(Primitive::Pstringmax),
        OcamlValue::Int(68) => Some(Primitive::Pstringadd),
        OcamlValue::Int(69) => Some(Primitive::Pmakearray),
        OcamlValue::Int(70) => Some(Primitive::Parraylength),
        OcamlValue::Int(71) => Some(Primitive::Parrayrefu),
        OcamlValue::Int(72) => Some(Primitive::Parraysetu),
        OcamlValue::Int(73) => Some(Primitive::Parrayrefs),
        OcamlValue::Int(74) => Some(Primitive::Parraysets),
        OcamlValue::Int(75) => Some(Primitive::Pmakelist),
        OcamlValue::Int(76) => Some(Primitive::Pmakedict),
        OcamlValue::Int(77) => Some(Primitive::PdictHas),
        OcamlValue::Int(78) => Some(Primitive::Pawait),
        OcamlValue::Int(79) => Some(Primitive::PinitMod),
        OcamlValue::Int(80) => Some(Primitive::PupdateMod),
        OcamlValue::Int(81) => Some(Primitive::Phash),
        OcamlValue::Int(82) => Some(Primitive::PhashMixint),
        OcamlValue::Int(83) => Some(Primitive::PhashMixstring),
        OcamlValue::Int(84) => Some(Primitive::PhashFinalmix),
        OcamlValue::Int(85) => Some(Primitive::Pisint),
        OcamlValue::Int(86) => Some(Primitive::PisNullUndefined),
        OcamlValue::Int(87) => Some(Primitive::PnullToOpt),
        OcamlValue::Int(88) => Some(Primitive::PnullUndefinedToOpt),
        OcamlValue::Int(89) => Some(Primitive::PisNull),
        OcamlValue::Int(90) => Some(Primitive::PisUndefined),
        OcamlValue::Int(91) => Some(Primitive::PisNotNone),
        OcamlValue::Int(92) => Some(Primitive::PvalFromOption),
        OcamlValue::Int(93) => Some(Primitive::PvalFromOptionNotNest),
        OcamlValue::Int(94) => Some(Primitive::PisPolyVarBlock),
        OcamlValue::Int(95) => Some(Primitive::PjsFnMethod),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            let tag_info = decode_cmj_tag_info(&fields[0])?;
            // `Lambda.mutable_flag_of_tag_info`: a block's mutability follows
            // from its shape.
            let mutable = match &tag_info {
                TagInfo::Record(_) | TagInfo::RecordInlined(_) | TagInfo::RecordExt { .. } => {
                    match tag_info.mutable_flag() {
                        crate::parser::ast::MutableFlag::Mutable => Mutable::Mutable,
                        crate::parser::ast::MutableFlag::Immutable => Mutable::Immutable,
                    }
                }
                _ => Mutable::Immutable,
            };
            Some(Primitive::Pmakeblock(tag_info, mutable))
        }
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(Primitive::Pfield(
            fields[0].as_int() as i32,
            decode_cmj_field_dbg_info(&fields[1])?,
        )),
        OcamlValue::Block(4, fields) if fields.len() == 4 => Some(Primitive::PjsCall(Box::new(
            crate::lambda::lam_primitive::JsCall {
                prim_name: fields[0].as_string().to_string(),
                arg_types: crate::cmi::ffi_decode::params(&fields[1])?,
                ffi: crate::cmi::ffi_decode::external_decl(&fields[2])?,
                transformed_jsx: fields[3].as_bool(),
            },
        ))),
        OcamlValue::Block(8, fields) if fields.len() == 1 => {
            Some(Primitive::Pobjcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(9, fields) if fields.len() == 1 => {
            Some(Primitive::Pboolcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(10, fields) if fields.len() == 1 => {
            Some(Primitive::Pintcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(11, fields) if fields.len() == 1 => {
            Some(Primitive::Pfloatcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(12, fields) if fields.len() == 1 => {
            Some(Primitive::Pbigintcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(13, fields) if fields.len() == 1 => {
            Some(Primitive::Pstringcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(18, fields) if fields.len() == 1 => Some(Primitive::PtaggedTemplate(
            decode_cmj_string_list(&fields[0])?,
        )),
        OcamlValue::Block(19, fields) if fields.len() == 1 => Some(Primitive::Ptemplate(
            decode_cmj_list(&fields[0], decode_cmj_template_segment)?,
        )),
        OcamlValue::Block(16, fields) if fields.len() == 1 => {
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

/// `String_literal.payload`: `Valid {source; semantic}` or `Invalid_source`.
fn decode_cmj_template_segment(
    value: &OcamlValue,
) -> Option<crate::string_literal::TemplateSegment> {
    use std::borrow::Cow;
    match value {
        OcamlValue::Block(0, fields) if fields.len() == 2 => {
            Some(crate::string_literal::StringLiteral::Valid {
                source: Cow::Owned(fields[0].as_string().to_string()),
                semantic: Cow::Owned(fields[1].as_string().to_string()),
            })
        }
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            Some(crate::string_literal::StringLiteral::InvalidSource(
                Cow::Owned(fields[0].as_string().to_string()),
            ))
        }
        _ => None,
    }
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
    match path.view() {
        PathView::Pident(id) => (id.stamp() != 0).then(|| (id.stamp(), id.name().to_string())),
        PathView::Pdot(prefix, _, _) => nonpersistent_path_head(prefix),
        PathView::Papply(left, right) => {
            nonpersistent_path_head(left).or_else(|| nonpersistent_path_head(right))
        }
    }
}

#[derive(Clone, Debug)]
struct SubstMaps {
    type_stamp_map: HashMap<i32, Path>,
    type_name_map: HashMap<String, Path>,
    module_stamp_map: ModuleStampSubstMap,
    module_name_map: HashMap<String, Path>,
    protected_module_head: Option<(i32, String)>,
}

/// Fixed hasher keys: `AHashMap::default()` derives fresh random keys per
/// map, and substitution maps are built for every qualified signature.
static SUBST_MAP_STATE: ahash::RandomState = ahash::RandomState::with_seeds(
    0x452821e6_38d01377,
    0xbe5466cf_34e90c6c,
    0xc0ac29b7_c97c50dd,
    0x3f84d5b5_b5470917,
);

fn subst_map<K, V>() -> HashMap<K, V> {
    std::collections::HashMap::with_hasher(SUBST_MAP_STATE.clone()).into()
}

impl Default for SubstMaps {
    fn default() -> Self {
        Self {
            type_stamp_map: subst_map(),
            type_name_map: subst_map(),
            module_stamp_map: subst_map(),
            module_name_map: subst_map(),
            protected_module_head: None,
        }
    }
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
                let qualified_path = Path::pdot(*module_path, id.name());
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
                let qualified_path = Path::pdot(*module_path, id.name());
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
    let new_path = Path::pident(*new_id);
    if old_id.stamp() != 0 {
        maps.type_stamp_map.insert(old_id.stamp(), new_path);
    } else {
        maps.type_name_map
            .insert(old_id.name().to_string(), new_path);
    }
}

fn insert_module_subst_path(maps: &mut SubstMaps, old_id: &Ident, new_id: &Ident) {
    let new_path = Path::pident(*new_id);
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
    let mut visited = HashSet::new();
    freshen_module_type_bound_idents_rec(module_type, maps, ctx, &mut visited);
}

/// OCaml `Subst.modtype` (compiler/ml/subst.ml:345-376) with the composed
/// substitution `maps`. Each path is substituted exactly once, through the
/// substitution in scope where it occurs (as `Subst` rewrites the original
/// identifiers), and each type node once (`visited`): renamed stamps can
/// coincide with original ones, so substituting a rewritten path again would
/// reach an unrelated identifier.
fn freshen_module_type_bound_idents_rec(
    module_type: &mut ModuleType,
    maps: &SubstMaps,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
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
            freshen_signature_bound_idents_rec(
                crate::types::decl::signature_mut(sig),
                maps,
                ctx,
                visited,
            );
        }
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            let old_param = *param;
            // OCaml compiler/ml/subst.ml:352-355 renames the functor
            // parameter, then observes `Mty_functor` argument evaluation by
            // freshening the result before the argument module type. This
            // stamp order is observable in strict typedtree identifiers.
            let new_param = ctx.rename_ident(&old_param);
            *param = new_param;
            let mut param_maps = SubstMaps::default();
            insert_module_subst_path(&mut param_maps, &old_param, &new_param);
            let result_maps = merge_subst_maps(maps, &param_maps);
            freshen_module_type_bound_idents_rec(result, &result_maps, ctx, visited);
            if let Some(param_type) = param_type.as_mut() {
                freshen_module_type_bound_idents_rec(param_type, maps, ctx, visited);
            }
        }
    }
}

/// OCaml `Subst.signature` (compiler/ml/subst.ml:322-364): rename this
/// level's bound identifiers, then rewrite its components once through the
/// outer substitution extended with those renamings; nested module types
/// continue with that composed substitution.
fn freshen_signature_bound_idents_rec(
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
) {
    let mut local_maps = SubstMaps::default();

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigTypext(id, _, _) => {
                *id = ctx.rename_ident(id);
            }
            SignatureItem::SigType(id, _, _) => {
                let old_id = *id;
                let new_id = ctx.rename_ident(&old_id);
                insert_type_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigModtype(id, _) => {
                let old_id = *id;
                let new_id = ctx.rename_ident(&old_id);
                insert_type_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigModule(id, _, _) => {
                let old_id = *id;
                let new_id = ctx.rename_ident(&old_id);
                insert_module_subst_path(&mut local_maps, &old_id, &new_id);
                *id = new_id;
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    let combined_maps = if local_maps.is_empty() {
        maps.clone()
    } else if maps.is_empty() && maps.protected_module_head.is_none() {
        local_maps
    } else {
        merge_subst_maps(maps, &local_maps)
    };

    substitute_type_paths_in_sig_items(sig_items, &combined_maps, ctx, visited, false);
    substitute_sig_decl_paths_in_place_with_maps_rec(sig_items, &combined_maps, false);

    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                freshen_module_type_bound_idents_rec(&mut md.md_type, &combined_maps, ctx, visited);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    freshen_module_type_bound_idents_rec(module_type, &combined_maps, ctx, visited);
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
                    + param_type
                        .as_ref()
                        .map_or(0, |param| module_type_count(param))
            }
        }
    }
    sig_items
        .iter()
        .map(|item| match item {
            SignatureItem::SigValue(..)
            | SignatureItem::SigTypext(..)
            | SignatureItem::SigType(..) => 1,
            SignatureItem::SigModtype(_, mtd) => {
                1 + mtd.mtd_type.as_ref().map_or(0, module_type_count)
            }
            SignatureItem::SigModule(_, md, _) => 1 + module_type_count(&md.md_type),
            SignatureItem::SigClass | SignatureItem::SigClassType => 0,
        })
        .sum()
}

fn freshen_nested_signature_module_types(sig_items: &mut [SignatureItem], ctx: &TypeContext) {
    let mut visited = HashSet::new();
    let no_maps = SubstMaps::default();
    for item in sig_items.iter_mut() {
        match item {
            SignatureItem::SigModule(_, md, _) => {
                freshen_module_type_bound_idents_rec(&mut md.md_type, &no_maps, ctx, &mut visited);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    freshen_module_type_bound_idents_rec(module_type, &no_maps, ctx, &mut visited);
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
            *path
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
            *path
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
        insert_module_stamp_subst(&mut maps.module_stamp_map, old_param, *arg_path);
    } else {
        maps.module_name_map
            .insert(old_param.name().to_string(), *arg_path);
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
            insert_module_stamp_subst(&mut maps.module_stamp_map, id, *path);
        } else {
            maps.module_name_map
                .insert(id.name().to_string(), *path);
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
            substitute_sig_decl_paths_in_place_with_maps(
                crate::types::decl::signature_mut(sig),
                maps,
            );
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
    substitute_sig_decl_paths_in_place_with_maps_rec(sig_items, maps, true);
}

/// Substitute the declaration paths of `sig_items`; without `recurse`, the
/// module types of nested modules and module types are left alone.
fn substitute_sig_decl_paths_in_place_with_maps_rec(
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
    recurse: bool,
) {
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
                if recurse {
                    substitute_module_type_paths_with_maps(&mut md.md_type, maps);
                }
            }
            SignatureItem::SigModtype(_, mtd) => {
                if recurse && let Some(module_type) = mtd.mtd_type.as_mut() {
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
    let mut visited = HashSet::new();
    substitute_type_paths_in_sig_items(sig_items, maps, ctx, &mut visited, true);
}

/// Substitute the type paths of `sig_items`' type expressions, visiting each
/// type node once per `visited` set. With `recurse`, nested module
/// signatures are included; without it only this level's items are.
fn substitute_type_paths_in_sig_items(
    sig_items: &[SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext,
    visited: &mut HashSet<usize>,
    recurse: bool,
) {
    if maps.is_empty() {
        return;
    }

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
                    visited,
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
                        visited,
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
                        visited,
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
                                            visited,
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
                                            visited,
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
                                    visited,
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
                                visited,
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
                        visited,
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
                                visited,
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
                                visited,
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
                        visited,
                    );
                }
            }
            SignatureItem::SigModule(_id, md, _) => {
                if recurse && let ModuleType::MtySignature(sub_sig) = &md.md_type {
                    substitute_type_paths_in_sig_items(sub_sig, maps, ctx, visited, true);
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

/// Rewrite module-alias targets of a scraped child signature through the
/// parent component substitution.
///
/// OCaml compiler/ml/env.ml:1573-1578 builds child component tables with the
/// parent `sub` from env.ml:1530 `prefix_idents`; `scrape_alias` at
/// env.ml:1396-1408 strengthens the scraped signature with the unprefixed alias
/// path (e.g. `X.B` for a sibling `X`), and forcing the child module thunk at
/// env.ml:475-477 applies `Subst.modtype sub`, which rewrites that `X` to the
/// selected parent path (compiler/ml/subst.ml:69-76).
pub fn substitute_module_alias_paths_in_child_sig(
    child_sig: &mut [SignatureItem],
    parent_sig: &[SignatureItem],
    parent_module_path: &Path,
) {
    let maps = build_subst_maps(parent_sig, parent_module_path);
    for item in child_sig.iter_mut() {
        if let SignatureItem::SigModule(_, md, _) = item
            && let ModuleType::MtyAlias(_, path) = &mut md.md_type
        {
            *path = substitute_module_path(
                path,
                &maps.module_stamp_map,
                &maps.module_name_map,
                maps.protected_module_head.as_ref(),
            );
        }
    }
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
        let desc = ctx.get_desc(manifest).into_desc();
        let TypeDesc::Tconstr { path, args, abbrev } = desc else {
            continue;
        };
        let PathView::Pident(manifest_id) = path.view() else {
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
                path: Path::pdot(*parent_module_path, child_id.name()),
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
                    .or_insert_with(|| Path::pdot(*module_path, id.name()));
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
                    type_stamp_map,
                    &type_name_map,
                    module_stamp_map,
                    module_name_map,
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
                        type_stamp_map,
                        &type_name_map,
                        module_stamp_map,
                        module_name_map,
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
                        type_stamp_map,
                        &type_name_map,
                        module_stamp_map,
                        module_name_map,
                        protected_module_head,
                    ) {
                        substitute_type_expr_path(
                            manifest,
                            type_stamp_map,
                            &type_name_map,
                            module_stamp_map,
                            module_name_map,
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
                                            type_stamp_map,
                                            &type_name_map,
                                            module_stamp_map,
                                            module_name_map,
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
                                            type_stamp_map,
                                            &type_name_map,
                                            module_stamp_map,
                                            module_name_map,
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
                                    type_stamp_map,
                                    &type_name_map,
                                    module_stamp_map,
                                    module_name_map,
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
                                type_stamp_map,
                                &type_name_map,
                                module_stamp_map,
                                module_name_map,
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
                        type_stamp_map,
                        &type_name_map,
                        module_stamp_map,
                        module_name_map,
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
                                type_stamp_map,
                                &type_name_map,
                                module_stamp_map,
                                module_name_map,
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
                                type_stamp_map,
                                &type_name_map,
                                module_stamp_map,
                                module_name_map,
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
                        type_stamp_map,
                        &type_name_map,
                        module_stamp_map,
                        module_name_map,
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
                    let mut new_desc = (*desc);
                    if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                        *path = new_path;
                    }
                    replacement = Some(new_desc);
                }

                // Push type arguments onto work stack
                for arg in ctx.type_list(args).iter() {
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tarrow { args, ret } => {
                work_stack.extend(ctx.type_args(args).iter().map(|arg| arg.typ));
                work_stack.push(*ret);
            }
            TypeDesc::Ttuple(types) => {
                for t in ctx.type_list(types).iter() {
                    work_stack.push(t);
                }
            }
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => {
                work_stack.push(*t);
            }
            TypeDesc::Tpoly { body, vars } => {
                work_stack.push(*body);
                for v in ctx.type_list(vars).iter() {
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
                let row = &ctx.row_desc(row);
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
                        let mut new_row = (*row).clone();
                        if let Some((ref mut path, _)) = new_row.row_name {
                            *path = new_path;
                        }
                        let new_desc = TypeDesc::Tvariant(ctx.new_row_desc(new_row));
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
                    let mut new_desc = (*desc);
                    if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                        *path = new_path;
                    }
                    replacement = Some(new_desc);
                }
                for arg in ctx.type_list(args).iter() {
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

/// Path prefixes that `prefix_idents` (env.ml:1454-1481) re-roots when a
/// component is reached through a module alias. OCaml's raw unit signature
/// names its own binders with local idents, which the component prefix
/// replaces; Rust's persistent signatures name them through the unit path,
/// so every `<alias source>.x` becomes `<component>.x`.
pub fn alias_reroot_prefixes(module_path: &Path, ctx: &TypeContext) -> Vec<(Path, Path)> {
    component_alias_sources(module_path, ctx)
        .into_iter()
        .filter(|source| !source.same(module_path))
        .map(|source| (source, *module_path))
        .collect()
}

/// Copy `desc` with its alias-source paths re-rooted at the component when
/// its type mentions any (`Subst.value_description` of env.ml:1537).
pub fn reroot_value_description(
    desc: &mut crate::types::decl::ValueDescription,
    prefixes: &[(Path, Path)],
    ctx: &TypeContext,
) {
    if prefixes.is_empty() || !type_expr_mentions_path_prefixes(desc.val_type, prefixes, ctx) {
        return;
    }
    let mut cache = crate::types::type_expr::TypeExprRefMap::new();
    let map_path = |p: &Path| reroot_path(p, prefixes);
    desc.val_type = crate::types::typecore::copy_type_expr_mapping_paths(
        ctx,
        desc.val_type,
        &mut cache,
        &map_path,
    );
}

/// Alias sources of a component path, including those inherited from its
/// ancestors: when `A.B` is reached through the alias `A = U`, `A.B.C` is the
/// component `U.B.C` re-rooted (env.ml:1567-1578 builds child components
/// from the parent's prefixed signature).
fn component_alias_sources(module_path: &Path, ctx: &TypeContext) -> Vec<Path> {
    let mut sources = ctx.alias_sources_for_component_path(module_path);
    if let PathView::Pdot(parent, name, _) = module_path.view() {
        for parent_source in component_alias_sources(parent, ctx) {
            let derived = Path::pdot(parent_source, name.as_str());
            if !derived.same(module_path) && !sources.iter().any(|s| s.same(&derived)) {
                sources.push(derived);
            }
        }
    }
    sources
}

/// Rewrite `path` through the first matching `(old, new)` prefix pair.
pub fn reroot_path(path: &Path, prefixes: &[(Path, Path)]) -> Path {
    rewrite_path_by_path_prefixes(path, &PathPrefixes::new(prefixes))
        .unwrap_or_else(|| *path)
}

/// Whether any type constructor or package path reachable from `ty` starts
/// with one of the `old` prefixes.
pub fn type_expr_mentions_path_prefixes(
    ty: TypeExprRef,
    prefixes: &[(Path, Path)],
    ctx: &TypeContext,
) -> bool {
    fn walk(
        ty: TypeExprRef,
        prefixes: &PathPrefixes<'_>,
        ctx: &TypeContext,
        visited: &mut HashSet<TypeExprRef>,
    ) -> bool {
        if !visited.insert(ty) {
            return false;
        }
        let desc = ctx.get_desc(ty);
        let hit = |p: &Path| rewrite_path_by_path_prefixes(p, prefixes).is_some();
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                hit(path)
                    || ctx
                        .type_list(args)
                        .iter()
                        .any(|a| walk(a, prefixes, ctx, visited))
            }
            TypeDesc::Tarrow { args, ret } => {
                ctx.type_args(args)
                    .iter()
                    .any(|a| walk(a.typ, prefixes, ctx, visited))
                    || walk(*ret, prefixes, ctx, visited)
            }
            TypeDesc::Ttuple(items) => ctx
                .type_list(items)
                .iter()
                .any(|a| walk(a, prefixes, ctx, visited)),
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => walk(*t, prefixes, ctx, visited),
            TypeDesc::Tpoly { body, vars } => {
                walk(*body, prefixes, ctx, visited)
                    || ctx
                        .type_list(vars)
                        .iter()
                        .any(|v| walk(v, prefixes, ctx, visited))
            }
            TypeDesc::Tobject { fields } => walk(*fields, prefixes, ctx, visited),
            TypeDesc::Tfield { typ, rest, .. } => {
                walk(*typ, prefixes, ctx, visited) || walk(*rest, prefixes, ctx, visited)
            }
            TypeDesc::Tvariant(row) => {
                let row = &ctx.row_desc(row);
                row.row_name.as_ref().is_some_and(|(p, args)| {
                    hit(p) || args.iter().any(|a| walk(*a, prefixes, ctx, visited))
                }) || walk(row.row_more, prefixes, ctx, visited)
                    || row.row_fields.iter().any(|(_, field)| match field {
                        crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                            walk(*t, prefixes, ctx, visited)
                        }
                        crate::types::type_expr::RowField::Reither { types, .. } => {
                            types.iter().any(|t| walk(*t, prefixes, ctx, visited))
                        }
                        _ => false,
                    })
            }
            TypeDesc::Tpackage { path, args, .. } => {
                hit(path)
                    || ctx
                        .type_list(args)
                        .iter()
                        .any(|a| walk(a, prefixes, ctx, visited))
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => false,
        }
    }
    walk(ty, &PathPrefixes::new(prefixes), ctx, &mut HashSet::new())
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
                    .or_insert_with(|| Path::pdot(*module_path, id.name()));
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

    for alias_source in component_alias_sources(module_path, ctx) {
        for item in sig_items {
            // `prefix_idents` (env.ml:1454-1481) re-roots type and module
            // binders alike: `Result.t` inside the aliased unit becomes
            // `<component>.Result.t`, so nested module prefixes move too.
            let (SignatureItem::SigType(id, _, _) | SignatureItem::SigModule(id, _, _)) = item
            else {
                continue;
            };
            let old_path = Path::pdot(alias_source, id.name());
            let new_path = Path::pdot(*module_path, id.name());
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
            rewrite_type_expr_by_path_prefix(desc.val_type, &old_path, &new_path, ctx);
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
    substituted.same(&Path::pdot(*module_path, id.name()))
}

fn substitute_type_path(
    path: &Path,
    type_stamp_map: &HashMap<i32, Path>,
    type_name_map: &HashMap<String, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
) -> Path {
    match path.view() {
        PathView::Pident(ident) => {
            if ident.stamp() != 0 {
                // OCaml compiler/ml/subst.ml:87-100 `type_path` rewrites
                // non-persistent ids through Ident.find_same only. It does not
                // fall back to declaration names or flattened path spelling.
                type_stamp_map
                    .get(&ident.stamp())
                    .cloned()
                    .unwrap_or_else(|| *path)
            } else {
                type_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| *path)
            }
        }
        PathView::Pdot(prefix, name, pos) => {
            let rewritten_prefix = substitute_module_path(
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            );
            Path::pdot_pos(rewritten_prefix, *name, *pos)
        }
        PathView::Papply(left, right) => Path::papply(
            substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
            substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
        ),
    }
}

fn substitute_module_path(
    path: &Path,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<String, Path>,
    protected_module_head: Option<&(i32, String)>,
) -> Path {
    match path.view() {
        PathView::Pident(ident) => {
            if ident.stamp() != 0 {
                let protected = protected_module_head
                    .is_some_and(|(stamp, name)| *stamp == ident.stamp() && name == ident.name());
                // OCaml compiler/ml/subst.ml:69-76 `module_path` rewrites
                // non-persistent ids through Ident.find_same only. It does not
                // fall back to declaration names or flattened path spelling.
                module_stamp_map
                    .get(&ident.stamp())
                    .and_then(|(_, path)| (!protected).then(|| *path))
                    .unwrap_or_else(|| *path)
            } else {
                module_name_map
                    .get(ident.name())
                    .cloned()
                    .unwrap_or_else(|| *path)
            }
        }
        PathView::Pdot(prefix, name, pos) => {
            let rewritten_prefix = substitute_module_path(
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            );
            Path::pdot_pos(rewritten_prefix, *name, *pos)
        }
        PathView::Papply(left, right) => Path::papply(
            substitute_module_path(
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
            substitute_module_path(
                right,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in ctx.type_args(args).iter() {
                rewrite_type_expr_prefix(arg.typ, old_name, new_prefix, ctx, visited);
            }
            rewrite_type_expr_prefix(*ret, old_name, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for t in ctx.type_list(types).iter() {
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
            for v in ctx.type_list(vars).iter() {
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
            let row = &ctx.row_desc(row);
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_prefix(path, old_name, new_prefix)
            {
                let mut new_row = (*row).clone();
                if let Some((ref mut path, _)) = new_row.row_name {
                    *path = new_path;
                }
                let new_desc = TypeDesc::Tvariant(ctx.new_row_desc(new_row));
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// Rewrite a path's module prefix from an old name to a new path.
/// Returns Some(new_path) if rewritten, None if unchanged.
fn rewrite_path_prefix(path: &Path, old_name: &str, new_prefix: &Path) -> Option<Path> {
    match path.view() {
        // Pident("Belt_Array") → new_prefix (e.g., Pdot(Pident("Belt"), "Array"))
        PathView::Pident(id) if id.name() == old_name => Some(*new_prefix),
        // Pdot(Pident("Belt_Array"), "t", pos) → Pdot(new_prefix, "t", pos)
        PathView::Pdot(inner, name, pos) => {
            if let PathView::Pident(id) = inner.view() {
                if id.name() == old_name {
                    return Some(Path::pdot_pos(*new_prefix, *name, *pos));
                }
            }
            // Recursively check deeper paths
            let rewritten_inner = rewrite_path_prefix(inner, old_name, new_prefix);
            rewritten_inner.map(|new_inner| Path::pdot_pos(new_inner, *name, *pos))
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
            rewrite_module_prefix_paths_in_sig(
                crate::types::decl::signature_mut(sig),
                old_name,
                new_prefix,
            );
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
        return Some(*new_prefix);
    }
    match path.view() {
        PathView::Pdot(inner, name, pos) => {
            if inner.same(old_prefix) {
                return Some(Path::pdot_pos(*new_prefix, *name, *pos));
            }
            rewrite_path_by_path_prefix(inner, old_prefix, new_prefix)
                .map(|new_inner| Path::pdot_pos(new_inner, *name, *pos))
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
                    .entry(crate::types::context::SamePathKey::new(*old_prefix))
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
            index.get(&crate::types::context::SamePathKey::new(*ancestor))
        {
            first = Some(first.map_or(position, |found| found.min(position)));
        }
        match ancestor.view() {
            PathView::Pdot(inner, _, _) => ancestor = inner,
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
            rewrite_sig_paths_by_path_prefix(
                crate::types::decl::signature_mut(sig),
                old_prefix,
                new_prefix,
            );
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
fn rewrite_type_expr_by_path_prefix_in(
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_by_path_prefix_in(arg, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in ctx.type_args(args).iter() {
                rewrite_type_expr_by_path_prefix_in(arg.typ, old_prefix, new_prefix, ctx, visited);
            }
            rewrite_type_expr_by_path_prefix_in(*ret, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for t in ctx.type_list(types).iter() {
                rewrite_type_expr_by_path_prefix_in(t, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) => {
            rewrite_type_expr_by_path_prefix_in(*t, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tsubst(t) => {
            rewrite_type_expr_by_path_prefix_in(*t, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_expr_by_path_prefix_in(*body, old_prefix, new_prefix, ctx, visited);
            for v in ctx.type_list(vars).iter() {
                rewrite_type_expr_by_path_prefix_in(v, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tobject { fields, .. } => {
            rewrite_type_expr_by_path_prefix_in(*fields, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tfield { typ, rest, .. } => {
            rewrite_type_expr_by_path_prefix_in(*typ, old_prefix, new_prefix, ctx, visited);
            rewrite_type_expr_by_path_prefix_in(*rest, old_prefix, new_prefix, ctx, visited);
        }
        TypeDesc::Tvariant(row) => {
            let row = &ctx.row_desc(row);
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_by_path_prefix(path, old_prefix, new_prefix)
            {
                let mut new_row = (*row).clone();
                if let Some((ref mut path, _)) = new_row.row_name {
                    *path = new_path;
                }
                let new_desc = TypeDesc::Tvariant(ctx.new_row_desc(new_row));
                ctx.set_desc(ty_ref, new_desc);
            }
            if let Some((_, args)) = &row.row_name {
                for &arg in args {
                    rewrite_type_expr_by_path_prefix_in(arg, old_prefix, new_prefix, ctx, visited);
                }
            }
            rewrite_type_expr_by_path_prefix_in(row.row_more, old_prefix, new_prefix, ctx, visited);
            for field in &row.row_fields {
                match &field.1 {
                    crate::types::type_expr::RowField::Rpresent(Some(t)) => {
                        rewrite_type_expr_by_path_prefix_in(
                            *t, old_prefix, new_prefix, ctx, visited,
                        );
                    }
                    crate::types::type_expr::RowField::Reither { types, .. } => {
                        for &t in types {
                            rewrite_type_expr_by_path_prefix_in(
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_by_path_prefix_in(arg, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
    }
}

/// [`rewrite_type_expr_by_path_prefix_in`] with a fresh visited set.
pub fn rewrite_type_expr_by_path_prefix(
    ty_ref: TypeExprRef,
    old_prefix: &Path,
    new_prefix: &Path,
    ctx: &TypeContext,
) {
    let mut visited = HashSet::new();
    rewrite_type_expr_by_path_prefix_in(ty_ref, old_prefix, new_prefix, ctx, &mut visited);
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tconstr { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_by_path_prefixes(arg, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tarrow { args, ret } => {
            for arg in ctx.type_args(args).iter() {
                rewrite_type_expr_by_path_prefixes(arg.typ, prefixes, ctx, visited);
            }
            rewrite_type_expr_by_path_prefixes(*ret, prefixes, ctx, visited);
        }
        TypeDesc::Ttuple(types) => {
            for t in ctx.type_list(types).iter() {
                rewrite_type_expr_by_path_prefixes(t, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => {
            rewrite_type_expr_by_path_prefixes(*t, prefixes, ctx, visited);
        }
        TypeDesc::Tpoly { body, vars } => {
            rewrite_type_expr_by_path_prefixes(*body, prefixes, ctx, visited);
            for v in ctx.type_list(vars).iter() {
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
            let row = &ctx.row_desc(row);
            if let Some((path, _)) = &row.row_name
                && let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes)
            {
                let mut new_row = (*row).clone();
                if let Some((ref mut path, _)) = new_row.row_name {
                    *path = new_path;
                }
                let new_desc = TypeDesc::Tvariant(ctx.new_row_desc(new_row));
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
                let mut new_desc = (*desc);
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
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
                rewrite_type_expr_by_path_prefix_in(
                    desc.val_type,
                    old_prefix,
                    new_prefix,
                    ctx,
                    &mut visited,
                );
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    rewrite_type_expr_by_path_prefix_in(
                        param,
                        old_prefix,
                        new_prefix,
                        ctx,
                        &mut visited,
                    );
                }
                if let Some(manifest) = decl.type_manifest {
                    rewrite_type_expr_by_path_prefix_in(
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
                                        rewrite_type_expr_by_path_prefix_in(
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
                                        rewrite_type_expr_by_path_prefix_in(
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
                                rewrite_type_expr_by_path_prefix_in(
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
                            rewrite_type_expr_by_path_prefix_in(
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

/// Recursively substitute type paths in sub-module signatures.
/// For a module like Belt with sub-modules Array, Map, etc.,
/// the types in Belt.Array should have paths like Pdot(Pdot(Pident "Belt") "Array") "t"
/// instead of Pident "t".
pub fn substitute_submodule_paths(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    // Match OCaml `prefix_idents`/`Subst` behavior: when descending into a
    // submodule, keep parent substitutions visible so child signatures can
    // reference parent-defined types through qualified paths.
    let parent_maps = build_subst_maps(sig_items, module_path);

    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            let sub_path = Path::pdot(*module_path, id.name());
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
                if let PathView::Pident(alias_id) = alias_path.view()
                    && !rewrites.has_alias_rewrite(alias_id.name())
                {
                    let qualified = Path::pdot(*module_path, id.name_atom());
                    rewrites.insert_alias_rewrite_if_absent(alias_id.name().to_string(), qualified);
                }
            }
            // Also recurse into MtySignature submodules to find nested aliases
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                let sub_path = Path::pdot(*module_path, id.name_atom());
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
    add_signature_to_env_with_options(sig_items, module_path, env, ctx, true, false, None);
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
    precomputed_components: Option<&crate::types::env_lazy::QualifiedModuleComponents>,
) {
    if as_opened {
        let layers = build_opened_layers(
            sig_items,
            module_path,
            ctx,
            apply_path_subst,
            precomputed_components,
        );
        env.add_prebuilt_open_layers(*module_path, &layers);
        return;
    }
    add_signature_to_env_with_options_inner(
        sig_items,
        module_path,
        env,
        ctx,
        false,
        apply_path_subst,
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
            Some(components),
        )
    });
    env.add_prebuilt_open_layers(*components.access_path(), &layers);
}

#[allow(clippy::too_many_arguments)]
fn add_signature_to_env_with_options_inner(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext,
    as_opened: bool,
    apply_path_subst: bool,
    precomputed_components: Option<&crate::types::env_lazy::QualifiedModuleComponents>,
    opened_out: Option<&mut Option<crate::types::env::OpenedLayers>>,
) {
    // Apply path substitution: rewrite Tconstr paths from internal
    // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
    // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
    if apply_path_subst {
        substitute_type_paths_in_sig(sig_items, module_path, ctx);
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
    let mut reroot_prefixes = alias_reroot_prefixes(module_path, ctx);
    // Components of an in-process unit keep their value types naming the
    // unit's items (`Unit.t`); re-root the opened values at the component
    // path like `prefix_idents` does (env.ml:1454-1481, 1530-1538).
    if let Some(source) = precomputed_components.and_then(|c| c.rerooted_value_source())
        && !reroot_prefixes.iter().any(|(from, _)| from.same(source))
    {
        reroot_prefixes.push((*source, *module_path));
    }
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
        let slot_path = |name: &str, p: i32| Path::pdot_pos(*module_path, name, p);
        match item {
            SignatureItem::SigValue(id, desc) => {
                // Add value binding with qualified path
                let mut desc = desc.clone();
                // env.ml:1874-1877 opens the component table, whose values
                // were substituted for the component path (env.ml:1537).
                reroot_value_description(&mut desc, &reroot_prefixes, ctx);
                let value_pos = pos;
                desc.val_path = Some(slot_path(id.name(), value_pos));
                // OCaml: only increment pos for non-primitive values
                if !matches!(desc.val_kind, crate::types::decl::ValueKind::ValPrim(_)) {
                    pos += 1;
                }
                if as_opened {
                    opened_values.push((*id, desc, value_pos));
                } else {
                    env.add_value(*id, desc);
                }
            }
            SignatureItem::SigType(id, decl, _rec_status) => {
                // Add type binding with qualified path
                let mut decl = (**decl).clone();
                decl.type_path = Some(Path::pdot(*module_path, id.name()));
                let decl = Arc::new(decl);
                if as_opened {
                    opened_types.push((*id, decl.clone()));
                } else {
                    env.add_type(*id, decl.clone());
                }

                // Also add constructors and labels from this type
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, layout) => {
                        let type_path = Path::pdot(*module_path, id.name());
                        for (position, cd) in constrs.iter().enumerate() {
                            let inline_record = match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    let inline_params =
                                        inline_record_type_params(ctx, &decl.type_params, labels);
                                    let inline_path =
                                        Path::pdot(type_path, cd.cd_id.name());
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
                                ctx.new_generic_constr(type_path, decl.type_params.clone())
                            };

                            // datarepr.ml:62-75: the variables of the arguments
                            // that the GADT result type does not mention.
                            let cstr_existentials = crate::types::env::constructor_existentials(
                                ctx,
                                &cstr_args,
                                cd.cd_res.map(|_| cstr_res),
                            );
                            let cstr_desc = ConstructorDescription {
                                cstr_name: cd.cd_id.name().to_string(),
                                cstr_res,
                                cstr_existentials,
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
                                // datarepr.ml:111-172 `cstr_loc = cd_loc`.
                                cstr_loc: cd.cd_loc,
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
                                        Path::pdot(type_path, cstr_desc.cstr_name.clone());
                                    let ty_res = ctx
                                        .new_constr(inline_path, inlined_decl.type_params.clone());
                                    for (pos, ld) in labels.iter().enumerate() {
                                        let label_desc = LabelDescription {
                                            lbl_name: ld.ld_id.name_atom(),
                                            lbl_runtime_name: ld.declaration_name(),
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
                                            lbl_loc: ld.ld_loc,
                                            lbl_attributes: ld.ld_attributes.clone(),
                                        };
                                        if as_opened {
                                            opened_labels.push((ld.ld_id, label_desc));
                                        } else {
                                            env.add_label(ld.ld_id, label_desc);
                                        }
                                    }
                                }
                            }

                            if as_opened {
                                opened_constructors.push((cd.cd_id, cstr_desc));
                            } else {
                                env.add_constructor(cd.cd_id, cstr_desc);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, repr) => {
                        let type_path = Path::pdot(*module_path, id.name());
                        let res_ty = ctx.new_generic_constr(type_path, decl.type_params.clone());

                        for (pos, ld) in labels.iter().enumerate() {
                            let label_desc = LabelDescription {
                                lbl_name: ld.ld_id.name_atom(),
                                lbl_runtime_name: ld.declaration_name(),
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
                                lbl_loc: ld.ld_loc,
                                lbl_attributes: ld.ld_attributes.clone(),
                            };
                            if as_opened {
                                opened_labels.push((ld.ld_id, label_desc));
                            } else {
                                env.add_label(ld.ld_id, label_desc);
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
                md.md_path = Some(access_path);
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
                        match path.view() {
                            PathView::Pident(alias_id) => {
                                if alias_id.is_persistent() {
                                    return path;
                                }
                                let clean = alias_id.name();
                                if clean == module_name {
                                    *access_path
                                } else if clean == module_path.last() {
                                    *module_path
                                } else {
                                    path
                                }
                            }
                            PathView::Pdot(prefix, name, pos) => Path::pdot_pos(
                                go(*prefix, module_path, module_name, access_path),
                                *name,
                                *pos,
                            ),
                            PathView::Papply(functor, arg) => Path::papply(
                                go(*functor, module_path, module_name, access_path),
                                go(*arg, module_path, module_name, access_path),
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
                        ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path)
                            if alias_path.as_pident().is_some_and(|alias_id| alias_id.is_persistent())
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
                            access_path,
                            md.clone(),
                        ));
                        opened_module_components.push((*id, stored, module_pos));
                        opened_modules.push((*id, md.clone(), module_pos));
                    } else if let Some((_, stored)) = precomputed_components
                        .and_then(|components| components.lookup_child_components(id.name(), ctx))
                    {
                        // OCaml compiler/ml/env.ml:1841-1877 opens the
                        // already-built `comp_components` table alongside
                        // `comp_modules`. Reuse that child component thunk so
                        // opened-module source lookup follows env.ml:1000-1013
                        // without forcing the parent module declaration.
                        opened_module_components.push((*id, stored, module_pos));
                        opened_modules.push((*id, md.clone(), module_pos));
                    } else {
                        opened_modules.push((*id, md.clone(), module_pos));
                    }
                } else {
                    env.add_module(*id, md.clone());
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
                    opened_modtypes.push((*id, mtd));
                } else {
                    env.add_modtype(*id, mtd);
                }
            }
            SignatureItem::SigTypext(id, ext, _status) => {
                let ext_slot = pos;
                pos += 1; // Extension constructors occupy runtime slots
                let ext_type_path = substitute_path(&ext.ext_type_path);
                // Add extension constructor
                let ext_cstr_args: Vec<TypeExprRef> = match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => args.clone(),
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        labels.iter().map(|l| l.ld_type).collect()
                    }
                };
                let cstr_desc = ConstructorDescription {
                    cstr_name: id.name().to_string(),
                    cstr_res: ctx.new_generic_constr(ext_type_path, ext.ext_type_params.clone()),
                    // datarepr.ml:62-75, extension_descr.
                    cstr_existentials: crate::types::env::constructor_existentials(
                        ctx,
                        &ext_cstr_args,
                        ext.ext_ret_type,
                    ),
                    cstr_args: ext_cstr_args,
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
                    // `Datarepr.extension_descr`: `cstr_loc = ext.ext_loc`.
                    cstr_loc: ext.ext_loc,
                    // `Datarepr.extension_descr`: `cstr_attributes = ext.ext_attributes`.
                    cstr_attributes: ext.ext_attributes.clone(),
                    cstr_inlined: None,
                };
                if as_opened {
                    opened_constructors.push((*id, cstr_desc));
                } else {
                    env.add_constructor(*id, cstr_desc);
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
            None => env.add_prebuilt_open_layers(*module_path, &layers),
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
        original.register_in_memory_signature("M", vec![], "M.res", None, vec![], &ctx);
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
    fn stored_modules_register_lazily_and_decode_on_first_lookup() {
        let portable = PortablePersStruct::new(
            "Stored".to_string(),
            "Stored.res".to_string(),
            None,
            Vec::new(),
            portable_types::PortableSignature {
                ps_sig: vec![],
                cmi_longident_names: vec![],
                type_graph: portable_types::PortableTypeGraph {
                    entries: vec![],
                    variant_layouts: vec![],
                    mutabilities: vec![],
                },
                locations: Default::default(),
            },
            None,
            7,
        );
        let mut compiled = ModuleRegistry::new();
        compiled.register_module(
            "Stored",
            portable,
            InMemoryModuleInfo::new(PathBuf::from("Stored.res"), true, HashMap::new(), true),
        );
        let data = compiled.encode_stored_module("Stored").unwrap();

        let mut registry = ModuleRegistry::new();
        assert!(registry.register_stored_lazily("Bad", &data[..3]).is_none());
        assert!(registry.register_stored_lazily("Stored", &data).is_some());
        assert!(registry.is_pending_stored("Stored"));
        assert!(!registry.is_empty());
        let env = PersistentEnv::from_registry(&registry);
        assert!(registry.is_pending_stored("Stored"));
        // A lookup through any snapshot decodes the module into the shared maps.
        let snapshot = registry.for_worker_snapshot();
        assert!(
            env.in_memory_info("Stored")
                .is_some_and(|info| info.is_runtime)
        );
        assert!(!registry.is_pending_stored("Stored"));
        assert_eq!(snapshot.registered("Stored").0.unwrap().fingerprint, 7);
        // A compiled module replaces a pending one.
        assert!(registry.register_stored_lazily("Other", &data).is_some());
        registry.register_module(
            "Other",
            PortablePersStruct::clone(&snapshot.registered("Stored").0.unwrap()),
            InMemoryModuleInfo::new(PathBuf::from("Other.res"), false, HashMap::new(), false),
        );
        assert!(!registry.is_pending_stored("Other"));
        assert!(!registry.module_info_is_runtime("Other"));
    }

    #[test]
    fn portable_override_first_write_keeps_backing_graph_shared() {
        let portable = Arc::new(PortablePersStruct::new(
            "Portable".to_string(),
            "Portable.res".to_string(),
            None,
            Vec::new(),
            portable_types::PortableSignature {
                ps_sig: vec![],
                cmi_longident_names: vec![],
                type_graph: portable_types::PortableTypeGraph {
                    entries: vec![],
                    variant_layouts: vec![],
                    mutabilities: vec![],
                },
                locations: Default::default(),
            },
            None,
            0,
        ));
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
        let (sig1, fallback1, _) = first
            .typecheck_source_signature(&unit, &ctx1)
            .expect("first fallback");
        let (sig2, fallback2, _) = second
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

/// The units the inlinable lambda exported under `name` refers to.
fn lambda_units_of(lambdas: &crate::lambda::CmjExportLambdas, name: &str) -> Vec<Name> {
    let Some(lambda) = lambdas.get(name) else {
        return Vec::new();
    };
    crate::lambda::lam_compile::collect_possible_required_modules_for_lambda(lambda)
        .into_iter()
        .map(|module| module.id.name_atom())
        .collect()
}

/// The registered modules as a [`super::item_deps::UnitSource`].
struct RegistryUnitSource<'a> {
    registry: &'a ModuleRegistry,
    /// Whether item references include what inlinable bodies refer to.
    lambdas: bool,
}

impl super::item_deps::UnitSource for RegistryUnitSource<'_> {
    fn lambda_units(&self, unit: Name, name: &str) -> Vec<Name> {
        if !self.lambdas {
            return Vec::new();
        }
        self.registry
            .with_info(&unit, |info| {
                lambda_units_of(&info.cmj_export_lambdas, name)
            })
            .unwrap_or_default()
    }
    fn ignored(&self, unit: Name) -> bool {
        self.registry.module_info_is_runtime(&unit)
    }
    fn refs(&self, unit: Name) -> Option<Arc<super::item_deps::UnitRefs>> {
        let registry = self.registry;
        let ps = registry
            .local_cached_modules
            .get(unit.as_str())
            .cloned()
            .or_else(|| registry.cached_modules.get_cloned(&unit))?;
        let lambdas = if self.lambdas {
            registry
                .with_info(&unit, |info| Arc::as_ptr(&info.cmj_export_lambdas) as usize)
                .unwrap_or(0)
        } else {
            usize::MAX
        };
        let key = (unit, Arc::as_ptr(&ps) as usize, ps.fingerprint, lambdas);
        if let Some(refs) = registry.item_refs_cache.read().unwrap().get(&key) {
            return Some(refs.clone());
        }
        let refs = Arc::new(super::item_deps::unit_refs(unit, &ps, self));
        registry
            .item_refs_cache
            .write()
            .unwrap()
            .insert(key, refs.clone());
        Some(refs)
    }
}
