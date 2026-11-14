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
use std::rc::Rc;
use std::sync::{Arc, Mutex, RwLock};

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::driver::{
    CompilerOptions, experimental_let_unwrap_for_structure, initial_type_env, jsx_module_name,
    jsx_version_for_structure, normalize_signature,
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
use crate::name::Name;
use crate::parser::{Parser, jsx_ppx, module};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, ConstructorDescription, ConstructorKind, ModtypeDeclaration,
    ModuleDeclaration, ModuleType, RecStatus, Signature, SignatureItem, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::type_marks::{TypeVisitSet, visit_set};
use crate::types::typecore::TypeCheckContext;
use crate::types::typedtree::{
    ModuleType as TypedModuleType, ModuleTypeDesc as TypedModuleTypeDesc,
};
use crate::types::typemod::{decl_module_type_from_typed, transl_signature, type_structure};

use super::cmi_format;
use super::portable_types::{self, PortablePersStruct};
use super::sig_reader::SigReadContext;

/// Short enough module names (most) stay inline, so a case-variant probe
/// does not allocate.
fn first_char_case_variant(name: &str) -> Option<smol_str::SmolStr> {
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
    let mut variant = smol_str::SmolStrBuilder::new();
    variant.push(swapped);
    variant.push_str(rest);
    Some(variant.finish())
}

fn resolve_first_char_case_key<'a, V>(map: &'a HashMap<String, V>, name: &str) -> Option<&'a str> {
    if let Some((key, _)) = map.get_key_value(name) {
        return Some(key.as_str());
    }
    let variant = first_char_case_variant(name)?;
    map.get_key_value(variant.as_str()).map(|(key, _)| key.as_str())
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

/// Database/inline entries retained when a package index is attached.
type PendingModules = Mutex<HashMap<String, Arc<Mutex<Option<PendingCore>>>>>;

/// The stored modules of a registry whose signature and JS metadata are not
/// decoded yet, with the registry maps that decoding one fills. An entry is
/// decoded once, by the first lookup of its name; until then the module
/// costs only its encoded bytes.
pub struct LazyStoredModules {
    pending: Arc<PendingModules>,
    snapshots: Vec<Arc<dyn SnapshotModules>>,
    cached_modules: Arc<RwLock<HashMap<String, Arc<PortablePersStruct>>>>,
    module_info: Arc<RwLock<HashMap<String, InMemoryModuleInfo>>>,
}

impl std::fmt::Debug for LazyStoredModules {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LazyStoredModules").finish_non_exhaustive()
    }
}

/// An immutable package index. Names are searched in embedded bytes; a slot
/// identifies its core without a second name lookup or a startup hash table.
pub trait SnapshotModules: Send + Sync {
    /// O(1), whether this index supplies the runtime package.
    fn is_runtime(&self) -> bool { false }
    /// O(log module count) comparisons, no allocation or decoding.
    fn find(&self, name: &str) -> Option<u32>;
    /// O(core bytes + filename bytes), called once for a referenced slot.
    fn decode(&self, slot: u32) -> Option<super::stored_module::StoredCore>;
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
            || first_char_case_variant(name).is_some_and(|variant| self.materialize(variant.as_str()))
    }

    fn materialize(&self, name: &str) -> bool {
        self.materialize_with(name, None)
    }

    /// [`Self::materialize`], from `bytes` when given (read ahead by the
    /// caller) instead of the entry's own.
    fn materialize_with(&self, name: &str, bytes: Option<Vec<u8>>) -> bool {
        let pending_index = self.pending.lock().unwrap();
        let Some(entry) = pending_index.get(name).cloned() else {
            let Some((snapshot, slot)) = self.snapshots.iter()
                .find_map(|snapshot| snapshot.find(name).map(|slot| (snapshot, slot)))
            else { return false; };
            // The existing pending-index acquisition serializes first decodes.
            // Already decoded lookups use the registry maps, not this path.
            if self.module_info.read().unwrap().contains_key(name) { return true; }
            let Some(core) = snapshot.decode(slot) else { return false; };
            self.insert_core(name, core);
            crate::perf_counters::record_snapshot_module_decode();
            return true;
        };
        drop(pending_index);
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
            self.insert_core(name, core);
        }
        drop(pending);
        self.pending.lock().unwrap().remove(name);
        true
    }

    /// O(1) registry insertions after a core decode; no type-node traversal.
    fn insert_core(&self, name: &str, core: super::stored_module::StoredCore) {
        if let Some(pers) = core.pers_struct {
            self.cached_modules.write().unwrap().insert(name.to_string(), Arc::new(pers));
        }
        self.module_info.write().unwrap().insert(name.to_string(), core.info);
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
        map.get_key_value(variant.as_str())
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
        map.get_key_value(variant.as_str())
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
    /// See [`PersStruct::own_alias_rewrites`].
    pub(crate) ps_alias_rewrites: std::sync::OnceLock<Option<Arc<UnitAliasRewrites>>>,
    /// The view cell of the unit's own path, set when the build's world owns
    /// the unit (`World::unit`); unset for a unit only this compilation holds.
    pub(crate) ps_view: std::sync::OnceLock<Arc<crate::types::module_view::ViewCell>>,
}

/// The alias rewrites of one unit's signature, by flattened module name.
pub(crate) type UnitAliasRewrites = HashMap<Name, Path>;

impl PersStruct {
    /// The alias rewrites `collect_alias_rewrites` finds in this unit's
    /// signature when the unit is reached under its own name, `None` when
    /// there are none. Computed once: a structure shared between
    /// compilations hands every one of them the same table.
    fn own_alias_rewrites(&self) -> Option<&Arc<UnitAliasRewrites>> {
        self.ps_alias_rewrites
            .get_or_init(|| {
                let mut rewrites = UnitAliasRewrites::new();
                let unit_path = Path::pident(Ident::create_persistent(&self.ps_name));
                collect_alias_rewrites(&self.ps_sig, &unit_path, &mut rewrites);
                (!rewrites.is_empty()).then(|| Arc::new(rewrites))
            })
            .as_ref()
    }
}

/// A closed constant a module exports, as its `.cmj` records it; other
/// modules inline it instead of reading the export.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CmjExportConstant {
    /// `true` or `false`.
    Bool(bool),
    /// `null`.
    Null,
    /// `undefined`.
    Undefined {
        /// Whether the constant is the unit value `()`.
        is_unit: bool,
    },
}

/// The arity of an export, as its `.cmj` records it.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum CmjExportArity {
    /// The arity of a value export.
    Single(Arity),
    /// A submodule (an immutable block): the arity of each of its fields.
    Submodule(Vec<Arity>),
}

/// The module-level facts of a decoded `.cmj` file.
#[derive(Debug, Clone)]
pub struct CmjModuleMetadata {
    /// Whether the module is side-effect free.
    pub is_pure: bool,
    /// The closed constants the module exports, by export name.
    pub export_constants: HashMap<String, CmjExportConstant>,
    /// The package the module belongs to and where its JavaScript goes.
    pub package_spec: CmjPackageSpec,
    /// The case of the module's JavaScript file name.
    pub file_case: CmjFileCase,
}

/// The package of a `.cmj` (`Js_packages_info.package_name`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CmjPackageName {
    /// No package (`Pkg_empty`).
    Empty,
    /// `@rescript/runtime` (`Pkg_runtime`).
    Runtime,
    /// A named package (`Pkg_normal`).
    Normal(String),
}

/// A JavaScript module system a package emits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CmjPackageModuleSystem {
    /// CommonJS (`require`).
    CommonJs,
    /// ES modules (`import`).
    EsModule,
}

/// Where a module's JavaScript goes for one module system.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct CmjPackageInfo {
    /// The module system.
    pub module_system: CmjPackageModuleSystem,
    /// The output directory, relative to the package root.
    pub path: String,
    /// The JavaScript file suffix.
    pub suffix: String,
}

/// A `.cmj`'s package information (`Js_packages_info.t`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CmjPackageSpec {
    /// The package.
    pub name: CmjPackageName,
    /// Where the module's JavaScript goes, per module system.
    pub module_systems: Vec<CmjPackageInfo>,
}

/// The case of a module's JavaScript file name (`Ext_js_file_kind.case`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmjFileCase {
    /// The module name, capitalized as it is.
    Upper,
    /// The module name with its first letter lowercased.
    Little,
}

/// What generating an import of a dependency needs to know of it
/// (`Lam_compile_env.get_package_info_from_cmj`).
#[derive(Debug, Clone)]
pub struct CmjModuleImportInfo {
    /// The dependency's package and output directories.
    pub package_spec: CmjPackageSpec,
    /// The case of the dependency's JavaScript file name.
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

/// A module's package name, package root and JS output suffix, as
/// [`PersistentEnv::module_js_package_info`] gives them.
pub type JsPackageInfo = (Arc<str>, Arc<PathBuf>, Option<Arc<str>>);

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
    /// Metadata with the given source path, purity and constants, and no
    /// arities, lambdas or package.
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
            is_runtime,
            package_name: None,
            package_root: None,
            js_output_suffix: None,
            package_outputs: Arc::new(Vec::new()),
        }
    }

    /// Set where the module's JavaScript goes, per module system.
    pub fn with_package_outputs(mut self, package_outputs: Vec<CmjPackageInfo>) -> Self {
        self.package_outputs = Arc::new(package_outputs);
        self
    }

    /// Set the exports other modules may inline.
    pub fn with_cmj_export_lambdas(
        mut self,
        cmj_export_lambdas: crate::lambda::CmjExportLambdas,
    ) -> Self {
        self.cmj_export_lambdas = Arc::new(cmj_export_lambdas);
        self
    }

    /// Set the arities of the exports.
    pub fn with_cmj_export_arities(
        mut self,
        cmj_export_arities: HashMap<String, CmjExportArity>,
    ) -> Self {
        self.cmj_export_arities = Arc::new(cmj_export_arities);
        self
    }

    /// Set the package name, root and JS suffix used for import rebasing.
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

/// The alias rewrites a compilation knows: the first rewrite recorded for a
/// flattened module name is the one that counts.
#[derive(Clone)]
struct AliasPrefixRewrites {
    base: SharedRegistryMap<Path>,
    /// Keyed by `Name`, so the view copies `view_mut` makes copy this table
    /// without cloning every key.
    local: HashMap<Name, Path>,
    /// The tables of loaded units that are reached under their own name, in
    /// load order (see [`PersStruct::own_alias_rewrites`]). A unit's table
    /// stands for recording each of its rewrites when the unit was loaded:
    /// it yields to `base`, to the entries `local` had by then and to the
    /// tables before it, and `local` never gains a name a table holds.
    units: Vec<Arc<UnitAliasRewrites>>,
}

impl AliasPrefixRewrites {
    fn new() -> Self {
        Self {
            base: SharedRegistryMap::default(),
            local: HashMap::new(),
            units: Vec::new(),
        }
    }

    fn from_base(base: SharedRegistryMap<Path>, local: HashMap<Name, Path>) -> Self {
        Self {
            base,
            local,
            units: Vec::new(),
        }
    }

    fn get(&self, key: &str) -> Option<Path> {
        let name = Name::lookup(key);
        name.and_then(|name| self.local.get(&name).copied())
            .or_else(|| self.base.get_cloned(key))
            .or_else(|| self.unit_rewrite(name?))
    }

    fn unit_rewrite(&self, key: Name) -> Option<Path> {
        self.units.iter().find_map(|unit| unit.get(&key).copied())
    }

    fn contains(&self, key: Name) -> bool {
        self.local.contains_key(&key)
            || self.base.contains_key(key.as_str())
            || self.unit_rewrite(key).is_some()
    }

    fn insert_if_absent(&mut self, key: Name, value: Path) {
        if !self.contains(key) {
            self.local.insert(key, value);
        }
    }

    /// Record every rewrite of a loaded unit's table that is not known yet.
    fn add_unit(&mut self, unit: &Arc<UnitAliasRewrites>) {
        if !self.units.iter().any(|known| Arc::ptr_eq(known, unit)) {
            self.units.push(unit.clone());
        }
    }

    fn extend_missing(&mut self, rewrites: HashMap<Name, Path>) {
        for (key, value) in rewrites {
            self.insert_if_absent(key, value);
        }
    }

    /// The rewrites this compilation recorded itself, outside `base`.
    fn recorded(&self) -> HashMap<Name, Path> {
        let mut rewrites = self.local.clone();
        for unit in &self.units {
            for (key, path) in unit.iter() {
                rewrites.entry(*key).or_insert(*path);
            }
        }
        rewrites
    }

    fn to_hash_map(&self) -> HashMap<String, Path> {
        let mut rewrites = self.base.clone_map();
        rewrites.extend(self.local.iter().map(|(key, path)| (key.to_string(), *path)));
        for unit in &self.units {
            for (key, path) in unit.iter() {
                rewrites.entry(key.to_string()).or_insert(*path);
            }
        }
        rewrites
    }

    fn flattened_alias_heads_for_path(&self, qualified_path: &Path) -> Vec<String> {
        let mut heads = Vec::new();
        self.base.for_each(|flat_head, qualified| {
            if !Name::lookup(flat_head).is_some_and(|key| self.local.contains_key(&key))
                && qualified.same(qualified_path)
            {
                heads.push(flat_head.clone());
            }
        });
        for (flat_head, qualified) in self.local.iter() {
            if qualified.same(qualified_path) {
                heads.push(flat_head.to_string());
            }
        }
        for (index, unit) in self.units.iter().enumerate() {
            for (flat_head, qualified) in unit.iter() {
                if qualified.same(qualified_path)
                    && !self.local.contains_key(flat_head)
                    && !self.base.contains_key(flat_head.as_str())
                    && !self.units[..index]
                        .iter()
                        .any(|earlier| earlier.contains_key(flat_head))
                {
                    heads.push(flat_head.to_string());
                }
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
    /// The source-fallback modules are the modules of `@rescript/runtime`:
    /// a page or a test that has the runtime as source only type checks it
    /// on demand and imports it from the package.
    source_fallback_is_runtime: bool,
    /// Package roots of registered modules that carry no `InMemoryModuleInfo`
    /// (namespace units), for load-path visibility.
    module_package_roots: SharedRegistryMap<PathBuf>,
    local_cached_modules: HashMap<String, Arc<PortablePersStruct>>,
    local_module_info: HashMap<String, InMemoryModuleInfo>,
    local_alias_rewrites: HashMap<Name, Path>,
    local_source_fallback_paths: HashMap<String, PathBuf>,
    write_to_local: bool,
    /// Item references of registered signatures (see `resolve_reads`),
    /// shared by every snapshot. Keyed by the signature's identity, so a
    /// module registered again gets fresh entries.
    /// Keyed by unit, signature identity and fingerprint, and the identity
    /// of the JS metadata whose inlinable bodies the references follow
    /// (`usize::MAX` for references without them).
    item_refs_cache: Arc<RwLock<HashMap<ItemRefsKey, Arc<super::item_deps::UnitRefs>>>>,
}

/// Key of `ModuleRegistry::item_refs_cache`: the unit, its signature's
/// identity and fingerprint, and the identity of its JS metadata.
type ItemRefsKey = (Name, usize, u64, usize);

impl ModuleRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// A copy for one worker's compilation: it shares the published entries
    /// and writes the entries the worker registers to tables of its own.
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

    /// Whether a signature is registered for `name`.
    pub fn has_cached_module(&self, name: &str) -> bool {
        self.local_cached_modules.contains_key(name) || self.cached_modules.contains_key(name)
    }

    /// Prepare the signature summary on a worker before metadata wakes dependents.
    pub fn prepare_signature_summary(&self, name: &str) {
        if let Some(pers) = self.local_cached_modules.get(name).cloned()
            .or_else(|| self.cached_modules.get_cloned(name))
        {
            pers.summary();
        }
    }

    /// A digest of everything another module's compile can read about
    /// `name`: its published signature and its JS metadata (purity,
    /// constants, arities, inlinable lambdas, package).
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
            .is_some_and(|lazy| lazy.snapshots.iter().any(|index| index.find(name).is_some())
                || lazy.pending.lock().unwrap().contains_key(name))
    }

    /// O(package count), no module lookups or allocations.
    pub fn has_runtime_snapshot(&self) -> bool {
        self.cached_modules.lazy.as_ref()
            .is_some_and(|lazy| lazy.snapshots.iter().any(|index| index.is_runtime()))
    }

    /// Attach one immutable snapshot index before workers acquire the registry.
    /// O(package count), preserving earlier package indexes and stored cores.
    /// Only package handles are copied, never module names or core bytes.
    pub fn register_snapshot(&mut self, snapshot: Arc<dyn SnapshotModules>) {
        let previous = self.lazy_stored_modules();
        let pending = previous.pending.clone();
        let mut snapshots = previous.snapshots.clone();
        snapshots.push(snapshot);
        let lazy = Arc::new(LazyStoredModules {
            pending, snapshots,
            cached_modules: self.cached_modules.inner.clone(),
            module_info: self.module_info.inner.clone(),
        });
        self.cached_modules.lazy = Some(lazy.clone());
        self.module_info.lazy = Some(lazy);
    }

    /// The registry's pending stored modules, created on first use and
    /// attached to the maps decoding fills, so every later snapshot and
    /// `PersistentEnv` of the registry decodes on lookup.
    fn lazy_stored_modules(&mut self) -> Arc<LazyStoredModules> {
        if let Some(lazy) = &self.cached_modules.lazy {
            return lazy.clone();
        }
        let lazy = Arc::new(LazyStoredModules {
            pending: Arc::new(Mutex::new(HashMap::new())),
            snapshots: Vec::new(),
            cached_modules: self.cached_modules.inner.clone(),
            module_info: self.module_info.inner.clone(),
        });
        self.cached_modules.lazy = Some(lazy.clone());
        self.module_info.lazy = Some(lazy.clone());
        lazy
    }

    /// Register a clean module whose typed artifacts on disk are valid, with
    /// its JS metadata; its signature is read from its `.cmi`.
    pub fn register_disk_module(&mut self, name: &str, info: InMemoryModuleInfo) {
        self.disk_modules.insert(name.to_string(), true);
        self.insert_module_info(name.to_string(), info);
    }

    /// Whether no module signatures are registered: none compiled, none on
    /// disk and none waiting to be decoded.
    pub fn is_empty(&self) -> bool {
        self.local_cached_modules.is_empty()
            && self.cached_modules.len() == 0
            && self.disk_modules.len() == 0
            && self
                .cached_modules
                .lazy
                .as_ref()
                .is_none_or(|lazy| lazy.snapshots.is_empty() && lazy.pending.lock().unwrap().is_empty())
    }

    /// Whether registered module `name` belongs to `@rescript/runtime`.
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
                        Arc::new(Path::pident(Ident::create_persistent(
                            internal_name.as_str(),
                        ))),
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
        self.local_alias_rewrites.retain(|key, _| key.as_str() != name);
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

    /// Register the JS metadata of module `name`.
    pub fn insert_module_info(&mut self, name: String, info: InMemoryModuleInfo) {
        if self.write_to_local {
            self.local_module_info.insert(name, info);
        } else {
            self.module_info.insert(name, info);
        }
    }

    /// Register alias prefix rewrites (flattened name -> qualified path).
    pub fn extend_alias_rewrites(&mut self, new_alias_rewrites: HashMap<String, Path>) {
        if self.write_to_local {
            self.local_alias_rewrites.extend(
                new_alias_rewrites
                    .into_iter()
                    .map(|(key, path)| (Name::new(&key), path)),
            );
        } else {
            self.alias_rewrites.extend(new_alias_rewrites);
        }
    }

    /// Declare the source-fallback modules to be the modules of
    /// `@rescript/runtime`: generated JavaScript then imports them from the
    /// package, as it does in a build that compiled the runtime.
    pub fn set_source_fallback_is_runtime(&mut self, is_runtime: bool) {
        self.source_fallback_is_runtime = is_runtime;
    }

    /// Register the source file of module `name`, for type checking it on
    /// demand before it is compiled.
    pub fn insert_source_fallback_path(&mut self, name: String, path: PathBuf) {
        if self.write_to_local {
            self.local_source_fallback_paths.insert(name, path);
        } else {
            self.source_fallback_paths.insert(name, path);
        }
    }

    /// Replace the source files registered for on-demand type checking.
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
    /// Tables that change about once per compilation, shared by the view
    /// copies that `view_mut` makes when a cloned env prepares a unit.
    overrides: Arc<ResolutionOverrides>,
    /// Cache entries whose alias-rewrite side effects have already been
    /// applied to this PersistentEnv. OCaml's persistent structures keep lazy
    /// module components in the environment table (`compiler/ml/env.ml:711-746,
    /// 1516-1605`); Rust shares loaded structures across env clones, so each
    /// env still has to rebuild its local flattened-alias table when it first
    /// observes a cached signature.
    prepared_cached_alias_rewrites: HashSet<Name>,
}

#[derive(Clone, Default)]
struct ResolutionOverrides {
    in_memory_module_overrides: HashMap<String, InMemoryModuleInfo>,
    source_fallback_path_overrides: HashMap<String, PathBuf>,
    portable_cache_overrides: HashMap<String, Arc<PortablePersStruct>>,
    /// Modules hidden from this worker environment. Used when the current
    /// module's transient signature must be removed before raw/JS compilation
    /// without copy-on-writing the shared in-process registry maps.
    hidden_modules: HashSet<String>,
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
    /// `-enable-experimental LetUnwrap` of the current compilation, which a
    /// source fallback compiles its dependency with.
    experimental_let_unwrap: bool,
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
    /// See `ModuleRegistry::source_fallback_is_runtime`.
    source_fallback_is_runtime: bool,
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
    crc_units: Arc<Mutex<CrcUnits>>,
    /// `imported_units` with their recorded CRCs (env.ml:612-646): the
    /// units this compilation found and the units their CRC lists name.
    imported_units: Arc<Mutex<ImportedUnits>>,
    /// Decoded `.cmj` files by path, so the per-kind disk queries
    /// (`module_cmj_*`) read and unmarshal each file once per compilation.
    cmj_values: Arc<Mutex<HashMap<PathBuf, Option<OcamlValue>>>>,
    view: Arc<ResolutionView>,
}

/// `Consistbl.t`: each imported interface's assumed digest, with the file
/// that first assumed it.
type CrcUnits = HashMap<String, (Vec<u8>, String)>;

/// Per-environment memo of `outside_load_path`. Each clone starts empty:
/// clones are per compilation, and sharing one lock across workers made it
/// contended.
#[derive(Default)]
struct OutsideLoadPathMemo(std::cell::RefCell<crate::fast_hash::AHashMap<Name, bool>>);

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

impl Default for PersistentEnv {
    fn default() -> Self {
        Self::new()
    }
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

    fn overrides_mut(&mut self) -> &mut ResolutionOverrides {
        Arc::make_mut(&mut self.view_mut().overrides)
    }

    fn unhide_module(&mut self, name: &str) {
        if self.view.overrides.hidden_modules.contains(name) {
            self.unhide_module(name);
        }
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
            experimental_let_unwrap: false,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: SharedRegistryMap::default(),
            in_process_mode: false,
            disk_modules: SharedRegistryMap::default(),
            source_fallback_paths: SharedRegistryMap::default(),
            source_fallback_is_runtime: false,
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
                overrides: Arc::default(),
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
            experimental_let_unwrap: false,
            nopervasives: false,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: registry.module_info.clone(),
            in_process_mode: true,
            disk_modules: registry.disk_modules.clone(),
            source_fallback_paths: registry.source_fallback_paths.clone(),
            source_fallback_is_runtime: registry.source_fallback_is_runtime,
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
                overrides: Arc::new(ResolutionOverrides {
                    in_memory_module_overrides: registry.local_module_info.clone(),
                    source_fallback_path_overrides: registry.local_source_fallback_paths.clone(),
                    portable_cache_overrides: registry.local_cached_modules.clone(),
                    hidden_modules: HashSet::new(),
                }),
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

    /// The first loader error recorded through any clone of this env.
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

    /// The cache key `name` resolves to (inline for most module names, so
    /// no allocation) and its entry.
    fn cache_lookup_entry(
        &self,
        name: &str,
    ) -> Option<(smol_str::SmolStr, Option<Arc<PersStruct>>)> {
        if self.view.overrides.hidden_modules.contains(name) || self.outside_load_path(name) {
            return Some((smol_str::SmolStr::new(name), None));
        }
        let cache = self.cache.lock().unwrap();
        let cache_key = resolve_first_char_case_key(&cache, name)?;
        cache
            .get(cache_key)
            .cloned()
            .map(|value| (smol_str::SmolStr::new(cache_key), value))
    }

    /// The already-loaded persistent structure of `name`, without loading it.
    pub(crate) fn loaded_pers_struct(&self, name: &str) -> Option<Arc<PersStruct>> {
        self.cache_lookup_entry(name).and_then(|(_, loaded)| loaded)
    }

    fn cache_contains_key(&self, name: &str) -> bool {
        let cache = self.cache.lock().unwrap();
        resolve_first_char_case_key(&cache, name).is_some()
    }

    /// Make `unit` the loaded unit of its name, as a build's registry does.
    #[cfg(test)]
    pub(crate) fn insert_loaded_unit(&self, unit: Arc<PersStruct>) {
        self.cache_insert(unit.ps_name.clone(), Some(unit));
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
        if let Some(key) = resolve_first_char_case_key(&self.view.overrides.in_memory_module_overrides, name)
        {
            if self.view.overrides.hidden_modules.contains(key) {
                return None;
            }
            return self.view.overrides.in_memory_module_overrides.get(key).cloned();
        }
        let (key, info) = self.in_memory_modules.get_case_cloned(name)?;
        if self.view.overrides.hidden_modules.contains(&key) {
            return None;
        }
        Some(info)
    }

    fn in_memory_info_with<R>(
        &self,
        name: &str,
        mut f: impl FnMut(&InMemoryModuleInfo) -> R,
    ) -> Option<R> {
        if let Some(key) = resolve_first_char_case_key(&self.view.overrides.in_memory_module_overrides, name)
        {
            if self.view.overrides.hidden_modules.contains(key) {
                return None;
            }
            return self.view.overrides.in_memory_module_overrides.get(key).map(&mut f);
        }
        self.in_memory_modules
            .get_case_with(name, |key, info| {
                if self.view.overrides.hidden_modules.contains(key) {
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
        if let Some(key) = resolve_first_char_case_key(&self.view.overrides.portable_cache_overrides, name) {
            return self
                .view
                .overrides.portable_cache_overrides
                .get(key)
                .cloned()
                .map(|portable| (key.to_string(), portable));
        }
        self.portable_cache.get_case_cloned(name)
    }

    fn source_fallback_path_entry(&self, name: &str) -> Option<(String, PathBuf)> {
        if let Some(key) =
            resolve_first_char_case_key(&self.view.overrides.source_fallback_path_overrides, name)
        {
            return self
                .view
                .overrides.source_fallback_path_overrides
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
        publication: portable_types::SignaturePublicationMode,
    ) -> Option<Arc<PortablePersStruct>> {
        self.cache_lookup(module_name)
            .and_then(|opt| opt)
            .map(|ps| {
                portable_types::publish_signature(ps.as_ref(), ctx, arena, publication, false).0
            })
    }

    /// [`Self::extract_module_update`] in signature check mode: the
    /// publication and its comparison with the frozen shared graph
    /// (`portable_types::publish_pers_struct_checked`).
    pub fn extract_module_update_checked(
        &self,
        module_name: &str,
        ctx: &TypeContext,
        arena: Option<&crate::parse_arena::ParseArena>,
        publication: portable_types::SignaturePublicationMode,
    ) -> Option<(Arc<PortablePersStruct>, super::signature_check::Comparison)> {
        self.cache_lookup(module_name)
            .and_then(|opt| opt)
            .map(|ps| {
                let (pps, comparison) = portable_types::publish_signature(
                    ps.as_ref(), ctx, arena, publication, true,
                );
                (pps, comparison.expect("checked publication"))
            })
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

    /// Set the load path, with the spelling of each entry that diagnostics
    /// show (`display_paths`, parallel to `paths`).
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
        !self.view.overrides.hidden_modules.contains(name) && !self.outside_load_path(name)
    }

    fn outside_load_path(&self, name: &str) -> bool {
        let Some(visible) = self.visible_package_roots.as_deref() else {
            return false;
        };
        if let Some(key) = Name::lookup(name)
            && let Some(&outside) = self.outside_load_path_memo.0.borrow().get(&key)
        {
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
            .insert(Name::new(name), outside);
        outside
    }

    /// Set the modules opened implicitly by `-open` flags.
    pub fn set_open_modules(&mut self, open_modules: Vec<String>) {
        self.open_modules = Arc::new(open_modules);
    }

    /// Set the JSX module from CLI flags.
    pub fn set_jsx_module(&mut self, jsx_module: Option<String>) {
        self.jsx_module = jsx_module;
    }

    /// Set the default JSX version from CLI flags.
    pub fn set_jsx_version(&mut self, jsx_version: Option<i32>) {
        self.jsx_version = jsx_version;
    }

    /// Set whether the compilation uses `-enable-experimental LetUnwrap`.
    pub fn set_experimental_let_unwrap(&mut self, experimental_let_unwrap: bool) {
        self.experimental_let_unwrap = experimental_let_unwrap;
    }

    /// Set whether the compilation uses `-nopervasives`.
    pub fn set_nopervasives(&mut self, nopervasives: bool) {
        self.nopervasives = nopervasives;
    }

    /// The name of the unit being compiled, if set.
    pub fn compiling_module_name(&self) -> Option<&str> {
        self.view.compiling_module.as_deref()
    }

    /// Set the name of the unit being compiled.
    pub fn set_compiling_module(&mut self, module_name: Option<String>) {
        self.view_mut().compiling_module = module_name;
    }

    /// Whether `module_name` is the unit being compiled.
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

    /// The qualified path a flattened unit name is an alias of, if any.
    pub fn qualified_alias_path_for_flattened_head(&self, flat_head: &str) -> Option<Path> {
        self.view.alias_prefix_rewrites.get(flat_head)
    }

    /// Whether unit `name` can be found, without loading its signature.
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
                if self.view.overrides.hidden_modules.contains(&portable_key) {
                    return false;
                }
                let ps = portable_types::internalize_pers_struct(portable, ctx);
                let cache_key = smol_str::SmolStr::new(&portable_key);
                self.cache_insert(portable_key, Some(ps.clone()));
                (cache_key, ps)
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
                && !self.view.overrides.hidden_modules.contains(cache_key.as_str())
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
            if self.view.overrides.hidden_modules.contains(&portable_key) {
                return None;
            }
            ctx.poison_store_build_for("find_pers_struct:load");
            let ps = portable_types::internalize_pers_struct(portable, ctx);
            self.record_alias_rewrites(&portable_key, &ps);
            if should_register_lazy_raw_sig(&portable_key, &self.view.alias_prefix_rewrites)
                && !ctx.has_raw_module_sig(&portable_key)
            {
                ctx.register_raw_module_sig(&portable_key, ps.ps_sig.clone());
            }
            self.view_mut()
                .prepared_cached_alias_rewrites
                .insert(Name::new(&portable_key));
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
                .insert(Name::new(&load_name));
            if should_register_lazy_raw_sig(&load_name, &self.view.alias_prefix_rewrites)
                && !ctx.has_raw_module_sig(&load_name)
            {
                ctx.register_raw_module_sig(&load_name, ps.ps_sig.clone());
            }
        }
        self.cache_insert(load_name, result.clone());
        result
    }

    /// Record the alias rewrites of the signature of `ps`, loaded as `key`.
    fn record_alias_rewrites(&mut self, key: &str, ps: &PersStruct) {
        match self.view.alias_prefix_rewrites.get(key) {
            // Reached under its own name: the rewrites are those of the
            // unit's own table, which is not walked again.
            None if ps.ps_name == key => {
                if let Some(unit) = ps.own_alias_rewrites() {
                    self.view_mut().alias_prefix_rewrites.add_unit(unit);
                }
            }
            effective_module_path => {
                let module_path = effective_module_path
                    .unwrap_or_else(|| Path::pident(Ident::create_persistent(key)));
                collect_alias_rewrites(
                    &ps.ps_sig,
                    &module_path,
                    &mut self.view_mut().alias_prefix_rewrites,
                );
            }
        }
    }

    fn prepare_cached_pers_struct(&mut self, cache_key: &str, ps: &PersStruct, ctx: &TypeContext) {
        if !Name::lookup(cache_key)
            .is_some_and(|key| self.view.prepared_cached_alias_rewrites.contains(&key))
        {
            ctx.poison_store_build_for("find_pers_struct:prepare");
            self.view_mut()
                .prepared_cached_alias_rewrites
                .insert(Name::new(cache_key));
            self.record_alias_rewrites(cache_key, ps);
        }

        if should_register_lazy_raw_sig(cache_key, &self.view.alias_prefix_rewrites)
            && !ctx.has_raw_module_sig(cache_key)
        {
            ctx.register_raw_module_sig(cache_key, ps.ps_sig.clone());
        }
    }

    /// The persistent structure of unit `name` loaded from a file: its
    /// signature with paths qualified by the unit, its aliases recorded.
    fn finalize_loaded_signature(
        &mut self,
        name: &str,
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
        qualify_unit_sig_decl_paths_in_place(&mut signature, &module_path, ctx);

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
            .unwrap_or(module_path);
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
            ps_name: name.to_string(),
            ps_sig: signature,
            ps_filename,
            ps_deprecated,
            ps_crcs,
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        }
    }

    /// The source path in the header of the binary AST at `ast_path`, read
    /// with `Binary_ast.read_header` (compiler/depends/binary_ast.ml).
    fn read_ast_source_path(ast_path: &FsPath) -> Option<PathBuf> {
        let content = fs::read(ast_path).ok()?;
        let header = crate::binary_ast::header::read_header(&content)?;
        let path_bytes = crate::binary_ast::header::header_source(&content, &header);
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
    pub fn module_js_package_info(&self, name: &str) -> Option<JsPackageInfo> {
        self.in_memory_info_with(name, |info| {
            Some((
                info.package_name.clone()?,
                info.package_root.clone()?,
                info.js_output_suffix.clone(),
            ))
        })?
    }

    /// Return package metadata recorded in a dependency `.cmj`, matching
    /// `Lam_compile_env.get_package_info_from_cmj`.
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
                package_spec: CmjPackageSpec {
                    name: CmjPackageName::Empty,
                    module_systems: Vec::new(),
                },
                file_case: CmjFileCase::Upper,
            });
        }

        let path = self.resolve_module_cmj_path(name)?;
        let metadata = decode_cmj_module_metadata(&self.cmj_value(&path)?)?;
        Some(CmjModuleImportInfo {
            package_spec: metadata.package_spec,
            file_case: metadata.file_case,
        })
    }

    /// Whether JS metadata is registered for module `name`.
    pub fn module_has_in_memory_info(&self, name: &str) -> bool {
        self.in_memory_info_with(name, |_| ()).is_some()
    }

    /// `Config_util.find_opt`: the load-path file, trying the name as written
    /// before its uncapitalized form.
    pub fn find_in_load_path_uncap(&self, filename: &str) -> Option<String> {
        self.find_in_path_uncap(filename)
    }

    /// Whether [`Self::find_in_load_path_uncap`] finds `filename`.
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
        let fallback_pers = PersistentEnv {
            cache: Arc::new(Mutex::new(placeholders)),
            load_path: self.load_path.clone(),
            load_path_display: self.load_path_display.clone(),
            open_modules: self.open_modules.clone(),
            jsx_version: self.jsx_version,
            jsx_module: self.jsx_module.clone(),
            experimental_let_unwrap: self.experimental_let_unwrap,
            nopervasives: self.nopervasives,
            renamed_sig_cache: Arc::new(HashMap::new()),
            in_memory_modules: self.in_memory_modules.clone(),
            in_process_mode: self.in_process_mode,
            disk_modules: self.disk_modules.clone(),
            source_fallback_paths: self.source_fallback_paths.clone(),
            source_fallback_is_runtime: self.source_fallback_is_runtime,
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
                overrides: self.view.overrides.clone(),
                prepared_cached_alias_rewrites: HashSet::new(),
            }),
        };
        let open_modules = fallback_pers.open_modules.clone();
        let nopervasives = fallback_pers.nopervasives;
        let compiling_module = fallback_pers.view.compiling_module.clone();

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
            let let_unwrap = self.experimental_let_unwrap
                || crate::driver::extract_file_config_from_signature(&signature, parser.arena())
                    .let_unwrap;
            let signature = crate::binary_ast::ppx::rewrite_signature(
                &signature,
                parser.arena_mut(),
                let_unwrap,
            )
            .ok()?;
            // The dependency's own compile raises on an invalid escape here
            // (typemod.ml:1825, js_implementation.ml:59): like a type error
            // below, it leaves nothing to load.
            let deprecated =
                crate::types::typemod::deprecated_of_sig(parser.arena(), &signature).ok()?;

            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let mut tctx = TypeCheckContext::new(ctx, parser.arena());
            tctx.set_persistent_env(fallback_pers);
            // Like a type error below, an `-open` that is not found leaves
            // nothing to load.
            let env = initial_type_env(
                &mut tctx,
                &open_modules,
                nopervasives,
                compiling_module.as_deref(),
            )
            .ok()?;
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
            experimental_let_unwrap: self.experimental_let_unwrap,
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
        let structure = crate::binary_ast::ppx::rewrite_structure(
            &structure,
            parser.arena_mut(),
            experimental_let_unwrap,
        )
        .ok()?;
        // The dependency's own compile raises on an invalid escape here
            // (typemod.ml:1825, js_implementation.ml:59): like a type error
            // below, it leaves nothing to load.
            let deprecated =
                crate::types::typemod::deprecated_of_str(parser.arena(), &structure).ok()?;

        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let mut tctx = TypeCheckContext::new(ctx, parser.arena());
        tctx.experimental_let_unwrap = experimental_let_unwrap;
        tctx.set_persistent_env(fallback_pers);
        let env = initial_type_env(
            &mut tctx,
            &open_modules,
            nopervasives,
            compiling_module.as_deref(),
        )
        .ok()?;
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
            .extend_missing(fallback_pers.view.alias_prefix_rewrites.recorded());
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
            .extend_missing(fallback_pers.view.alias_prefix_rewrites.recorded());
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
        // config_util.ml `find_in_path_uncap`: try the name as written before
        // its uncapitalized form. On a case-insensitive file system both
        // match, and the result is shown in error messages and used in
        // generated import paths.
        for (index, dir) in self.load_path.iter().enumerate() {
            let display_dir = self.load_path_display.get(index).unwrap_or(dir);
            let exact = dir.join(filename);
            if exact.exists() {
                return Some((
                    exact.to_string_lossy().into_owned(),
                    display_dir.join(filename).to_string_lossy().into_owned(),
                ));
            }

            if let Some(uncap) = &uncap {
                let uncap_path = dir.join(uncap);
                if uncap_path.exists() {
                    return Some((
                        uncap_path.to_string_lossy().into_owned(),
                        display_dir.join(uncap).to_string_lossy().into_owned(),
                    ));
                }
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

    /// [`Self::get_renamed_sig_shared`], copied.
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

    /// Open the persistent unit `name` under `root`, the path of the open
    /// (env.ml `open_signature`: the `Pdot (root, name, pos)` of opened
    /// names share it).
    pub fn open_module(
        &mut self,
        name: &str,
        root: Path,
        env: &mut Env,
        ctx: &TypeContext,
        slot: Option<u32>,
    ) -> bool {
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
        if ctx
            .with_qualified_module_components(&components_key, |components| {
                open_components_into_env(components, root, env, ctx, slot)
            })
            .is_some()
        {
            return true;
        }
        // The view of a unit the world owns is the same for every
        // compilation (OCaml builds `ps_comps` once per process): it is
        // built once per build and adopted here.
        if self.in_process_mode
            && let Some(view) =
                crate::types::typecore::adopt_unit_view(&ps, components_key.clone(), ctx)
        {
            open_components_into_env(
                crate::types::env_lazy::Components::World(&view),
                root,
                env,
                ctx,
                slot,
            );
            return true;
        }
        // OCaml compiler/ml/env.ml:1513-1519 builds the component
        // table after `scrape_alias`, and env.ml:1581-1585 stores the
        // substituted modtypes in that table. When ReScript's
        // persistent registry knows this opened unit is the flattened
        // backing head for a selected alias path, share the same
        // component modtype force with that alias path.
        let components = Rc::new(
            crate::types::env_lazy::QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix(
                module_path,
                ps.ps_sig.clone(),
                crate::fast_hash::AHashMap::new(),
                alias_source,
                ctx,
            ),
        );
        ctx.register_qualified_module_components_shared(components_key, components.clone());
        open_components_into_env(
            crate::types::env_lazy::Components::Local(&components),
            root,
            env,
            ctx,
            slot,
        );
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
        self.unhide_module(name);
        self.overrides_mut()
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
            signature,
            source_filename.to_string(),
            deprecated,
            crcs,
            ctx,
        );
        self.unhide_module(name);
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
        self.overrides_mut().hidden_modules.insert(name.to_string());
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
                        Arc::new(Path::pident(Ident::create_persistent(
                            internal_name.as_str(),
                        ))),
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
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        };
        self.unhide_module(namespace_name);
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

    /// Keep an opened module's raw signature registered for ps_comps-style
    /// descriptor lookup (disk mode only).
    pub fn register_opened_raw_sig(&mut self, ctx: &TypeContext, name: &str) {
        if self.in_process_mode {
            return;
        }
        if let Some(md) = self.get_module_declaration(name, ctx)
            && let crate::types::decl::ModuleType::MtySignature(ref sig) = md.md_type
        {
            ctx.register_raw_module_sig(name, sig.clone());
        }
    }

    /// Whether module `name` belongs to `@rescript/runtime` (in-memory
    /// metadata, or a source-only runtime: see
    /// `ModuleRegistry::set_source_fallback_is_runtime`).
    pub fn module_is_runtime(&self, name: &str) -> bool {
        self.in_memory_info_with(name, |info| info.is_runtime)
            .unwrap_or_else(|| {
                self.source_fallback_is_runtime && self.source_fallback_path_entry(name).is_some()
            })
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
        let load_path = tmp.path().join("lib").join("rescript");
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
        env.overrides_mut()
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
        package_spec: decode_cmj_package_spec(value)?,
        file_case: decode_cmj_file_case(value)?,
    })
}

fn decode_cmj_pure(value: &OcamlValue) -> Option<bool> {
    // js_cmj_format.ml `t = {values; pure; package_spec; case}`.
    let (_, fields) = value.as_block_opt()?;
    fields.get(1).map(|field| field.as_bool())
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
            OcamlValue::String(name) => name.to_string(),
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
            OcamlValue::String(name) => name.to_string(),
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
            OcamlValue::String(name) => name.to_string(),
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
    let package_field = fields.get(2)?;
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
    match fields.get(3)?.as_int() {
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
    if fields.len() < 3 {
        return None;
    }
    Some(Apply {
        ap_func: Box::new(decode_cmj_lambda(&fields[0])?),
        ap_args: decode_cmj_list(&fields[1], decode_cmj_lambda)?,
        ap_info: decode_cmj_ap_info(&fields[2])?,
    })
}

fn decode_cmj_ap_info(value: &OcamlValue) -> Option<ApInfo> {
    // `Lambda.lambda_apply.ap_loc` (a `Location.t`); the location itself
    // is not needed for inlining.
    value.as_block_opt()?;
    Some(ApInfo {
        loc: crate::lambda::LamLoc::NONE,
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
        name: crate::name::Name::new(fields[0].as_string()),
        literal: decode_cmj_variant_literal_tag(&fields[1])?,
    })
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
        // `Blk_record {fields; mutable_flag; array}`.
        OcamlValue::Block(2, fields) if fields.len() == 3 => Some(TagInfo::Record(Box::new(
            crate::lambda::lam_tag_info::RecordTag {
                fields: record_fields(&fields[0])?,
                logical_field_count: None,
                mutable_flag: mutable_flag(&fields[1])?,
                array: fields[2].as_bool(),
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
        OcamlValue::Int(74) => Some(Primitive::Pmakelist),
        OcamlValue::Int(75) => Some(Primitive::Pmakedict),
        OcamlValue::Int(76) => Some(Primitive::PdictHas),
        OcamlValue::Int(77) => Some(Primitive::Pawait),
        OcamlValue::Int(78) => Some(Primitive::PinitMod),
        OcamlValue::Int(79) => Some(Primitive::PupdateMod),
        OcamlValue::Int(80) => Some(Primitive::Phash),
        OcamlValue::Int(81) => Some(Primitive::PhashMixint),
        OcamlValue::Int(82) => Some(Primitive::PhashMixstring),
        OcamlValue::Int(83) => Some(Primitive::PhashFinalmix),
        OcamlValue::Int(84) => Some(Primitive::PisNullUndefined),
        OcamlValue::Int(85) => Some(Primitive::PnullToOpt),
        OcamlValue::Int(86) => Some(Primitive::PnullUndefinedToOpt),
        OcamlValue::Int(87) => Some(Primitive::PisNull),
        OcamlValue::Int(88) => Some(Primitive::PisUndefined),
        OcamlValue::Int(89) => Some(Primitive::PisNotNone),
        OcamlValue::Int(90) => Some(Primitive::PvalFromOption),
        OcamlValue::Int(91) => Some(Primitive::PvalFromOptionNotNest),
        OcamlValue::Int(92) => Some(Primitive::PisPolyVarBlock),
        OcamlValue::Int(93) => Some(Primitive::PjsFnMethod),
        OcamlValue::Int(94) => Some(Primitive::PdictSpread),
        OcamlValue::Int(95) => Some(Primitive::ParraySpread),
        OcamlValue::Int(96) => Some(Primitive::PlistSpread),
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
        OcamlValue::Block(4, fields) if fields.len() == 3 => Some(Primitive::PjsCall(Box::new(
            crate::lambda::lam_primitive::JsCall {
                prim_name: fields[0].as_string().to_string(),
                arg_types: crate::cmi::ffi_decode::params(&fields[1])?,
                ffi: crate::cmi::ffi_decode::external_decl(&fields[2])?,
            },
        ))),
        // `Pjsx of jsx_element`
        OcamlValue::Block(5, fields) if fields.len() == 1 => {
            let (_, jsx) = fields[0].as_block_opt()?;
            if jsx.len() != 8 {
                return None;
            }
            Some(Primitive::Pjsx(Box::new(
                crate::lambda::lam_primitive::JsxElement {
                    jsx_name: jsx[0].as_string().to_string(),
                    jsx_ffi: crate::cmi::ffi_decode::external_decl(&jsx[1])?,
                    jsx_multi: jsx[2].as_bool(),
                    jsx_fragment: jsx[3].as_bool(),
                    jsx_spread: jsx[4].as_bool(),
                    jsx_props: decode_cmj_list(&jsx[5], |prop| {
                        let (_, pair) = prop.as_block_opt()?;
                        match pair {
                            [name, optional] => {
                                Some((name.as_string().to_string(), optional.as_bool()))
                            }
                            _ => None,
                        }
                    })?,
                    jsx_children: jsx[6].as_option().map(|n| n.as_int() as usize),
                    jsx_key: jsx[7].as_bool(),
                },
            )))
        }
        OcamlValue::Block(9, fields) if fields.len() == 1 => {
            Some(Primitive::Pobjcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(10, fields) if fields.len() == 1 => {
            Some(Primitive::Pboolcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(11, fields) if fields.len() == 1 => {
            Some(Primitive::Pintcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(12, fields) if fields.len() == 1 => {
            Some(Primitive::Pfloatcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(13, fields) if fields.len() == 1 => {
            Some(Primitive::Pbigintcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(14, fields) if fields.len() == 1 => {
            Some(Primitive::Pstringcomp(decode_cmj_comparison(&fields[0])?))
        }
        OcamlValue::Block(19, fields) if fields.len() == 1 => Some(Primitive::PtaggedTemplate(
            decode_cmj_string_list(&fields[0])?,
        )),
        OcamlValue::Block(20, fields) if fields.len() == 1 => Some(Primitive::Ptemplate(
            decode_cmj_list(&fields[0], decode_cmj_template_segment)?,
        )),
        OcamlValue::Block(17, fields) if fields.len() == 1 => {
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
            name: Name::new(fields[0].as_string()),
        }),
        OcamlValue::Block(1, fields) if fields.len() == 1 => Some(FieldDbgInfo::Module {
            name: Name::new(fields[0].as_string()),
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
///
/// OCaml's `Subst.modules` is a `Path_map` (subst.ml:29-34): `add_module`
/// keys an identifier, `add_module_path` any path, and `module_path` looks the
/// whole path up before substituting its prefix (subst.ml:69-76). Identifier
/// keys live in `stamps`, other paths in `paths`.
#[derive(Clone, Debug)]
struct ModuleStampSubstMap {
    stamps: HashMap<i32, (Name, Arc<Path>)>,
    paths: HashMap<crate::types::context::SamePathKey, Arc<Path>>,
}

impl Default for ModuleStampSubstMap {
    fn default() -> Self {
        Self {
            stamps: subst_map(),
            paths: subst_map(),
        }
    }
}

impl ModuleStampSubstMap {
    fn new() -> Self {
        Self::default()
    }

    fn get(&self, stamp: &i32) -> Option<&(Name, Arc<Path>)> {
        self.stamps.get(stamp)
    }

    fn is_empty(&self) -> bool {
        self.stamps.is_empty() && self.paths.is_empty()
    }

    fn extend(&mut self, other: ModuleStampSubstMap) {
        self.stamps.extend(other.stamps);
        self.paths.extend(other.paths);
    }

    /// The target of a non-identifier key `path` (`Path_map.find`,
    /// subst.ml:70).
    fn path_target(&self, path: &Path) -> Option<&Arc<Path>> {
        if self.paths.is_empty() || matches!(path.view(), PathView::Pident(_)) {
            return None;
        }
        self.paths
            .get(&crate::types::context::SamePathKey::new(*path))
    }
}

fn insert_module_stamp_subst(map: &mut ModuleStampSubstMap, id: &Ident, path: Path) {
    map.stamps
        .insert(id.stamp(), (id.name_atom(), Arc::new(path)));
}

fn nonpersistent_path_head(path: &Path) -> Option<(i32, Name)> {
    match path.view() {
        PathView::Pident(id) => (id.stamp() != 0).then(|| (id.stamp(), id.name_atom())),
        PathView::Pdot(prefix, _, _) => nonpersistent_path_head(prefix),
        PathView::Papply(left, right) => {
            nonpersistent_path_head(left).or_else(|| nonpersistent_path_head(right))
        }
    }
}

/// The type-path domain of a component substitution. In-process signatures
/// retain qualified declaration paths as well as their original binders.
/// Both denote the same explicit substitution entry, not equivalent spellings.
/// OCaml `Subst.type_path` checks its Path_map before descending (subst.ml:87-94).
#[derive(Clone, Debug)]
struct TypeSubstPaths {
    stamps: HashMap<i32, Path>,
    qualified: HashMap<crate::types::context::SamePathKey, Path>,
    /// `Type_function {params; body}` replacements (subst.ml:23-25, 47-48):
    /// a constructor with this path becomes `Ctype.apply Env.empty params
    /// body args` (subst.ml:165-172).
    functions: HashMap<crate::types::context::SamePathKey, (Vec<TypeExprRef>, TypeExprRef)>,
}

impl Default for TypeSubstPaths {
    fn default() -> Self {
        Self {
            stamps: subst_map(),
            qualified: subst_map(),
            functions: subst_map(),
        }
    }
}

impl TypeSubstPaths {
    fn is_empty(&self) -> bool {
        self.stamps.is_empty() && self.qualified.is_empty() && self.functions.is_empty()
    }

    /// The type function `path` is substituted by, if any.
    fn function(&self, path: &Path) -> Option<&(Vec<TypeExprRef>, TypeExprRef)> {
        if self.functions.is_empty() {
            return None;
        }
        self.functions
            .get(&crate::types::context::SamePathKey::new(*path))
    }
}

#[derive(Clone, Debug)]
struct SubstMaps {
    type_stamp_map: TypeSubstPaths,
    type_name_map: HashMap<Name, Path>,
    module_stamp_map: ModuleStampSubstMap,
    module_name_map: HashMap<Name, Arc<Path>>,
    protected_module_head: Option<(i32, Name)>,
}

/// Fixed hasher keys: `AHashMap::default()` derives fresh random keys per
/// map, and substitution maps are built for every qualified signature.
///
/// The first seed must not equal the first word of ahash's second constant
/// table: `with_seeds` combines its arguments with that table by exclusive
/// or, a first key of zero results, and integer keys (on every target) and
/// all keys of ahash's fallback hasher then hash to 0 (one bucket, quadratic
/// inserts). `subst_map_hashes_are_distinct` checks it.
static SUBST_MAP_STATE: ahash::RandomState = ahash::RandomState::with_seeds(
    0x9e37_79b9_7f4a_7c15,
    0xf39c_c060_5ced_c834,
    0x1082_276b_f3a2_7251,
    0xf86c_6a11_d0c1_8e95,
);

fn subst_map<K, V>() -> HashMap<K, V> {
    std::collections::HashMap::with_hasher(SUBST_MAP_STATE.clone()).into()
}

impl Default for SubstMaps {
    fn default() -> Self {
        Self {
            type_stamp_map: TypeSubstPaths::default(),
            type_name_map: subst_map(),
            module_stamp_map: ModuleStampSubstMap::default(),
            module_name_map: subst_map(),
            protected_module_head: None,
        }
    }
}

/// The substitution maps a type-path walk reads, borrowed: those of a
/// [`SubstMaps`], or ones with a type-name map of the caller's own.
#[derive(Clone, Copy)]
struct SubstPaths<'a> {
    type_stamp_map: &'a TypeSubstPaths,
    type_name_map: &'a HashMap<Name, Path>,
    module_stamp_map: &'a ModuleStampSubstMap,
    module_name_map: &'a HashMap<Name, Arc<Path>>,
    protected_module_head: Option<&'a (i32, Name)>,
}

impl SubstMaps {
    fn paths(&self) -> SubstPaths<'_> {
        SubstPaths {
            type_stamp_map: &self.type_stamp_map,
            type_name_map: &self.type_name_map,
            module_stamp_map: &self.module_stamp_map,
            module_name_map: &self.module_name_map,
            protected_module_head: self.protected_module_head.as_ref(),
        }
    }

    fn is_empty(&self) -> bool {
        self.type_stamp_map.is_empty()
            && self.type_name_map.is_empty()
            && self.module_stamp_map.is_empty()
            && self.module_name_map.is_empty()
    }
}

#[cfg(test)]
thread_local! {
    /// Component substitutions built on this thread (one pass over a
    /// signature each).
    pub(crate) static SUBST_MAP_BUILDS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Walks of one type that rewrite one path prefix
    /// (`rewrite_type_expr_by_path_prefix`).
    pub(crate) static TYPE_PREFIX_WALKS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Signature items those builds visited.
    pub(crate) static SUBST_MAP_ITEMS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn build_subst_maps(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) -> SubstMaps {
    #[cfg(test)]
    {
        SUBST_MAP_BUILDS.with(|builds| builds.set(builds.get() + 1));
        SUBST_MAP_ITEMS.with(|items| items.set(items.get() + sig_items.len() as u64));
    }
    let mut maps = SubstMaps {
        protected_module_head: nonpersistent_path_head(module_path),
        ..SubstMaps::default()
    };

    let prefix = Arc::new(*module_path);
    for item in sig_items {
        match item {
            SignatureItem::SigType(id, _, _) | SignatureItem::SigModtype(id, _) => {
                let qualified_path =
                    ctx.dotted_from_ident(prefix.clone(), *id, crate::types::path::NOPOS);
                if let SignatureItem::SigType(_, decl, _) = item
                    && let Some(source) = &decl.type_path
                    && matches!(source.view(), PathView::Pdot(..))
                {
                    maps.type_stamp_map.qualified.insert(
                        crate::types::context::SamePathKey::new(*source),
                        qualified_path,
                    );
                }
                if id.stamp() != 0 {
                    // OCaml Subst uses identifier identity for non-persistent ids.
                    maps.type_stamp_map.stamps.insert(id.stamp(), qualified_path);
                } else {
                    // Persistent ids (stamp=0) rewrite by name.
                    maps.type_name_map
                        .insert(id.name_atom(), qualified_path);
                }
            }
            SignatureItem::SigModule(id, _, _) => {
                let qualified_path =
                    ctx.dotted_from_ident(prefix.clone(), *id, crate::types::path::NOPOS);
                if id.stamp() != 0 {
                    // OCaml Subst uses identifier identity for non-persistent ids.
                    insert_module_stamp_subst(&mut maps.module_stamp_map, id, qualified_path);
                } else {
                    // Persistent ids (stamp=0) rewrite by name.
                    maps.module_name_map
                        .insert(id.name_atom(), Arc::new(qualified_path));
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
        maps.type_stamp_map.stamps.insert(old_id.stamp(), new_path);
    } else {
        maps.type_name_map
            .insert(old_id.name_atom(), new_path);
    }
}

fn insert_module_subst_path(maps: &mut SubstMaps, old_id: &Ident, new_id: &Ident) {
    let new_path = Path::pident(*new_id);
    if old_id.stamp() != 0 {
        insert_module_stamp_subst(&mut maps.module_stamp_map, old_id, new_path);
    } else {
        maps.module_name_map
            .insert(old_id.name_atom(), Arc::new(new_path));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alias_targets_keep_their_block_or_take_the_stored_substitution_target() {
        use crate::types::decl::AliasPresence;
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let kept = ctx.create_ident("Kept");
        let renamed = ctx.create_ident("Renamed");
        let mut maps = SubstMaps::default();
        insert_module_stamp_subst(
            &mut maps.module_stamp_map,
            &renamed,
            Path::pident(ctx.create_ident("Fresh")),
        );
        let stored = maps
            .module_stamp_map
            .get(&renamed.stamp())
            .unwrap()
            .1
            .clone();
        let alias =
            |target: &Arc<Path>| ModuleType::MtyAlias(AliasPresence::MtaPresent, target.clone());
        let target_of = |mty: &ModuleType| match mty {
            ModuleType::MtyAlias(_, target) => target.clone(),
            _ => panic!("alias"),
        };
        // subst.ml:69-75: an unreplaced `Pident` target is the block itself.
        let kept_target = Arc::new(Path::pident(kept));
        let mut a = alias(&kept_target);
        substitute_module_type_paths_with_maps(&ctx, &mut a, &maps);
        assert!(Arc::ptr_eq(&target_of(&a), &kept_target));
        // A replaced target is the substitution's one stored target block,
        // shared by separately allocated equal sources.
        let (first, second) = (
            Arc::new(Path::pident(renamed)),
            Arc::new(Path::pident(renamed)),
        );
        let (mut b, mut c) = (alias(&first), alias(&second));
        substitute_module_type_paths_with_maps(&ctx, &mut b, &maps);
        substitute_module_type_paths_with_maps(&ctx, &mut c, &maps);
        assert!(Arc::ptr_eq(&target_of(&b), &stored));
        assert!(Arc::ptr_eq(&target_of(&c), &stored));
        // The lookup copy shares the target block.
        let copied = crate::types::typecore::copy_alias_target(&kept_target);
        assert!(Arc::ptr_eq(&copied, &kept_target));
    }

    #[test]
    fn signature_prefix_rewrites_share_targets_across_types_and_declarations() {
        for by_name in [false, true] {
            for shallow in [false, true] {
                let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
                let root = Arc::new(Path::pident(ctx.create_ident("Source")));
                let name = ctx.create_ident("t");
                let source = ctx.dotted_from_ident(root.clone(), name, 7);
                let target = Arc::new(Path::pident(ctx.create_ident("Target")));
                let ty = ctx.new_generic_constr(source, vec![]);
                let mut sig = vec![
                    SignatureItem::SigValue(
                        ctx.create_ident("value"),
                        crate::types::decl::ValueDescription {
                            val_type: ty,
                            val_kind: crate::types::decl::ValueKind::ValReg,
                            val_loc: Default::default(),
                            val_attributes: Default::default(),
                            val_path: Some(source),
                        },
                    ),
                    SignatureItem::SigModule(
                        ctx.create_ident("Child"),
                        crate::types::decl::ModuleDeclaration {
                            md_type: ModuleType::MtyAlias(
                                crate::types::decl::AliasPresence::MtaPresent,
                                Arc::new(source),
                            ),
                            md_loc: Default::default(),
                            md_attributes: vec![],
                            md_path: Some(source),
                        },
                        RecStatus::TrecNot,
                    ),
                ];
                match (by_name, shallow) {
                    (true, true) => {
                        rewrite_module_prefix_in_sig_shallow(&sig, "Source", &target, &ctx);
                        rewrite_module_prefix_paths_in_sig_shallow(
                            &mut sig, "Source", &target, &ctx,
                        );
                    }
                    (true, false) => {
                        rewrite_module_prefix_in_sig(&sig, "Source", &target, &ctx);
                        rewrite_module_prefix_paths_in_sig(&mut sig, "Source", &target, &ctx);
                    }
                    (false, true) => {
                        rewrite_sig_by_path_prefix(&sig, &root, &target, &ctx);
                        rewrite_sig_paths_by_path_prefix_shallow(&mut sig, &root, &target, &ctx);
                    }
                    (false, false) => {
                        rewrite_sig_by_path_prefix(&sig, &root, &target, &ctx);
                        rewrite_sig_paths_by_path_prefix(&mut sig, &root, &target, &ctx);
                    }
                }
                let desc = ctx.get_desc(ty);
                let TypeDesc::Tconstr { path, .. } = &*desc else {
                    panic!("constructor")
                };
                let expected = Path::pdot_pos(*target, name.name_atom(), 7);
                assert_eq!(*path, expected);
                let SignatureItem::SigValue(_, value) = &sig[0] else {
                    panic!("value")
                };
                assert_eq!(value.val_path, Some(expected));
                let SignatureItem::SigModule(_, child, _) = &sig[1] else {
                    panic!("child")
                };
                let ModuleType::MtyAlias(_, alias) = &child.md_type else {
                    panic!("alias")
                };
                for path in [alias, child.md_path.as_ref().unwrap()] {
                    assert_eq!(*path, if shallow { source } else { expected });
                }
                let unknown = Path::pdot(*root, "unknown");
                let copied =
                    rewrite_path_with_shared_prefix(&unknown, &root, &target, &ctx).unwrap();
                assert!(copied.same(&Path::pdot(*target, "unknown")));
            }
        }
    }

    #[test]
    fn scoped_rerooting_keeps_suffix_names_and_target_prefix_allocations() {
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let root = Arc::new(Path::pident(ctx.create_ident("Root")));
        let name = ctx.create_ident("t");
        let source = ctx.dotted_from_ident(root.clone(), name, 7);
        let target = Path::pident(ctx.create_ident("Target"));
        let pairs = vec![((*root), target)];
        let mapper = reroot_path_mapper(&pairs, &ctx);
        let a = mapper(&source);
        let b = mapper(&source);
        let expected = Path::pdot_pos(target, name.name_atom(), 7);
        assert_eq!(a, expected);
        assert_eq!(b, expected);
        assert_eq!(reroot_path_mapper(&pairs, &ctx)(&source), expected);
        let nested = ctx.dotted_from_ident(Arc::new(source), name, 9);
        let expected_nested = Path::pdot_pos(expected, name.name_atom(), 9);
        assert_eq!(mapper(&nested), expected_nested);
        let untouched =
            Path::pdot_pos(Path::pident(ctx.create_ident("Other")), name.name_atom(), 7);
        assert_eq!(mapper(&untouched), untouched);
        let other = Path::pident(ctx.create_ident("OtherSource"));
        let other_dot = Path::pdot_pos(other, name.name_atom(), 7);
        let pairs = vec![(*root, target), (other, target)];
        let mapper = reroot_path_mapper(&pairs, &ctx);
        assert_eq!(mapper(&source), mapper(&other_dot));

        // Both linear and indexed lookup choose the first matching pair,
        // rather than preferring the nearest matching ancestor.
        for count in [2, 6] {
            let mut pairs = vec![
                ((*root), target),
                (source, Path::pident(ctx.create_ident("Later"))),
            ];
            for _ in 2..count {
                pairs.push((Path::pident(ctx.create_ident("Unused")), target));
            }
            let prefixes = PathPrefixes::new(&pairs);
            assert_eq!(prefixes.matching_prefix(&nested), Some(0));
            assert!(prefixes.targets.get().is_none());
            let copied = rewrite_path_by_path_prefixes(&nested, &prefixes, &ctx).unwrap();
            assert_eq!(copied, expected_nested);
        }
    }

    #[test]
    fn dotted_substitution_keeps_suffix_names_and_module_prefix_allocations() {
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let root_id = ctx.create_ident("Root");
        let root = Arc::new(Path::pident(root_id));
        let name = ctx.create_ident("t");
        let source = ctx.dotted_from_ident(root.clone(), name, 7);
        let types = TypeSubstPaths::default();
        let type_names = HashMap::new();
        let mut modules = ModuleStampSubstMap::new();
        let module_names = HashMap::new();
        let copy = |modules: &ModuleStampSubstMap| {
            substitute_type_path(
                &ctx,
                &source,
                &types,
                &type_names,
                modules,
                &module_names,
                None,
            )
        };
        let a = copy(&modules);
        let b = copy(&modules);
        assert_eq!(a, source);
        assert_eq!(b, source);
        let target = ctx.create_ident("Other");
        insert_module_stamp_subst(&mut modules, &root_id, Path::pident(target));
        let expected = Path::pdot_pos(Path::pident(target), name.name_atom(), 7);
        assert_eq!(copy(&modules), expected);
        assert_eq!(copy(&modules), expected);
        let mut separate = ModuleStampSubstMap::new();
        insert_module_stamp_subst(&mut separate, &root_id, Path::pident(target));
        assert_eq!(copy(&separate), expected);
        // Nested dots are rebuilt, but their unchanged terminal prefix is retained.
        let nested = ctx.dotted_from_ident(Arc::new(source), name, 9);
        let copied = substitute_module_path(
            &ctx,
            &nested,
            &ModuleStampSubstMap::new(),
            &module_names,
            None,
        );
        assert_eq!(copied, nested);
    }

    #[test]
    fn renamed_substitution_targets_follow_identifier_identity() {
        use crate::types::typecore::copy_type_expr_mapping_paths;
        use crate::types::type_expr::{TypeExprRefMap};
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let old = ctx.create_ident("t");
        let new = ctx.rename_ident(&old);
        let mut maps = SubstMaps::default();
        insert_type_subst_path(&mut maps, &old, &new);
        let mapper = |path: &Path| {
            substitute_type_path(
                &ctx,
                path,
                &maps.type_stamp_map,
                &maps.type_name_map,
                &maps.module_stamp_map,
                &maps.module_name_map,
                None,
            )
        };
        let a = ctx.new_generic_constr(Path::pident(old), vec![]);
        let b = ctx.new_generic_constr(Path::pident(old), vec![]);
        let unrelated = ctx.create_ident("t");
        let c = ctx.new_generic_constr(Path::pident(unrelated), vec![]);
        let mut cache = TypeExprRefMap::new();
        for ty in [a, b, c] {
            let copied = copy_type_expr_mapping_paths(&ctx, ty, &mut cache, &mapper);
            let desc = ctx.get_desc(copied);
            let TypeDesc::Tconstr { path, .. } = &*desc else {
                panic!("constructor")
            };
            assert!(path.same(&Path::pident(if ty == c { unrelated } else { new })));
        }
    }

    #[test]
    fn component_substitution_keeps_values_and_distinct_bindings() {
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let root_id = Ident::create_local("Component");
        let root = Arc::new(Path::pident(root_id));
        let binder = Ident::create_local("t");
        let source = Path::pdot(*root, binder.name_atom());
        let target = ctx.dotted_from_ident(root, binder, crate::types::path::NOPOS);
        assert_eq!(source, target);
        assert_eq!(source, target);
        let mut types = TypeSubstPaths::default();
        types.qualified.insert(
            crate::types::context::SamePathKey::new(source),
            target,
        );
        let names = HashMap::new();
        let modules = ModuleStampSubstMap::new();
        let module_names = HashMap::new();
        let paths = SubstPaths {
            type_stamp_map: &types,
            type_name_map: &names,
            module_stamp_map: &modules,
            module_name_map: &module_names,
            protected_module_head: None,
        };
        let a = ctx.new_generic_constr(source, vec![]);
        let b = ctx.new_generic_constr(source, vec![]);
        for node in [a, b] {
            substitute_type_expr_path(node, paths, &ctx, &mut visit_set());
            let desc = ctx.get_desc(node);
            let TypeDesc::Tconstr { path, .. } = &*desc else {
                panic!("constructor")
            };
            assert_eq!(*path, target);
        }
        // An equal-spelled but different binding is not this substitution's key.
        let unrelated = Path::pdot(Path::pident(Ident::create_local("Component")), "t");
        let result = substitute_type_path(
            &ctx,
            &unrelated,
            &types,
            &names,
            &modules,
            &HashMap::new(),
            None,
        );
        assert_eq!(result, unrelated);
        assert!(!result.same(&target));
    }

    /// Outside in-process builds a module's source path comes from the
    /// header of its `.ast` on the load path, read like
    /// `Binary_ast.read_header`: an `.ast` whose source path lacks its
    /// newline, as when a killed build cut it short, names no source. A
    /// `.cmj` cut short, which `Ext_io.unmarshal` reads as `End_of_file`,
    /// has no exports. Files are removed one by one, and the directory only
    /// when empty.
    #[test]
    fn damaged_ast_headers_and_truncated_cmjs_resolve_to_nothing() {
        let dir = std::env::temp_dir().join(format!("pers-env-ast-header-{}", std::process::id()));
        std::fs::create_dir(&dir).expect("fresh test directory");
        let cmj = include_bytes!("../../tests/fixtures/Belt_MapString.cmj");
        let files: [(&str, &[u8]); 4] = [
            (
                "Whole.ast",
                b"\x00\x00\x00\x06\nBelt\n/src/Whole.res\n\x84\x95",
            ),
            ("Cut.ast", b"\x00\x00\x00\x06\nBelt\n/src/Cut.res"),
            ("Belt_MapString.cmj", &cmj[..cmj.len() - 1]),
            ("Header.cmj", &cmj[..16]),
        ];
        for (name, contents) in &files {
            std::fs::write(dir.join(name), contents).expect("write fixture");
        }
        let mut env = PersistentEnv::new();
        env.add_load_path(dir.clone());
        let whole = env.resolve_module_source_path("Whole");
        let cut = env.resolve_module_source_path("Cut");
        let truncated = env.module_cmj_export_constants("Belt_MapString").is_none();
        let header_only = env.module_cmj_export_constants("Header").is_none();
        for (name, _) in &files {
            std::fs::remove_file(dir.join(name)).expect("remove fixture");
        }
        std::fs::remove_dir(&dir).expect("remove empty test directory");
        assert_eq!(whole, Some(PathBuf::from("/src/Whole.res")));
        assert_eq!(cut, None);
        assert!(truncated, "a truncated .cmj has no exports");
        assert!(header_only, "a .cmj of only its digest has no exports");
    }

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
    merged
        .type_stamp_map
        .stamps
        .extend(child.type_stamp_map.stamps.clone());
    merged
        .type_stamp_map
        .qualified
        .extend(child.type_stamp_map.qualified.clone());
    merged
        .type_stamp_map
        .functions
        .extend(child.type_stamp_map.functions.clone());
    merged.type_name_map.extend(child.type_name_map.clone());
    merged
        .module_stamp_map
        .extend(child.module_stamp_map.clone());
    merged.module_name_map.extend(child.module_name_map.clone());
    if merged.protected_module_head.is_none() {
        merged.protected_module_head = child.protected_module_head;
    }
    merged
}

fn freshen_module_type_bound_idents_with_maps(
    module_type: &mut ModuleType,
    maps: &SubstMaps,
    ctx: &TypeContext,
) {
    let mut visited = visit_set();
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
    visited: &mut TypeVisitSet,
) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            if !maps.is_empty() {
                // OCaml compiler/ml/subst.ml:345-348 handles `Mty_ident`
                // through the modtype substitution table; Rust shares the
                // type/modtype id map here, with dotted prefixes still going
                // through `module_path` like compiler/ml/subst.ml:78-84.
                *path = substitute_type_path(
                    ctx,
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
                *path = substitute_shared_module_path(
                    ctx,
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
    visited: &mut TypeVisitSet,
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
    substitute_sig_decl_paths_in_place_with_maps_rec(
        ctx,
        sig_items,
        &combined_maps,
        false,
        AliasTargets::Substitute,
    );

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

fn freshen_nested_signature_module_types(sig_items: &mut [SignatureItem], ctx: &TypeContext) {
    let mut visited = visit_set();
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
        crate::perf_counters::record_signature_freshen(ctx, kind, sig_items.len());
    }
    let (new_idents, local_maps, has_nested_module_types) =
        freshened_signature_ident_plan(sig_items, ctx);
    let maps_empty = local_maps.is_empty();
    let rewrite_type_path = |path: &Path| {
        if maps_empty {
            *path
        } else {
            substitute_type_path(
                ctx,
                path,
                &local_maps.type_stamp_map,
                &local_maps.type_name_map,
                &local_maps.module_stamp_map,
                &local_maps.module_name_map,
                local_maps.protected_module_head.as_ref(),
            )
        }
    };
    // Alias targets: the stored substitution target, or an unreplaced
    // `Pident` block itself (subst.ml:69-75).
    let rewrite_module_path = |path: &Arc<Path>| {
        if maps_empty {
            crate::types::typecore::copy_alias_target(path)
        } else {
            substitute_shared_module_path(
                ctx,
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
            .insert(old_param.name_atom(), Arc::new(*arg_path));
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
                .insert(id.name_atom(), Arc::new(*path));
        }
    }
    freshen_module_type_bound_idents_with_maps(&mut copied, &maps, ctx);
    copied
}

/// A `Subst.type_replacement` (subst.ml:23-25).
pub(crate) enum TypeReplacement {
    Path(Path),
    Function {
        params: Vec<TypeExprRef>,
        body: TypeExprRef,
    },
}

/// OCaml `Subst.signature sub sg` for a substitution built from
/// `Subst.identity` with `add_type_path`/`add_type_function` and
/// `add_module_path` (subst.ml:44-51), as `merge_constraint` does for a
/// destructive substitution (typemod.ml:414-467). A key is any path: an
/// identifier, or a dotted path such as `A.O`, which `module_path` and
/// `type_path` look up before substituting its prefix (subst.ml:69-100).
/// The signature's bound identifiers are renamed as `Subst.signature` does.
pub(crate) fn substitute_signature_with_path_subst(
    sig_items: &[SignatureItem],
    types: &[(Path, TypeReplacement)],
    modules: &[(Path, Path)],
    ctx: &TypeContext,
) -> Signature {
    let mut maps = SubstMaps::default();
    for (key, replacement) in types {
        match replacement {
            TypeReplacement::Path(target) => match &key.view() {
                PathView::Pident(id) if id.stamp() != 0 => {
                    maps.type_stamp_map
                        .stamps
                        .insert(id.stamp(), *target);
                }
                PathView::Pident(id) => {
                    maps.type_name_map
                        .insert(id.name_atom(), *target);
                }
                _ => {
                    maps.type_stamp_map.qualified.insert(
                        crate::types::context::SamePathKey::new(*key),
                        *target,
                    );
                }
            },
            TypeReplacement::Function { params, body } => {
                maps.type_stamp_map.functions.insert(
                    crate::types::context::SamePathKey::new(*key),
                    (params.clone(), *body),
                );
            }
        }
    }
    for (key, target) in modules {
        match &key.view() {
            PathView::Pident(id) if id.stamp() != 0 => {
                insert_module_stamp_subst(&mut maps.module_stamp_map, id, *target);
            }
            PathView::Pident(id) => {
                maps.module_name_map
                    .insert(id.name_atom(), Arc::new(*target));
            }
            _ => {
                maps.module_stamp_map.paths.insert(
                    crate::types::context::SamePathKey::new(*key),
                    Arc::new(*target),
                );
            }
        }
    }
    let mut copied = crate::types::typecore::copy_lookup_module_type_for_subst(
        &ModuleType::MtySignature(Arc::new(sig_items.to_vec())),
        ctx,
    );
    freshen_module_type_bound_idents_with_maps(&mut copied, &maps, ctx);
    match copied {
        ModuleType::MtySignature(sig) => Arc::unwrap_or_clone(sig),
        _ => unreachable!("Subst.signature copies a signature"),
    }
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
        .map(|(parent_module_path, parent_sig)| {
            build_subst_maps(parent_sig, parent_module_path, ctx)
        })
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
        let maps = build_subst_maps(parent_sig, parent_module_path, ctx);
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
    //
    // An alias to a persistent module, such as each item of a namespace's
    // module (`module Price = Price-Shop`), has no binder and names no item
    // of `parent_sig`, so the substitution leaves it as it is. Building that
    // substitution walks all of `parent_sig`, which for a namespace is every
    // module of the package, so every module of the package would do work
    // proportional to its size (compiler/ml/env.ml `alias_map_components`).
    if let ModuleType::MtyAlias(_, target) = &md.md_type
        && let PathView::Pident(target) = target.view()
        && target.is_persistent()
    {
        return;
    }
    md.md_type = crate::types::typecore::copy_lookup_module_type_for_subst(&md.md_type, ctx);
    let maps = build_subst_maps(parent_sig, parent_module_path, ctx);
    freshen_module_type_bound_idents_with_maps(&mut md.md_type, &maps, ctx);
}

fn build_subst_maps_for_module(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) -> SubstMaps {
    // OCaml compiler/ml/env.ml:1530-1538 builds substitution maps from the
    // component signature with `prefix_idents`, and compiler/ml/subst.ml:69-95
    // rewrites module paths only through those explicit maps.
    build_subst_maps(sig_items, module_path, ctx)
}

/// The module type of a component module declaration as forcing its
/// `comp_modules` thunk returns it (compiler/ml/env.ml:446-448, 1568), for
/// declarations that are paths: OCaml compiler/ml/subst.ml:345-364
/// `Subst.modtype` rewrites an `Mty_ident` target through the modtype table
/// and an `Mty_alias` target through `module_path`, renaming no binder. The
/// substitution is the component's `prefix_idents` one (env.ml:1530), built
/// from `sig_items` at `module_path` as `freshen_component_module_declaration_bound_idents`
/// builds it. Persistent targets are not bound by that substitution.
pub(crate) fn substitute_component_module_type_path(
    module_type: &ModuleType,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) -> Option<ModuleType> {
    let target = match module_type {
        ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
            module_type.ident_or_alias_path().unwrap()
        }
        _ => return None,
    };
    if target.head().is_persistent() {
        return Some(module_type.clone());
    }
    let mut module_type = module_type.clone();
    let maps = build_subst_maps(sig_items, module_path, ctx);
    substitute_module_type_paths_with_maps(ctx, &mut module_type, &maps);
    Some(module_type)
}

/// The component substitution of one signature at one path
/// (`prefix_idents`, env.ml:1530), built once for a builder that applies it
/// to many items: [`substitute_sig_path`] and
/// [`substitute_component_module_type_path`] build it on every call.
pub(crate) struct ComponentSubst(SubstMaps);

impl ComponentSubst {
    /// One pass over `sig_items`.
    pub(crate) fn new(sig_items: &[SignatureItem], module_path: &Path, ctx: &TypeContext) -> Self {
        ComponentSubst(build_subst_maps(sig_items, module_path, ctx))
    }

    /// [`substitute_sig_path`]: one walk of `path`.
    pub(crate) fn path(&self, path: &Path, ctx: &TypeContext) -> Path {
        substitute_type_path(
            ctx,
            path,
            &self.0.type_stamp_map,
            &self.0.type_name_map,
            &self.0.module_stamp_map,
            &self.0.module_name_map,
            self.0.protected_module_head.as_ref(),
        )
    }

    /// [`freshen_component_modtype_declaration_bound_idents`]: one copy of
    /// the declaration's module type.
    pub(crate) fn freshen_modtype_declaration(&self, mtd: &mut ModtypeDeclaration, ctx: &TypeContext) {
        if let Some(module_type) = mtd.mtd_type.as_mut() {
            *module_type =
                crate::types::typecore::copy_lookup_module_type_for_subst(module_type, ctx);
            freshen_module_type_bound_idents_with_maps(module_type, &self.0, ctx);
        }
    }

    /// [`freshen_component_module_declaration_bound_idents`] without
    /// building the substitution again: one copy of the declaration's
    /// module type (`Subst.modtype sub md.md_type`, env.ml:475-477), none
    /// for an alias of a persistent unit, which names no item of the
    /// signature and binds nothing.
    pub(crate) fn freshen_module_declaration(&self, md: &mut ModuleDeclaration, ctx: &TypeContext) {
        if let ModuleType::MtyAlias(_, target) = &md.md_type
            && let PathView::Pident(target) = target.view()
            && target.is_persistent()
        {
            return;
        }
        md.md_type = crate::types::typecore::copy_lookup_module_type_for_subst(&md.md_type, ctx);
        freshen_module_type_bound_idents_with_maps(&mut md.md_type, &self.0, ctx);
    }

    /// What a child component table's signature gets from its parent's
    /// substitution (this one, of `parent_sig` at `parent_module_path`):
    /// [`substitute_type_paths_in_child_sig`] and
    /// [`substitute_module_alias_paths_in_child_sig`] without building the
    /// parent's maps again. One walk of the child's type nodes and one of
    /// its items; a child type whose manifest is its own name also scans
    /// the parent's items for a type of that name.
    pub(crate) fn substitute_child_signature(
        &self,
        child_sig: &mut [SignatureItem],
        parent_sig: &[SignatureItem],
        parent_module_path: &Path,
        ctx: &TypeContext,
    ) {
        substitute_type_paths_in_sig_with_maps(child_sig, &self.0, ctx);
        restore_child_self_manifests_from_parent_scope(
            child_sig,
            parent_sig,
            parent_module_path,
            ctx,
        );
        for item in child_sig.iter_mut() {
            if let SignatureItem::SigModule(_, md, _) = item
                && let ModuleType::MtyAlias(_, path) = &mut md.md_type
            {
                *path = substitute_shared_module_path(
                    ctx,
                    path,
                    &self.0.module_stamp_map,
                    &self.0.module_name_map,
                    self.0.protected_module_head.as_ref(),
                );
            }
        }
    }

    /// [`substitute_component_module_type_path`]: one walk of the target.
    pub(crate) fn module_type_path(
        &self,
        module_type: &ModuleType,
        ctx: &TypeContext,
    ) -> Option<ModuleType> {
        let target = match module_type {
            ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                module_type.ident_or_alias_path().unwrap()
            }
            _ => return None,
        };
        if target.head().is_persistent() {
            return Some(module_type.clone());
        }
        let mut module_type = module_type.clone();
        substitute_module_type_paths_with_maps(ctx, &mut module_type, &self.0);
        Some(module_type)
    }
}

/// `path` with the items of `sig_items` it names qualified by `module_path`.
pub fn substitute_sig_path(
    path: &Path,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) -> Path {
    let maps = build_subst_maps_for_module(sig_items, module_path, ctx);
    substitute_type_path(
        ctx,
        path,
        &maps.type_stamp_map,
        &maps.type_name_map,
        &maps.module_stamp_map,
        &maps.module_name_map,
        maps.protected_module_head.as_ref(),
    )
}

fn substitute_module_type_paths_with_maps(
    ctx: &TypeContext,
    module_type: &mut ModuleType,
    maps: &SubstMaps,
) {
    substitute_module_type_paths_with_maps_mode(ctx, module_type, maps, AliasTargets::Substitute);
}

/// Whether a declaration-path substitution also rewrites `Mty_alias` targets.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AliasTargets {
    Substitute,
    /// Leave alias targets as the raw signature has them. OCaml
    /// compiler/ml/env.ml:677 and env.ml:1970 keep `ps_sig` as
    /// `Subst.signature Subst.identity sign`, so `module Aliased = One` stays
    /// `Mty_alias (Pident One)`; compiler/ml/subst.ml:358-364 rewrites the
    /// target only when env.ml:1568's `comp_modules` thunk is forced
    /// (env.ml:446-448, `freshen_module_type_bound_idents_rec` here).
    KeepRaw,
}

fn substitute_module_type_paths_with_maps_mode(
    ctx: &TypeContext,
    module_type: &mut ModuleType,
    maps: &SubstMaps,
    alias_targets: AliasTargets,
) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            *path = substitute_type_path(
                ctx,
                path,
                &maps.type_stamp_map,
                &maps.type_name_map,
                &maps.module_stamp_map,
                &maps.module_name_map,
                maps.protected_module_head.as_ref(),
            );
        }
        ModuleType::MtyAlias(_, path) => {
            if alias_targets == AliasTargets::Substitute {
                *path = substitute_shared_module_path(
                    ctx,
                    path,
                    &maps.module_stamp_map,
                    &maps.module_name_map,
                    maps.protected_module_head.as_ref(),
                );
            }
        }
        ModuleType::MtySignature(sig) => {
            substitute_sig_decl_paths_in_place_with_maps_rec(
                ctx,
                crate::types::decl::signature_mut(sig),
                maps,
                true,
                alias_targets,
            );
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                substitute_module_type_paths_with_maps_mode(ctx, param_type, maps, alias_targets);
            }
            substitute_module_type_paths_with_maps_mode(ctx, result, maps, alias_targets);
        }
    }
}

fn substitute_sig_decl_paths_in_place_with_maps(
    ctx: &TypeContext,
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
) {
    substitute_sig_decl_paths_in_place_with_maps_rec(
        ctx,
        sig_items,
        maps,
        true,
        AliasTargets::Substitute,
    );
}

/// Substitute the declaration paths of `sig_items`; without `recurse`, the
/// module types of nested modules and module types are left alone.
fn substitute_sig_decl_paths_in_place_with_maps_rec(
    ctx: &TypeContext,
    sig_items: &mut [SignatureItem],
    maps: &SubstMaps,
    recurse: bool,
    alias_targets: AliasTargets,
) {
    if maps.is_empty() {
        return;
    }

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    *path = substitute_type_path(
                        ctx,
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
                        ctx,
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
                    ctx,
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
                        ctx,
                        path,
                        &maps.type_stamp_map,
                        &maps.type_name_map,
                        &maps.module_stamp_map,
                        &maps.module_name_map,
                        maps.protected_module_head.as_ref(),
                    );
                }
                if recurse {
                    substitute_module_type_paths_with_maps_mode(
                        ctx,
                        &mut md.md_type,
                        maps,
                        alias_targets,
                    );
                }
            }
            SignatureItem::SigModtype(_, mtd) => {
                if recurse && let Some(module_type) = mtd.mtd_type.as_mut() {
                    substitute_module_type_paths_with_maps_mode(
                        ctx,
                        module_type,
                        maps,
                        alias_targets,
                    );
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// Qualify the declaration paths of `sig_items` (value, type and extension
/// paths, and module type paths) that name its own items by `module_path`,
/// in nested signatures too.
pub fn substitute_sig_decl_paths_in_place(
    sig_items: &mut [SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let maps = build_subst_maps_for_module(sig_items, module_path, ctx);
    substitute_sig_decl_paths_in_place_with_maps(ctx, sig_items, &maps);
}

/// Qualify the declaration paths Rust caches on a loaded unit's signature
/// (`type_path`, `val_path`, `md_path`), keeping module alias targets raw as
/// OCaml's `ps_sig` keeps them (see `AliasTargets::KeepRaw`).
pub fn qualify_unit_sig_decl_paths_in_place(
    sig_items: &mut [SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let maps = build_subst_maps_for_module(sig_items, module_path, ctx);
    substitute_sig_decl_paths_in_place_with_maps_rec(
        ctx,
        sig_items,
        &maps,
        true,
        AliasTargets::KeepRaw,
    );
}

fn substitute_type_paths_in_sig_with_maps(
    sig_items: &[SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext,
) {
    let mut visited = visit_set();
    substitute_type_paths_in_sig_items(sig_items, maps, ctx, &mut visited, true);
}

/// Substitute the type paths of `sig_items`' type expressions, visiting each
/// type node once per `visited` set. With `recurse`, nested module
/// signatures are included; without it only this level's items are.
fn substitute_type_paths_in_sig_items(
    sig_items: &[SignatureItem],
    maps: &SubstMaps,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
    recurse: bool,
) {
    if maps.is_empty() {
        return;
    }

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(desc.val_type, maps.paths(), ctx, visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    substitute_type_expr_path(param, maps.paths(), ctx, visited);
                }

                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(manifest, maps.paths(), ctx, visited);
                }

                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        substitute_type_expr_path(arg, maps.paths(), ctx, visited);
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        substitute_type_expr_path(
                                            lbl.ld_type,
                                            maps.paths(),
                                            ctx,
                                            visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                substitute_type_expr_path(res, maps.paths(), ctx, visited);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, maps.paths(), ctx, visited);
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    substitute_type_expr_path(param, maps.paths(), ctx, visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            substitute_type_expr_path(arg, maps.paths(), ctx, visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, maps.paths(), ctx, visited);
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    substitute_type_expr_path(ret, maps.paths(), ctx, visited);
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
    let parent_maps = build_subst_maps(parent_sig, parent_module_path, ctx);
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
    ctx: &TypeContext,
) {
    let maps = build_subst_maps(parent_sig, parent_module_path, ctx);
    for item in child_sig.iter_mut() {
        if let SignatureItem::SigModule(_, md, _) = item
            && let ModuleType::MtyAlias(_, path) = &mut md.md_type
        {
            *path = substitute_shared_module_path(
                ctx,
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
        let TypeDesc::Tconstr {
            path, args, abbrev, ..
        } = desc
        else {
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

/// Qualify the paths in the type expressions of `sig_items` that name its
/// own items by `module_path`.
pub fn substitute_type_paths_in_sig(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let maps = build_subst_maps_for_module(sig_items, module_path, ctx);
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
                    .entry(id.name_atom())
                    .or_insert_with(|| maps.type_stamp_map.stamps[&id.stamp()]);
            }
            _ => {}
        }
    }
    let type_name_map = direct_type_name_map;
    let module_stamp_map = &maps.module_stamp_map;
    let module_name_map = &maps.module_name_map;
    let protected_module_head = maps.protected_module_head.as_ref();
    let paths = SubstPaths {
        type_stamp_map,
        type_name_map: &type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
    };

    if type_stamp_map.is_empty()
        && type_name_map.is_empty()
        && module_stamp_map.is_empty()
        && module_name_map.is_empty()
    {
        return;
    }

    // Now walk all type expressions referenced from the signature
    // and rewrite Tconstr paths that match our maps
    let mut visited = visit_set();

    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(desc.val_type, paths, ctx, &mut visited);
            }
            SignatureItem::SigType(id, decl, _) => {
                // Substitute in type params
                for &param in &decl.type_params {
                    substitute_type_expr_path(param, paths, ctx, &mut visited);
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
                        paths,
                    ) {
                        substitute_type_expr_path(manifest, paths, ctx, &mut visited);
                    }
                }
                // Substitute in constructor/label types
                match &decl.type_kind {
                    TypeKind::TypeVariant(constrs, _) => {
                        for cd in constrs {
                            match &cd.cd_args {
                                crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                                    for &arg in args {
                                        substitute_type_expr_path(arg, paths, ctx, &mut visited);
                                    }
                                }
                                crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                                    for lbl in labels {
                                        substitute_type_expr_path(
                                            lbl.ld_type,
                                            paths,
                                            ctx,
                                            &mut visited,
                                        );
                                    }
                                }
                            }
                            if let Some(res) = cd.cd_res {
                                substitute_type_expr_path(res, paths, ctx, &mut visited);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, paths, ctx, &mut visited);
                        }
                    }
                    _ => {}
                }
            }
            SignatureItem::SigTypext(_id, ext, _) => {
                for &param in &ext.ext_type_params {
                    substitute_type_expr_path(param, paths, ctx, &mut visited);
                }
                match &ext.ext_args {
                    crate::types::decl::ConstructorArguments::CstrTuple(args) => {
                        for &arg in args {
                            substitute_type_expr_path(arg, paths, ctx, &mut visited);
                        }
                    }
                    crate::types::decl::ConstructorArguments::CstrRecord(labels) => {
                        for lbl in labels {
                            substitute_type_expr_path(lbl.ld_type, paths, ctx, &mut visited);
                        }
                    }
                }
                if let Some(ret) = ext.ext_ret_type {
                    substitute_type_expr_path(ret, paths, ctx, &mut visited);
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
    let stamp_map = &TypeSubstPaths {
        stamps: stamp_map.clone(),
        ..TypeSubstPaths::default()
    };
    let empty: HashMap<Name, Path> = HashMap::new();
    let empty_module_stamp = ModuleStampSubstMap::new();
    let empty_module_names: HashMap<Name, Arc<Path>> = HashMap::new();
    let paths = SubstPaths {
        type_stamp_map: stamp_map,
        type_name_map: &empty,
        module_stamp_map: &empty_module_stamp,
        module_name_map: &empty_module_names,
        protected_module_head: None,
    };
    let mut visited = visit_set();
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_id, desc) => {
                substitute_type_expr_path(desc.val_type, paths, ctx, &mut visited);
            }
            SignatureItem::SigType(_id, decl, _) => {
                for &param in &decl.type_params {
                    substitute_type_expr_path(param, paths, ctx, &mut visited);
                }
                if let Some(manifest) = decl.type_manifest {
                    substitute_type_expr_path(manifest, paths, ctx, &mut visited);
                }
            }
            _ => {}
        }
    }
}



/// Recursively walk a type expression and substitute Tconstr paths.
fn substitute_type_expr_path(
    initial_ty_ref: TypeExprRef,
    paths: SubstPaths<'_>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
) {
    let SubstPaths {
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
    } = paths;
    // Use an explicit work stack instead of recursion to avoid stack overflow
    // on large type graphs (e.g., objects with hundreds of fields create deep
    // Tfield chains, and Tlink chains from unification can be thousands deep).
    let mut work_stack = vec![initial_ty_ref];

    while let Some(ty_ref) = work_stack.pop() {
        if !visited.visit(ty_ref) {
            continue; // Already visited (cycle detection)
        }

        let desc = ctx.borrow_desc(ty_ref);
        let mut replacement = None;

        // subst.ml:165-172: the arguments are substituted first, then the
        // constructor becomes the type function applied to them.
        if let TypeDesc::Tconstr { path, args, .. } = &*desc
            && let Some((params, body)) = type_stamp_map.function(path)
        {
            let (params, body, args) = (params.clone(), *body, ctx.type_list(*args).to_vec());
            for &arg in &args {
                substitute_type_expr_path(arg, paths, ctx, visited);
            }
            let applied = crate::types::ctype::apply(
                ctx,
                &crate::types::env::Env::empty(),
                &params,
                body,
                &args,
            )
            .expect("Ctype.apply of a substituted type function");
            // `ty'.desc <- (apply ...).desc` shares the result's descriptor.
            let applied_desc = ctx.get_desc(applied).into_desc();
            ctx.set_desc(ty_ref, applied_desc);
            continue;
        }

        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let new_path = substitute_type_path(
                    ctx,
                    path,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    protected_module_head,
                );
                if new_path != *path {
                    let mut new_desc = *desc;
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
                // polymorphic-variant row_name paths while copying the row,
                // and drops a name substituted by a type function.
                if let Some((path, _)) = &row.row_name
                    && type_stamp_map.function(path).is_some()
                {
                    let mut new_row = row.clone();
                    new_row.row_name = None;
                    replacement = Some(TypeDesc::Tvariant(ctx.new_row_desc(new_row)));
                } else if let Some((path, _)) = &row.row_name {
                    let new_path = substitute_type_path(
                        ctx,
                        path,
                        type_stamp_map,
                        type_name_map,
                        module_stamp_map,
                        module_name_map,
                        protected_module_head,
                    );
                    if new_path != *path {
                        let mut new_row = row.clone();
                        if let Some((path, _)) = &mut new_row.row_name {
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
                    ctx,
                    path,
                    type_stamp_map,
                    type_name_map,
                    module_stamp_map,
                    module_name_map,
                    protected_module_head,
                );
                if new_path != *path {
                    let mut new_desc = *desc;
                    if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                        *path = new_path;
                    }
                    replacement = Some(new_desc);
                }
                for arg in ctx.type_list(args).iter() {
                    work_stack.push(arg);
                }
            }
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
        }
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
    let map_path = reroot_path_mapper(prefixes, ctx);
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

/// Build one scoped mapper so all uses of a replacement prefix retain the
/// same allocation. Matching remains ordered by the original prefix list.
pub fn reroot_path_mapper<'a>(
    prefixes: &'a [(Path, Path)],
    ctx: &'a TypeContext,
) -> impl Fn(&Path) -> Path + 'a {
    let prefixes = PathPrefixes::new(prefixes);
    move |path| rewrite_path_by_path_prefixes(path, &prefixes, ctx).unwrap_or(*path)
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
        visited: &mut TypeVisitSet,
    ) -> bool {
        if !visited.visit(ty) {
            return false;
        }
        let desc = ctx.get_desc(ty);
        let hit = |p: &Path| prefixes.matching_prefix(p).is_some();
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
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => false,
        }
    }
    walk(ty, &PathPrefixes::new(prefixes), ctx, &mut visit_set())
}

/// Component substitution used by `substitute_type_paths_in_value_from_sig`.
/// It depends only on the component signature and access path, so component
/// tables can build it once and reuse it for every value lookup.
#[derive(Debug)]
pub struct ValueSubstMaps {
    maps: SubstMaps,
    direct_type_name_map: HashMap<Name, Path>,
}

/// The substitution qualifying the items of `sig_items` by `module_path` in
/// value types (see [`substitute_type_paths_in_value_with_maps`]).
pub fn build_value_subst_maps(
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) -> ValueSubstMaps {
    let maps = build_subst_maps_for_module(sig_items, module_path, ctx);
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
                    .entry(id.name_atom())
                    .or_insert_with(|| maps.type_stamp_map.stamps[&id.stamp()]);
            }
            _ => {}
        }
    }
    ValueSubstMaps {
        maps,
        direct_type_name_map,
    }
}

/// [`substitute_type_paths_in_value_with_maps`] with the maps of
/// `sig_items` and `module_path`.
pub fn substitute_type_paths_in_value_from_sig(
    desc: &mut crate::types::decl::ValueDescription,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    let value_maps = build_value_subst_maps(sig_items, module_path, ctx);
    substitute_type_paths_in_value_with_maps(desc, &value_maps, sig_items, module_path, ctx);
}

/// Qualify the paths in the type of `desc`, a value of `sig_items`, that
/// name items of `sig_items` by `module_path`, and re-root paths through the
/// module's alias sources at `module_path`.
pub fn substitute_type_paths_in_value_with_maps(
    desc: &mut crate::types::decl::ValueDescription,
    value_maps: &ValueSubstMaps,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    substitute_value_type_paths(desc, value_maps, sig_items, module_path, true, ctx);
}

/// The component substitution of one value (`Subst.value_description sub
/// decl`, env.ml:1537) for a builder that has put the value's type at
/// `module_path` already when the module is reached through an alias (one
/// rewrite of the whole source prefix): the per-item re-rooting of
/// [`substitute_type_paths_in_value_with_maps`], one walk of the type for
/// every type and module of the signature, would find nothing. One walk of
/// the value's type.
pub(crate) fn substitute_value_type_paths_at_component(
    desc: &mut crate::types::decl::ValueDescription,
    value_maps: &ValueSubstMaps,
    sig_items: &[SignatureItem],
    module_path: &Path,
    ctx: &TypeContext,
) {
    substitute_value_type_paths(desc, value_maps, sig_items, module_path, false, ctx);
}

fn substitute_value_type_paths(
    desc: &mut crate::types::decl::ValueDescription,
    value_maps: &ValueSubstMaps,
    sig_items: &[SignatureItem],
    module_path: &Path,
    reroot_alias_sources: bool,
    ctx: &TypeContext,
) {
    let maps = &value_maps.maps;
    let direct_type_name_map = &value_maps.direct_type_name_map;
    let type_stamp_map = &maps.type_stamp_map;
    let type_name_map = direct_type_name_map;
    let module_stamp_map = &maps.module_stamp_map;
    let module_name_map = &maps.module_name_map;
    let protected_module_head = maps.protected_module_head.as_ref();
    let paths = SubstPaths {
        type_stamp_map,
        type_name_map,
        module_stamp_map,
        module_name_map,
        protected_module_head,
    };

    if type_stamp_map.is_empty()
        && type_name_map.is_empty()
        && module_stamp_map.is_empty()
        && module_name_map.is_empty()
    {
        return;
    }

    let mut visited = visit_set();
    substitute_type_expr_path(desc.val_type, paths, ctx, &mut visited);
    if !reroot_alias_sources {
        return;
    }

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
            // Reuse the component's one prefix_idents target, including
            // its allocation, for every selected value description.
            let new_path = match item {
                SignatureItem::SigType(..) => {
                    direct_type_name_map.get(&id.name_atom()).cloned().map(Arc::new)
                }
                SignatureItem::SigModule(..) if id.stamp() != 0 => module_stamp_map
                    .get(&id.stamp())
                    .map(|(_, path)| path.clone()),
                SignatureItem::SigModule(..) => module_name_map.get(&id.name_atom()).cloned(),
                _ => unreachable!(),
            }
            .expect("component binder has no prefix substitution");
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
    paths: SubstPaths<'_>,
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
        ctx,
        path,
        paths.type_stamp_map,
        paths.type_name_map,
        paths.module_stamp_map,
        paths.module_name_map,
        paths.protected_module_head,
    );
    substituted.same(&Path::pdot(*module_path, id.name_atom()))
}

/// A Subst module target already is one path allocation; an unchanged Pident
/// returns the original prefix. Neither case creates a new prefix block.
fn substitute_shared_module_path(
    ctx: &TypeContext,
    path: &Arc<Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<Name, Arc<Path>>,
    protected_module_head: Option<&(i32, Name)>,
) -> Arc<Path> {
    if let PathView::Pident(id) = &path.view() {
        let target =
            module_path_target(id, module_stamp_map, module_name_map, protected_module_head);
        return target.unwrap_or(path).clone();
    }
    if let Some(target) = module_stamp_map.path_target(path) {
        return target.clone();
    }
    Arc::new(substitute_module_path(
        ctx,
        path,
        module_stamp_map,
        module_name_map,
        protected_module_head,
    ))
}

fn module_path_target<'a>(
    id: &Ident,
    module_stamp_map: &'a ModuleStampSubstMap,
    module_name_map: &'a HashMap<Name, Arc<Path>>,
    protected_module_head: Option<&(i32, Name)>,
) -> Option<&'a Arc<Path>> {
    if id.stamp() != 0 {
        let protected = protected_module_head
            .is_some_and(|(stamp, name)| *stamp == id.stamp() && name == id.name());
        module_stamp_map
            .get(&id.stamp())
            .and_then(|(_, path)| (!protected).then_some(path))
    } else {
        module_name_map.get(&id.name_atom())
    }
}

fn substitute_type_path(
    ctx: &TypeContext,
    path: &Path,
    type_stamp_map: &TypeSubstPaths,
    type_name_map: &HashMap<Name, Path>,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<Name, Arc<Path>>,
    protected_module_head: Option<&(i32, Name)>,
) -> Path {
    if !type_stamp_map.qualified.is_empty()
        && let Some(target) = type_stamp_map
            .qualified
            .get(&crate::types::context::SamePathKey::new(*path))
    {
        return *target;
    }
    match &path.view() {
        PathView::Pident(ident) => {
            if ident.stamp() != 0 {
                // OCaml compiler/ml/subst.ml:87-100 `type_path` rewrites
                // non-persistent ids through Ident.find_same only. It does not
                // fall back to declaration names or flattened path spelling.
                type_stamp_map
                    .stamps
                    .get(&ident.stamp())
                    .cloned()
                    .unwrap_or(*path)
            } else {
                type_name_map
                    .get(&ident.name_atom())
                    .cloned()
                    .unwrap_or(*path)
            }
        }
        PathView::Pdot(..) => ctx.rebuild_dotted(path, |prefix| {
            substitute_shared_module_path(
                ctx,
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            )
        }),
        PathView::Papply(left, right) => Path::papply(
            substitute_module_path(
                ctx,
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
            substitute_module_path(
                ctx,
                right,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
        ),
    }
}

fn substitute_module_path(
    ctx: &TypeContext,
    path: &Path,
    module_stamp_map: &ModuleStampSubstMap,
    module_name_map: &HashMap<Name, Arc<Path>>,
    protected_module_head: Option<&(i32, Name)>,
) -> Path {
    if let Some(target) = module_stamp_map.path_target(path) {
        return **target;
    }
    match &path.view() {
        PathView::Pident(ident) => module_path_target(
            ident,
            module_stamp_map,
            module_name_map,
            protected_module_head,
        )
        .map_or(*path, |target| **target),
        PathView::Pdot(..) => ctx.rebuild_dotted(path, |prefix| {
            substitute_shared_module_path(
                ctx,
                prefix,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            )
        }),
        PathView::Papply(left, right) => Path::papply(
            substitute_module_path(
                ctx,
                left,
                module_stamp_map,
                module_name_map,
                protected_module_head,
            ),
            substitute_module_path(
                ctx,
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
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
) {
    if !visited.visit(ty_ref) {
        return; // Already visited (cycle detection)
    }

    let desc = ctx.get_desc(ty_ref);

    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let rewritten = rewrite_path_prefix(path, old_name, new_prefix, ctx);
            if let Some(new_path) = rewritten {
                let mut new_desc = *desc;
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
                && let Some(new_path) = rewrite_path_prefix(path, old_name, new_prefix, ctx)
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
            if let Some(new_path) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                let mut new_desc = *desc;
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_prefix(arg, old_name, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
    }
}

/// Rewrite a path's module prefix from an old name to a new path.
/// Returns Some(new_path) if rewritten, None if unchanged.
fn rewrite_path_prefix(
    path: &Path,
    old_name: &str,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) -> Option<Path> {
    match &path.view() {
        PathView::Pident(id) if id.name() == old_name => Some(**new_prefix),
        PathView::Pdot(inner, _, _) => {
            let prefix = match &inner.view() {
                PathView::Pident(id) if id.name() == old_name => new_prefix.clone(),
                _ => Arc::new(rewrite_path_prefix(inner, old_name, new_prefix, ctx)?),
            };
            Some(ctx.copy_dotted_with_prefix(path, prefix))
        }
        _ => None,
    }
}

fn rewrite_module_type_prefix_paths(
    module_type: &mut ModuleType,
    old_name: &str,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                *path = rewritten;
            }
        }
        ModuleType::MtyAlias(_, path) => {
            // A replaced `Pident` target is the shared replacement block.
            if matches!(path.view(), PathView::Pident(id) if id.name() == old_name) {
                *path = new_prefix.clone();
            } else if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                *path = Arc::new(rewritten);
            }
        }
        ModuleType::MtySignature(sig) => {
            rewrite_module_prefix_paths_in_sig(
                crate::types::decl::signature_mut(sig),
                old_name,
                new_prefix,
                ctx,
            );
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_module_type_prefix_paths(param_type, old_name, new_prefix, ctx);
            }
            rewrite_module_type_prefix_paths(result, old_name, new_prefix, ctx);
        }
    }
}

/// Rewrite the declaration paths of `sig_items` rooted at unit `old_name`
/// to be rooted at `new_prefix` instead, in nested signatures too.
pub fn rewrite_module_prefix_paths_in_sig(
    sig_items: &mut [SignatureItem],
    old_name: &str,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_prefix(&ext.ext_type_path, old_name, new_prefix, ctx)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                if let Some(path) = md.md_path.as_mut() {
                    if let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx) {
                        *path = rewritten;
                    }
                }
                rewrite_module_type_prefix_paths(&mut md.md_type, old_name, new_prefix, ctx);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    rewrite_module_type_prefix_paths(module_type, old_name, new_prefix, ctx);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// [`rewrite_module_prefix_paths_in_sig`] for this signature level only.
// OCaml compiler/ml/env.ml:1530-1578 builds one component-table level at a
// time; child module declarations remain lazy component thunks at env.ml:1568
// and env.ml:1573. This path-metadata rewrite therefore intentionally stops at
// the current signature level instead of descending into child modules.
pub fn rewrite_module_prefix_paths_in_sig_shallow(
    sig_items: &mut [SignatureItem],
    old_name: &str,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut()
                    && let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut()
                    && let Some(rewritten) = rewrite_path_prefix(path, old_name, new_prefix, ctx)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_prefix(&ext.ext_type_path, old_name, new_prefix, ctx)
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
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    let mut visited = visit_set();
    rewrite_module_prefix_in_sig_with_visited(sig_items, old_name, new_prefix, ctx, &mut visited);
}

/// Rewrite the paths rooted at unit `old_name` in the type expressions of
/// `sig_items` to be rooted at `new_prefix`, for this signature level only.
// OCaml compiler/ml/env.ml:1530-1578 applies prefix_idents substitution only to
// the component table currently being built. Child module bodies are represented
// by env.ml:1568/env.ml:1573 lazy thunks, so their type expressions are rewritten
// only when those component thunks are forced.
pub fn rewrite_module_prefix_in_sig_shallow(
    sig_items: &[SignatureItem],
    old_name: &str,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    let mut visited = visit_set();
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
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
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
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
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
/// Prefix rewrites `(old, new)` tried in order, with an index from each old
/// prefix (compared with `Path::same`) to its first position.
struct PathPrefixes<'a> {
    pairs: &'a [(Path, Path)],
    targets: std::cell::OnceCell<Vec<Arc<Path>>>,
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
        PathPrefixes {
            pairs,
            targets: std::cell::OnceCell::new(),
            index,
        }
    }
}

impl PathPrefixes<'_> {
    fn matching_prefix(&self, path: &Path) -> Option<usize> {
        if self.index.is_none() {
            return self.pairs.iter().position(|(old, _)| {
                let mut ancestor = *path;
                loop {
                    if ancestor.same(old) {
                        return true;
                    }
                    match ancestor.view() {
                        PathView::Pdot(inner, _, _) => ancestor = *inner,
                        _ => return false,
                    }
                }
            });
        }
        // Preserve first-pair order, not nearest-ancestor order.
        let index = self.index.as_ref().unwrap();
        let mut first: Option<usize> = None;
        let mut ancestor = *path;
        loop {
            if let Some(&position) =
                index.get(&crate::types::context::SamePathKey::new(ancestor))
            {
                first = Some(first.map_or(position, |found| found.min(position)));
            }
            match ancestor.view() {
                PathView::Pdot(inner, _, _) => ancestor = *inner,
                _ => break,
            }
        }
        first
    }
}

fn rewrite_path_with_shared_prefix(
    path: &Path,
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) -> Option<Path> {
    if path.same(old_prefix) {
        return Some(**new_prefix);
    }
    match &path.view() {
        PathView::Pdot(inner, _, _) => {
            let prefix = if inner.same(old_prefix) {
                new_prefix.clone()
            } else {
                Arc::new(rewrite_path_with_shared_prefix(
                    inner, old_prefix, new_prefix, ctx,
                )?)
            };
            // Subst.module_path/type_path rebuild dotted blocks, but retain
            // their suffix strings (compiler/ml/subst.ml:69-100).
            Some(ctx.copy_dotted_with_prefix(path, prefix))
        }
        _ => None,
    }
}

fn rewrite_path_by_path_prefixes(
    path: &Path,
    prefixes: &PathPrefixes<'_>,
    ctx: &TypeContext,
) -> Option<Path> {
    let position = prefixes.matching_prefix(path)?;
    let targets = prefixes.targets.get_or_init(|| {
        prefixes
            .pairs
            .iter()
            .map(|(_, target)| Arc::new(*target))
            .collect()
    });
    rewrite_path_with_shared_prefix(path, &prefixes.pairs[position].0, &targets[position], ctx)
}

fn rewrite_module_type_by_path_prefix(
    module_type: &mut ModuleType,
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    match module_type {
        ModuleType::MtyIdent(path) => {
            if let Some(rewritten) =
                rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
            {
                *path = rewritten;
            }
        }
        ModuleType::MtyAlias(_, path) => {
            // A replaced whole target is the shared replacement block.
            if path.same(old_prefix) {
                *path = new_prefix.clone();
            } else if let Some(rewritten) =
                rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
            {
                *path = Arc::new(rewritten);
            }
        }
        ModuleType::MtySignature(sig) => {
            rewrite_sig_paths_by_path_prefix(
                crate::types::decl::signature_mut(sig),
                old_prefix,
                new_prefix,
                ctx,
            );
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(param_type) = param_type.as_mut() {
                rewrite_module_type_by_path_prefix(param_type, old_prefix, new_prefix, ctx);
            }
            rewrite_module_type_by_path_prefix(result, old_prefix, new_prefix, ctx);
        }
    }
}

/// Rewrite the declaration paths of `sig_items` that are or extend
/// `old_prefix` to start with `new_prefix` instead, in nested signatures too.
pub fn rewrite_sig_paths_by_path_prefix(
    sig_items: &mut [SignatureItem],
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
                    {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
                    {
                        *path = rewritten;
                    }
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_with_shared_prefix(&ext.ext_type_path, old_prefix, new_prefix, ctx)
                {
                    ext.ext_type_path = rewritten;
                }
            }
            SignatureItem::SigModule(_, md, _) => {
                if let Some(path) = md.md_path.as_mut() {
                    if let Some(rewritten) =
                        rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
                    {
                        *path = rewritten;
                    }
                }
                rewrite_module_type_by_path_prefix(&mut md.md_type, old_prefix, new_prefix, ctx);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(module_type) = mtd.mtd_type.as_mut() {
                    rewrite_module_type_by_path_prefix(module_type, old_prefix, new_prefix, ctx);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// [`rewrite_sig_paths_by_path_prefix`] for this signature level only.
// OCaml compiler/ml/env.ml:1530-1578 exposes selected component paths for the
// current table, while mtype.ml:98-102 keeps child modules strengthened as
// aliases to the scraped target. Keep this rewrite shallow so child module
// aliases are left for their env.ml:1568/env.ml:1573 component thunks.
pub fn rewrite_sig_paths_by_path_prefix_shallow(
    sig_items: &mut [SignatureItem],
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    for item in sig_items {
        match item {
            SignatureItem::SigValue(_, desc) => {
                if let Some(path) = desc.val_path.as_mut()
                    && let Some(rewritten) =
                        rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigType(_, decl, _) => {
                if let Some(path) = std::sync::Arc::make_mut(decl).type_path.as_mut()
                    && let Some(rewritten) =
                        rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
                {
                    *path = rewritten;
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                if let Some(rewritten) =
                    rewrite_path_with_shared_prefix(&ext.ext_type_path, old_prefix, new_prefix, ctx)
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
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
) {
    if !visited.visit(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if let Some(new_path) =
                rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
            {
                let mut new_desc = *desc;
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
                && let Some(new_path) =
                    rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
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
            if let Some(new_path) =
                rewrite_path_with_shared_prefix(path, old_prefix, new_prefix, ctx)
            {
                let mut new_desc = *desc;
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_by_path_prefix_in(arg, old_prefix, new_prefix, ctx, visited);
            }
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
    }
}

/// `rewrite_type_expr_by_path_prefix_in` with a fresh visited set.
pub fn rewrite_type_expr_by_path_prefix(
    ty_ref: TypeExprRef,
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    #[cfg(test)]
    TYPE_PREFIX_WALKS.with(|walks| walks.set(walks.get() + 1));
    let mut visited = visit_set();
    rewrite_type_expr_by_path_prefix_in(ty_ref, old_prefix, new_prefix, ctx, &mut visited);
}

fn rewrite_type_expr_by_path_prefixes(
    ty_ref: TypeExprRef,
    prefixes: &PathPrefixes<'_>,
    ctx: &TypeContext,
    visited: &mut TypeVisitSet,
) {
    if !visited.visit(ty_ref) {
        return;
    }

    let desc = ctx.get_desc(ty_ref);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            if let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes, ctx) {
                let mut new_desc = *desc;
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
                && let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes, ctx)
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
            if let Some(new_path) = rewrite_path_by_path_prefixes(path, prefixes, ctx) {
                let mut new_desc = *desc;
                if let TypeDesc::Tpackage { ref mut path, .. } = new_desc {
                    *path = new_path;
                }
                ctx.set_desc(ty_ref, new_desc);
            }
            for arg in ctx.type_list(args).iter() {
                rewrite_type_expr_by_path_prefixes(arg, prefixes, ctx, visited);
            }
        }
        TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
    }
}

/// Rewrite all type paths in a signature by replacing path prefix `old_prefix`
/// with `new_prefix`. Used when resolving module aliases like `module J = Js.Json`:
/// rewrites `Pdot(Pdot(Pident("Js"), "Json"), "Kind")` → `Pdot(Pident("J"), "Kind")`.
pub fn rewrite_sig_by_path_prefix(
    sig_items: &[SignatureItem],
    old_prefix: &Path,
    new_prefix: &Arc<Path>,
    ctx: &TypeContext,
) {
    let mut visited = visit_set();

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
    let mut visited = visit_set();

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
    let parent_maps = build_subst_maps(sig_items, module_path, ctx);

    for item in sig_items {
        if let SignatureItem::SigModule(id, md, _) = item {
            let sub_path = module_path_target(
                id,
                &parent_maps.module_stamp_map,
                &parent_maps.module_name_map,
                parent_maps.protected_module_head.as_ref(),
            )
            .expect("child module has no prefix substitution");
            if let ModuleType::MtySignature(sub_sig) = &md.md_type {
                substitute_type_paths_in_sig_with_maps(sub_sig, &parent_maps, ctx);
                restore_child_self_manifests_from_parent_scope(
                    sub_sig,
                    sig_items,
                    module_path,
                    ctx,
                );
                substitute_type_paths_in_sig(sub_sig, sub_path, ctx);
                substitute_submodule_paths(sub_sig, sub_path, ctx);
            }
        }
    }
}

trait AliasRewriteSink {
    fn has_alias_rewrite(&self, key: Name) -> bool;
    fn insert_alias_rewrite_if_absent(&mut self, key: Name, value: Path);
}

impl AliasRewriteSink for HashMap<String, Path> {
    fn has_alias_rewrite(&self, key: Name) -> bool {
        self.contains_key(key.as_str())
    }

    fn insert_alias_rewrite_if_absent(&mut self, key: Name, value: Path) {
        self.entry(key.to_string()).or_insert(value);
    }
}

impl AliasRewriteSink for UnitAliasRewrites {
    fn has_alias_rewrite(&self, key: Name) -> bool {
        self.contains_key(&key)
    }

    fn insert_alias_rewrite_if_absent(&mut self, key: Name, value: Path) {
        self.entry(key).or_insert(value);
    }
}

impl AliasRewriteSink for AliasPrefixRewrites {
    fn has_alias_rewrite(&self, key: Name) -> bool {
        self.contains(key)
    }

    fn insert_alias_rewrite_if_absent(&mut self, key: Name, value: Path) {
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
            if let ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) = &md.md_type {
                let alias_path = md.md_type.ident_or_alias_path().unwrap();
                // OCaml compiler/ml/env.ml:1517 scrapes aliases before
                // env.ml:1530-1538 prefixes component identifiers. Rust can store
                // that alias-shaped module as either MtyAlias or MtyIdent after CMI
                // loading, so record both forms for flattened namespace units such
                // as `Webapi__Fetch`.
                // Only the first mapping for a name is kept; skip building
                // the key and path for names already mapped.
                if let PathView::Pident(alias_id) = alias_path.view()
                    && !rewrites.has_alias_rewrite(alias_id.name_atom())
                {
                    let qualified = Path::pdot(*module_path, id.name_atom());
                    rewrites.insert_alias_rewrite_if_absent(alias_id.name_atom(), qualified);
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

pub(crate) fn open_module_components_into_env(
    components: crate::types::env_lazy::Components<'_>,
    root: Path,
    env: &mut Env,
    ctx: &TypeContext,
    slot: Option<u32>,
) {
    // OCaml compiler/ml/env.ml:1874-1877 calls `get_components
    // (find_module_descr root)` and compiler/ml/env.ml:1841-1860 installs that
    // same component table into the opened environment. Reuse the component view
    // that module lookup already forced so opened `comp_modules` and
    // `comp_components` share the same lazy state.
    open_components_into_env(components, root, env, ctx, slot);
}

/// Where `add_signature_to_env_with_options_inner` puts what an open
/// installs.
enum OpenedOut<'a> {
    /// The layer tables, for the caller to attach.
    Layers(&'a mut Option<crate::types::env::OpenedLayers>),
    /// The items themselves, for a world view.
    Items(&'a mut crate::types::module_view::OpenedItems),
}

/// The layer tables that opening the component table `components` adds.
fn build_opened_layers(
    components: &crate::types::env_lazy::QualifiedModuleComponents,
    ctx: &TypeContext,
) -> crate::types::env::OpenedLayers {
    let mut out = None;
    add_signature_to_env_with_options_inner(
        components.signature(),
        components.access_path(),
        &mut Env::empty(),
        ctx,
        true,
        false,
        Some(crate::types::env_lazy::Components::Local(components)),
        OpenedOut::Layers(&mut out),
    );
    out.expect("opened layers built")
}

/// What `open` installs for the view being built (env.ml:1841-1877 opens
/// the component table as is), described on the build's scratch context.
/// One pass over the view's signature; one description per constructor.
pub(crate) fn opened_items_of_view(
    view: &Arc<crate::types::module_view::ModuleView>,
    ctx: &TypeContext,
) -> crate::types::module_view::OpenedItems {
    let mut items = Default::default();
    add_signature_to_env_with_options_inner(
        view.signature(),
        view.access_path(),
        &mut Env::empty(),
        ctx,
        true,
        false,
        Some(crate::types::env_lazy::Components::World(view)),
        OpenedOut::Items(&mut items),
    );
    items
}

/// Open the component view `components` into `env`, reusing the view's
/// layer tables when another Env already opened it.
fn open_components_into_env(
    components: crate::types::env_lazy::Components<'_>,
    root: Path,
    env: &mut Env,
    ctx: &TypeContext,
    slot: Option<u32>,
) {
    use crate::types::env_lazy::Components;
    let layers = match components {
        Components::World(view) => ctx.thread_store().view_tables(view).opened_layers(view, ctx),
        Components::Local(components) => {
            components.opened_layers(ctx, || build_opened_layers(components, ctx))
        }
    };
    env.add_prebuilt_open_layers(root, &layers, slot);
}

#[allow(clippy::too_many_arguments)]
fn add_signature_to_env_with_options_inner(
    sig_items: &[SignatureItem],
    module_path: &Path,
    env: &mut Env,
    ctx: &TypeContext,
    as_opened: bool,
    apply_path_subst: bool,
    precomputed_components: Option<crate::types::env_lazy::Components<'_>>,
    opened_out: OpenedOut<'_>,
) {
    let collect_items = matches!(opened_out, OpenedOut::Items(_));
    // For `OpenedOut::Items`: whether each opened module is a direct alias
    // of a persistent unit.
    let mut opened_module_aliases = Vec::new();
    // Apply path substitution: rewrite Tconstr paths from internal
    // (e.g., Pident "ref") to qualified (e.g., Pdot(Pident "Pervasives") "ref").
    // This matches OCaml's `prefix_idents` + `Subst.type_path` mechanism.
    if apply_path_subst {
        substitute_type_paths_in_sig(sig_items, module_path, ctx);
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
            .get_or_insert_with(|| build_subst_maps_for_module(sig_items, module_path, ctx));
        substitute_type_path(
            ctx,
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
                                        crate::types::typecore::inline_record_type_params(
                                            ctx, labels,
                                        );
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
                                        type_shape: crate::types::ValueShape::Unstated,
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

                            // `comp_labels` holds `labels_of_type`, which describes
                            // no labels for a variant (datarepr.ml:292-298): an
                            // inline record's labels are reached through its
                            // constructor (`cstr_inlined`), never by name.
                            if as_opened {
                                opened_constructors.push((cd.cd_id, cstr_desc));
                            } else {
                                env.add_constructor(cd.cd_id, cstr_desc);
                            }
                        }
                    }
                    TypeKind::TypeRecord(labels, _) => {
                        // `add_components` opens the component table's
                        // `comp_labels` (compiler/ml/env.ml:1841-1860): the
                        // array stored with the type in `comp_types`.
                        // An open installs the component table's own labels
                        // (env.ml:1874-1877 opens `find_module_descr root`).
                        // A record without fields describes no labels.
                        let descs = if labels.is_empty() {
                            Vec::new()
                        } else {
                            let components = precomputed_components
                                .expect("an open installs a module's component table");
                            let family = components
                                .type_label_family(id.name(), ctx)
                                .expect("a record type of a component has its label family");
                            ctx.label_family(family)
                                .expect("a component label family is registered")
                                .as_ref()
                                .clone()
                        };
                        for (ld, label_desc) in labels.iter().zip(descs) {
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
                        let rewritten = normalize_hidden_alias_path(substitute_path(&alias_path));
                        // An unrewritten target keeps its block.
                        let target = if rewritten.same(&alias_path) {
                            alias_path
                        } else {
                            Arc::new(rewritten)
                        };
                        ModuleType::MtyAlias(alias_presence, target)
                    }
                    ModuleType::MtyIdent(path) => {
                        let rewritten = substitute_path(&path);
                        ModuleType::MtyIdent(normalize_hidden_alias_path(rewritten))
                    }
                    other => other,
                };
                if as_opened {
                    let direct_persistent_alias = matches!(
                        md.md_type.ident_or_alias_path().map(|p| p.view()),
                        Some(PathView::Pident(alias_id)) if alias_id.is_persistent()
                    );
                    if collect_items {
                        // A view records the module; each worker creates its
                        // component thunk (`env_lazy::ViewTables`).
                        opened_module_aliases.push(direct_persistent_alias);
                        opened_modules.push((*id, md.clone(), module_pos));
                    } else if direct_persistent_alias && precomputed_components.is_some() {
                        // OCaml compiler/ml/env.ml:1516-1518 scrapes a
                        // direct persistent child alias through env.ml:865-875
                        // `find_module`, so the child component table does not
                        // need the parent component environment. Avoid forcing
                        // the parent's `comp_components` just to open an
                        // equivalent persistent-alias thunk.
                        let stored = Rc::new(crate::types::env_lazy::StoredModuleComponents::new(
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
        if let OpenedOut::Items(items) = opened_out {
            *items = crate::types::module_view::OpenedItems {
                values: opened_values
                    .into_iter()
                    .map(|(id, desc, pos)| (id, Arc::new(desc), pos))
                    .collect(),
                types: opened_types,
                constructors: opened_constructors
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
                labels: opened_labels
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
                modules: opened_modules
                    .into_iter()
                    .zip(opened_module_aliases)
                    .map(|((id, decl, pos), direct_persistent_alias)| {
                        crate::types::module_view::OpenedModule {
                            id,
                            decl: Arc::new(decl),
                            pos,
                            direct_persistent_alias,
                        }
                    })
                    .collect(),
                modtypes: opened_modtypes
                    .into_iter()
                    .map(|(id, decl)| (id, Arc::new(decl)))
                    .collect(),
            };
            return;
        }
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
            OpenedOut::Layers(out) => *out = Some(layers),
            OpenedOut::Items(_) => unreachable!("returned above"),
        }
    }
}

#[cfg(test)]
mod resolution_view_tests {
    use super::*;
    use crate::context::IdGenerator;

    fn alias_module(name: &str, target: &str) -> SignatureItem {
        SignatureItem::SigModule(
            Ident::create_persistent(name),
            ModuleDeclaration {
                md_type: ModuleType::MtyAlias(
                    AliasPresence::MtaAbsent,
                    Arc::new(Path::pident(Ident::create_persistent(target))),
                ),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
            RecStatus::TrecNot,
        )
    }

    /// `module A = Unit_A`, `module B = Unit_B`, `module Again = Unit_A` and
    /// `module Inner: { module C = Unit_C }`.
    fn unit_with_aliases(name: &str) -> PersStruct {
        let inner = SignatureItem::SigModule(
            Ident::create_persistent("Inner"),
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(Arc::new(vec![alias_module("C", "Unit_C")])),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
            RecStatus::TrecNot,
        );
        PersStruct {
            ps_name: name.to_string(),
            ps_sig: Arc::new(vec![
                alias_module("A", "Unit_A"),
                alias_module("B", "Unit_B"),
                alias_module("Again", "Unit_A"),
                inner,
            ]),
            ps_filename: format!("{name}.res"),
            ps_deprecated: None,
            ps_crcs: Vec::new(),
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        }
    }

    /// What every reader of the rewrites sees, in a comparable form.
    fn alias_rewrite_readings(rewrites: &AliasPrefixRewrites) -> Vec<String> {
        let mut readings = Vec::new();
        for flat in ["Unit_A", "Unit_B", "Unit_C", "Late", "Unknown"] {
            let path = rewrites.get(flat);
            readings.push(format!("{flat} -> {:?}", path.map(|path| path.name())));
            if let Some(path) = path {
                let mut heads = rewrites.flattened_alias_heads_for_path(&path);
                heads.sort();
                readings.push(format!("{} <- {heads:?}", path.name()));
            }
        }
        let mut all: Vec<_> = rewrites
            .to_hash_map()
            .into_iter()
            .map(|(flat, path)| format!("{flat}={}", path.name()))
            .collect();
        all.sort();
        readings.push(format!("all: {all:?}"));
        let mut recorded: Vec<_> = rewrites
            .recorded()
            .into_iter()
            .map(|(flat, path)| format!("{flat}={}", path.name()))
            .collect();
        recorded.sort();
        readings.push(format!("recorded: {recorded:?}"));
        readings
    }

    #[test]
    fn a_units_alias_table_reads_like_recording_each_of_its_rewrites() {
        let first = unit_with_aliases("First");
        let second = unit_with_aliases("Second");
        // `walked` records every rewrite as the signatures are walked,
        // `shared` adds each unit's table.
        let mut walked = AliasPrefixRewrites::new();
        let mut shared = AliasPrefixRewrites::new();
        let earlier = Path::pident(Ident::create_persistent("Earlier"));
        let late = Path::pident(Ident::create_persistent("Late_target"));
        for rewrites in [&mut walked, &mut shared] {
            // Known before either unit is loaded: it wins over both.
            rewrites.insert_if_absent(Name::new("Unit_B"), earlier);
        }
        for unit in [&first, &second] {
            let unit_path = Path::pident(Ident::create_persistent(&unit.ps_name));
            collect_alias_rewrites(&unit.ps_sig, &unit_path, &mut walked);
            shared.add_unit(unit.own_alias_rewrites().expect("the unit has aliases"));
            // Adding a unit again changes nothing.
            shared.add_unit(unit.own_alias_rewrites().expect("the unit has aliases"));
        }
        for rewrites in [&mut walked, &mut shared] {
            // Recorded after the units: a name they hold stays theirs.
            rewrites.insert_if_absent(Name::new("Unit_A"), late);
            rewrites.insert_if_absent(Name::new("Late"), late);
        }

        assert_eq!(shared.units.len(), 2);
        assert_eq!(
            alias_rewrite_readings(&shared),
            alias_rewrite_readings(&walked)
        );
        assert_eq!(
            shared.get("Unit_A").map(|path| path.name()).as_deref(),
            Some("First.A")
        );
        assert_eq!(
            shared.get("Unit_B").map(|path| path.name()).as_deref(),
            Some("Earlier")
        );
        assert_eq!(
            shared.get("Unit_C").map(|path| path.name()).as_deref(),
            Some("First.Inner.C")
        );
    }

    #[test]
    fn a_loaded_unit_shares_its_alias_table_unless_it_is_reached_through_an_alias() {
        let unit = unit_with_aliases("Shared");
        let mut own_name = PersistentEnv::new();
        own_name.record_alias_rewrites("Shared", &unit);
        let table = unit.own_alias_rewrites().expect("the unit has aliases");
        assert!(own_name.view.alias_prefix_rewrites.local.is_empty());
        assert_eq!(own_name.view.alias_prefix_rewrites.units.len(), 1);
        assert!(Arc::ptr_eq(
            &own_name.view.alias_prefix_rewrites.units[0],
            table
        ));

        // Reached as `Outer.Shared`: its rewrites carry that prefix, so they
        // are recorded for this compilation only.
        let mut aliased = PersistentEnv::new();
        aliased.view_mut().alias_prefix_rewrites.insert_if_absent(
            Name::new("Shared"),
            Path::pdot(Path::pident(Ident::create_persistent("Outer")), "Shared"),
        );
        aliased.record_alias_rewrites("Shared", &unit);
        assert!(aliased.view.alias_prefix_rewrites.units.is_empty());
        assert_eq!(
            aliased
                .view
                .alias_prefix_rewrites
                .get("Unit_C")
                .map(|path| path.name())
                .as_deref(),
            Some("Outer.Shared.Inner.C")
        );

        // A unit without aliases costs a compilation nothing.
        let plain = PersStruct {
            ps_sig: Arc::new(Vec::new()),
            ..unit_with_aliases("Plain")
        };
        let mut env = PersistentEnv::new();
        let view = env.view.clone();
        env.record_alias_rewrites("Plain", &plain);
        assert!(Arc::ptr_eq(&env.view, &view));
    }

    #[test]
    fn cloned_views_share_reads_but_isolate_every_owned_overlay() {
        let mut original = PersistentEnv::new();
        original.set_compiling_module(Some("Original".to_string()));
        original.register_in_memory_module(
            "Original",
            InMemoryModuleInfo::new(PathBuf::from("original.res"), true, HashMap::new(), false),
        );
        original
            .overrides_mut()
            .source_fallback_path_overrides
            .insert("Source".to_string(), PathBuf::from("source.res"));
        original
            .overrides_mut()
            .hidden_modules
            .insert("Hidden".to_string());
        original
            .view_mut()
            .prepared_cached_alias_rewrites
            .insert(Name::new("Prepared"));
        original.view_mut().alias_prefix_rewrites.insert_if_absent(
            Name::new("Backing"),
            Path::pident(Ident::create_persistent("Selected")),
        );
        let mut query = original.clone();
        assert!(Arc::ptr_eq(&original.view, &query.view));
        assert!(query.is_compiling_module("Original"));
        assert!(Arc::ptr_eq(&original.view, &query.view));

        query.set_compiling_module(Some("Query".to_string()));
        query.overrides_mut().source_fallback_path_overrides.clear();
        query.overrides_mut().in_memory_module_overrides.clear();
        query.overrides_mut().hidden_modules.clear();
        query.view_mut().prepared_cached_alias_rewrites.clear();
        query.view_mut().alias_prefix_rewrites.local.clear();
        assert!(!Arc::ptr_eq(&original.view, &query.view));
        assert!(original.is_compiling_module("Original"));
        assert_eq!(original.view.overrides.source_fallback_path_overrides.len(), 1);
        assert_eq!(original.view.overrides.in_memory_module_overrides.len(), 1);
        assert!(original.view.overrides.hidden_modules.contains("Hidden"));
        assert!(
            original
                .view
                .prepared_cached_alias_rewrites
                .contains(&Name::new("Prepared"))
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
                .contains(&Name::new("Other"))
        );
        assert!(cold.view.prepared_cached_alias_rewrites.contains(&Name::new("Other")));
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
            .overrides_mut()
            .portable_cache_overrides
            .insert("Portable".to_string(), portable.clone());
        let mut query = original.clone();
        query
            .overrides_mut()
            .portable_cache_overrides
            .insert("Other".to_string(), portable.clone());
        assert!(!Arc::ptr_eq(&original.view, &query.view));
        assert!(!original.view.overrides.portable_cache_overrides.contains_key("Other"));
        assert!(Arc::ptr_eq(
            &original.view.overrides.portable_cache_overrides["Portable"],
            &query.view.overrides.portable_cache_overrides["Portable"]
        ));
        assert!(Arc::ptr_eq(
            &portable,
            &query.view.overrides.portable_cache_overrides["Other"]
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
                .overrides_mut()
                .source_fallback_path_overrides
                .insert(name.to_string(), path);
        }
        original
            .view_mut()
            .prepared_cached_alias_rewrites
            .insert(Name::new("AlreadyPrepared"));
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
                    .contains(&Name::new("AlreadyPrepared"))
            );
        }
        assert!(
            original
                .view
                .prepared_cached_alias_rewrites
                .contains(&Name::new("AlreadyPrepared"))
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
        // The references of the signature itself come with it, unless it
        // is registered under another name than its own.
        let summary = ps.summary();
        let own_refs = (summary.unit == unit).then(|| &summary.refs);
        let lambdas = if self.lambdas {
            registry
                .with_info(&unit, |info| Arc::as_ptr(&info.cmj_export_lambdas) as usize)
                .unwrap_or(0)
        } else if let Some(refs) = own_refs {
            return Some(refs.clone());
        } else {
            usize::MAX
        };
        let key = (unit, Arc::as_ptr(&ps) as usize, ps.fingerprint, lambdas);
        if let Some(refs) = registry.item_refs_cache.read().unwrap().get(&key) {
            return Some(refs.clone());
        }
        let signature_refs = match own_refs {
            Some(refs) => refs.clone(),
            None => Arc::new(super::item_deps::signature_refs(unit, &ps.signature())),
        };
        let refs = if self.lambdas {
            Arc::new(super::item_deps::with_lambda_units(&signature_refs, unit, self))
        } else {
            signature_refs
        };
        registry
            .item_refs_cache
            .write()
            .unwrap()
            .insert(key, refs.clone());
        Some(refs)
    }
}

#[cfg(test)]
mod snapshot_index_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Index { decodes: AtomicUsize, prefix: char }
    impl SnapshotModules for Index {
        fn find(&self, name: &str) -> Option<u32> {
            name.strip_prefix(self.prefix)?.parse::<u32>().ok().filter(|&slot| slot < 10_000)
        }
        fn decode(&self, slot: u32) -> Option<super::super::stored_module::StoredCore> {
            self.decodes.fetch_add(1, Ordering::Relaxed);
            Some(super::super::stored_module::StoredCore {
                pers_struct: None,
                info: InMemoryModuleInfo::new(PathBuf::from(format!("M{slot}.res")), true, HashMap::new(), false),
            })
        }
    }

    #[test]
    fn snapshot_of_ten_thousand_modules_decodes_only_requested_slots() {
        let index = Arc::new(Index { decodes: AtomicUsize::new(0), prefix: 'M' });
        let mut registry = ModuleRegistry::new();
        registry.register_snapshot(index.clone());
        let other = Arc::new(Index { decodes: AtomicUsize::new(0), prefix: 'N' });
        registry.register_snapshot(other.clone());
        assert!(!registry.is_empty());
        assert!(registry.is_pending_stored("M9999"));
        assert_eq!(index.decodes.load(Ordering::Relaxed), 0);
        for _ in 0..10_000 {
            assert!(registry.module_info.with_value("M7", |info| info.is_pure).unwrap());
        }
        assert_eq!(index.decodes.load(Ordering::Relaxed), 1);
        assert!(registry.module_info.with_value("M9999", |info| info.is_pure).unwrap());
        assert_eq!(index.decodes.load(Ordering::Relaxed), 2);
        assert!(registry.module_info.with_value("M10000", |_| ()).is_none());
        assert_eq!(index.decodes.load(Ordering::Relaxed), 2);
        assert_eq!(other.decodes.load(Ordering::Relaxed), 0);
        assert!(registry.module_info.with_value("N7", |_| ()).is_some());
        assert_eq!(other.decodes.load(Ordering::Relaxed), 1);
    }
}

#[cfg(test)]
mod subst_map_hash_tests {
    /// 10,000 integers and 10,000 names (the key kinds of the substitution
    /// maps) must not share a hash: a first key of zero gives one hash for
    /// all of them, and every substitution map becomes one bucket.
    #[test]
    fn subst_map_hashes_are_distinct() {
        use std::hash::BuildHasher;
        let ints: std::collections::HashSet<u64> = (0..10_000i32)
            .map(|n| BuildHasher::hash_one(&super::SUBST_MAP_STATE, n))
            .collect();
        assert!(ints.len() >= 9_990, "{} distinct hashes of 10,000 integers", ints.len());
        let names: std::collections::HashSet<u64> = (0..10_000)
            .map(|n| {
                let name = crate::name::Name::new(&format!("t{n}"));
                BuildHasher::hash_one(&super::SUBST_MAP_STATE, name)
            })
            .collect();
        assert!(names.len() >= 9_990, "{} distinct hashes of 10,000 names", names.len());
    }
}
