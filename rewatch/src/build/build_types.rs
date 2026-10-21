use crate::build::packages::Package;
use crate::config::{Config, SourceMapCommand};
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use blake3::Hash;
use rescript_compiler::binary_ast::Dependencies;
use rescript_compiler::cmi::persistent_env::{CmjExportConstant, ModuleRegistry};
use rescript_compiler::cmi::portable_types::PortablePersStruct;
use rescript_compiler::parse_arena::ParseArena;
use rescript_compiler::parser::ast::{Signature, Structure};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::{fmt::Display, ops::Deref, path::PathBuf, time::SystemTime};

/// How rewatch compiles.
///
/// - `InProcess`: the Rust compiler linked into rewatch. This is the build.
/// - `ExternalBsc`: test-only, file-backed builds with an external compiler
///   executable, selected by `RESCRIPT_SUBPROCESS_BUILD` so parity scripts can
///   produce OCaml reference outputs.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BuildMode {
    /// External compiler executable, file-backed (test-only)
    ExternalBsc,
    /// Rust compiler fully in-process
    InProcess,
}

impl BuildMode {
    /// Whether parsing runs in this process with the Rust parser.
    pub fn use_rust_parser(&self) -> bool {
        matches!(self, BuildMode::InProcess)
    }

    /// Whether this mode uses in-process compilation with no disk artifacts
    pub fn is_in_process(&self) -> bool {
        matches!(self, BuildMode::InProcess)
    }
}

/// Per-module in-memory compilation state for `--in-process` builds.
///
/// Stores a generation number that replaces timestamp-based invalidation
/// (`last_compiled_cmi`/`last_compiled_cmt`).
/// When a module is recompiled and its interface changes, the generation is
/// bumped so downstream dependents know to recompile.
pub struct InMemoryModuleState {
    /// Monotonically increasing generation number. Bumped only when the
    /// module's published interface actually changes (fingerprint differs).
    /// Downstream dependents compare their recorded dependency generation
    /// against this to detect staleness.
    pub generation: u64,
    /// Stamp-independent structural fingerprint of the published interface.
    /// Used to detect whether a recompilation actually changed the interface.
    pub fingerprint: u64,
    /// Whether this module's source is pure (no side effects), used for
    /// JS import resolution.
    pub is_pure: bool,
    /// Digest of everything dependents compile against: the signature plus
    /// the JS metadata their code generation inlines (constants, arities,
    /// inlinable bodies). The signature fingerprint alone misses a change
    /// such as `let flag = true` becoming `false`.
    pub published_digest: Option<u64>,
}

impl std::fmt::Debug for InMemoryModuleState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InMemoryModuleState")
            .field("generation", &self.generation)
            .field("is_pure", &self.is_pure)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseState {
    Pending,
    ParseError,
    Warning,
    Success,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CompileState {
    Pending,
    Error,
    Warning,
    Success,
}
#[derive(Debug, Clone, PartialEq)]
pub struct Interface {
    pub path: PathBuf,
    pub parse_state: ParseState,
    pub compile_state: CompileState,
    pub last_modified: SystemTime,
    pub parse_dirty: bool,
    /// Compiler warning output (from bsc stderr) stored for re-emission
    /// during incremental builds when this module is not recompiled.
    /// Written to `.compiler.log` on each build cycle.
    pub compile_warnings: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Implementation {
    pub path: PathBuf,
    pub parse_state: ParseState,
    pub compile_state: CompileState,
    pub last_modified: SystemTime,
    pub parse_dirty: bool,
    /// Compiler warning output (from bsc stderr) stored for re-emission
    /// during incremental builds when this module is not recompiled.
    /// Written to `.compiler.log` on each build cycle.
    pub compile_warnings: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SourceFile {
    pub implementation: Implementation,
    pub interface: Option<Interface>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MlMap {
    pub parse_dirty: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SourceType {
    SourceFile(SourceFile),
    MlMap(MlMap),
}

impl Display for SourceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceType::SourceFile(_) => write!(f, "SourceFile"),
            SourceType::MlMap(_) => write!(f, "MlMap"),
        }
    }
}

#[derive(Debug)]
pub struct StoredStructureAst {
    pub arena: ParseArena,
    pub structure: Structure,
    pub source_len: usize,
}

#[derive(Debug)]
pub struct StoredSignatureAst {
    pub arena: ParseArena,
    pub signature: Signature,
    pub source_len: usize,
}

#[derive(Clone)]
pub enum StoredAst {
    Structure(Arc<StoredStructureAst>),
    Signature(Arc<StoredSignatureAst>),
}

impl std::fmt::Debug for StoredAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoredAst::Structure(_) => write!(f, "StoredAst::Structure(..)"),
            StoredAst::Signature(_) => write!(f, "StoredAst::Signature(..)"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub source_type: SourceType,
    pub deps: AHashSet<String>,
    pub dependents: AHashSet<String>,
    pub package_name: String,
    pub compile_dirty: bool,
    pub last_compiled_cmi: Option<SystemTime>,
    pub last_compiled_cmt: Option<SystemTime>,
    pub deps_dirty: bool,
    pub is_type_dev: bool,
}

impl Module {
    pub fn is_mlmap(&self) -> bool {
        matches!(self.source_type, SourceType::MlMap(_))
    }

    pub fn get_interface(&self) -> &Option<Interface> {
        match &self.source_type {
            SourceType::SourceFile(source_file) => &source_file.interface,
            _ => &None,
        }
    }
}

/// Core build state containing all the essential data needed for compilation.
/// This is the minimal state required for basic build operations like cleaning.
/// Used by commands that don't need command-line specific overrides (e.g., `clean`).
#[derive(Debug)]
pub struct BuildState {
    pub project_context: ProjectContext,
    pub modules: AHashMap<String, Module>,
    pub packages: AHashMap<String, Package>,
    pub module_names: AHashSet<String>,
    pub deleted_modules: AHashSet<String>,
    /// The output files each package's previous build recorded (see
    /// `state_db::META_OUTPUTS`), read before a compiler or configuration
    /// change cleans the package's build state.
    pub recorded_outputs: AHashMap<String, AHashSet<String>>,
    pub compiler_info: CompilerInfo,
    pub deps_initialized: bool,
    pub source_map_command: SourceMapCommand,
}

/// Parse warnings by source file (`Module:impl` or `Module:intf`), with the
/// package that reported them.
pub type ParseWarnings = Mutex<AHashMap<String, (String, String)>>;

pub struct GentypeCompileContext {
    pub config: Arc<rescript_compiler::gentype::config::T>,
    pub resolver: Arc<rescript_compiler::gentype::module_resolver::Resolver>,
}

/// Extended build state that includes command-line specific overrides.
/// Wraps `BuildState` and adds command-specific data like warning overrides.
/// Used by commands that need to respect CLI flags (e.g., `build`, `watch`).
///
/// The separation exists because:
/// - `clean` command only needs core build data, no CLI overrides
/// - `build`/`watch` commands need both core data AND CLI overrides
/// - This prevents the "code smell" of optional fields that are None for some commands
pub struct BuildCommandState {
    pub root_folder: PathBuf,
    pub build_state: BuildState,
    // Command-line --warn-error flag override (takes precedence over rescript.json config)
    pub warn_error_override: Option<String>,
    // The build mode (in-process, or the test-only external compiler)
    pub build_mode: BuildMode,
    // Command-line --dump-typed-sexp flag: add -dtyped-sexp to bsc invocations.
    pub dump_typed_sexp: bool,
    // Stored ASTs from parse phase, keyed by "{module_name}:impl" or "{module_name}:intf"
    pub stored_asts: Mutex<AHashMap<String, StoredAst>>,
    // In-memory published interfaces, keyed by module name. Only used in --in-process mode.
    // Maps module_name -> InMemoryModuleState.
    pub in_memory_interfaces: Mutex<AHashMap<String, InMemoryModuleState>>,
    // Monotonically increasing generation counter for in-memory interface invalidation.
    // Each compilation that produces a new interface bumps this counter.
    pub interface_generation: AtomicU64,
    // Shared module registry for --in-process mode. Contains all previously-published
    // module interfaces, metadata, and namespace aliases. Shared across parallel waves.
    pub module_registry: Mutex<ModuleRegistry>,
    // In-memory extracted dependencies from the parse phase for --in-process mode.
    // Keyed by "{module_name}:impl" or "{module_name}:intf" (matching stored_asts convention).
    // Values are the raw module names extracted from the parsed AST.
    pub in_memory_deps: Mutex<AHashMap<String, Dependencies>>,
    // The units each module's last compile in this process read the
    // interface of (type checking its interface and implementation, plus
    // the modules its generated code may require).
    pub loaded_units: Mutex<AHashMap<String, AHashSet<String>>>,
    // What the last compile of a module read of other units (see
    // `rescript_compiler::cmi::item_deps`), resolved when the build is
    // recorded.
    pub unit_reads: Mutex<AHashMap<String, PendingReads>>,
    // Recorded imports a build checked item by item and found unaffected:
    // module -> unit -> the unit's interface digest now.
    pub verified_imports: Mutex<AHashMap<String, AHashMap<String, u64>>>,
    // The alias rewrites each module registered, for its stored interface.
    pub module_alias_rewrites: Mutex<AHashMap<String, Vec<(String, rescript_compiler::types::path::Path)>>>,
    // The modules this build compiled (written or not).
    pub compiled_modules: AHashSet<String>,
    // The build stopped at a parse error, before planning: it compiled
    // nothing and leaves the previous build record in place.
    pub stopped_at_parse: bool,
    // Modules compiled after a dependency failed: their results were dropped,
    // but their JavaScript may have been written from the failed module's
    // incomplete metadata. The build record forgets what they imported, so
    // the next build recompiles them.
    pub invalidated_modules: AHashSet<String>,
    // The modules whose stored interface this build loaded instead of
    // compiling them.
    pub loaded_modules: AHashSet<String>,
    // Set while parsing modules whose saved parse warnings were already
    // reported this build: the parse then only records them.
    pub parse_warnings_replayed: bool,
    // The modules whose JavaScript this process wrote.
    pub written_modules: AHashSet<String>,
    // GenType config and resolver inputs are immutable within one compile wave.
    pub gentype_contexts: Mutex<AHashMap<PathBuf, Arc<GentypeCompileContext>>>,
    // In-process compiler options shared by every module of a package (keyed
    // by package path and whether the module is a dev source); immutable
    // within one compile wave like the GenType contexts.
    pub package_compiler_options:
        Mutex<AHashMap<(PathBuf, bool), Arc<rescript_compiler::driver::CompilerOptions>>>,
    // Command-line --features override. `None` means all features are active; `Some(list)`
    // restricts the root package to those features (and whatever they transitively imply).
    pub features: Option<Vec<String>>,
    // What the previous in-process build recorded (see `incremental`). Read
    // during initialization, in-process builds only.
    pub previous_in_process: Option<super::incremental::PreviousInProcessBuild>,
    // The incremental plan of a fresh in-process build, consumed by `compile`.
    pub incremental_plan: Option<super::incremental::IncrementalPlan>,
    // When the latest build started, and whether it finished without errors;
    // recorded in the in-process manifest.
    pub build_started_at: Option<std::time::SystemTime>,
    pub last_build_ok: bool,
    // The parse warnings of the latest parse of each source file, saved so a
    // build that parses nothing can report them again.
    pub parse_warnings: ParseWarnings,
    // When each module's JavaScript was last known to be up to date: the start
    // of the build that compiled it. Identical output is not rewritten, so the
    // file's own modification time can be older (see `incremental`).
    pub js_confirmed_at: AHashMap<String, std::time::SystemTime>,
    // Each source file's modification time (`Module:impl` / `Module:intf`),
    // read before it is parsed; recorded with its dependencies.
    pub source_mtimes: AHashMap<String, i64>,
}

impl std::fmt::Debug for BuildCommandState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BuildCommandState")
            .field("root_folder", &self.root_folder)
            .field("build_state", &self.build_state)
            .field("warn_error_override", &self.warn_error_override)
            .field("build_mode", &self.build_mode)
            .field("dump_typed_sexp", &self.dump_typed_sexp)
            .field("stored_asts", &"<Mutex<..>>")
            .field("in_memory_interfaces", &"<Mutex<..>>")
            .field(
                "interface_generation",
                &self.interface_generation.load(Ordering::Relaxed),
            )
            .field("module_registry", &"<Mutex<ModuleRegistry>>")
            .field("in_memory_deps", &"<Mutex<..>>")
            .field("gentype_contexts", &"<Mutex<..>>")
            .field("features", &self.features)
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct CompilerInfo {
    pub bsc_path: PathBuf,
    pub bsc_hash: Hash,
    pub runtime_path: PathBuf,
}

impl BuildState {
    pub fn get_package(&self, package_name: &str) -> Option<&Package> {
        self.packages.get(package_name)
    }

    pub fn get_module(&self, module_name: &str) -> Option<&Module> {
        self.modules.get(module_name)
    }

    pub fn new(
        project_context: ProjectContext,
        packages: AHashMap<String, Package>,
        compiler: CompilerInfo,
        source_map_command: SourceMapCommand,
    ) -> Self {
        Self {
            project_context,
            module_names: AHashSet::new(),
            modules: AHashMap::new(),
            packages,
            deleted_modules: AHashSet::new(),
            recorded_outputs: AHashMap::new(),
            compiler_info: compiler,
            deps_initialized: false,
            source_map_command,
        }
    }

    pub fn insert_module(&mut self, module_name: &str, module: Module) {
        self.modules.insert(module_name.to_owned(), module);
        self.module_names.insert(module_name.to_owned());
    }

    pub fn get_root_config(&self) -> &Config {
        self.project_context.get_root_config()
    }
}

impl BuildCommandState {
    pub fn new(
        root_folder: PathBuf,
        project_context: ProjectContext,
        packages: AHashMap<String, Package>,
        compiler: CompilerInfo,
        warn_error_override: Option<String>,
        build_mode: BuildMode,
        dump_typed_sexp: bool,
        features: Option<Vec<String>>,
        source_map_command: SourceMapCommand,
    ) -> Self {
        Self {
            root_folder,
            build_state: BuildState::new(project_context, packages, compiler, source_map_command),
            warn_error_override,
            build_mode,
            dump_typed_sexp,
            stored_asts: Mutex::new(AHashMap::new()),
            in_memory_interfaces: Mutex::new(AHashMap::new()),
            interface_generation: AtomicU64::new(0),
            module_registry: Mutex::new(ModuleRegistry::new()),
            in_memory_deps: Mutex::new(AHashMap::new()),
            loaded_units: Mutex::new(AHashMap::new()),
            unit_reads: Mutex::new(AHashMap::new()),
            verified_imports: Mutex::new(AHashMap::new()),
            module_alias_rewrites: Mutex::new(AHashMap::new()),
            compiled_modules: AHashSet::new(),
            stopped_at_parse: false,
            invalidated_modules: AHashSet::new(),
            loaded_modules: AHashSet::new(),
            parse_warnings_replayed: false,
            written_modules: AHashSet::new(),
            gentype_contexts: Mutex::new(AHashMap::new()),
            package_compiler_options: Mutex::new(AHashMap::new()),
            features,
            previous_in_process: None,
            incremental_plan: None,
            build_started_at: None,
            last_build_ok: false,
            parse_warnings: Mutex::new(AHashMap::new()),
            js_confirmed_at: AHashMap::new(),
            source_mtimes: AHashMap::new(),
        }
    }

    pub fn gentype_context(
        &self,
        package_path: &std::path::Path,
        build_config: impl FnOnce() -> rescript_compiler::gentype::config::T,
    ) -> Arc<GentypeCompileContext> {
        let mut contexts = self.gentype_contexts.lock().unwrap();
        contexts
            .entry(package_path.to_path_buf())
            .or_insert_with(|| {
                let config = Arc::new(build_config());
                let resolver = Arc::new(rescript_compiler::gentype::module_resolver::create_lazy_resolver(
                    &config,
                    &[".res".to_string(), ".shim.ts".to_string()],
                    |fname| fname == "React.res" || fname == "ReasonReact.res",
                ));
                Arc::new(GentypeCompileContext { config, resolver })
            })
            .clone()
    }

    pub fn clear_gentype_contexts(&self) {
        self.gentype_contexts.lock().unwrap().clear();
        self.package_compiler_options.lock().unwrap().clear();
    }

    pub fn get_warn_error_override(&self) -> Option<String> {
        self.warn_error_override.clone()
    }

    pub fn build_mode(&self) -> BuildMode {
        self.build_mode
    }

    pub fn use_rust_parser(&self) -> bool {
        self.build_mode.use_rust_parser()
    }

    pub fn dump_typed_sexp(&self) -> bool {
        self.dump_typed_sexp
    }

    pub fn get_features(&self) -> Option<Vec<String>> {
        self.features.clone()
    }

    /// Allocate the next interface generation number.
    pub fn next_interface_generation(&self) -> u64 {
        self.interface_generation.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Register a compiled module's interface in the in-memory registry.
    /// Only bumps the generation counter if the interface fingerprint actually
    /// changed (or if this is the first registration). Returns the generation
    /// number assigned (which may be the same as before if unchanged).
    /// Record units a compile of `module_name` read. An interface compile
    /// records first, then its implementation adds to it.
    pub fn record_loaded_units(&self, module_name: &str, units: Vec<String>, reads: PendingReads) {
        let mut loaded = self.loaded_units.lock().unwrap();
        let entry = loaded.entry(module_name.to_string()).or_default();
        entry.extend(units.into_iter().filter(|unit| unit != module_name));
        drop(loaded);
        let mut all_reads = self.unit_reads.lock().unwrap();
        let entry = all_reads.entry(module_name.to_string()).or_default();
        for (unit, keys) in reads.resolved {
            if unit != module_name {
                entry.resolved.entry(unit).or_default().extend(keys);
            }
        }
        entry.module_level.extend(reads.module_level);
    }

    pub fn register_in_memory_interface(&self, module_name: String, fingerprint: u64, is_pure: bool) -> u64 {
        let mut interfaces = self.in_memory_interfaces.lock().unwrap();
        // Check if the existing interface has the same fingerprint
        if let Some(existing) = interfaces.get(&module_name)
            && existing.fingerprint == fingerprint
        {
            // Interface unchanged — keep the same generation number
            return existing.generation;
        }
        // Interface changed (or first registration) — bump generation
        let generation = self.next_interface_generation();
        let state = InMemoryModuleState {
            generation,
            fingerprint,
            is_pure,
            published_digest: None,
        };
        interfaces.insert(module_name, state);
        generation
    }

    /// Get the current generation number for a module's published interface.
    /// Returns None if the module has not been compiled yet in this session.
    pub fn get_interface_generation(&self, module_name: &str) -> Option<u64> {
        self.in_memory_interfaces
            .lock()
            .unwrap()
            .get(module_name)
            .map(|s| s.generation)
    }

    /// Record the digest of what dependents compile against of a module whose
    /// JS metadata is final (see [`InMemoryModuleState::published_digest`]).
    /// Returns whether it equals the digest recorded when the module was last
    /// compiled with the same signature.
    pub fn record_published_digest(&self, module_name: &str) -> bool {
        let digest = self
            .module_registry
            .lock()
            .unwrap()
            .item_digests(module_name)
            .and_then(|digests| digests.get(rescript_compiler::cmi::item_deps::WHOLE).copied());
        let mut interfaces = self.in_memory_interfaces.lock().unwrap();
        let Some(state) = interfaces.get_mut(module_name) else {
            return false;
        };
        let previous = std::mem::replace(&mut state.published_digest, digest);
        previous.is_some() && previous == digest
    }

    /// Purge deleted/renamed modules from the in-memory registries.
    /// Must be called before compilation when modules have been removed from the
    /// build graph (e.g., source file deleted or renamed in watch mode).
    pub fn purge_deleted_modules(&self, deleted_modules: &ahash::AHashSet<String>) {
        if deleted_modules.is_empty() {
            return;
        }
        let mut registry = self.module_registry.lock().unwrap();
        let mut interfaces = self.in_memory_interfaces.lock().unwrap();
        for name in deleted_modules {
            registry.purge_module(name);
            interfaces.remove(name);
        }
    }

    /// Take a snapshot of the module registry for use during a compilation wave.
    /// Each worker in a parallel wave gets a clone of this snapshot.
    pub fn snapshot_module_registry(&self) -> ModuleRegistry {
        self.module_registry.lock().unwrap().for_worker_snapshot()
    }

    /// Update the module registry with a compiled module's portable PersStruct.
    pub fn update_module_registry(
        &self,
        module_name: &str,
        pers_struct: PortablePersStruct,
        source_path: std::path::PathBuf,
        is_pure: bool,
        cmj_export_constants: AHashMap<String, CmjExportConstant>,
        is_runtime: bool,
        new_alias_rewrites: ahash::AHashMap<String, rescript_compiler::types::path::Path>,
    ) {
        self.update_module_registry_arc(
            module_name,
            Arc::new(pers_struct),
            source_path,
            is_pure,
            cmj_export_constants,
            is_runtime,
            new_alias_rewrites,
        );
    }

    /// Update the module registry with a compiled module's shared portable PersStruct.
    pub fn update_module_registry_arc(
        &self,
        module_name: &str,
        pers_struct: Arc<PortablePersStruct>,
        source_path: std::path::PathBuf,
        is_pure: bool,
        cmj_export_constants: AHashMap<String, CmjExportConstant>,
        is_runtime: bool,
        new_alias_rewrites: ahash::AHashMap<String, rescript_compiler::types::path::Path>,
    ) {
        let info = rescript_compiler::cmi::persistent_env::InMemoryModuleInfo::new(
            source_path,
            is_pure,
            cmj_export_constants,
            is_runtime,
        );
        self.module_registry.lock().unwrap().register_module_arc(
            module_name,
            pers_struct,
            info,
            new_alias_rewrites,
        );
    }

    /// Register a namespace in the module registry.
    pub fn register_namespace_in_registry(
        &self,
        namespace_name: &str,
        module_aliases: &[(String, String)],
        package_root: PathBuf,
        crcs: Vec<(String, Option<[u8; 16]>)>,
    ) {
        self.module_registry
            .lock()
            .unwrap()
            .register_namespace_for_package(namespace_name, module_aliases, Some(package_root), crcs);
    }

    /// Store extracted dependencies from the parse phase for a module file.
    /// Key should be "{module_name}:impl" or "{module_name}:intf".
    pub fn store_in_memory_deps(&self, key: String, deps: Dependencies) {
        self.in_memory_deps.lock().unwrap().insert(key, deps);
    }

    /// Get the extracted dependencies for a module file.
    /// Returns None if no deps have been stored (e.g., not in --in-process mode).
    pub fn get_in_memory_deps(&self, key: &str) -> Option<Dependencies> {
        self.in_memory_deps.lock().unwrap().get(key).cloned()
    }

    /// Clone the complete parse-phase dependency table once for a dependency
    /// resolution pass. In-process builds resolve all module deps after parsing,
    /// so the table is stable and parallel workers should not contend on the
    /// mutex for every module lookup.
    pub fn snapshot_in_memory_deps(&self) -> AHashMap<String, Dependencies> {
        self.in_memory_deps.lock().unwrap().clone()
    }

    /// Clone the parse-phase AST table once for an in-process compile wave.
    /// Stored AST payloads are already behind `Arc`, so this keeps worker
    /// lookups immutable and avoids a contended mutex plus per-lookup Arc
    /// cloning while modules compile in parallel.
    pub fn snapshot_stored_asts(&self) -> AHashMap<String, StoredAst> {
        self.stored_asts.lock().unwrap().clone()
    }

    pub fn module_name_package_pairs(&self) -> Vec<(String, String)> {
        self.build_state
            .modules
            .iter()
            .map(|(name, module)| (name.clone(), module.package_name.clone()))
            .collect()
    }
}

// Implement Deref to automatically delegate method calls to the inner BuildState
impl Deref for BuildCommandState {
    type Target = BuildState;

    fn deref(&self) -> &Self::Target {
        &self.build_state
    }
}

// Implement DerefMut to allow mutable access to the inner BuildState
impl std::ops::DerefMut for BuildCommandState {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.build_state
    }
}

#[derive(Debug)]
pub struct AstModule {
    pub module_name: String,
    pub package_name: String,
    pub last_modified: SystemTime,
    pub ast_file_path: PathBuf,
    pub suffix: String,
}

#[derive(Debug)]
pub struct CompileAssetsState {
    pub ast_modules: AHashMap<PathBuf, AstModule>,
    pub cmi_modules: AHashMap<String, SystemTime>,
    pub cmt_modules: AHashMap<String, SystemTime>,
    pub ast_rescript_file_locations: AHashSet<PathBuf>,
    pub rescript_file_locations: AHashSet<PathBuf>,
}

/// What a compile read of other units: the item keys read through the
/// units' signatures (final when the module compiles). What the inlinable
/// bodies of those items refer to comes from JS metadata a dependency may
/// publish after this compile, so it is added when the build is recorded
/// (`ModuleRegistry::lambda_reads`).
#[derive(Debug, Default)]
pub struct PendingReads {
    pub resolved: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
    /// Units read only at module level (the modules the generated code may
    /// require).
    pub module_level: Vec<String>,
}
