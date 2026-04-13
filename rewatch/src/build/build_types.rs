use crate::build::packages::{Namespace, Package};
use crate::config::Config;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use blake3::Hash;
use rescript_compiler::cmi::persistent_env::PersistentEnv;
use rescript_compiler::parse_arena::ParseArena;
use rescript_compiler::parser::ast::{Signature, Structure};
use rescript_compiler::types::Signature as DeclSignature;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::{fmt::Display, ops::Deref, path::PathBuf, time::SystemTime};

/// The three explicit build modes for rewatch.
///
/// - `Default`: OCaml/file-backed build (no special flags)
/// - `Rust`: Rust parser with bsc compilation, file-backed (`--rust`)
/// - `InProcess`: Rust compiler fully in-process, memory-backed (`--in-process`)
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BuildMode {
    /// Current OCaml/file-based build (default, no flags)
    Default,
    /// Rust parser, bsc compilation, file-backed (`--rust`)
    Rust,
    /// Rust compiler fully in-process, memory-backed (`--in-process`)
    InProcess,
}

impl BuildMode {
    /// Whether this mode uses the Rust parser (true for Rust and InProcess)
    pub fn use_rust_parser(&self) -> bool {
        matches!(self, BuildMode::Rust | BuildMode::InProcess)
    }

    /// Whether this mode uses in-process compilation with no disk artifacts
    pub fn is_in_process(&self) -> bool {
        matches!(self, BuildMode::InProcess)
    }
}

/// Per-module in-memory compilation state for `--in-process` builds.
///
/// Stores the published interface signature and a generation number that
/// replaces timestamp-based invalidation (`last_compiled_cmi`/`last_compiled_cmt`).
/// When a module is recompiled and its interface changes, the generation is
/// bumped so downstream dependents know to recompile.
pub struct InMemoryModuleState {
    /// The module's published interface signature.
    /// For modules with `.resi`, this comes from typechecking the `.resi`.
    /// For modules without `.resi`, this is the inferred signature from `.res`.
    pub signature: DeclSignature,
    /// Monotonically increasing generation number. Bumped each time the
    /// module's published interface changes. Downstream dependents compare
    /// their recorded dependency generation against this to detect staleness.
    pub generation: u64,
    /// Whether this module's source is pure (no side effects), used for
    /// JS import resolution.
    pub is_pure: bool,
}

impl std::fmt::Debug for InMemoryModuleState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InMemoryModuleState")
            .field("generation", &self.generation)
            .field("is_pure", &self.is_pure)
            .field("signature", &format!("<{} items>", self.signature.len()))
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Implementation {
    pub path: PathBuf,
    pub parse_state: ParseState,
    pub compile_state: CompileState,
    pub last_modified: SystemTime,
    pub parse_dirty: bool,
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

pub enum StoredAst {
    Structure(ParseArena, Structure),
    Signature(ParseArena, Signature),
}

impl std::fmt::Debug for StoredAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoredAst::Structure(_, _) => write!(f, "StoredAst::Structure(..)"),
            StoredAst::Signature(_, _) => write!(f, "StoredAst::Signature(..)"),
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
    pub compiler_info: CompilerInfo,
    pub deps_initialized: bool,
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
    pub build_state: BuildState,
    // Command-line --warn-error flag override (takes precedence over rescript.json config)
    pub warn_error_override: Option<String>,
    // The explicit build mode (Default, Rust, or InProcess)
    pub build_mode: BuildMode,
    // Command-line --subprocess flag: run bsc as subprocess with timeout (instead of in-process).
    pub subprocess: bool,
    // Command-line --dump-typed-sexp flag: add -dtyped-sexp to bsc invocations.
    pub dump_typed_sexp: bool,
    // Stored ASTs from parse phase, keyed by "{module_name}:impl" or "{module_name}:intf"
    pub stored_asts: Mutex<AHashMap<String, StoredAst>>,
    // In-memory published interfaces, keyed by module name. Only used in --in-process mode.
    // Maps module_name -> InMemoryModuleState (signature + generation).
    pub in_memory_interfaces: Mutex<AHashMap<String, InMemoryModuleState>>,
    // Monotonically increasing generation counter for in-memory interface invalidation.
    // Each compilation that produces a new interface bumps this counter.
    pub interface_generation: AtomicU64,
    // Shared PersistentEnv for --in-process mode. Holds cached module interfaces
    // and metadata needed by the compiler for dependency resolution.
    pub persistent_env: Mutex<Option<PersistentEnv>>,
}

impl std::fmt::Debug for BuildCommandState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BuildCommandState")
            .field("build_state", &self.build_state)
            .field("warn_error_override", &self.warn_error_override)
            .field("build_mode", &self.build_mode)
            .field("subprocess", &self.subprocess)
            .field("dump_typed_sexp", &self.dump_typed_sexp)
            .field("stored_asts", &"<Mutex<..>>")
            .field("in_memory_interfaces", &"<Mutex<..>>")
            .field(
                "interface_generation",
                &self.interface_generation.load(Ordering::Relaxed),
            )
            .field("persistent_env", &"<Mutex<Option<PersistentEnv>>>")
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
    ) -> Self {
        Self {
            project_context,
            module_names: AHashSet::new(),
            modules: AHashMap::new(),
            packages,
            deleted_modules: AHashSet::new(),
            compiler_info: compiler,
            deps_initialized: false,
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
        project_context: ProjectContext,
        packages: AHashMap<String, Package>,
        compiler: CompilerInfo,
        warn_error_override: Option<String>,
        build_mode: BuildMode,
        subprocess: bool,
        dump_typed_sexp: bool,
    ) -> Self {
        Self {
            build_state: BuildState::new(project_context, packages, compiler),
            warn_error_override,
            build_mode,
            subprocess,
            dump_typed_sexp,
            stored_asts: Mutex::new(AHashMap::new()),
            in_memory_interfaces: Mutex::new(AHashMap::new()),
            interface_generation: AtomicU64::new(0),
            persistent_env: Mutex::new(None),
        }
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

    pub fn subprocess(&self) -> bool {
        self.subprocess
    }

    pub fn dump_typed_sexp(&self) -> bool {
        self.dump_typed_sexp
    }

    /// Allocate the next interface generation number.
    pub fn next_interface_generation(&self) -> u64 {
        self.interface_generation.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Register a compiled module's interface in the in-memory registry.
    /// Returns the generation number assigned.
    pub fn register_in_memory_interface(
        &self,
        module_name: String,
        signature: DeclSignature,
        is_pure: bool,
    ) -> u64 {
        let generation = self.next_interface_generation();
        let state = InMemoryModuleState {
            signature,
            generation,
            is_pure,
        };
        self.in_memory_interfaces
            .lock()
            .unwrap()
            .insert(module_name, state);
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

    /// Take ownership of the PersistentEnv for use during compilation.
    /// Returns None if no PersistentEnv has been initialized or it's already taken.
    pub fn take_persistent_env(&self) -> Option<PersistentEnv> {
        self.persistent_env.lock().unwrap().take()
    }

    /// Return the PersistentEnv after compilation.
    pub fn return_persistent_env(&self, env: PersistentEnv) {
        *self.persistent_env.lock().unwrap() = Some(env);
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
    pub namespace: Namespace,
    pub last_modified: SystemTime,
    pub ast_file_path: PathBuf,
    pub is_root: bool,
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
