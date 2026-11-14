//! Editor tooling inside the watcher.
//!
//! Builds write no `.cmi`/`.cmt`/`.cmti` files and keep only the published
//! interfaces (the module registry) in memory. Editor tooling runs inside a
//! watch session instead: a command names a source file, which is
//! type-checked on demand against the registry, and the command works on the
//! resulting Rust typed tree.

use super::build_types::{BuildCommandState, SourceType, StoredAst, StoredSignatureAst, StoredStructureAst};
use super::{compile, packages, parse};
use crate::{config, helpers};
use anyhow::{Result, anyhow};
use rescript_compiler::analysis::reanalyze;
use rescript_compiler::analysis::session::{Project, SourcePaths, TypedSource};
use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::parse_arena::ParseArena;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// `path` with its nearest existing ancestor canonicalized, so tooling may
/// name a project through another spelling (e.g. a symlink).
fn canonical(path: &Path) -> PathBuf {
    let mut existing = path;
    let mut rest = Vec::new();
    while !existing.exists() {
        match (existing.file_name(), existing.parent()) {
            (Some(name), Some(parent)) => {
                rest.push(name);
                existing = parent;
            }
            _ => return path.to_path_buf(),
        }
    }
    let mut canonical = existing.canonicalize().unwrap_or_else(|_| existing.to_path_buf());
    for part in rest.iter().rev() {
        canonical.push(part);
    }
    canonical
}

/// A project source file of this watch session.
pub struct SourceModule<'a> {
    pub module_name: &'a str,
    pub package: &'a packages::Package,
    /// The implementation, relative to the package root.
    pub implementation: &'a Path,
    /// The interface, relative to the package root.
    pub interface: Option<&'a Path>,
    /// Whether `path` named the interface.
    pub is_interface: bool,
}

/// The module whose implementation or interface is at `path`.
pub fn source_module<'a>(build_state: &'a BuildCommandState, path: &Path) -> Option<SourceModule<'a>> {
    let path = canonical(path);
    build_state.modules.iter().find_map(|(module_name, module)| {
        let SourceType::SourceFile(source_file) = &module.source_type else {
            return None;
        };
        let package = build_state.packages.get(&module.package_name)?;
        let root = Path::new(&package.path);
        let implementation = source_file.implementation.path.as_path();
        let interface = source_file.interface.as_ref().map(|i| i.path.as_path());
        let is_interface = if root.join(implementation) == path {
            false
        } else if interface.is_some_and(|i| root.join(i) == path) {
            true
        } else {
            return None;
        };
        Some(SourceModule {
            module_name,
            package,
            implementation,
            interface,
            is_interface,
        })
    })
}

impl rescript_compiler::analysis::session::ParsedSource for StoredStructureAst {
    fn arena(&self) -> &ParseArena {
        &self.arena
    }
}

impl rescript_compiler::analysis::session::ParsedSource for StoredSignatureAst {
    fn arena(&self) -> &ParseArena {
        &self.arena
    }
}

/// A parsed runtime source.
struct RuntimeParsed(ParseArena);

impl rescript_compiler::analysis::session::ParsedSource for RuntimeParsed {
    fn arena(&self) -> &ParseArena {
        &self.0
    }
}

/// The runtime sources, which builds compile from source as well.
struct Runtime {
    root: PathBuf,
    path: PathBuf,
    config: config::Config,
    /// Module name to implementation path.
    modules: BTreeMap<String, PathBuf>,
}

impl Runtime {
    fn load(root: &Path) -> Option<Runtime> {
        let config = super::snapshot::runtime_config(root).ok()?;
        // The runtime ships its sources at its root; `path` is its artifact
        // directory, the runtime compile's `-I`.
        let path = packages::get_build_path(root);
        let modules = compile::runtime_source_paths(root).ok()?.into_iter().collect();
        Some(Runtime {
            root: root.to_path_buf(),
            path,
            config,
            modules,
        })
    }

    fn interface(implementation: &Path) -> Option<PathBuf> {
        let interface = implementation.with_extension("resi");
        interface.exists().then_some(interface)
    }
}

/// The watch session as the analysis sees it: the project's modules, the
/// runtime's, and on-demand type-checking against the published interfaces.
pub struct WatchProject<'a> {
    build_state: &'a BuildCommandState,
    /// The package of the file a command is about (OCaml's `package`).
    package: Option<&'a packages::Package>,
    runtime: Option<Runtime>,
    registry: std::sync::OnceLock<ModuleRegistry>,
}

impl<'a> WatchProject<'a> {
    pub fn new(build_state: &'a BuildCommandState, cwd: &Path, args: &[String]) -> Self {
        // The package of the first argument naming a project source.
        let package = args
            .iter()
            .filter(|arg| arg.ends_with(".res") || arg.ends_with(".resi"))
            .find_map(|arg| source_module(build_state, &cwd.join(arg)))
            .map(|source| source.package)
            .or_else(|| build_state.packages.values().find(|p| p.is_root));
        WatchProject {
            build_state,
            package,
            runtime: Runtime::load(&build_state.compiler_info.runtime_path),
            registry: std::sync::OnceLock::new(),
        }
    }

    fn registry(&self) -> &ModuleRegistry {
        self.registry
            .get_or_init(|| self.build_state.snapshot_module_registry())
    }

    fn typecheck_project_module(&self, source: &SourceModule<'_>, interface: bool) -> Result<TypedSource> {
        let relative = match (interface, source.interface) {
            (true, Some(interface)) => interface,
            (true, None) => return Err(anyhow!("{} has no interface", source.module_name)),
            (false, _) => source.implementation,
        };
        let options =
            compile::build_compiler_options(source.package, source.module_name, relative, self.build_state)?;
        let path = Path::new(&source.package.path).join(relative);
        let filename = helpers::ocaml_absname(&path).to_string_lossy().into_owned();
        let parsed = parse::parse_for_tooling(source.package, relative, self.build_state)?;
        Ok(match parsed {
            StoredAst::Structure(ast) => {
                let typed = rescript_compiler::driver::typecheck_structure_for_tooling(
                    &ast.arena,
                    &ast.structure,
                    &filename,
                    source.module_name,
                    &options,
                    self.registry(),
                );
                TypedSource {
                    parsed: ast,
                    typed,
                    path,
                }
            }
            StoredAst::Signature(ast) => {
                let typed = rescript_compiler::driver::typecheck_signature_for_tooling(
                    &ast.arena,
                    &ast.signature,
                    &filename,
                    source.module_name,
                    &options,
                    self.registry(),
                );
                TypedSource {
                    parsed: ast,
                    typed,
                    path,
                }
            }
        })
    }

    fn typecheck_runtime_module(
        &self,
        runtime: &Runtime,
        module_name: &str,
        interface: bool,
    ) -> Result<TypedSource> {
        let implementation = runtime
            .modules
            .get(module_name)
            .ok_or_else(|| anyhow!("no runtime module {module_name}"))?;
        let options = compile::runtime_compiler_options(
            &runtime.root,
            &runtime.path,
            module_name,
            implementation,
            &runtime.config,
        );
        let path = if interface {
            Runtime::interface(implementation).ok_or_else(|| anyhow!("{module_name} has no interface"))?
        } else {
            implementation.clone()
        };
        let source = compile::read_source_latin1(&path)?;
        let filename = path.to_string_lossy().into_owned();
        Ok(if interface {
            let (arena, signature, _) =
                compile::parse_runtime_signature(&path, &source, options.experimental_let_unwrap)?;
            let typed = rescript_compiler::driver::typecheck_signature_for_tooling(
                &arena,
                &signature,
                &filename,
                module_name,
                &options,
                self.registry(),
            );
            TypedSource {
                parsed: Arc::new(RuntimeParsed(arena)),
                typed,
                path,
            }
        } else {
            let (arena, structure, _) =
                compile::parse_runtime_structure(&path, &source, options.experimental_let_unwrap)?;
            let typed = rescript_compiler::driver::typecheck_structure_for_tooling(
                &arena,
                &structure,
                &filename,
                module_name,
                &options,
                self.registry(),
            );
            TypedSource {
                parsed: Arc::new(RuntimeParsed(arena)),
                typed,
                path,
            }
        })
    }

    fn project_source(&self, module_name: &str) -> Option<SourceModule<'a>> {
        let (module_name, module) = self.build_state.modules.get_key_value(module_name)?;
        let SourceType::SourceFile(source_file) = &module.source_type else {
            return None;
        };
        Some(SourceModule {
            module_name,
            package: self.build_state.packages.get(&module.package_name)?,
            implementation: source_file.implementation.path.as_path(),
            interface: source_file.interface.as_ref().map(|i| i.path.as_path()),
            is_interface: false,
        })
    }
}

impl Project for WatchProject<'_> {
    fn module_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.build_state.modules.keys().cloned().collect();
        if let Some(runtime) = &self.runtime {
            names.extend(
                runtime
                    .modules
                    .keys()
                    .filter(|name| !self.build_state.modules.contains_key(*name))
                    .cloned(),
            );
        }
        names
    }

    fn module_for_path(&self, path: &Path) -> Option<String> {
        if let Some(source) = source_module(self.build_state, path) {
            return Some(source.module_name.to_string());
        }
        let path = canonical(path);
        let runtime = self.runtime.as_ref()?;
        runtime.modules.iter().find_map(|(name, implementation)| {
            let implementation = canonical(implementation);
            let is_module =
                implementation == path || Runtime::interface(&implementation).is_some_and(|i| i == path);
            is_module.then(|| name.clone())
        })
    }

    fn paths_for_module(&self, module_name: &str) -> Option<SourcePaths> {
        if let Some(module) = self.build_state.modules.get(module_name) {
            return Some(match &module.source_type {
                SourceType::SourceFile(_) => {
                    let source = self.project_source(module_name)?;
                    let root = Path::new(&source.package.path);
                    SourcePaths {
                        implementation: Some(root.join(source.implementation)),
                        interface: source.interface.map(|i| root.join(i)),
                    }
                }
                SourceType::MlMap(_) => SourcePaths::default(),
            });
        }
        let implementation = self.runtime.as_ref()?.modules.get(module_name)?;
        Some(SourcePaths {
            implementation: Some(implementation.clone()),
            interface: Runtime::interface(implementation),
        })
    }

    fn project_files(&self) -> Vec<String> {
        let Some(package) = self.package else {
            return Vec::new();
        };
        let mut names: Vec<String> = self
            .build_state
            .modules
            .iter()
            .filter(|(_, module)| {
                module.package_name == package.name && matches!(module.source_type, SourceType::SourceFile(_))
            })
            .map(|(name, _)| name.clone())
            .collect();
        names.sort();
        names
    }

    fn namespace(&self) -> Option<String> {
        match &self.package?.namespace {
            packages::Namespace::Namespace(namespace) => Some(namespace.clone()),
            packages::Namespace::NamespaceWithEntry { namespace, .. } => Some(namespace.clone()),
            packages::Namespace::NoNamespace => None,
        }
    }

    fn namespace_aliases(&self, module_name: &str) -> Option<Vec<(String, String)>> {
        let module = self.build_state.modules.get(module_name)?;
        let SourceType::MlMap(_) = module.source_type else {
            return None;
        };
        let package = self.build_state.packages.get(&module.package_name)?;
        compile::namespace_aliases(package).map(|(_, aliases)| aliases)
    }

    fn typecheck(&self, module_name: &str, interface: bool) -> Option<TypedSource> {
        let result = match self.project_source(module_name) {
            Some(source) => self.typecheck_project_module(&source, interface),
            None => match &self.runtime {
                Some(runtime) => self.typecheck_runtime_module(runtime, module_name, interface),
                None => return None,
            },
        };
        match result {
            Ok(typed) => Some(typed),
            Err(err) => {
                log::debug!("tooling: cannot type-check {module_name}: {err:#}");
                None
            }
        }
    }
}

/// Run `command` on a thread of its own, with the stack the build's compile
/// workers get: typed trees are not `Send`, so a tooling command type-checks
/// and reads its modules on one thread.
fn on_tooling_thread(command: impl FnOnce() -> Result<Vec<u8>, String> + Send) -> Result<Vec<u8>> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("rewatch-tooling".to_string())
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(scope, command)
            .map_err(|err| anyhow!("could not start the tooling thread: {err}"))?
            .join()
            .map_err(|_| anyhow!("the tooling command panicked"))?
            .map_err(|err| anyhow!(err))
    })
}

/// Run an editor tooling command (the arguments of `rescript-editor-analysis`,
/// relative paths resolved against `cwd`) and return what it prints.
pub fn run_command(build_state: &BuildCommandState, cwd: PathBuf, args: Vec<String>) -> Result<Vec<u8>> {
    on_tooling_thread(|| {
        let project = WatchProject::new(build_state, &cwd, &args);
        rescript_compiler::analysis::run(&rescript_compiler::analysis::Request { cwd, args }, &project)
    })
}

/// `rescript-tools doc <path>`: the documentation of the module at `path`
/// (relative to `cwd`) as JSON.
///
/// The OCaml tool reads the module's `.cmt`, which builds do not write.
/// Instead the project of the file is type-checked here, writing no files,
/// and the module is documented from its Rust typed tree. The docs give the
/// position of every item, also of those other modules declare, so this
/// build keeps source locations, as the diagnostic rebuild does.
pub fn doc(cwd: &Path, path: &str, plain_output: bool) -> Result<Vec<u8>> {
    let file = cwd.join(path);
    if !file.is_file() {
        return Err(anyhow!(
            "error: failed to generate doc for {path}, there is no such file"
        ));
    }
    let project_root = helpers::get_nearest_config(&file)
        .ok_or_else(|| anyhow!("error: failed to generate doc for {path}, it is in no ReScript project"))?;
    let failed = |err: &dyn std::fmt::Display| {
        anyhow!("error: failed to generate doc for {path}, the project does not build: {err:#}")
    };
    // `build::build` in check-only mode (no lock taken, no files written),
    // keeping locations and printing no warnings.
    let mut build_state = super::initialize_build_with_mode(
        /* no_timing */ true,
        &None,
        /* show_progress */ false,
        &project_root,
        plain_output,
        /* warn_error */ None,
        /* prod */ false,
        /* features */ None,
        config::SourceMapCommand::Build,
        /* check_only */ true,
    )
    .map_err(|err| failed(&format!("{err:#}")))?;
    build_state.print_warnings = false;
    build_state.diagnostic_locations = true;
    super::incremental_build_without_lock(
        &mut build_state,
        /* no_timing */ true,
        /* initial_build */ true,
        /* show_progress */ false,
        /* only_incremental */ false,
        plain_output,
        super::CompilerInfoWrite::WithRecord,
    )
    .map_err(|err| failed(&err))?;
    let docs = on_tooling_thread(|| {
        let project = WatchProject::new(&build_state, cwd, &[path.to_string()]);
        rescript_compiler::analysis::doc(cwd, path, &project)
    });
    // A one-shot command: let the OS reclaim the build graph at exit.
    std::mem::forget(build_state);
    docs
}

/// The packages `reanalyze` reads: the project's own and the local packages
/// it depends on, in the order of their build directories.
fn reanalyze_packages(build_state: &BuildCommandState) -> Vec<reanalyze::Package> {
    let root = build_state.packages.values().find(|package| package.is_root);
    let mut packages: Vec<reanalyze::Package> = build_state
        .packages
        .values()
        .filter(|package| package.is_local_dep)
        // OCaml writes no `.cmt` files for a package compiled with
        // `-bs-no-bin-annot`, so its tool reads none of its modules.
        .filter(|package| {
            !config::flatten_flags(&package.config.compiler_flags)
                .iter()
                .any(|flag| flag == "-bs-no-bin-annot")
        })
        .map(|package| {
            let modules: Vec<reanalyze::Module> = build_state
                .modules
                .iter()
                .filter(|(_, module)| module.package_name == package.name)
                .filter_map(|(name, module)| match &module.source_type {
                    SourceType::SourceFile(source) => Some(reanalyze::Module {
                        name: name.clone(),
                        artifact: helpers::file_path_to_compiler_asset_basename(
                            &source.implementation.path,
                            &package.namespace,
                        ),
                        has_interface: source.interface.is_some(),
                    }),
                    SourceType::MlMap(_) => None,
                })
                .collect();
            reanalyze::Package {
                build_root: package.get_build_path().to_string_lossy().into_owned(),
                modules,
            }
        })
        .collect();
    // The order of the build directories relative to the project root.
    let relative = |package: &reanalyze::Package| {
        let path = Path::new(&package.build_root);
        root.and_then(|root| path.strip_prefix(&root.path).ok())
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned()
    };
    packages.sort_by_key(relative);
    packages
}

/// `rescript-tools reanalyze <args>`: the dead code, exception and
/// termination analyses of the project `cwd` is in. `color` says standard
/// output is a terminal.
///
/// The OCaml tool reads the `.cmt` files of a build, which builds do not
/// write. Instead the project is type-checked here, writing no files, and
/// the analyses read each module's typed tree as the build checks it, on
/// the build's workers: the build keeps no typed trees. The analyses refer
/// to the declarations of other modules by position, so this build keeps
/// source locations, as the diagnostic rebuild does.
pub fn reanalyze(cwd: &Path, args: &[String], plain_output: bool, color: bool) -> Result<Vec<u8>> {
    // The version and the list of options need no project.
    if let Some(text) = reanalyze::output_without_project(args) {
        return Ok(text.into_bytes());
    }
    let project_root = helpers::get_nearest_config(cwd)
        .ok_or_else(|| anyhow!("Error: cannot find project root containing rescript.json."))?;
    let failed = |err: &dyn std::fmt::Display| anyhow!("error: the project does not build: {err:#}");
    // `build::build` in check-only mode (no lock taken, no files written),
    // keeping locations and printing no warnings.
    let mut build_state = super::initialize_build_with_mode(
        /* no_timing */ true,
        &None,
        /* show_progress */ false,
        &project_root,
        plain_output,
        /* warn_error */ None,
        /* prod */ false,
        /* features */ None,
        config::SourceMapCommand::Build,
        /* check_only */ true,
    )
    .map_err(|err| failed(&format!("{err:#}")))?;
    let analysis = match reanalyze::start(cwd, args, color, &reanalyze_packages(&build_state))
        .map_err(|err| anyhow!(err))?
    {
        reanalyze::Start::Analyze(analysis) => analysis,
        reanalyze::Start::Print(text) => return Ok(text),
    };
    build_state.print_warnings = false;
    build_state.diagnostic_locations = true;
    build_state.typed_trees = Some(analysis.clone());
    super::incremental_build_without_lock(
        &mut build_state,
        /* no_timing */ true,
        /* initial_build */ true,
        /* show_progress */ false,
        /* only_incremental */ false,
        plain_output,
        super::CompilerInfoWrite::WithRecord,
    )
    .map_err(|err| failed(&err))?;
    let report = analysis.report().map_err(|err| anyhow!(err));
    // A one-shot command: let the OS reclaim the build graph at exit.
    std::mem::forget(build_state);
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn published_runtime_without_config_is_visible_to_tooling() {
        let root = tempfile::tempdir().unwrap();
        let implementation = root.path().join("Stdlib_List.res");
        let interface = root.path().join("Stdlib_List.resi");
        std::fs::write(&implementation, "let value = 1\n").unwrap();
        std::fs::write(&interface, "let value: int\n").unwrap();
        let runtime = Runtime::load(root.path()).expect("published runtime is discoverable");
        assert_eq!(runtime.modules.get("Stdlib_List"), Some(&implementation));
        assert_eq!(Runtime::interface(&implementation), Some(interface));
        assert_eq!(runtime.config.name, "@rescript/runtime");
    }
}
