#![allow(clippy::too_many_arguments)]

mod dependency_cycle;

use super::build_types::*;
use super::logs;
use super::packages;
use crate::config;
use crate::config::Config;
use crate::helpers;
use crate::helpers::StrippedVerbatimPath;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::{Result, anyhow};
use console::style;
use log::{debug, trace};
use rayon::prelude::*;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;
use std::time::SystemTime;

/// Execute js-post-build command for a compiled JavaScript file.
/// Unlike bsb which passes relative paths, rewatch passes absolute paths for clarity.
fn execute_post_build_command(cmd: &str, js_file_path: &Path) -> Result<()> {
    let full_command = format!("{} {}", cmd, js_file_path.display());

    let output = if cfg!(target_os = "windows") {
        Command::new("cmd").args(["/C", &full_command]).output()
    } else {
        Command::new("sh").args(["-c", &full_command]).output()
    };

    match output {
        Ok(output) if !output.status.success() => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            Err(anyhow!(
                "js-post-build command failed for {}: {}{}",
                js_file_path.display(),
                stderr,
                stdout
            ))
        }
        Err(e) => Err(anyhow!("Failed to execute js-post-build command: {}", e)),
        Ok(_) => Ok(()),
    }
}

/// Extract sexp output from bsc stderr.
/// When -dtyped-sexp-locs is passed, bsc writes the sexp to stderr.
/// The sexp starts with "(structure" or "(signature" and continues to the end.
/// Everything before that is warnings.
/// Returns (warnings, Option<sexp>).
fn extract_sexp_from_stderr(stderr: &str) -> (String, Option<String>) {
    // Find the start of the sexp - it begins with "(structure" or "(signature" at the start of a line
    let pos = stderr
        .find("\n(structure")
        .map(|p| p + 1)
        .or_else(|| stderr.find("\n(signature").map(|p| p + 1))
        .or_else(|| {
            if stderr.starts_with("(structure") || stderr.starts_with("(signature") {
                Some(0)
            } else {
                None
            }
        });
    if let Some(pos) = pos {
        let warnings = stderr[..pos].to_string();
        let sexp = stderr[pos..].to_string();
        (warnings, Some(sexp))
    } else {
        (stderr.to_string(), None)
    }
}

pub fn compile(
    build_state: &mut BuildCommandState,
    show_progress: bool,
    inc: impl Fn() + std::marker::Sync,
    set_length: impl Fn(u64),
) -> anyhow::Result<(String, String, usize)> {
    let mut compiled_modules = AHashSet::<String>::new();
    let dirty_modules = build_state
        .modules
        .iter()
        .filter_map(|(module_name, module)| {
            if module.compile_dirty {
                Some(module_name.to_owned())
            } else {
                None
            }
        })
        .collect::<AHashSet<String>>();

    // dirty_modules.iter().for_each(|m| println!("dirty module: {}", m));
    // println!("{} dirty modules", dirty_modules.len());
    let mut sorted_dirty_modules = dirty_modules.iter().collect::<Vec<&String>>();
    sorted_dirty_modules.sort();
    // dirty_modules.iter().for_each(|m| println!("dirty module: {}", m));
    // sorted_dirty_modules
    //     .iter()
    //     .for_each(|m| println!("dirty module: {}", m));

    // for sure clean modules -- after checking the hash of the cmi
    let mut clean_modules = AHashSet::<String>::new();

    // TODO: calculate the real dirty modules from the original dirty modules in each iteration
    // taken into account the modules that we know are clean, so they don't propagate through the
    // deps graph
    // create a hashset of all clean modules from the file-hashes
    let mut loop_count = 0;
    let mut files_total_count = compiled_modules.len();
    let mut files_current_loop_count;
    let mut compile_errors = "".to_string();
    let mut compile_warnings = "".to_string();
    let mut num_compiled_modules = 0;
    let mut sorted_modules = build_state.module_names.iter().collect::<Vec<&String>>();
    sorted_modules.sort();

    // In --in-process mode, purge deleted/renamed modules from the in-memory
    // registries so stale entries don't remain resolvable in watch mode.
    if build_state.build_mode().is_in_process() {
        build_state.purge_deleted_modules(&build_state.build_state.deleted_modules.clone());
    }

    // In --in-process mode, synthesize namespace module signatures in memory
    // before any source modules are compiled. Source modules may use `-open Namespace`,
    // so the namespace signature must be available in the PersistentEnv first.
    if build_state.build_mode().is_in_process() {
        register_namespace_signatures(build_state);
        register_source_fallback_paths(build_state);
        // Pre-compile all @rescript/runtime modules into the registry.
        // In in-process mode, the registry is the sole source of truth —
        // no CMI fallback. Every dependency must be in the registry.
        let pre_compile_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            rayon::scope(|s| {
                s.spawn(|_| {
                    pre_compile_runtime_modules(build_state);
                });
            });
        }));
        if let Err(e) = pre_compile_result {
            let msg = if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = e.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown".to_string()
            };
            eprintln!("Warning: runtime pre-compilation panicked: {}", msg);
        }
        // Clear source-fallback paths after pre-compilation.
        build_state
            .module_registry
            .lock()
            .unwrap()
            .source_fallback_paths
            .clear();
    }

    // this is the whole "compile universe" all modules that might be dirty
    // we get this by expanding the dependents from the dirty modules

    let mut compile_universe = dirty_modules.clone();
    let mut current_step_modules = compile_universe.clone();
    loop {
        let mut dependents: AHashSet<String> = AHashSet::new();
        for dirty_module in current_step_modules.iter() {
            dependents.extend(build_state.get_module(dirty_module).unwrap().dependents.clone());
        }

        current_step_modules = dependents
            .difference(&compile_universe)
            .map(|s| s.to_string())
            .collect::<AHashSet<String>>();

        compile_universe.extend(current_step_modules.to_owned());
        if current_step_modules.is_empty() {
            break;
        }
    }

    let compile_universe_count = compile_universe.len();
    set_length(compile_universe_count as u64);

    // start off with all modules that have no deps in this compile universe
    let mut in_progress_modules = compile_universe
        .iter()
        .filter(|module_name| {
            let module = build_state.get_module(module_name).unwrap();
            module.deps.intersection(&compile_universe).count() == 0
        })
        .map(|module_name| module_name.to_string())
        .collect::<AHashSet<String>>();

    loop {
        files_current_loop_count = 0;
        loop_count += 1;

        trace!(
            "Compiled: {} out of {}. Compile loop: {}",
            files_total_count,
            compile_universe.len(),
            loop_count,
        );

        let current_in_progres_modules = in_progress_modules.clone();

        let results: Vec<(String, Result<Option<String>>, Option<Result<Option<String>>>, bool, bool)> = if is_in_process {
            // --in-process: parallel compilation using the Rust compiler directly.
            // No compiler assets are emitted or read; interfaces are kept in memory.
            // Each worker gets a read-only snapshot of the ModuleRegistry and creates
            // its own fresh PersistentEnv from it.
            let registry = build_state.snapshot_module_registry();
            current_in_progres_modules
            .par_iter()
            .filter_map(|module_name| {
                let module = build_state.get_module(module_name).unwrap();
                let package = build_state
                    .get_package(&module.package_name)
                    .expect("Package not found");

                if !module
                    .deps
                    .intersection(&compile_universe)
                    .all(|dep| compiled_modules.contains(dep))
                {
                    return None;
                }

                if !module.compile_dirty {
                    if show_progress { inc(); }
                    return Some((module_name.to_string(), Ok(None), Some(Ok(None)), true, false));
                }

                match &module.source_type {
                    SourceType::MlMap(_) => {
                        Some((
                            package.namespace.to_suffix().unwrap(),
                            Ok(None),
                            Some(Ok(None)),
                            false,
                            false,
                        ))
                    }
                    SourceType::SourceFile(_) => {
                        // Record interface generation before compilation for staleness detection
                        let gen_before = build_state.get_interface_generation(module_name);

                        let compile_start = std::time::Instant::now();
                        let result = compile_module_in_process(
                            package,
                            module,
                            module_name,
                            &registry,
                            &build_state.build_state,
                            build_state,
                        );
                        let elapsed = compile_start.elapsed();
                        if elapsed.as_millis() > 100 {
                            eprintln!("[timing] {} {:.0}ms", module_name, elapsed.as_secs_f64() * 1000.0);
                        }

                        let gen_after = build_state.get_interface_generation(module_name);

                        // Interface is "clean" if the generation didn't change
                        let is_clean = gen_before == gen_after;

                        let (impl_result, intf_result) = match result {
                            Ok(warning) => (Ok(warning), Some(Ok(None))),
                            Err(e) => (Err(e), None),
                        };

                        if show_progress { inc(); }

                        Some((
                            module_name.to_string(),
                            impl_result,
                            intf_result,
                            is_clean,
                            true,
                        ))
                    }
                }
            })
            .collect()
        } else {
            // Default / --rust: parallel compilation via bsc subprocess
            current_in_progres_modules
            .par_iter()
            .filter_map(|module_name| {
                let module = build_state.get_module(module_name).unwrap();
                let package = build_state
                    .get_package(&module.package_name)
                    .expect("Package not found");
                // all dependencies that we care about are compiled
                if module
                    .deps
                    .intersection(&compile_universe)
                    .all(|dep| compiled_modules.contains(dep))
                {
                    if !module.compile_dirty {
                        // we are sure we don't have to compile this, so we can mark it as compiled and clean
                        return Some((module_name.to_string(), Ok(None), Some(Ok(None)), true, false));
                    }
                    match module.source_type.to_owned() {
                        SourceType::MlMap(_) => {
                            // the mlmap needs to be compiled before the files are compiled
                            // in the same namespace, otherwise we get a compile error
                            // this is why mlmap is compiled in the AST generation stage
                            // compile_mlmap(&module.package, module_name, &project_root);
                            Some((
                                package.namespace.to_suffix().unwrap(),
                                Ok(None),
                                Some(Ok(None)),
                                false,
                                false,
                            ))
                        }
                        SourceType::SourceFile(source_file) => {
                            let cmi_path = helpers::get_compiler_asset(
                                package,
                                &package.namespace,
                                &source_file.implementation.path,
                                "cmi",
                            );

                            let cmi_digest = helpers::compute_file_hash(Path::new(&cmi_path));

                            let package = build_state
                                .get_package(&module.package_name)
                                .expect("Package not found");

                            let subprocess = build_state.subprocess;
                            let dump_typed_sexp = build_state.dump_typed_sexp;
                            let interface_result = match source_file.interface.to_owned() {
                                Some(Interface { path, .. }) => {
                                    let result = compile_file(
                                        package,
                                        &helpers::get_ast_path(&path),
                                        module,
                                        module_name,
                                        true,
                                        build_state,
                                        build_state.get_warn_error_override(),
                                        subprocess,
                                        dump_typed_sexp,
                                    );
                                    Some(result)
                                }
                                _ => None,
                            };
                            let result = compile_file(
                                package,
                                &helpers::get_ast_path(&source_file.implementation.path),
                                module,
                                module_name,
                                false,
                                build_state,
                                build_state.get_warn_error_override(),
                                subprocess,
                                dump_typed_sexp,
                            );
                            let cmi_digest_after = helpers::compute_file_hash(Path::new(&cmi_path));

                            // we want to compare both the hash of interface and the implementation
                            // compile assets to verify that nothing changed. We also need to checke the interface
                            // because we can include MyModule, so the modules that depend on this module might
                            // change when this modules interface does not change, but the implementation does
                            let is_clean_cmi = match (cmi_digest, cmi_digest_after) {
                                (Some(cmi_digest), Some(cmi_digest_after)) => {
                                    cmi_digest.eq(&cmi_digest_after)
                                }

                                _ => false,
                            };

                            Some((
                                module_name.to_string(),
                                result,
                                interface_result,
                                is_clean_cmi,
                                true,
                            ))
                        }
                    }
                } else {
                    None
                }
                .inspect(|_res| {
                    if show_progress {
                        inc();
                    }
                })
            })
            .collect::<Vec<_>>();

        for result in results.iter() {
            let (module_name, result, interface_result, is_clean, is_compiled) = result;
            in_progress_modules.remove(module_name);

            if *is_compiled {
                num_compiled_modules += 1;
            }

            files_current_loop_count += 1;
            compiled_modules.insert(module_name.to_string());

            if *is_clean {
                // actually add it to a list of clean modules
                clean_modules.insert(module_name.to_string());
            }

            let module_dependents = build_state.get_module(module_name).unwrap().dependents.clone();

            // if not clean -- compile modules that depend on this module
            for dep in module_dependents.iter() {
                //  mark the reverse dep as dirty when the source is not clean
                if !*is_clean {
                    let dep_module = build_state.modules.get_mut(dep).unwrap();
                    //  mark the reverse dep as dirty when the source is not clean
                    dep_module.compile_dirty = true;
                }
                if !compiled_modules.contains(dep) {
                    in_progress_modules.insert(dep.to_string());
                }
            }

            let package_name = {
                let module = build_state
                    .build_state
                    .modules
                    .get(module_name)
                    .ok_or(anyhow!("Module not found"))?;
                module.package_name.clone()
            };

            let package = build_state
                .build_state
                .packages
                .get(&package_name)
                .ok_or(anyhow!("Package name not found"))?;

            // Process results and update module state
            let (compile_warning, compile_error, interface_warning, interface_error) = {
                let module = build_state
                    .build_state
                    .modules
                    .get_mut(module_name)
                    .ok_or(anyhow!("Module not found"))?;

                let (compile_warning, compile_error) = match module.source_type {
                    SourceType::MlMap(ref mut mlmap) => {
                        module.compile_dirty = false;
                        mlmap.parse_dirty = false;
                        (None, None)
                    }
                    SourceType::SourceFile(ref mut source_file) => match result {
                        Ok(Some(err)) => {
                            source_file.implementation.compile_state = CompileState::Warning;
                            (Some(err.to_string()), None)
                        }
                        Ok(None) => {
                            source_file.implementation.compile_state = CompileState::Success;
                            (None, None)
                        }
                        Err(err) => {
                            source_file.implementation.compile_state = CompileState::Error;
                            (None, Some(err.to_string()))
                        }
                    },
                };

                let (interface_warning, interface_error) =
                    if let SourceType::SourceFile(ref mut source_file) = module.source_type {
                        match interface_result {
                            Some(Ok(Some(err))) => {
                                source_file.interface.as_mut().unwrap().compile_state = CompileState::Warning;
                                (Some(err.to_string()), None)
                            }
                            Some(Ok(None)) => {
                                if let Some(interface) = source_file.interface.as_mut() {
                                    interface.compile_state = CompileState::Success;
                                }
                                (None, None)
                            }
                            Some(Err(err)) => {
                                source_file.interface.as_mut().unwrap().compile_state = CompileState::Error;
                                (None, Some(err.to_string()))
                            }
                            _ => (None, None),
                        }
                    } else {
                        (None, None)
                    };

                // Update compilation timestamps for successful compilation
                if result.is_ok() && interface_result.as_ref().is_none_or(|r| r.is_ok()) {
                    module.compile_dirty = false;
                    module.last_compiled_cmi = Some(SystemTime::now());
                    module.last_compiled_cmt = Some(SystemTime::now());
                }

                (compile_warning, compile_error, interface_warning, interface_error)
            };

            // Handle logging outside the mutable borrow
            if let Some(warning) = compile_warning {
                logs::append(package, &warning);
                compile_warnings.push_str(&warning);
            }
            if let Some(error) = compile_error {
                logs::append(package, &error);
                compile_errors.push_str(&error);
            }
            if let Some(warning) = interface_warning {
                logs::append(package, &warning);
                compile_warnings.push_str(&warning);
            }
            if let Some(error) = interface_error {
                logs::append(package, &error);
                compile_errors.push_str(&error);
            }
        }

        files_total_count += files_current_loop_count;

        if files_total_count == compile_universe_count {
            break;
        }
        if in_progress_modules.is_empty() || in_progress_modules.eq(&current_in_progres_modules) {
            // find the dependency cycle
            let cycle = dependency_cycle::find(
                &compile_universe
                    .iter()
                    .map(|s| (s, build_state.get_module(s).unwrap()))
                    .collect::<Vec<(&String, &Module)>>(),
            );

            let guidance = "Possible solutions:\n- Extract shared code into a new module both depend on.\n";
            let message = format!(
                "\n{}\n{}\n{}",
                style("Can't continue... Found a circular dependency in your code:").red(),
                dependency_cycle::format(&cycle, build_state),
                guidance
            );

            // Append the error to the logs of all packages involved in the cycle,
            // so editor tooling can surface it from .compiler.log
            let mut touched_packages = AHashSet::<String>::new();
            for module_name in cycle.iter() {
                if let Some(module) = build_state.get_module(module_name)
                    && touched_packages.insert(module.package_name.clone())
                    && let Some(package) = build_state.get_package(&module.package_name)
                {
                    logs::append(package, &message);
                }
            }

            compile_errors.push_str(&message)
        }
        if !compile_errors.is_empty() {
            break;
        };
    }

    Ok((compile_errors, compile_warnings, num_compiled_modules))
}

static RUNTIME_PATH_MEMO: OnceLock<PathBuf> = OnceLock::new();

pub fn get_runtime_path(package_config: &Config, project_context: &ProjectContext) -> Result<PathBuf> {
    if let Some(p) = RUNTIME_PATH_MEMO.get() {
        return Ok(p.clone());
    }

    let resolved = match std::env::var("RESCRIPT_RUNTIME") {
        Ok(runtime_path) => Ok(PathBuf::from(runtime_path)),
        Err(_) => match helpers::try_package_path(package_config, project_context, "@rescript/runtime") {
            Ok(runtime_path) => Ok(runtime_path),
            Err(err) => Err(anyhow!(
                "The rescript runtime package could not be found.\nPlease set RESCRIPT_RUNTIME environment variable or make sure the runtime package is installed.\nError: {err}"
            )),
        },
    }?;

    let _ = RUNTIME_PATH_MEMO.set(resolved.clone());
    Ok(resolved)
}

pub fn get_runtime_path_args(
    package_config: &Config,
    project_context: &ProjectContext,
) -> Result<Vec<String>> {
    let runtime_path = get_runtime_path(package_config, project_context)?;
    Ok(vec![
        "-runtime-path".to_string(),
        runtime_path.to_string_lossy().to_string(),
    ])
}

pub fn compiler_args(
    config: &config::Config,
    ast_path: &Path,
    file_path: &Path,
    is_interface: bool,
    has_interface: bool,
    project_context: &ProjectContext,
    // if packages are known, we pass a reference here
    // this saves us a scan to find their paths.
    // This is None when called by build::get_compiler_args
    packages: &Option<&AHashMap<String, packages::Package>>,
    // Is the file listed as "type":"dev"?
    is_type_dev: bool,
    is_local_dep: bool,
    // Command-line --warn-error flag override (takes precedence over rescript.json config)
    warn_error_override: Option<String>,
) -> Result<Vec<String>> {
    let bsc_flags = config::flatten_flags(&config.compiler_flags);
    let dependency_paths = get_dependency_paths(config, project_context, packages, is_type_dev);
    let module_name = helpers::file_path_to_module_name(file_path, &config.get_namespace());

    let namespace_args = match &config.get_namespace() {
        packages::Namespace::NamespaceWithEntry { namespace: _, entry } if &module_name == entry => {
            // if the module is the entry we just want to open the namespace
            vec![
                "-open".to_string(),
                config.get_namespace().to_suffix().unwrap().to_string(),
            ]
        }
        packages::Namespace::Namespace(_)
        | packages::Namespace::NamespaceWithEntry {
            namespace: _,
            entry: _,
        } => {
            vec![
                "-bs-ns".to_string(),
                config.get_namespace().to_suffix().unwrap().to_string(),
            ]
        }
        packages::Namespace::NoNamespace => vec![],
    };

    let root_config = project_context.get_root_config();
    let jsx_args = root_config.get_jsx_args();
    let jsx_module_args = root_config.get_jsx_module_args();
    let jsx_mode_args = root_config.get_jsx_mode_args();
    let jsx_preserve_args = root_config.get_jsx_preserve_args();
    let gentype_arg = config.get_gentype_arg();
    let experimental_args = root_config.get_experimental_features_args();
    let warning_args = config.get_warning_args(is_local_dep, warn_error_override);

    let read_cmi_args = match has_interface {
        true => {
            if is_interface {
                vec![]
            } else {
                vec!["-bs-read-cmi".to_string()]
            }
        }
        false => vec![],
    };

    let package_name_arg = vec!["-bs-package-name".to_string(), config.name.to_owned()];

    let implementation_args = if is_interface {
        debug!("Compiling interface file: {}", &module_name);
        vec![]
    } else {
        debug!("Compiling file: {}", &module_name);
        let specs = root_config.get_package_specs();

        specs
            .iter()
            .flat_map(|spec| {
                vec![
                    "-bs-package-output".to_string(),
                    format!(
                        "{}:{}:{}",
                        spec.module,
                        if spec.in_source {
                            file_path.parent().unwrap().to_str().unwrap().to_string()
                        } else {
                            Path::new("lib")
                                .join(Path::join(
                                    Path::new(&spec.get_out_of_source_dir()),
                                    file_path.parent().unwrap(),
                                ))
                                .to_str()
                                .unwrap()
                                .to_string()
                        },
                        root_config.get_suffix(spec),
                    ),
                ]
            })
            .collect()
    };

    let runtime_path_args = get_runtime_path_args(config, project_context)?;

    Ok(vec![
        namespace_args,
        read_cmi_args,
        vec![
            "-I".to_string(),
            Path::new("..").join("ocaml").to_string_lossy().to_string(),
        ],
        runtime_path_args,
        dependency_paths,
        jsx_args,
        jsx_module_args,
        jsx_mode_args,
        jsx_preserve_args,
        bsc_flags.to_owned(),
        warning_args,
        gentype_arg,
        experimental_args,
        // vec!["-warn-error".to_string(), "A".to_string()],
        // ^^ this one fails for bisect-ppx
        // this is the default
        // we should probably parse the right ones from the package config
        // vec!["-w".to_string(), "a".to_string()],
        package_name_arg,
        implementation_args,
        // vec![
        //     "-I".to_string(),
        //     abs_node_modules_path.to_string() + "/rescript/ocaml",
        // ],
        vec![ast_path.to_string_lossy().to_string()],
    ]
    .concat())
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DependentPackage {
    Normal(String),
    Dev(String),
}

impl DependentPackage {
    fn name(&self) -> &str {
        match self {
            Self::Normal(name) => name,
            Self::Dev(name) => name,
        }
    }

    fn is_dev(&self) -> bool {
        match self {
            Self::Normal(_) => false,
            Self::Dev(_) => true,
        }
    }
}

fn get_dependency_paths(
    config: &config::Config,
    project_context: &ProjectContext,
    packages: &Option<&AHashMap<String, packages::Package>>,
    is_file_type_dev: bool,
) -> Vec<String> {
    let normal_deps = config
        .dependencies
        .clone()
        .unwrap_or_default()
        .into_iter()
        .map(DependentPackage::Normal)
        .collect();

    // We can only access dev dependencies for source_files that are marked as "type":"dev"
    let dev_deps = if is_file_type_dev {
        config
            .dev_dependencies
            .clone()
            .unwrap_or_default()
            .into_iter()
            .map(DependentPackage::Dev)
            .collect()
    } else {
        vec![]
    };

    [dev_deps, normal_deps]
        .concat()
        .par_iter()
        .filter_map(|dependent_package| {
            let package_name = dependent_package.name();
            let dependency_path = if let Some(packages) = packages {
                packages
                    .get(package_name)
                    .as_ref()
                    .map(|package| package.path.clone())
            } else {
                // packages will only be None when called by build::get_compiler_args
                // in that case we can safely pass config as the package config.
                packages::read_dependency(package_name, config, project_context).ok()
            }
            .map(|canonicalized_path| {
                vec![
                    "-I".to_string(),
                    packages::get_ocaml_build_path(&canonicalized_path)
                        .to_string_lossy()
                        .to_string(),
                ]
            });

            if !dependent_package.is_dev() && dependency_path.is_none() {
                panic!(
                    "Expected to find dependent package {} of {}",
                    package_name, config.name
                );
            }

            dependency_path
        })
        .collect::<Vec<Vec<String>>>()
        .concat()
}

/// Build `CompilerOptions` for an in-process compilation from the package config.
fn build_compiler_options(
    package: &packages::Package,
    module_name: &str,
    source_file_path: &Path,
    build_state: &BuildState,
) -> Result<rescript_compiler::driver::CompilerOptions> {
    let root_config = build_state.get_root_config();
    let project_context = &build_state.project_context;

    // Parse package compiler-flags for flags the in-process compiler needs to honor.
    // In the subprocess path, these are passed as raw CLI args to bsc.
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let mut nopervasives = false;
    let mut flag_open_modules: Vec<String> = Vec::new();
    {
        let mut iter = bsc_flags.iter();
        while let Some(flag) = iter.next() {
            match flag.as_str() {
                "-nopervasives" => nopervasives = true,
                "-open" => {
                    if let Some(mod_name) = iter.next() {
                        flag_open_modules.push(mod_name.clone());
                    }
                }
                _ => {} // Other flags (-nostdlib, -make-runtime, etc.) are not needed in-process
            }
        }
    }

    // Collect -I paths from all dependencies (same logic as get_dependency_paths)
    let mut include_paths: Vec<PathBuf> = Vec::new();

    // Add the package's own lib/ocaml directory
    include_paths.push(package.get_ocaml_build_path());

    // Add dependency lib/ocaml paths
    let dep_names: Vec<&str> = package
        .config
        .dependencies
        .as_ref()
        .map(|d| d.iter().map(|s| s.as_str()).collect())
        .unwrap_or_default();
    for dep_name in dep_names {
        if let Some(dep_pkg) = build_state.packages.get(dep_name) {
            include_paths.push(dep_pkg.get_ocaml_build_path());
        }
    }


    // Add dev dependency paths if the module is type:dev
    // (omitted for simplicity in first cut; can be added later)

    // Extract JSX version from root config
    let jsx_version = root_config
        .jsx
        .as_ref()
        .and_then(|jsx| jsx.version)
        .filter(|&v| v == 4);

    // Build open_modules: namespace opens first, then explicit -open flags from compiler-flags.
    // In the file-based mode, `-bs-ns Namespace` is passed to all namespaced modules.
    // In --in-process, we translate that to `-open Namespace` so sibling modules
    // are resolvable through the namespace.
    let mut open_modules: Vec<String> = Vec::new();
    if let Some(ns_suffix) = package.config.get_namespace().to_suffix() {
        open_modules.push(ns_suffix.to_string());
    }

    // Append explicit -open flags from package compiler-flags.
    // Self-open filtering (e.g., skip `-open Pervasives` when compiling Pervasives.res)
    // is handled inside load_pervasives via the module_name field.
    open_modules.extend(flag_open_modules);

    // Runtime path
    let runtime_path = get_runtime_path(&package.config, project_context).ok();

    // Source filename for interface constraint resolution
    let source_filename = Some(source_file_path.to_string_lossy().to_string());

    // Output path for JS import resolution
    let output_path = root_config.get_package_specs().first().map(|spec| {
        if spec.in_source {
            PathBuf::from(source_file_path.parent().unwrap_or(Path::new(".")))
        } else {
            Path::new("lib")
                .join(spec.get_out_of_source_dir())
                .join(source_file_path.parent().unwrap_or(Path::new(".")))
        }
    });

    Ok(rescript_compiler::driver::CompilerOptions {
        include_paths,
        runtime_path,
        open_modules,
        source_filename,
        output_path,
        jsx_version,
        nopervasives,
        module_name: Some(module_name.to_string()),
        ..Default::default()
    })
}

/// Write JS output to the correct location(s) based on package specs.
fn write_js_output(
    js_output: &str,
    package: &packages::Package,
    source_file_path: &Path,
    root_config: &config::Config,
) -> Result<()> {
    for spec in root_config.get_package_specs() {
        let suffix = root_config.get_suffix(&spec);
        let js_path = if spec.in_source {
            // In-source: JS goes alongside the .res file, within the package root
            let source_abs = Path::new(&package.path).join(source_file_path);
            helpers::get_source_file_from_rescript_file(&source_abs, &suffix)
        } else {
            // Out-of-source: JS goes in lib/js/ or lib/es6/ preserving relative path
            let out_dir = spec.get_out_of_source_dir();
            let js_relative =
                helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
            Path::new(&package.path)
                .join("lib")
                .join(out_dir)
                .join(js_relative)
        };

        if let Some(parent) = js_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&js_path, js_output)?;
    }
    Ok(())
}

/// Register namespace module signatures in the PersistentEnv for --in-process mode.
///
/// For each package with a namespace, synthesizes the namespace module's
/// alias signature (e.g., `module Foo = Foo-MyApp`) and registers it in
/// the shared ModuleRegistry so that `-open Namespace` works during compilation.
///
/// This replaces the `compile_mlmap` bsc subprocess call used in file-based modes.
fn register_namespace_signatures(build_state: &BuildCommandState) {
    for (_package_name, package) in build_state.packages.iter() {
        let namespace_suffix = match package.namespace.to_suffix() {
            Some(suffix) => suffix,
            None => continue, // No namespace for this package
        };

        let entry = match &package.namespace {
            packages::Namespace::NamespaceWithEntry {
                namespace: _,
                entry,
            } => Some(entry.as_str()),
            _ => None,
        };

        // Build the list of (short_name, internal_name) alias pairs.
        // This mirrors the logic in packages::parse_packages that calls gen_mlmap.
        let source_files = match &package.source_files {
            Some(sf) => sf,
            None => continue,
        };

        let module_aliases: Vec<(String, String)> = source_files
            .keys()
            .map(|path| {
                helpers::file_path_to_module_name(path, &packages::Namespace::NoNamespace)
            })
            .filter(|module_name| {
                // Exclude the entry module (it's not aliased in the namespace)
                if let Some(entry) = entry {
                    module_name != entry
                } else {
                    true
                }
            })
            .filter(|module_name| helpers::is_non_exotic_module_name(module_name))
            .map(|short_name| {
                let internal_name = format!("{}-{}", short_name, namespace_suffix);
                (short_name, internal_name)
            })
            .collect();

        if !module_aliases.is_empty() {
            build_state.register_namespace_in_registry(&namespace_suffix, &module_aliases);
        }
    }
}

/// Register source file paths for all modules in the ModuleRegistry.
///
/// This enables on-demand source-based type checking for implicit dependencies
/// (modules accessed via `-open Pervasives`, namespace opens, etc.) that aren't
/// captured by the AST-based dep graph. Without these fallback paths, modules
/// needed as implicit deps but not yet compiled in the current wave would be
/// unfindable by the in-process PersistentEnv.
fn register_source_fallback_paths(build_state: &BuildCommandState) {
    let mut fallback_paths = ahash::AHashMap::new();

    // Register source paths for all modules in the build graph
    for (module_name, module) in build_state.modules.iter() {
        if let SourceType::SourceFile(source_file) = &module.source_type {
            let package = build_state
                .get_package(&module.package_name)
                .expect("Package not found");

            // Prefer .resi if it exists, otherwise use .res
            let source_path = if let Some(interface) = &source_file.interface {
                Path::new(&package.path).join(&interface.path)
            } else {
                Path::new(&package.path).join(&source_file.implementation.path)
            };

            fallback_paths.insert(module_name.clone(), source_path);
        }
    }

    // Register source paths for @rescript/runtime modules.
    // The runtime is NOT a regular dependency in the build graph — it's
    // resolved via RESCRIPT_RUNTIME. In file-based mode, runtime modules
    // are loaded from .cmi files on the load path. In --in-process mode,
    // we need source fallback paths so they can be type-checked on demand.
    let runtime_path = &build_state.build_state.compiler_info.runtime_path;
    if let Ok(entries) = std::fs::read_dir(runtime_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
                if ext == "res" || ext == "resi" {
                    if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                        // Capitalize the module name (Pervasives, Js, etc.)
                        let module_name = {
                            let mut chars = stem.chars();
                            match chars.next() {
                                None => continue,
                                Some(ch) => {
                                    format!("{}{}", ch.to_uppercase(), chars.as_str())
                                }
                            }
                        };

                        // For .res files, check if a .resi exists and prefer it
                        if ext == "res" {
                            let resi_path = path.with_extension("resi");
                            if resi_path.exists() {
                                fallback_paths.insert(module_name, resi_path);
                            } else {
                                fallback_paths.entry(module_name).or_insert(path.clone());
                            }
                        } else {
                            // .resi always takes precedence
                            fallback_paths.insert(module_name, path.clone());
                        }
                    }
                }
            }
        }
    }

    build_state
        .module_registry
        .lock()
        .unwrap()
        .source_fallback_paths = fallback_paths;
}

/// Pre-compile all @rescript/runtime modules into the ModuleRegistry before the
/// main compile loop. This eliminates source-fallback recursion during parallel
/// compilation: without pre-compilation, every module that implicitly needs
/// Pervasives (via `-open Pervasives`) would trigger recursive source-fallback
/// type-checking, creating deep stack frames that overflow worker thread stacks.
///
/// After this step, all runtime modules (Pervasives, Js, Belt, etc.) are in the
/// registry and found directly without any source-fallback.
///
/// Runs on a dedicated thread with a large stack to handle any remaining
/// source-fallback chains during the pre-compilation itself.
fn pre_compile_runtime_modules(build_state: &BuildCommandState) {
    let runtime_root = &build_state.build_state.compiler_info.runtime_path;
    // Runtime .res sources live in lib/ocaml/ alongside the .cmi/.cmj files
    let runtime_path = runtime_root.join("lib").join("ocaml");

    // Collect all runtime .res files and check for .resi siblings
    let mut runtime_modules: Vec<(String, PathBuf, Option<PathBuf>)> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&runtime_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("res") {
                continue;
            }
            if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                let module_name = {
                    let mut chars = stem.chars();
                    match chars.next() {
                        None => continue,
                        Some(ch) => format!("{}{}", ch.to_uppercase(), chars.as_str()),
                    }
                };
                let resi_path = path.with_extension("resi");
                let has_resi = resi_path.exists();
                runtime_modules.push((
                    module_name,
                    path.clone(),
                    if has_resi { Some(resi_path) } else { None },
                ));
            }
        }
    }

    if runtime_modules.is_empty() {
        return;
    }

    // Sort for deterministic compilation order.
    // Put Pervasives first since everything depends on it.
    runtime_modules.sort_by(|a, b| {
        let a_priority = if a.0 == "Pervasives" { 0 } else { 1 };
        let b_priority = if b.0 == "Pervasives" { 0 } else { 1 };
        a_priority.cmp(&b_priority).then_with(|| a.0.cmp(&b.0))
    });

    let root_config = build_state.get_root_config();
    let runtime_path_for_opts = runtime_root.clone();
    let jsx_version = root_config
        .jsx
        .as_ref()
        .and_then(|jsx| jsx.version)
        .filter(|&v| v == 4);

    let module_count = runtime_modules.len();

    // Compile sequentially. After each module compiles, its result is in
    // the registry, so subsequent modules find deps directly without
    // deep source-fallback chains. Pervasives compiles first (sorted above)
    // so all other runtime modules find it immediately.
    let mut compiled = 0;
    for (module_name, res_path, resi_path) in &runtime_modules {
        let options = rescript_compiler::driver::CompilerOptions {
            include_paths: vec![runtime_path.clone()],
            nopervasives: true,
            open_modules: vec!["Pervasives".to_string()],
            module_name: Some(module_name.clone()),
            runtime_path: Some(runtime_path_for_opts.clone()),
            jsx_version,
            source_filename: Some(res_path.to_string_lossy().to_string()),
            ..Default::default()
        };

        let registry = build_state.snapshot_module_registry();

        // Register this module's metadata in the registry before compilation
        // so the compiler can find its own source info
        {
            let mut reg = build_state.module_registry.lock().unwrap();
            reg.module_info.insert(
                module_name.clone(),
                rescript_compiler::cmi::persistent_env::InMemoryModuleInfo {
                    source_path: res_path.clone(),
                    is_pure: true,
                    is_runtime: true,
                },
            );
        }

        // Step 1: If .resi exists, typecheck the interface first
        let mut local_registry = registry.clone();
        if let Some(resi) = resi_path {
            if let Ok(intf_source) = std::fs::read_to_string(resi) {
                let intf_result = rescript_compiler::driver::typecheck_interface_in_process(
                    &intf_source,
                    &resi.to_string_lossy(),
                    module_name,
                    &options,
                    &local_registry,
                );
                match intf_result {
                    Ok(result) => {
                        if let Some(ps) = result.pers_struct {
                            local_registry.cached_modules.insert(module_name.clone(), ps.clone());
                            build_state.update_module_registry(
                                module_name,
                                ps,
                                res_path.clone(),
                                true,
                                true,
                                result.new_alias_rewrites,
                            );
                        }
                    }
                    Err(e) => {
                        debug!("Runtime interface typecheck failed for {}: {}", module_name, e);
                        continue;
                    }
                }
            }
        }

        // Step 2: Type-check the implementation (no lambda/JS — we only need the interface)
        let has_interface = resi_path.is_some();
        if let Ok(impl_source) = std::fs::read_to_string(res_path) {
            let typecheck_result = rescript_compiler::driver::typecheck_implementation_in_process(
                &impl_source,
                &res_path.to_string_lossy(),
                module_name,
                &options,
                &local_registry,
                has_interface,
            );

            match typecheck_result {
                Ok(result) => {
                    let rt_fingerprint = result
                        .pers_struct
                        .as_ref()
                        .map(|ps| ps.fingerprint)
                        .unwrap_or(0);
                    if let Some(ps) = result.pers_struct {
                        build_state.update_module_registry(
                            module_name,
                            ps,
                            res_path.clone(),
                            true,
                            true,
                            result.new_alias_rewrites,
                        );
                    }
                    if !has_interface {
                        build_state.register_in_memory_interface(
                            module_name.clone(),
                            result.signature,
                            rt_fingerprint,
                            true,
                        );
                    }
                    compiled += 1;
                }
                Err(e) => {
                    debug!("Runtime typecheck failed for {}: {}", module_name, e);
                }
            }
        }
    }

    debug!(
        "Pre-compiled {}/{} runtime modules into registry",
        compiled, module_count
    );
}

/// Compile a single module fully in-process using the Rust compiler.
///
/// This replaces the bsc subprocess path for `--in-process` mode:
/// - Reads source from disk
/// - If .resi exists, typechecks it first and registers the interface
/// - Compiles the .res implementation
/// - Writes only JS output (no .cmi, .cmj, .cmt, .cmti)
/// - Returns the finalized PersStruct and signature for the caller to
///   update the shared ModuleRegistry.
///
/// Takes a `&ModuleRegistry` (read-only snapshot from the current wave)
/// instead of a shared mutable `PersistentEnv`. Each call creates its own
/// fresh `PersistentEnv` internally, enabling parallel compilation.
///
/// Returns Ok(None) on success, Ok(Some(warning)) on success with warnings,
/// Err on failure.
fn compile_module_in_process(
    package: &packages::Package,
    module: &Module,
    module_name: &str,
    registry: &ModuleRegistry,
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
) -> Result<Option<String>> {
    let source_file = match &module.source_type {
        SourceType::SourceFile(sf) => sf,
        _ => return Ok(None), // MlMap handled elsewhere
    };

    let implementation_path = &source_file.implementation.path;
    let has_interface = source_file.interface.is_some();
    let root_config = build_command_state.get_root_config();

    // Build compiler options from package config
    let options =
        build_compiler_options(package, module_name, implementation_path, build_state)?;

    let source_abs = Path::new(&package.path).join(implementation_path);
    let is_runtime = package.name == "@rescript/runtime";
    let is_pure = true;

    // For .resi + .res, we need the .resi to be in the registry before compiling .res.
    // Build a local registry that includes the .resi result (if any).
    let mut local_registry = registry.clone();

    // Register this module's metadata in the local registry
    local_registry.module_info.insert(
        module_name.to_string(),
        rescript_compiler::cmi::persistent_env::InMemoryModuleInfo {
            source_path: source_abs.clone(),
            is_pure,
            is_runtime,
        },
    );

    // Step 1: If .resi exists, typecheck the interface first
    if let Some(interface) = &source_file.interface {
        let intf_source_abs = Path::new(&package.path).join(&interface.path);
        let intf_source = std::fs::read_to_string(&intf_source_abs).map_err(|e| {
            anyhow!(
                "Failed to read interface file {}: {}",
                intf_source_abs.display(),
                e
            )
        })?;

        let intf_result = rescript_compiler::driver::typecheck_interface_in_process(
            &intf_source,
            &intf_source_abs.to_string_lossy(),
            module_name,
            &options,
            &local_registry,
        )
        .map_err(|e| anyhow!("Interface typecheck failed for {}: {}", module_name, e));

        let intf_result = match intf_result {
            Ok(r) => r,
            Err(e) => {
                let warning = format!("{}", e);
                eprintln!("{}", warning);
                return Ok(Some(warning));
            }
        };

        // Register the .resi's PersStruct in the local registry so the
        // .res compilation can find it for moregen constraints.
        let intf_fingerprint = intf_result
            .pers_struct
            .as_ref()
            .map(|ps| ps.fingerprint)
            .unwrap_or(0);
        if let Some(ps) = intf_result.pers_struct {
            local_registry
                .cached_modules
                .insert(module_name.to_string(), ps.clone());
            // Update the shared registry with the .resi result
            build_command_state.update_module_registry(
                module_name,
                ps,
                source_abs.clone(),
                is_pure,
                is_runtime,
                intf_result.new_alias_rewrites,
            );
        }

        // Register the interface signature in rewatch's in-memory registry
        build_command_state.register_in_memory_interface(
            module_name.to_string(),
            intf_result.signature,
            intf_fingerprint,
            is_pure,
        );
    }

    // Step 2: Compile the implementation
    let impl_source = std::fs::read_to_string(&source_abs).map_err(|e| {
        anyhow!(
            "Failed to read source file {}: {}",
            source_abs.display(),
            e
        )
    })?;

    let compile_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rescript_compiler::driver::compile_source_in_process(
            &impl_source,
            &source_abs.to_string_lossy(),
            module_name,
            &options,
            &local_registry,
            has_interface,
        )
    }));

    let compile_result = match compile_result {
        Ok(Ok(result)) => result,
        Ok(Err(e)) => {
            // Return as a warning, not an error. The module won't produce JS
            // output but the build should continue for other modules.
            let warning = format!("Compilation failed for {}: {}", module_name, e);
            eprintln!("{}", warning);
            return Ok(Some(warning));
        }
        Err(panic) => {
            let msg = if let Some(s) = panic.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic".to_string()
            };
            // Return as a warning, not an error. The module won't produce JS
            // output but the build should continue for other modules.
            let warning = format!("Compilation panicked for {}: {}", module_name, msg);
            eprintln!("{}", warning);
            return Ok(Some(warning));
        }
    };

    // Update the shared registry with the implementation's PersStruct
    let impl_fingerprint = compile_result
        .pers_struct
        .as_ref()
        .map(|ps| ps.fingerprint)
        .unwrap_or(0);
    if let Some(ps) = compile_result.pers_struct {
        build_command_state.update_module_registry(
            module_name,
            ps,
            source_abs.clone(),
            is_pure,
            is_runtime,
            compile_result.new_alias_rewrites,
        );
    }

    // Register the implementation's inferred signature if no .resi
    if !has_interface {
        build_command_state.register_in_memory_interface(
            module_name.to_string(),
            compile_result.signature,
            impl_fingerprint,
            is_pure,
        );
    }

    // Step 3: Write only JS output (no compiler assets)
    write_js_output(
        &compile_result.js_output,
        package,
        implementation_path,
        root_config,
    )?;

    // Execute js-post-build command if configured
    if let Some(js_post_build) = &package.config.js_post_build {
        for spec in root_config.get_package_specs() {
            let suffix = root_config.get_suffix(&spec);
            let js_file = if spec.in_source {
                helpers::get_source_file_from_rescript_file(
                    &Path::new(&package.path).join(implementation_path),
                    &suffix,
                )
            } else {
                let out_dir = spec.get_out_of_source_dir();
                let js_relative =
                    helpers::get_source_file_from_rescript_file(implementation_path, &suffix);
                Path::new(&package.path)
                    .join("lib")
                    .join(out_dir)
                    .join(js_relative)
            };
            if js_file.exists() {
                execute_post_build_command(&js_post_build.cmd, &js_file)?;
            }
        }
    }

    Ok(None)
}

fn compile_file(
    package: &packages::Package,
    ast_path: &Path,
    module: &Module,
    module_name: &str,
    is_interface: bool,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    subprocess: bool,
    dump_typed_sexp: bool,
) -> Result<Option<String>> {
    let BuildState {
        packages,
        project_context,
        compiler_info,
        ..
    } = build_state;
    let root_config = build_state.get_root_config();
    let ocaml_build_path_abs = package.get_ocaml_build_path();
    let build_path_abs = package.get_build_path();
    let implementation_file_path = match &module.source_type {
        SourceType::SourceFile(source_file) => Ok(&source_file.implementation.path),
        sourcetype => Err(format!(
            "Tried to compile a file that is not a source file ({}). Path to AST: {}. ",
            sourcetype,
            ast_path.to_string_lossy()
        )),
    }
    .map_err(|e| anyhow!(e))?;
    let basename =
        helpers::file_path_to_compiler_asset_basename(implementation_file_path, &package.namespace);
    let has_interface = module.get_interface().is_some();
    let is_type_dev = module.is_type_dev;
    let mut to_mjs_args = compiler_args(
        &package.config,
        ast_path,
        implementation_file_path,
        is_interface,
        has_interface,
        project_context,
        &Some(packages),
        is_type_dev,
        package.is_local_dep,
        warn_error_override,
    )?;

    // --dump-typed-sexp: add -dtyped-sexp to bsc invocation
    if dump_typed_sexp {
        to_mjs_args.push("-dtyped-sexp".to_string());
    }

    let cwd = build_path_abs
        .canonicalize()
        .map(StrippedVerbatimPath::to_stripped_verbatim_path)
        .ok()
        .unwrap();

    // --subprocess: run bsc as subprocess with timeout (non-fatal on crash/timeout).
    // This REPLACES the normal bsc call — only one bsc runs per compile_file.
    if subprocess {
        let module_name =
            helpers::file_path_to_module_name(implementation_file_path, &package.namespace);

        // Redirect stderr to sexp file when dump_typed_sexp is set
        let sexp_file = if dump_typed_sexp {
            let path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
            if let Some(parent) = path.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            Some(std::fs::File::create(&path).map_err(|e| anyhow!("Failed to create sexp file: {e}"))?)
        } else {
            None
        };

        match Command::new(&compiler_info.bsc_path)
            .current_dir(&cwd)
            .args(&to_mjs_args)
            .stdout(std::process::Stdio::null())
            .stderr(match sexp_file {
                Some(f) => std::process::Stdio::from(f),
                None => std::process::Stdio::piped(),
            })
            .spawn()
        {
            Ok(mut child) => {
                let timeout = std::time::Duration::from_secs(30);
                let start = std::time::Instant::now();
                let mut timed_out = false;
                let mut exit_status = None;
                loop {
                    match child.try_wait() {
                        Ok(Some(status)) => {
                            exit_status = Some(status);
                            break;
                        }
                        Ok(None) if start.elapsed() > timeout => {
                            let _ = child.kill();
                            let _ = child.wait();
                            timed_out = true;
                            break;
                        }
                        Ok(None) => {
                            std::thread::sleep(std::time::Duration::from_millis(50))
                        }
                        Err(_) => break,
                    }
                }

                if timed_out {
                    if dump_typed_sexp {
                        // Truncate the sexp file (partial output is invalid)
                        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                        let _ = std::fs::write(&sexp_path, "");
                    }
                    let msg = format!("Timeout ({:.0}s) compiling `{module_name}`", timeout.as_secs_f64());
                    log::warn!("{}", msg);
                    return Ok(Some(msg));
                } else if exit_status.is_some_and(|s| !s.success()) {
                    log::warn!("bsc subprocess crashed for `{module_name}`");
                }
            }
            Err(e) => {
                log::warn!("Failed to spawn bsc subprocess: {e}");
            }
        }
        return Ok(None);
    }

    // Normal mode: run bsc via Command::output()
    // When generating sexp, redirect stderr directly to file to avoid buffering
    // huge output in memory (e.g., Icon.res produces 882MB of sexp).
    let sexp_file = if dump_typed_sexp {
        let path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        Some(std::fs::File::create(&path).map_err(|e| anyhow!("Failed to create sexp file: {e}"))?)
    } else {
        None
    };

    let to_mjs = Command::new(&compiler_info.bsc_path)
        .current_dir(&cwd)
        .args(to_mjs_args)
        .stderr(match sexp_file {
            Some(f) => std::process::Stdio::from(f),
            None => std::process::Stdio::piped(),
        })
        .output();

    match to_mjs {
        Ok(x) if !x.status.success() => {
            let stderr = if dump_typed_sexp {
                // stderr was redirected to file — read error from there
                let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                std::fs::read_to_string(&sexp_path).unwrap_or_default()
            } else {
                String::from_utf8_lossy(&x.stderr).to_string()
            };
            let stdout = String::from_utf8_lossy(&x.stdout);
            Err(anyhow!(stderr + &stdout))
        }
        Err(e) => Err(anyhow!(
            "Could not compile file. Error: {e}. Path to AST: {ast_path:?}"
        )),
        Ok(x) => {
            let raw_stderr = String::from_utf8_lossy(&x.stderr).to_string();

            let err = if dump_typed_sexp {
                let (warnings, sexp) = extract_sexp_from_stderr(&raw_stderr);
                if let Some(sexp_content) = sexp {
                    let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                    let _ = std::fs::write(&sexp_path, sexp_content);
                }
                warnings
            } else {
                raw_stderr
            };

            let dir = Path::new(implementation_file_path).parent().unwrap();

            // perhaps we can do this copying somewhere else
            if !is_interface {
                let _ = std::fs::copy(
                    package
                        .get_build_path()
                        .join(dir)
                        // because editor tooling doesn't support namespace entries yet
                        // we just remove the @ for now. This makes sure the editor support
                        // doesn't break
                        .join(format!("{basename}.cmi")),
                    ocaml_build_path_abs.join(format!("{basename}.cmi")),
                );
                let _ = std::fs::copy(
                    package.get_build_path().join(dir).join(format!("{basename}.cmj")),
                    ocaml_build_path_abs.join(format!("{basename}.cmj")),
                );
                let _ = std::fs::copy(
                    package
                        .get_build_path()
                        .join(dir)
                        // because editor tooling doesn't support namespace entries yet
                        // we just remove the @ for now. This makes sure the editor support
                        // doesn't break
                        .join(format!("{basename}.cmt")),
                    ocaml_build_path_abs.join(format!("{basename}.cmt")),
                );
            } else {
                let _ = std::fs::copy(
                    package
                        .get_build_path()
                        .join(dir)
                        .join(format!("{basename}.cmti")),
                    ocaml_build_path_abs.join(format!("{basename}.cmti")),
                );
                let _ = std::fs::copy(
                    package.get_build_path().join(dir).join(format!("{basename}.cmi")),
                    ocaml_build_path_abs.join(format!("{basename}.cmi")),
                );
            }

            if let SourceType::SourceFile(SourceFile {
                interface: Some(Interface { path, .. }),
                ..
            }) = &module.source_type
            {
                let _ = std::fs::copy(
                    Path::new(&package.path).join(path),
                    package.get_build_path().join(path),
                )
                .expect("copying source file failed");

                let _ = std::fs::copy(
                    Path::new(&package.path).join(path),
                    package
                        .get_ocaml_build_path()
                        .join(std::path::Path::new(path).file_name().unwrap()),
                )
                .expect("copying source file failed");
            }
            if let SourceType::SourceFile(SourceFile {
                implementation: Implementation { path, .. },
                ..
            }) = &module.source_type
            {
                let _ = std::fs::copy(
                    Path::new(&package.path).join(path),
                    package.get_build_path().join(path),
                )
                .expect("copying source file failed");

                let _ = std::fs::copy(
                    Path::new(&package.path).join(path),
                    package
                        .get_ocaml_build_path()
                        .join(std::path::Path::new(path).file_name().unwrap()),
                )
                .expect("copying source file failed");
            }

            // copy js file
            root_config.get_package_specs().iter().for_each(|spec| {
                if spec.in_source
                    && let SourceType::SourceFile(SourceFile {
                        implementation: Implementation { path, .. },
                        ..
                    }) = &module.source_type
                {
                    let source = helpers::get_source_file_from_rescript_file(
                        &Path::new(&package.path).join(path),
                        &root_config.get_suffix(spec),
                    );
                    let destination = helpers::get_source_file_from_rescript_file(
                        &package.get_build_path().join(path),
                        &root_config.get_suffix(spec),
                    );

                    if source.exists() {
                        let _ = std::fs::copy(&source, &destination).expect("copying source file failed");
                    }
                }
            });

            // Execute js-post-build command if configured
            // Only run for implementation files (not interfaces)
            if !is_interface
                && let Some(js_post_build) = &package.config.js_post_build
                && let SourceType::SourceFile(SourceFile {
                    implementation: Implementation { path, .. },
                    ..
                }) = &module.source_type
            {
                // Execute post-build command for each package spec (each output format)
                for spec in root_config.get_package_specs() {
                    let js_file = helpers::get_source_file_from_rescript_file(
                        &package.get_build_path().join(path),
                        &root_config.get_suffix(&spec),
                    );

                    if js_file.exists() {
                        // Fail the build if post-build command fails (matches bsb behavior with &&)
                        execute_post_build_command(&js_post_build.cmd, &js_file)?;
                    }
                }
            }

            let warnings = if helpers::contains_ascii_characters(&err) {
                if package.is_local_dep {
                    Some(err)
                } else {
                    None
                }
            } else {
                None
            };

            Ok(warnings)
        }
    }
}

pub fn mark_modules_with_deleted_deps_dirty(build_state: &mut BuildState) {
    build_state.modules.iter_mut().for_each(|(_, module)| {
        if !module.deps.is_disjoint(&build_state.deleted_modules) {
            module.compile_dirty = true;
        }
    });
}

// this happens when a compile is not completed successfully in some way
// a dependent module could be compiled with a new interface, but the dependent
// modules have not finished compiling. This can cause a stale build.
// When the build is clean this doesn't happen. But when we interupt the build,
// such as force quitting the watcher, it can happen.
//
// If a build stops in the middle of errors, this will also happen, because
// basically we interrupt a build and we stop compiling somewhere in the middle.
//
// In watch mode, we retain the dirty state of the modules, so we don't need
// to do this, which will make it more efficient.
//
// We could clean up the build after errors. But I think we probably still need
// to do this, because people can also force quit the watcher of
pub fn mark_modules_with_expired_deps_dirty(build_state: &mut BuildCommandState) {
    let mut modules_with_expired_deps: AHashSet<String> = AHashSet::new();
    build_state
        .modules
        .iter()
        .filter(|m| !m.1.is_mlmap())
        .for_each(|(module_name, module)| {
            for dependent in module.dependents.iter() {
                let dependent_module = build_state.modules.get(dependent).unwrap();
                match dependent_module.source_type {
                    SourceType::SourceFile(_) => {
                        match (module.last_compiled_cmt, module.last_compiled_cmt) {
                            (None, None) | (Some(_), None) | (None, Some(_)) => {
                                // println!(
                                //     "🛑 {} is a dependent of {} but has no cmt/cmi",
                                //     module_name, dependent
                                // );
                                modules_with_expired_deps.insert(module_name.to_string());
                            }
                            (Some(_), Some(_)) => (),
                        }

                        // we compare the last compiled time of the dependent module with the last
                        // compile of the interface of the module it depends on, if the interface
                        // didn't change it doesn't matter
                        match (dependent_module.last_compiled_cmt, module.last_compiled_cmt) {
                            (Some(last_compiled_dependent), Some(last_compiled)) => {
                                if last_compiled_dependent < last_compiled {
                                    // println!(
                                    //     "✅ {} is a dependent of {} ({:?} / {:?})",
                                    //     module_name, dependent, last_compiled_dependent, last_compiled
                                    // );

                                    modules_with_expired_deps.insert(dependent.to_string());
                                } else {
                                    // println!(
                                    //     "🛑 {} is a dependent of {} ({:?} / {:?})",
                                    //     module_name, dependent, last_compiled_dependent, last_compiled
                                    // );
                                }
                            }
                            (None, _) => {
                                // println!(
                                //     "🛑 {} is a dependent of {} (no last compiled time)",
                                //     module_name, dependent
                                // );
                                modules_with_expired_deps.insert(dependent.to_string());
                            }
                            _ => (),
                        }
                    }
                    // a namespace is never a dependent of a module (it can be a dependency, but not the other
                    // way around)
                    SourceType::MlMap(_) => {
                        for dependent_of_namespace in dependent_module.dependents.iter() {
                            let dependent_module = build_state.modules.get(dependent_of_namespace).unwrap();

                            if let (Some(last_compiled_dependent), Some(last_compiled)) =
                                (dependent_module.last_compiled_cmt, module.last_compiled_cmt)
                                && last_compiled_dependent < last_compiled
                            {
                                modules_with_expired_deps.insert(dependent.to_string());
                            }
                        }
                    }
                }
            }
        });
    build_state.modules.iter_mut().for_each(|(module_name, module)| {
        if modules_with_expired_deps.contains(module_name) {
            module.compile_dirty = true;
        }
    });
}
