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

    // Extract stored_asts reference for use in par_iter (avoids borrow conflict with build_state)
    let stored_asts_ref: Option<&std::sync::Mutex<ahash::AHashMap<String, super::build_types::StoredAst>>> =
        if build_state.dump_typed_sexp() && build_state.use_rust_parser() {
            let ptr = &build_state.stored_asts as *const std::sync::Mutex<ahash::AHashMap<String, super::build_types::StoredAst>>;
            Some(unsafe { &*ptr })
        } else {
            None
        };

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

        let results = current_in_progres_modules
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

                            let rust_bsc = build_state.rust_bsc_path.as_deref();
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
                                        build_state.dump_typed_sexp,
                                        build_state.use_rust_parser,
                                        stored_asts_ref,
                                        rust_bsc,
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
                                build_state.dump_typed_sexp,
                                build_state.use_rust_parser,
                                stored_asts_ref,
                                rust_bsc,
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

fn compile_file(
    package: &packages::Package,
    ast_path: &Path,
    module: &Module,
    module_name: &str,
    is_interface: bool,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    dump_typed_sexp: bool,
    use_rust_parser: bool,
    stored_asts: Option<&std::sync::Mutex<ahash::AHashMap<String, super::build_types::StoredAst>>>,
    rust_bsc_path: Option<&Path>,
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

    // When dump_typed_sexp with Rust parser: skip OCaml bsc entirely,
    // just typecheck in-process and write sexp.
    if dump_typed_sexp && use_rust_parser {
        // Resolve include paths relative to build_path_abs (lib/bs), since compiler args
        // use relative paths like "../ocaml" that are meant to be resolved from lib/bs.
        let mut include_paths: Vec<PathBuf> = Vec::new();
        let mut runtime_path: Option<PathBuf> = None;
        let mut i = 0;
        while i < to_mjs_args.len() {
            if to_mjs_args[i] == "-I" && i + 1 < to_mjs_args.len() {
                let p = PathBuf::from(&to_mjs_args[i + 1]);
                let resolved = if p.is_relative() {
                    build_path_abs.join(&p)
                } else {
                    p
                };
                include_paths.push(resolved);
                i += 2;
            } else if to_mjs_args[i] == "-runtime-path" && i + 1 < to_mjs_args.len() {
                runtime_path = Some(PathBuf::from(&to_mjs_args[i + 1]));
                i += 2;
            } else {
                i += 1;
            }
        }

        let ast_key = format!("{}:{}", module_name, if is_interface { "intf" } else { "impl" });
        let stored = stored_asts.and_then(|m| m.lock().unwrap().remove(&ast_key));

        let source_filename = implementation_file_path.to_string_lossy().into_owned();
        let opts = rescript_compiler::driver::CompilerOptions {
            dump_typed_sexp_locs: true,
            include_paths,
            runtime_path,
            source_filename: Some(source_filename),
            ..Default::default()
        };

        // Run typed-sexp generation on a large-stack worker to avoid overflowing
        // rayon worker stacks on deeply nested typed trees.
        let worker_name = format!("rust-typed-sexp-{module_name}");
        let worker = std::thread::Builder::new()
            .name(worker_name)
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                let mut sexp_bytes = Vec::new();
                let mut typed_error: Option<String> = None;
                if let Some(stored_ast) = stored {
                    let result = match stored_ast {
                        super::build_types::StoredAst::Structure(arena, structure) => {
                            rescript_compiler::driver::typecheck_stored_structure_and_dump_sexp(
                                arena,
                                structure,
                                &opts,
                                &mut sexp_bytes,
                            )
                        }
                        super::build_types::StoredAst::Signature(arena, signature) => {
                            rescript_compiler::driver::typecheck_stored_signature_and_dump_sexp(
                                arena,
                                signature,
                                &opts,
                                &mut sexp_bytes,
                            )
                        }
                    };
                    if let Err(err) = result {
                        typed_error = Some(format!("{err:#}"));
                    }
                }
                (sexp_bytes, typed_error)
            })
            .map_err(|err| anyhow!("Failed to spawn rust typed-sexp worker: {err}"))?;

        let (sexp_bytes, typed_error) = worker
            .join()
            .map_err(|_| anyhow!("Rust typed-sexp worker panicked"))?;

        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
        let sexp_error_path = ocaml_build_path_abs.join(format!("{basename}.sexp.error"));
        // Keep Rust parity output on the same UTF-8-lossy path as OCaml
        // stderr extraction in this script.
        let lossy = String::from_utf8_lossy(&sexp_bytes);
        let _ = std::fs::write(&sexp_path, lossy.as_ref());
        if let Some(err) = typed_error {
            let header = format!(
                "Rust typed-sexp typecheck failed for module `{}` ({})",
                module_name,
                if is_interface {
                    "interface"
                } else {
                    "implementation"
                }
            );
            let full = format!("{header}\n{err}\n");
            let _ = std::fs::write(&sexp_error_path, &full);
            return Ok(Some(full));
        } else {
            let _ = std::fs::remove_file(&sexp_error_path);
        }

        return Ok(None);
    }

    // When --bsc is provided, use that binary with -dtyped-sexp-locs and a timeout
    if let Some(bsc_path) = rust_bsc_path {
        let mut sexp_args = to_mjs_args.clone();
        sexp_args.push("-dtyped-sexp-locs".to_string());

        let module_name =
            helpers::file_path_to_module_name(implementation_file_path, &package.namespace);
        let cwd = build_path_abs
            .canonicalize()
            .map(StrippedVerbatimPath::to_stripped_verbatim_path)
            .ok()
            .unwrap();

        let mut child = Command::new(bsc_path)
            .current_dir(&cwd)
            .args(&sexp_args)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| anyhow!("Failed to spawn bsc subprocess: {e}"))?;

        let stderr_pipe = child.stderr.take();
        let stderr_thread = std::thread::spawn(move || -> String {
            let mut buf = String::new();
            if let Some(mut pipe) = stderr_pipe {
                use std::io::Read;
                let _ = pipe.read_to_string(&mut buf);
            }
            buf
        });

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
                Ok(None) => std::thread::sleep(std::time::Duration::from_millis(50)),
                Err(e) => return Err(anyhow!("Error waiting for bsc subprocess: {e}")),
            }
        }

        let stderr_output = stderr_thread.join().unwrap_or_default();

        if timed_out {
            // Write empty sexp file so downstream doesn't see stale data
            let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
            let _ = std::fs::write(&sexp_path, "");
            return Ok(Some(format!("Timeout (30s) compiling `{module_name}`")));
        }

        // Check exit status for compilation errors
        if let Some(status) = exit_status {
            if !status.success() {
                return Err(anyhow!(stderr_output));
            }
        }

        // Write sexp file from stderr output
        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
        let _ = std::fs::write(&sexp_path, &stderr_output);

        return Ok(None);
    }

    if dump_typed_sexp {
        to_mjs_args.push("-dtyped-sexp-locs".to_string());
    }


    let needs_sexp = dump_typed_sexp || rust_bsc_path.is_some();

    // When --dump-typed-sexp or --bsc is set, add -dtyped-sexp to OCaml bsc
    if needs_sexp {
        to_mjs_args.push("-dtyped-sexp".to_string());
    }

    // When generating sexp, redirect stderr directly to file to avoid buffering
    // huge output in memory (e.g., Icon.res produces 882MB of sexp).
    let ocaml_sexp_file = if needs_sexp {
        let path = ocaml_build_path_abs.join(format!("{basename}.ocaml-sexp"));
        // Ensure the output directory exists (it may not on clean builds)
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        Some(std::fs::File::create(&path).map_err(|e| anyhow!("Failed to create sexp file: {e}"))?)
    } else {
        None
    };

    let to_mjs = Command::new(&compiler_info.bsc_path)
        .current_dir(
            build_path_abs
                .canonicalize()
                .map(StrippedVerbatimPath::to_stripped_verbatim_path)
                .ok()
                .unwrap(),
        )
        .args(to_mjs_args)
        .stderr(match ocaml_sexp_file {
            Some(f) => std::process::Stdio::from(f),
            None => std::process::Stdio::piped(),
        })
        .output();

    match to_mjs {
        Ok(x) if !x.status.success() => {
            let stderr = if needs_sexp {
                // stderr was redirected to file — read error from there
                let sexp_path = ocaml_build_path_abs.join(format!("{basename}.ocaml-sexp"));
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
                // we need to copy the source file to the build directory.
                // editor tools expects the source file in lib/bs for finding the current package
                // and in lib/ocaml when referencing modules in other packages
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
                // we need to copy the source file to the build directory.
                // editor tools expects the source file in lib/bs for finding the current package
                // and in lib/ocaml when referencing modules in other packages
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

            // After normal compilation succeeds, optionally run --bsc subprocess for sexp generation
            let mut warnings = if helpers::contains_ascii_characters(&err) {
                if package.is_local_dep {
                    Some(err)
                } else {
                    None
                }
            } else {
                None
            };

            if let (Some(bsc_path), Some(sexp_args_base)) = (rust_bsc_path, to_mjs_args_for_bsc) {
                let module_name =
                    helpers::file_path_to_module_name(implementation_file_path, &package.namespace);
                let cwd = build_path_abs
                    .canonicalize()
                    .map(StrippedVerbatimPath::to_stripped_verbatim_path)
                    .ok()
                    .unwrap();

                let mut sexp_args = sexp_args_base;
                sexp_args.push("-dtyped-sexp".to_string());

                match Command::new(bsc_path)
                    .current_dir(&cwd)
                    .args(&sexp_args)
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::piped())
                    .spawn()
                {
                    Ok(mut child) => {
                        let stderr_pipe = child.stderr.take();
                        let stderr_thread = std::thread::spawn(move || -> String {
                            let mut buf = String::new();
                            if let Some(mut pipe) = stderr_pipe {
                                use std::io::Read;
                                let _ = pipe.read_to_string(&mut buf);
                            }
                            buf
                        });

                        let timeout = std::time::Duration::from_millis(100);
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

                        let stderr_output = stderr_thread.join().unwrap_or_default();
                        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));

                        if timed_out {
                            let _ = std::fs::write(&sexp_path, "");
                            let msg = format!("Timeout ({:.1}s) generating sexp for `{module_name}`", timeout.as_secs_f64());
                            log::warn!("{}", msg);
                            warnings = Some(
                                warnings.map_or(msg.clone(), |w| format!("{w}\n{msg}")),
                            );
                        } else if exit_status.is_some_and(|s| s.success()) {
                            let _ = std::fs::write(&sexp_path, &stderr_output);
                        } else {
                            // Rust bsc crashed — don't write invalid sexp
                            log::warn!(
                                "bsc subprocess crashed for `{module_name}`"
                            );
                        }
                    }
                    Err(e) => {
                        log::warn!("Failed to spawn bsc subprocess for sexp: {e}");
                    }
                }
            }

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
