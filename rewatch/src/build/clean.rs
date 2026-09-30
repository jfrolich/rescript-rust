use super::build_types::*;
use super::packages;
use crate::build;
use crate::build::packages::Package;
use crate::config::{Config, SourceMapCommand};
use crate::helpers;
use crate::helpers::emojis::*;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::{Result, anyhow};
use console::style;
use rayon::prelude::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;
use tracing::instrument;

fn remove_ast(package: &packages::Package, source_file: &Path) {
    let _ = std::fs::remove_file(helpers::get_compiler_asset(
        package,
        &packages::Namespace::NoNamespace,
        source_file,
        "ast",
    ));
}

fn remove_iast(package: &packages::Package, source_file: &Path) {
    let _ = std::fs::remove_file(helpers::get_compiler_asset(
        package,
        &packages::Namespace::NoNamespace,
        source_file,
        "iast",
    ));
}

fn remove_mjs_file(source_file: &Path, suffix: &str) {
    let js_file = source_file.with_extension(
        // suffix.to_string includes the ., so we need to remove it
        &suffix[1..],
    );
    let _ = std::fs::remove_file(&js_file);

    let mut map_file = js_file.into_os_string();
    map_file.push(".map");
    let _ = std::fs::remove_file(PathBuf::from(map_file));
}

fn remove_compile_asset(package: &packages::Package, source_file: &Path, extension: &str) {
    let _ = std::fs::remove_file(helpers::get_compiler_asset(
        package,
        &package.namespace,
        source_file,
        extension,
    ));
    let _ = std::fs::remove_file(helpers::get_bs_compiler_asset(
        package,
        &package.namespace,
        source_file,
        extension,
    ));
}

pub fn remove_compile_assets(package: &packages::Package, source_file: &Path) {
    // optimization
    // only issue cmti if there is an interfacce file
    for extension in &["cmj", "cmi", "cmt", "cmti"] {
        remove_compile_asset(package, source_file, extension);
    }
}

fn clean_source_files(build_state: &BuildState, root_config: &Config) {
    // get all rescript file locations
    let rescript_file_locations = build_state
        .modules
        .values()
        .filter_map(|module| match &module.source_type {
            SourceType::SourceFile(source_file) => {
                build_state.packages.get(&module.package_name).map(|package| {
                    root_config
                        .get_package_specs()
                        .into_iter()
                        .filter_map(|spec| {
                            if spec.in_source {
                                Some((
                                    package.path.join(&source_file.implementation.path),
                                    match spec.suffix {
                                        None => root_config.get_suffix(&spec),
                                        Some(suffix) => suffix,
                                    },
                                ))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<(PathBuf, String)>>()
                })
            }
            _ => None,
        })
        .flatten()
        .collect::<Vec<(PathBuf, String)>>();

    rescript_file_locations
        .par_iter()
        .for_each(|(rescript_file_location, suffix)| remove_mjs_file(rescript_file_location, suffix));
}

// TODO: change to scan_previous_build => CompileAssetsState
// and then do cleanup on that state (for instance remove all .mjs files that are not in the state)

#[instrument(name = "clean.cleanup_previous_build", skip_all)]
pub fn cleanup_previous_build(
    build_state: &mut BuildCommandState,
    compile_assets_state: CompileAssetsState,
) -> (usize, usize) {
    // delete the .mjs file which appear in our previous compile assets
    // but does not exists anymore
    // delete the compiler assets for which modules we can't find a rescript file
    // location of rescript file is in the AST
    // delete the .mjs file for which we DO have a compiler asset, but don't have a
    // rescript file anymore (path is found in the .ast file)
    let diff = compile_assets_state
        .ast_rescript_file_locations
        .difference(&compile_assets_state.rescript_file_locations)
        .collect::<Vec<&PathBuf>>();

    let diff_len = diff.len();

    let deleted_interfaces = diff
        .par_iter()
        .map(|res_file_location| {
            let AstModule {
                module_name,
                package_name,
                ast_file_path,
                suffix,
                ..
            } = compile_assets_state
                .ast_modules
                .get(*res_file_location)
                .expect("Could not find module name for ast file");

            let package = build_state
                .packages
                .get(package_name)
                .expect("Could not find package");
            remove_compile_assets(package, res_file_location);
            remove_mjs_file(res_file_location, suffix);
            remove_iast(package, res_file_location);
            remove_ast(package, res_file_location);
            match helpers::get_extension(ast_file_path).as_str() {
                "iast" => Some(module_name.to_owned()),
                "ast" => None,
                _ => None,
            }
        })
        .collect::<Vec<Option<String>>>()
        .iter()
        .filter_map(|module_name| module_name.to_owned())
        .collect::<AHashSet<String>>();

    compile_assets_state
        .ast_rescript_file_locations
        .intersection(&compile_assets_state.rescript_file_locations)
        .for_each(|res_file_location| {
            let AstModule {
                module_name,
                last_modified: ast_last_modified,
                ast_file_path,
                ..
            } = compile_assets_state
                .ast_modules
                .get(res_file_location)
                .expect("Could not find module name for ast file");
            let module = build_state
                .modules
                .get_mut(module_name)
                .expect("Could not find module for ast file");

            let cmt_last_modified = compile_assets_state.cmt_modules.get(module_name);
            // if there is a new AST but it has not been compiled yet, we mark the module as compile dirty
            // we do this by checking if the cmt file is newer than the AST file. We always compile the
            // interface AND implementation. For some reason the CMI file is not always rewritten if it
            // doesn't have any changes, that's why we just look at the CMT file.
            if let Some(cmt_last_modified) = cmt_last_modified
                && cmt_last_modified >= ast_last_modified
                && !deleted_interfaces.contains(module_name)
            {
                module.compile_dirty = false;
            }

            match &mut module.source_type {
                SourceType::MlMap(_) => unreachable!("MlMap is not matched with a ReScript file"),
                SourceType::SourceFile(source_file) => {
                    if helpers::is_interface_ast_file(ast_file_path) {
                        let interface = source_file
                            .interface
                            .as_mut()
                            .expect("Could not find interface for module");

                        let source_last_modified = interface.last_modified;
                        if ast_last_modified >= &source_last_modified {
                            interface.parse_dirty = false;
                        }
                    } else {
                        let implementation = &mut source_file.implementation;
                        let source_last_modified = implementation.last_modified;
                        if ast_last_modified >= &source_last_modified
                            && !deleted_interfaces.contains(module_name)
                        {
                            implementation.parse_dirty = false;
                        }
                    }
                }
            }
        });

    compile_assets_state
        .cmi_modules
        .iter()
        .for_each(|(module_name, last_modified)| {
            if let Some(module) = build_state.modules.get_mut(module_name) {
                module.last_compiled_cmi = Some(*last_modified);
            }
        });

    compile_assets_state
        .cmt_modules
        .iter()
        .for_each(|(module_name, last_modified)| {
            if let Some(module) = build_state.modules.get_mut(module_name) {
                module.last_compiled_cmt = Some(*last_modified);
            }
        });

    let ast_module_names = compile_assets_state
        .ast_modules
        .values()
        .filter_map(
            |AstModule {
                 module_name,
                 ast_file_path,
                 ..
             }| {
                match helpers::get_extension(ast_file_path).as_str() {
                    "iast" => None,
                    "ast" => Some(module_name),
                    _ => None,
                }
            },
        )
        .collect::<AHashSet<&String>>();

    let all_module_names = build_state.modules.keys().collect::<AHashSet<&String>>();

    let deleted_module_names = ast_module_names
        .difference(&all_module_names)
        .flat_map(|module_name| {
            // if the module is a namespace, we need to mark the whole namespace as dirty when a module has been deleted
            if let Some(namespace) = helpers::get_namespace_from_module_name(module_name) {
                return vec![namespace, module_name.to_string()];
            }
            vec![module_name.to_string()]
        })
        .collect::<AHashSet<String>>();

    build_state.deleted_modules = deleted_module_names;

    (diff_len, compile_assets_state.ast_rescript_file_locations.len())
}

fn has_parse_warnings(module: &Module) -> bool {
    matches!(
        &module.source_type,
        SourceType::SourceFile(SourceFile {
            implementation: Implementation {
                parse_state: ParseState::Warning,
                ..
            },
            ..
        }) | SourceType::SourceFile(SourceFile {
            interface: Some(Interface {
                parse_state: ParseState::Warning,
                ..
            }),
            ..
        })
    )
}

fn has_compile_warnings(module: &Module) -> bool {
    matches!(
        &module.source_type,
        SourceType::SourceFile(SourceFile {
            implementation: Implementation {
                compile_state: CompileState::Warning,
                ..
            },
            ..
        }) | SourceType::SourceFile(SourceFile {
            interface: Some(Interface {
                compile_state: CompileState::Warning,
                ..
            }),
            ..
        })
    )
}

/// Per-package record of the sources an in-process build compiled. In-process
/// builds write no `.ast` files, whose recorded source paths drive
/// [`cleanup_previous_build`]; this manifest lets the next build remove the
/// outputs of modules whose sources disappeared.
const IN_PROCESS_MANIFEST: &str = "in-process-sources.txt";

fn in_process_source_paths(build_state: &BuildCommandState) -> AHashMap<String, Vec<(String, PathBuf)>> {
    let mut by_package: AHashMap<String, Vec<(String, PathBuf)>> = AHashMap::new();
    for (module_name, module) in build_state.modules.iter() {
        if let SourceType::SourceFile(source_file) = &module.source_type {
            let entries = by_package.entry(module.package_name.clone()).or_default();
            entries.push((module_name.clone(), source_file.implementation.path.clone()));
            if let Some(interface) = &source_file.interface {
                entries.push((module_name.clone(), interface.path.clone()));
            }
        }
    }
    by_package
}

/// Record the compiled sources of an in-process build (see [`IN_PROCESS_MANIFEST`]).
pub fn write_in_process_manifest(build_state: &BuildCommandState) {
    for (package_name, mut entries) in in_process_source_paths(build_state) {
        let Some(package) = build_state.packages.get(&package_name) else {
            continue;
        };
        entries.sort();
        let content: String = entries
            .iter()
            .map(|(module_name, path)| format!("{module_name}\t{}\n", path.to_string_lossy()))
            .collect();
        let dir = package.get_ocaml_build_path();
        let path = dir.join(IN_PROCESS_MANIFEST);
        if std::fs::read_to_string(&path).is_ok_and(|existing| existing == content) {
            continue;
        }
        let _ = std::fs::create_dir_all(&dir);
        let _ = std::fs::write(path, content);
    }
}

/// Remove the outputs of sources recorded by the previous in-process build
/// that no longer exist: the JS output and the typed artifacts in `lib/bs`
/// and `lib/ocaml`. Returns (removed sources, recorded sources).
pub fn cleanup_previous_in_process_build(build_state: &mut BuildCommandState) -> (usize, usize) {
    let root_config = build_state.get_root_config();
    let suffix = root_config.get_suffix(root_config.get_package_specs().first().unwrap());
    let current = in_process_source_paths(build_state);
    let mut removed = 0;
    let mut total = 0;
    let mut deleted_modules = AHashSet::new();
    for package in build_state.packages.values() {
        let Ok(content) = std::fs::read_to_string(package.get_ocaml_build_path().join(IN_PROCESS_MANIFEST))
        else {
            continue;
        };
        let current_paths: AHashSet<&PathBuf> = current
            .get(&package.name)
            .map(|entries| entries.iter().map(|(_, path)| path).collect())
            .unwrap_or_default();
        for line in content.lines() {
            let Some((module_name, path)) = line.split_once('\t') else {
                continue;
            };
            total += 1;
            let path = PathBuf::from(path);
            if current_paths.contains(&path) {
                continue;
            }
            removed += 1;
            let basename = helpers::file_path_to_compiler_asset_basename(&path, &package.namespace);
            let dir = path.parent().unwrap_or_else(|| Path::new(""));
            for extension in ["cmi", "cmt", "cmti", "cmj"] {
                let file = format!("{basename}.{extension}");
                let _ = std::fs::remove_file(package.get_build_path().join(dir).join(&file));
                let _ = std::fs::remove_file(package.get_ocaml_build_path().join(&file));
            }
            if path
                .extension()
                .and_then(|ext| ext.to_str())
                .is_some_and(helpers::is_implementation_file)
            {
                remove_mjs_file(&package.path.join(&path), &suffix);
            }
            if !build_state.modules.contains_key(module_name) {
                deleted_modules.insert(module_name.to_string());
            }
        }
    }
    build_state.deleted_modules = deleted_modules;
    (removed, total)
}

pub fn cleanup_after_build(build_state: &BuildCommandState) {
    if build_state.build_mode().is_in_process() {
        write_in_process_manifest(build_state);
    }
    build_state.modules.par_iter().for_each(|(_module_name, module)| {
        let package = build_state.get_package(&module.package_name).unwrap();
        if has_parse_warnings(module)
            && let SourceType::SourceFile(source_file) = &module.source_type
        {
            remove_iast(package, &source_file.implementation.path);
            remove_ast(package, &source_file.implementation.path);
        }
        if has_compile_warnings(module) {
            // only retain AST file if the compilation doesn't have warnings, we remove the AST in favor
            // of the CMI/CMT/CMJ files because if we delete these, the editor tooling doesn't
            // work anymore. If we remove the intermediate AST file, the editor tooling will
            // work, and we have an indication that we need to recompile the file.
            //
            // Recompiling this takes a bit more time, because we have to parse again, but
            // if we have warnings it's usually not a lot of files so the additional
            // latency shouldn't be too bad
            match &module.source_type {
                SourceType::SourceFile(source_file) => {
                    // we only clean the ast here, this will cause the file to be recompiled
                    // (and thus keep showing the warning), but it will keep the cmi file, so that we don't
                    // unecessary mark all the dependents as dirty, when there is no change in the interface
                    remove_ast(package, &source_file.implementation.path);
                    remove_iast(package, &source_file.implementation.path);
                }
                SourceType::MlMap(_) => (),
            }
        }
    });
}

#[instrument(name = "clean.clean", skip_all)]
pub fn clean(path: &Path, show_progress: bool, plain_output: bool, prod: bool) -> Result<()> {
    let project_context = ProjectContext::new(path)?;
    let build_mode = crate::cli::resolve_build_mode(false, false).map_err(|err| anyhow!(err))?;
    let compiler_info = build::get_compiler_info(&project_context, build_mode)?;
    // `clean` always acts on the full set of source directories regardless of which features are
    // active. We explicitly pass `None` so every tagged source folder is included and its
    // artifacts can be removed, even for features the user hasn't enabled for this build.
    let packages = packages::make(&None, &project_context, show_progress, prod, None)?;

    let timing_clean_compiler_assets = Instant::now();
    if !plain_output && show_progress {
        print!(
            "{} {}Cleaning compiler assets...",
            style("[1/2]").bold().dim(),
            SWEEP
        );
        let _ = std::io::stdout().flush();
    };

    for (_, package) in &packages {
        clean_package(show_progress, plain_output, package)
    }

    let timing_clean_compiler_assets_elapsed = timing_clean_compiler_assets.elapsed();

    if !plain_output && show_progress {
        println!(
            "{}{} {}Cleaned compiler assets in {:.2}s",
            LINE_CLEAR,
            style("[1/2]").bold().dim(),
            SWEEP,
            timing_clean_compiler_assets_elapsed.as_secs_f64()
        );
        let _ = std::io::stdout().flush();
    }

    let timing_clean_mjs = Instant::now();
    let mut build_state = BuildState::new(project_context, packages, compiler_info, SourceMapCommand::Build);
    packages::parse_packages(&mut build_state)?;
    let root_config = build_state.get_root_config();
    let suffix_for_print = match root_config.package_specs {
        None => match &root_config.suffix {
            None => String::from(".js"),
            Some(suffix) => suffix.clone(),
        },
        Some(_) => root_config
            .get_package_specs()
            .into_iter()
            .filter_map(|spec| {
                if spec.in_source {
                    spec.suffix.or_else(|| root_config.suffix.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<String>>()
            .join(", "),
    };

    if !plain_output && show_progress {
        print!(
            "{} {}Cleaning {} files...",
            style("[2/2]").bold().dim(),
            SWEEP,
            suffix_for_print
        );
        let _ = std::io::stdout().flush();
    }

    clean_source_files(&build_state, root_config);
    let timing_clean_mjs_elapsed = timing_clean_mjs.elapsed();

    if !plain_output && show_progress {
        println!(
            "{}{} {}Cleaned {} files in {:.2}s",
            LINE_CLEAR,
            style("[2/2]").bold().dim(),
            SWEEP,
            suffix_for_print,
            timing_clean_mjs_elapsed.as_secs_f64()
        );
        let _ = std::io::stdout().flush();
    }

    Ok(())
}

pub fn clean_package(show_progress: bool, plain_output: bool, package: &Package) {
    if show_progress {
        if plain_output {
            println!("Cleaning {}", package.name)
        } else {
            print!(
                "{}{} {}Cleaning {}...",
                LINE_CLEAR,
                style("[1/2]").bold().dim(),
                SWEEP,
                package.name
            );
        }
        let _ = std::io::stdout().flush();
    }

    let path_str = package.get_build_path();
    let path = std::path::Path::new(&path_str);
    let _ = std::fs::remove_dir_all(path);

    let path_str = package.get_ocaml_build_path();
    let path = std::path::Path::new(&path_str);
    let _ = std::fs::remove_dir_all(path);

    // remove the per-package compiler metadata file so that a subsequent build writes fresh metadata
    let _ = std::fs::remove_file(package.get_compiler_info_path());
}
