use super::build_types::*;
use super::packages;
use crate::build;
use crate::build::packages::Package;
use crate::config::{Config, SourceMapCommand};
use crate::helpers;
use crate::helpers::emojis::*;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::Result;
use console::style;
use rayon::prelude::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;
use tracing::instrument;

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

/// Record this in-process build in each package's database (see
/// [`build::state_db`]): the sources it compiled, when each module's
/// JavaScript was confirmed up to date, and the warnings to report again.
pub fn write_in_process_record(build_state: &BuildCommandState) {
    if build_state.stopped_at_parse {
        return;
    }
    let digests = build::incremental::UnitDigests::all(build_state);
    crate::build::phase_mark("record-digests");
    build_state
        .packages
        .par_iter()
        .for_each(|(package_name, package)| {
            let record = build::incremental::current_record(build_state, package_name, &digests);
            let previous = build_state
                .previous_in_process
                .as_ref()
                .and_then(|previous| previous.packages.get(package_name))
                .map(|record| &record.state);
            build::state_db::write_record(package, previous, &record);
            build::state_db::remove_legacy_files(package);
        });
}

/// Read the previous in-process build's records and remove the outputs of
/// sources it compiled that no longer exist: the JS output and any typed
/// artifacts in `lib/bs` and `lib/ocaml`. Returns (removed sources, recorded
/// sources).
/// Remove the genType output of a removed source file, when genType wrote it.
fn remove_gentype_file(package: &Package, source: &Path) {
    let Some(gentype) = package.config.gentype_config.as_ref() else {
        return;
    };
    let extension = gentype.generated_file_extension.as_deref().unwrap_or(".gen.tsx");
    let source = package.path.join(source);
    let (Some(dir), Some(stem)) = (source.parent(), source.file_stem()) else {
        return;
    };
    let file = dir.join(format!("{}{extension}", stem.to_string_lossy()));
    let generated = std::fs::read_to_string(&file)
        .is_ok_and(|content| content.starts_with("/* TypeScript file generated from"));
    if generated {
        let _ = std::fs::remove_file(file);
    }
}

pub fn cleanup_previous_in_process_build(build_state: &mut BuildCommandState) -> (usize, usize) {
    let root_config = build_state.get_root_config();
    let suffix = root_config.get_suffix(root_config.get_package_specs().first().unwrap());
    let current = in_process_source_paths(build_state);
    let mut removed = 0;
    let mut total = 0;
    let mut deleted_modules = AHashSet::new();
    let mut previous = build::incremental::PreviousInProcessBuild::default();
    let states: Vec<(&String, build::state_db::PackageState)> = build_state
        .packages
        .par_iter()
        .filter_map(|(name, package)| build::state_db::read(package).map(|state| (name, state)))
        .collect();
    for (package_name, state) in states {
        let package = &build_state.packages[package_name];
        let current_paths: AHashSet<&PathBuf> = current
            .get(package_name)
            .map(|entries| entries.iter().map(|(_, path)| path).collect())
            .unwrap_or_default();
        for (path, module_name) in &state.sources {
            total += 1;
            if current_paths.contains(path) {
                continue;
            }
            removed += 1;
            let basename = helpers::file_path_to_compiler_asset_basename(path, &package.namespace);
            let dir = path.parent().unwrap_or_else(|| Path::new(""));
            for extension in ["cmi", "cmt", "cmti", "cmj", "in-process-js.json"] {
                let file = format!("{basename}.{extension}");
                let _ = std::fs::remove_file(package.get_build_path().join(dir).join(&file));
                let _ = std::fs::remove_file(package.get_ocaml_build_path().join(&file));
            }
            if path
                .extension()
                .and_then(|ext| ext.to_str())
                .is_some_and(helpers::is_implementation_file)
            {
                remove_mjs_file(&package.path.join(path), &suffix);
                remove_gentype_file(package, path);
            }
            if !build_state.modules.contains_key(module_name) {
                deleted_modules.insert(module_name.to_string());
            }
        }
        previous.packages.insert(
            package_name.clone(),
            build::incremental::PackageRecord::new(state),
        );
    }
    build_state.deleted_modules = deleted_modules;
    build_state.previous_in_process = Some(previous);
    (removed, total)
}

pub fn cleanup_after_build(build_state: &BuildCommandState) {
    write_in_process_record(build_state);
    crate::build::phase_mark("record-written");
}

#[instrument(name = "clean.clean", skip_all)]
pub fn clean(path: &Path, show_progress: bool, plain_output: bool, prod: bool) -> Result<()> {
    let project_context = ProjectContext::new(path)?;
    let compiler_info = build::get_compiler_info(&project_context)?;
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

    // The build state database lives in the build directory removed above;
    // remove what older builds kept elsewhere.
    build::state_db::remove_legacy_files(package);
}
