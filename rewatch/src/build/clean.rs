use super::build_types::*;
use super::packages;
use crate::build;
use crate::build::packages::Package;
use crate::config::Config;
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

fn clean_source_files(packages: &AHashMap<String, Package>, root_config: &Config) {
    let mut rescript_file_locations = Vec::new();
    for package in packages.values() {
        let Some(source_files) = &package.source_files else {
            continue;
        };
        for source_file in source_files.keys().filter(|source_file| {
            source_file
                .extension()
                .and_then(|extension| extension.to_str())
                .is_some_and(helpers::is_implementation_file)
        }) {
            for spec in root_config.get_package_specs() {
                let output_base = if spec.in_source {
                    package.path.join(source_file)
                } else {
                    package
                        .path
                        .join("lib")
                        .join(spec.get_out_of_source_dir())
                        .join(source_file)
                };
                let suffix = match &spec.suffix {
                    None => root_config.get_suffix(&spec),
                    Some(suffix) => suffix.clone(),
                };
                rescript_file_locations.push((output_base, suffix));
            }
        }
    }

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
    if build_state.build_run.stopped_at_parse() {
        return;
    }
    let digests = build::incremental::UnitDigests::of_compiled(build_state);
    crate::build::phase_mark("record-digests");
    let compiles = build::incremental::CompileRecords::lock(build_state);
    build_state
        .packages
        .par_iter()
        .for_each(|(package_name, package)| {
            let record = build::incremental::current_record(build_state, &compiles, package_name, &digests);
            let previous = build_state
                .previous_in_process
                .as_ref()
                .and_then(|previous| previous.packages.get(package_name))
                .map(|record| &record.state);
            let current: AHashSet<&str> = record
                .meta
                .get(build::state_db::META_OUTPUTS)
                .map(|outputs| outputs.lines().collect())
                .unwrap_or_default();
            remove_obsolete_outputs(package, build_state.recorded_outputs.get(package_name), &current);
            build::state_db::write_record(package, previous, &record);
            build::state_db::remove_legacy_files(package);
        });
}

/// Remove the outputs the recorded build had that this one no longer
/// produces (see [`remove_obsolete_outputs`]) now, rather than when the build
/// is recorded: a watcher records its builds only before it reinitializes and
/// when it exits.
pub fn remove_obsolete_outputs_of_build(build_state: &BuildCommandState) {
    build_state
        .packages
        .par_iter()
        .for_each(|(package_name, package)| {
            let Some(previous) = build_state.recorded_outputs.get(package_name) else {
                return;
            };
            let expected = build::incremental::expected_outputs(build_state, package_name);
            let current: AHashSet<&str> = expected.iter().map(String::as_str).collect();
            remove_obsolete_outputs(package, Some(previous), &current);
        });
}

/// The output files each package's last recorded build listed.
pub fn recorded_outputs(
    metas: &AHashMap<String, std::collections::BTreeMap<String, String>>,
) -> AHashMap<String, AHashSet<String>> {
    metas
        .par_iter()
        .filter_map(|(name, meta)| {
            let outputs = meta.get(build::state_db::META_OUTPUTS)?;
            Some((
                name.clone(),
                outputs.lines().map(str::to_string).collect::<AHashSet<_>>(),
            ))
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect()
}

/// Remove the files the previous build's sources compiled to that the
/// current configuration no longer produces (another suffix or package spec,
/// genType turned off, or a removed source). GenType files are removed only
/// when genType wrote them.
fn remove_obsolete_outputs(package: &Package, previous: Option<&AHashSet<String>>, current: &AHashSet<&str>) {
    let Some(previous) = previous else {
        return;
    };
    for output in previous {
        if current.contains(output.as_str()) {
            continue;
        }
        let file = package.path.join(output);
        if output.contains(".gen.") && !written_by_gentype(&file) {
            continue;
        }
        let _ = std::fs::remove_file(&file);
        let mut map_file = file.into_os_string();
        map_file.push(".map");
        let _ = std::fs::remove_file(PathBuf::from(map_file));
    }
}

/// Whether `file` starts with the header genType writes, i.e. genType owns it.
fn written_by_gentype(file: &Path) -> bool {
    const HEADER: &[u8] = b"/* TypeScript file generated from";
    let mut prefix = [0u8; HEADER.len()];
    std::fs::File::open(file)
        .and_then(|mut f| std::io::Read::read_exact(&mut f, &mut prefix))
        .is_ok_and(|()| prefix == HEADER)
}

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
    if written_by_gentype(&file) {
        let _ = std::fs::remove_file(file);
    }
}

/// Read the previous in-process build's records and remove the outputs of
/// sources it compiled that no longer exist: the JS output and any typed
/// artifacts in `lib/bs` and `lib/ocaml`. Returns (removed sources, recorded
/// sources).
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
    // Recording a large build encodes and hashes every module it compiled.
    build::pools::with_pool_for(build_state.compiled_modules.len(), || {
        write_in_process_record(build_state)
    });
    crate::build::phase_mark("record-written");
}

#[instrument(name = "clean.clean", skip_all)]
pub fn clean(path: &Path, show_progress: bool, plain_output: bool, prod: bool) -> Result<()> {
    let project_context = ProjectContext::new(path)?;
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
    let root_config = project_context.get_root_config();
    let suffix_for_print = root_config
        .get_package_specs()
        .iter()
        .map(|spec| root_config.get_suffix(spec))
        .collect::<Vec<String>>()
        .join(", ");

    if !plain_output && show_progress {
        print!(
            "{} {}Cleaning {} files...",
            style("[2/2]").bold().dim(),
            SWEEP,
            suffix_for_print
        );
        let _ = std::io::stdout().flush();
    }

    clean_source_files(&packages, root_config);
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
