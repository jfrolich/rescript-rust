//! Timestamp-based incremental builds for the in-process compiler.
//!
//! In-process builds keep no compiler artifacts on disk, so a new process
//! knows nothing about the previous build except its outputs: the JavaScript
//! files and the per-package source manifest written by
//! [`super::clean::write_in_process_manifest`]. A module is up to date when
//! its JavaScript is newer than every source it was compiled from: its own
//! implementation and interface, those of every module it depends on
//! (transitively), and the configuration files that shape its compilation.
//!
//! Modules are planned into three groups:
//!
//! - stale modules, and everything that depends on them, compile and write
//!   their JavaScript (the existing compile universe);
//! - support modules, the unchanged dependencies of those, compile without
//!   rendering or writing JavaScript: the registry needs their signatures and
//!   backend metadata, which nothing on disk records;
//! - every other module is not compiled at all.
//!
//! Without a saved signature to compare against, a changed module is assumed
//! to change its interface, so all of its dependents are recompiled.
//!
//! The warnings of the previous build are saved next to the manifest and
//! reported again for the modules that are not recompiled, as the build does
//! for any module it does not recompile.

use super::build_types::{BuildCommandState, Module, SourceType};
use super::packages::Package;
use crate::config::{Config, SourceMapCommand};
use ahash::{AHashMap, AHashSet};
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// The manifest line that records when the previous build started and
/// whether it finished without errors.
const BUILD_HEADER: &str = "#build";
/// Per-package file with the warnings of the previous build, by module.
pub const WARNINGS_FILE: &str = "in-process-warnings.json";

/// A module's warnings from the build that last compiled it.
#[derive(Debug, Default, Clone, serde::Serialize, serde::Deserialize)]
pub struct StoredWarnings {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub implementation: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interface: Option<String>,
}

/// What one package's manifest recorded about the previous build.
#[derive(Debug, Default)]
pub struct PackageRecord {
    /// When the previous build started, if it finished without errors.
    pub clean_build_started_at: Option<SystemTime>,
    /// Each module's recorded source paths, sorted.
    pub sources: AHashMap<String, Vec<PathBuf>>,
    /// When each module's JavaScript was last known to be up to date.
    pub js_confirmed_at: AHashMap<String, SystemTime>,
    /// The warnings of the modules that warned.
    pub warnings: AHashMap<String, StoredWarnings>,
    /// The package's parse warnings, by source file.
    pub parse_warnings: std::collections::BTreeMap<String, String>,
}

/// The per-package warnings file.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct PackageWarnings {
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    parse: std::collections::BTreeMap<String, String>,
    #[serde(default)]
    modules: std::collections::BTreeMap<String, StoredWarnings>,
}

/// The previous in-process build, as recorded by the package manifests.
#[derive(Debug, Default)]
pub struct PreviousInProcessBuild {
    pub packages: AHashMap<String, PackageRecord>,
}

/// The incremental part of a fresh in-process build's plan, consumed by
/// [`super::compile::compile`].
#[derive(Debug, Default)]
pub struct IncrementalPlan {
    /// Watch mode keeps every module in memory for later rebuilds and editor
    /// tooling, so every up-to-date module is a support module.
    pub support_everything: bool,
}

pub fn parse_manifest(content: &str) -> PackageRecord {
    let mut record = PackageRecord::default();
    for line in content.lines() {
        let mut columns = line.split('\t');
        let (Some(first), Some(second)) = (columns.next(), columns.next()) else {
            continue;
        };
        if first == BUILD_HEADER {
            let ok = columns.next() == Some("1");
            record.clean_build_started_at = parse_time(second).filter(|_| ok);
            continue;
        }
        record
            .sources
            .entry(first.to_string())
            .or_default()
            .push(PathBuf::from(second));
        if let Some(confirmed) = columns.next().and_then(parse_time) {
            record.js_confirmed_at.insert(first.to_string(), confirmed);
        }
    }
    for paths in record.sources.values_mut() {
        paths.sort();
    }
    record
}

/// Read a package's warnings file into its record.
pub fn read_warnings(content: &str, record: &mut PackageRecord) {
    let warnings: PackageWarnings = serde_json::from_str(content).unwrap_or_default();
    record.parse_warnings = warnings.parse;
    record.warnings = warnings.modules.into_iter().collect();
}

/// The warnings file of a package, `None` when nothing warned.
pub fn render_warnings<'a>(
    parse_warnings: std::collections::BTreeMap<String, String>,
    modules: impl Iterator<Item = (&'a String, &'a Module)>,
) -> Option<String> {
    let mut warnings = std::collections::BTreeMap::new();
    for (module_name, module) in modules {
        let SourceType::SourceFile(source_file) = &module.source_type else {
            continue;
        };
        let stored = StoredWarnings {
            implementation: source_file.implementation.compile_warnings.clone(),
            interface: source_file
                .interface
                .as_ref()
                .and_then(|interface| interface.compile_warnings.clone()),
        };
        if stored.implementation.is_some() || stored.interface.is_some() {
            warnings.insert(module_name.clone(), stored);
        }
    }
    let file = PackageWarnings {
        parse: parse_warnings,
        modules: warnings,
    };
    (!file.parse.is_empty() || !file.modules.is_empty())
        .then(|| serde_json::to_string(&file).unwrap_or_default())
}

/// The saved parse warnings, restored for a build that parses nothing:
/// recorded for the next manifest and appended to each package's log.
/// Returns them for printing.
pub fn restore_parse_warnings(build_state: &BuildCommandState) -> String {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return String::new();
    };
    let mut packages: Vec<&String> = previous.packages.keys().collect();
    packages.sort();
    let mut all = String::new();
    let mut recorded = build_state.parse_warnings.lock().unwrap();
    for package_name in packages {
        let Some(package) = build_state.get_package(package_name) else {
            continue;
        };
        for (key, text) in &previous.packages[package_name].parse_warnings {
            super::logs::append(package, text);
            recorded.insert(key.clone(), (package_name.clone(), text.clone()));
            all.push_str(text);
        }
    }
    all
}

/// Report the saved warnings of the modules in `up_to_date` again.
fn restore_warnings(build_state: &mut BuildCommandState, up_to_date: &dyn Fn(&str) -> bool) {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return;
    };
    for (module_name, module) in build_state.build_state.modules.iter_mut() {
        if !up_to_date(module_name) {
            continue;
        }
        let Some(stored) = previous
            .packages
            .get(&module.package_name)
            .and_then(|record| record.warnings.get(module_name))
        else {
            continue;
        };
        let SourceType::SourceFile(source_file) = &mut module.source_type else {
            continue;
        };
        source_file.implementation.compile_warnings = stored.implementation.clone();
        if let Some(interface) = source_file.interface.as_mut() {
            interface.compile_warnings = stored.interface.clone();
        }
    }
}

/// Render a package manifest. `entries` must be sorted.
pub fn render_manifest(
    entries: &[(String, PathBuf)],
    js_confirmed_at: &AHashMap<String, SystemTime>,
    build_started_at: Option<SystemTime>,
    build_ok: bool,
) -> String {
    let mut content = String::new();
    if let Some(started) = build_started_at {
        content.push_str(&format!(
            "{BUILD_HEADER}\t{}\t{}\n",
            format_time(started),
            if build_ok { "1" } else { "0" }
        ));
    }
    for (module_name, path) in entries {
        content.push_str(module_name);
        content.push('\t');
        content.push_str(&path.to_string_lossy());
        if let Some(confirmed) = js_confirmed_at.get(module_name) {
            content.push('\t');
            content.push_str(&format_time(*confirmed));
        }
        content.push('\n');
    }
    content
}

fn format_time(time: SystemTime) -> String {
    let since = time.duration_since(UNIX_EPOCH).unwrap_or_default();
    format!("{}.{:09}", since.as_secs(), since.subsec_nanos())
}

fn parse_time(text: &str) -> Option<SystemTime> {
    let (secs, nanos) = text.split_once('.')?;
    let duration = Duration::new(secs.parse().ok()?, nanos.parse().ok()?);
    UNIX_EPOCH.checked_add(duration)
}

/// Whether incremental planning applies: a fresh in-process build that does
/// not have to dump every module's typed tree.
pub fn applies(build_state: &BuildCommandState) -> bool {
    build_state.build_mode().is_in_process()
        && !build_state.dump_typed_sexp()
        && build_state.previous_in_process.is_some()
        && std::env::var_os("RESCRIPT_FULL_BUILD").is_none()
}

fn mtime(path: &Path) -> Option<SystemTime> {
    std::fs::metadata(path)
        .and_then(|metadata| metadata.modified())
        .ok()
}

/// The source files a module is compiled from, relative to its package.
fn source_paths(module: &Module) -> Option<Vec<&Path>> {
    let SourceType::SourceFile(source_file) = &module.source_type else {
        return None;
    };
    let mut paths = vec![source_file.implementation.path.as_path()];
    if let Some(interface) = &source_file.interface {
        paths.push(interface.path.as_path());
    }
    Some(paths)
}

/// The newest of a module's own inputs: its sources and `config_time`, the
/// newer of its package's and the root configuration. `None` if one is
/// unreadable.
fn newest_own_input(module: &Module, package: &Package, config_time: Option<SystemTime>) -> Option<SystemTime> {
    let mut newest = config_time?;
    for path in source_paths(module)? {
        newest = newest.max(mtime(&package.path.join(path))?);
    }
    Some(newest)
}

/// The oldest modification time of a module's JavaScript outputs, `None` if
/// one is missing.
fn oldest_output(module: &Module, package: &Package, root_config: &Config) -> Option<SystemTime> {
    let SourceType::SourceFile(source_file) = &module.source_type else {
        return None;
    };
    let targets =
        super::compile::js_output_targets_for_source(package, &source_file.implementation.path, root_config);
    let mut oldest: Option<SystemTime> = None;
    for target in targets {
        let time = mtime(&target.path)?;
        oldest = Some(oldest.map_or(time, |oldest| oldest.min(time)));
    }
    oldest
}

/// Whether the manifest recorded exactly this module's current sources.
fn recorded_as_is(module_name: &str, module: &Module, record: Option<&PackageRecord>) -> bool {
    let (Some(record), Some(mut paths)) = (record, source_paths(module)) else {
        return false;
    };
    paths.sort();
    record
        .sources
        .get(module_name)
        .is_some_and(|recorded| recorded.iter().map(PathBuf::as_path).eq(paths.into_iter()))
}

/// Facts about one source module, gathered from the file system.
struct ModuleTimes {
    recorded: bool,
    newest_input: Option<SystemTime>,
    /// When the JavaScript was last known to be up to date: the oldest output
    /// file's modification time, or the recorded build start if later. `None`
    /// when an output is missing.
    output: Option<SystemTime>,
    js_confirmed_at: Option<SystemTime>,
}

fn module_times(build_state: &BuildCommandState) -> AHashMap<String, ModuleTimes> {
    let previous = build_state.previous_in_process.as_ref();
    let root_config = build_state.get_root_config();
    let root_config_time = mtime(&root_config.path);
    let config_times: AHashMap<&String, Option<SystemTime>> = build_state
        .packages
        .iter()
        .map(|(name, package)| {
            let package_time = mtime(&package.config.path);
            (name, root_config_time.zip(package_time).map(|(a, b)| a.max(b)))
        })
        .collect();
    build_state
        .modules
        .par_iter()
        .filter(|(_, module)| !module.is_mlmap())
        .map(|(module_name, module)| {
            let package = build_state.get_package(&module.package_name).expect("package");
            let record = previous.and_then(|previous| previous.packages.get(&module.package_name));
            if !recorded_as_is(module_name, module, record) {
                // Stale whatever its files say, and so is everything that
                // depends on it.
                let times = ModuleTimes {
                    recorded: false,
                    newest_input: None,
                    output: None,
                    js_confirmed_at: None,
                };
                return (module_name.clone(), times);
            }
            let js_confirmed_at = record.and_then(|record| record.js_confirmed_at.get(module_name).copied());
            let output = oldest_output(module, package, root_config)
                .map(|oldest| js_confirmed_at.map_or(oldest, |confirmed| oldest.max(confirmed)));
            let times = ModuleTimes {
                recorded: true,
                newest_input: newest_own_input(module, package, config_times[&module.package_name]),
                output,
                js_confirmed_at,
            };
            (module_name.clone(), times)
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect()
}

/// Whether the previous build left every module up to date, decided before
/// any source is parsed. This holds when the previous build finished without
/// errors, recorded exactly the current sources, and started after every
/// input was last modified, and every JavaScript output still exists. The
/// saved warnings are then restored for reporting.
pub fn everything_up_to_date(build_state: &mut BuildCommandState) -> bool {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return false;
    };
    if !build_state.deleted_modules.is_empty() {
        return false;
    }
    let times = module_times(build_state);
    times
        .iter()
        .all(|(module_name, times)| {
            let module = &build_state.modules[module_name];
            let Some(started) = previous
                .packages
                .get(&module.package_name)
                .and_then(|record| record.clean_build_started_at)
            else {
                return false;
            };
            times.recorded
                && times.output.is_some()
                && times.newest_input.is_some_and(|newest| newest < started)
        })
        .then(|| {
            restore_warnings(build_state, &|_| true);
            carry_js_confirmed_at(build_state, &times, &|_| true);
        })
        .is_some()
}

/// Keep the recorded confirmation times of modules this build does not
/// recompile, for the next manifest.
fn carry_js_confirmed_at(
    build_state: &mut BuildCommandState,
    times: &AHashMap<String, ModuleTimes>,
    up_to_date: &dyn Fn(&str) -> bool,
) {
    for (module_name, times) in times {
        if let Some(confirmed) = times.js_confirmed_at
            && up_to_date(module_name)
        {
            build_state.js_confirmed_at.insert(module_name.clone(), confirmed);
        }
    }
}

/// Mark the stale modules `compile_dirty` and the rest clean, and record the
/// plan for [`super::compile::compile`]. Needs the dependency graph.
pub fn plan(build_state: &mut BuildCommandState) {
    let times = module_times(build_state);

    // The newest input over each module's transitive dependencies. A
    // dependency cycle is a compile error reported later; it only has to
    // terminate here.
    fn newest_closure(
        module_name: &str,
        build_state: &BuildCommandState,
        times: &AHashMap<String, ModuleTimes>,
        memo: &mut AHashMap<String, Option<SystemTime>>,
        visiting: &mut AHashSet<String>,
    ) -> Option<SystemTime> {
        if let Some(known) = memo.get(module_name) {
            return *known;
        }
        if !visiting.insert(module_name.to_string()) {
            return None;
        }
        let mut newest = match times.get(module_name) {
            Some(times) => times.newest_input,
            // A namespace map has no sources of its own.
            None => Some(UNIX_EPOCH),
        };
        if let Some(module) = build_state.get_module(module_name) {
            for dep in &module.deps {
                if build_state.get_module(dep).is_none() {
                    continue;
                }
                let dep_newest = newest_closure(dep, build_state, times, memo, visiting);
                newest = match (newest, dep_newest) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    _ => None,
                };
            }
        }
        visiting.remove(module_name);
        memo.insert(module_name.to_string(), newest);
        newest
    }

    let mut memo = AHashMap::new();
    let mut visiting = AHashSet::new();
    let mut stale = AHashSet::new();
    let mut names: Vec<&String> = times.keys().collect();
    names.sort();
    for module_name in names {
        let own = &times[module_name];
        let newest = newest_closure(module_name, build_state, &times, &mut memo, &mut visiting);
        let up_to_date =
            own.recorded && matches!((newest, own.output), (Some(newest), Some(output)) if newest <= output);
        if !up_to_date {
            stale.insert(module_name.clone());
        }
    }

    log::debug!(
        "incremental build: {} of {} modules are stale",
        stale.len(),
        times.len()
    );
    for (module_name, module) in build_state.build_state.modules.iter_mut() {
        module.compile_dirty = stale.contains(module_name);
    }
    restore_warnings(build_state, &|module_name| !stale.contains(module_name));
    carry_js_confirmed_at(build_state, &times, &|module_name| !stale.contains(module_name));
    build_state.incremental_plan = Some(IncrementalPlan {
        support_everything: build_state.build_state.source_map_command == SourceMapCommand::Watch,
    });
}

/// The support modules of a compile universe: the modules to compile without
/// writing JavaScript.
pub fn support_modules(
    build_state: &BuildCommandState,
    universe: &AHashSet<String>,
    plan: &IncrementalPlan,
) -> AHashSet<String> {
    if plan.support_everything {
        return build_state
            .modules
            .keys()
            .filter(|module_name| !universe.contains(*module_name))
            .cloned()
            .collect();
    }
    let mut support = AHashSet::new();
    let mut frontier: Vec<&String> = universe.iter().collect();
    while let Some(module_name) = frontier.pop() {
        let Some(module) = build_state.get_module(module_name) else {
            continue;
        };
        for dep in &module.deps {
            if build_state.get_module(dep).is_some() && !universe.contains(dep) && support.insert(dep.clone())
            {
                frontier.push(dep);
            }
        }
    }
    support
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_round_trips_the_build_header() {
        let started = UNIX_EPOCH + Duration::new(1_700_000_000, 123_456_789);
        let entries = vec![
            ("A".to_string(), PathBuf::from("src/A.res")),
            ("A".to_string(), PathBuf::from("src/A.resi")),
            ("B".to_string(), PathBuf::from("src/B.res")),
        ];
        let confirmed = AHashMap::from_iter([("B".to_string(), started)]);
        let record = parse_manifest(&render_manifest(&entries, &confirmed, Some(started), true));
        assert_eq!(record.clean_build_started_at, Some(started));
        assert_eq!(
            record.sources["A"],
            vec![PathBuf::from("src/A.res"), PathBuf::from("src/A.resi")]
        );
        assert_eq!(record.sources["B"], vec![PathBuf::from("src/B.res")]);
        assert_eq!(record.js_confirmed_at.get("B"), Some(&started));
        assert_eq!(record.js_confirmed_at.get("A"), None);
    }

    #[test]
    fn a_failed_build_records_no_clean_start() {
        let started = UNIX_EPOCH + Duration::from_secs(5);
        let record = parse_manifest(&render_manifest(&[], &AHashMap::new(), Some(started), false));
        assert_eq!(record.clean_build_started_at, None);
    }

    #[test]
    fn old_manifests_without_a_header_still_parse() {
        let record = parse_manifest("A\tsrc/A.res\n");
        assert_eq!(record.clean_build_started_at, None);
        assert_eq!(record.sources["A"], vec![PathBuf::from("src/A.res")]);
    }

    #[test]
    fn warnings_file_reads_parse_and_module_warnings() {
        let text = r#"{"parse":{"C:impl":"parse warning"},"modules":{"A":{"implementation":"warning A"},"B":{"interface":"warning B"}}}"#;
        let mut record = PackageRecord::default();
        read_warnings(text, &mut record);
        assert_eq!(record.parse_warnings["C:impl"], "parse warning");
        assert_eq!(record.warnings["A"].implementation.as_deref(), Some("warning A"));
        assert_eq!(record.warnings["A"].interface, None);
        assert_eq!(record.warnings["B"].interface.as_deref(), Some("warning B"));
        let mut record = PackageRecord::default();
        read_warnings("not json", &mut record);
        assert!(record.warnings.is_empty() && record.parse_warnings.is_empty());
    }
}
