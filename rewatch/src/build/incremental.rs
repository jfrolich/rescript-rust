//! Timestamp-based incremental builds for the in-process compiler.
//!
//! In-process builds keep no compiler artifacts on disk, so a new process
//! knows nothing about the previous build except its outputs: the JavaScript
//! files and each package's build record in [`super::state_db`]. A module is
//! up to date when its JavaScript is newer than every source it was compiled
//! from: its own implementation and interface, those of every module it
//! depends on (transitively), and the configuration files that shape its
//! compilation.
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
//! The warnings of the previous build are recorded with it and reported again
//! for the modules that are not recompiled, as the build does for any module
//! it does not recompile.

use super::build_types::{BuildCommandState, Module, SourceType};
use super::packages::Package;
use super::state_db::{self, ModuleRow, PackageState, SourceDeps};
use crate::config::{Config, SourceMapCommand};
use ahash::{AHashMap, AHashSet};
use rayon::prelude::*;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// What one package's database recorded about the previous build.
#[derive(Debug, Default)]
pub struct PackageRecord {
    /// The record as read, to write back only what changed.
    pub state: PackageState,
    /// When the previous build started, if it finished without errors.
    pub clean_build_started_at: Option<SystemTime>,
    /// Each module's recorded source paths, sorted.
    pub sources: AHashMap<String, Vec<PathBuf>>,
}

impl PackageRecord {
    pub fn new(state: PackageState) -> Self {
        let clean_build_started_at = (state.meta.get(state_db::META_BUILD_OK).map(String::as_str)
            == Some("1"))
        .then(|| state_db::meta_time(&state.meta, state_db::META_BUILD_STARTED_AT))
        .flatten();
        let mut sources: AHashMap<String, Vec<PathBuf>> = AHashMap::new();
        for (path, module) in &state.sources {
            sources.entry(module.clone()).or_default().push(path.clone());
        }
        for paths in sources.values_mut() {
            paths.sort();
        }
        Self {
            state,
            clean_build_started_at,
            sources,
        }
    }

    fn js_confirmed_at(&self, module_name: &str) -> Option<SystemTime> {
        self.state.modules.get(module_name)?.js_confirmed_at
    }
}

/// The previous in-process build, as recorded by the package databases.
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

/// The build record to save for `package` after this build.
pub fn current_record(build_state: &BuildCommandState, package_name: &str) -> PackageState {
    let mut record = PackageState::default();
    if let Some(started) = build_state.build_started_at {
        record.meta.insert(
            state_db::META_BUILD_STARTED_AT.to_string(),
            state_db::nanos_from_time(started).to_string(),
        );
        record.meta.insert(
            state_db::META_BUILD_OK.to_string(),
            if build_state.last_build_ok { "1" } else { "0" }.to_string(),
        );
    }
    for (module_name, module) in build_state.modules.iter() {
        if module.package_name != package_name {
            continue;
        }
        let SourceType::SourceFile(source_file) = &module.source_type else {
            continue;
        };
        record
            .sources
            .insert(source_file.implementation.path.clone(), module_name.clone());
        if let Some(interface) = &source_file.interface {
            record.sources.insert(interface.path.clone(), module_name.clone());
        }
        record.modules.insert(
            module_name.clone(),
            ModuleRow {
                js_confirmed_at: build_state.js_confirmed_at.get(module_name).copied(),
                implementation_warnings: source_file.implementation.compile_warnings.clone(),
                interface_warnings: source_file
                    .interface
                    .as_ref()
                    .and_then(|interface| interface.compile_warnings.clone()),
            },
        );
    }
    let previous = build_state
        .previous_in_process
        .as_ref()
        .and_then(|previous| previous.packages.get(package_name));
    let in_memory_deps = build_state.in_memory_deps.lock().unwrap();
    for (module_name, module) in build_state.modules.iter() {
        if module.package_name != package_name {
            continue;
        }
        let SourceType::SourceFile(source_file) = &module.source_type else {
            continue;
        };
        let kinds: &[&str] = if source_file.interface.is_some() {
            &["impl", "intf"]
        } else {
            &["impl"]
        };
        for kind in kinds {
            let key = format!("{module_name}:{kind}");
            let row = match (in_memory_deps.get(&key), build_state.source_mtimes.get(&key)) {
                (Some(deps), Some(mtime)) => Some(SourceDeps {
                    mtime: *mtime,
                    deps: deps.iter().cloned().collect(),
                }),
                // Not parsed in this build: the recorded row still holds.
                _ => previous.and_then(|previous| previous.state.deps.get(&key).cloned()),
            };
            if let Some(row) = row {
                record.deps.insert(key, row);
            }
        }
    }
    drop(in_memory_deps);
    record.parse_warnings = build_state
        .parse_warnings
        .lock()
        .unwrap()
        .iter()
        .filter(|(_, (package, _))| package == package_name)
        .map(|(key, (_, text))| (key.clone(), text.clone()))
        .collect::<BTreeMap<_, _>>();
    record
}

/// The saved parse warnings, restored for a build that parses nothing:
/// recorded for the next build record and appended to each package's log.
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
        for (key, text) in &previous.packages[package_name].state.parse_warnings {
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
            .and_then(|record| record.state.modules.get(module_name))
        else {
            continue;
        };
        let SourceType::SourceFile(source_file) = &mut module.source_type else {
            continue;
        };
        source_file.implementation.compile_warnings = stored.implementation_warnings.clone();
        if let Some(interface) = source_file.interface.as_mut() {
            interface.compile_warnings = stored.interface_warnings.clone();
        }
    }
}

/// The source files of a module, keyed `Module:impl` / `Module:intf`, with
/// their paths relative to the package.
fn source_keys<'a>(module_name: &str, module: &'a Module) -> Vec<(String, &'a Path)> {
    let SourceType::SourceFile(source_file) = &module.source_type else {
        return Vec::new();
    };
    let mut keys = vec![(
        format!("{module_name}:impl"),
        source_file.implementation.path.as_path(),
    )];
    if let Some(interface) = &source_file.interface {
        keys.push((format!("{module_name}:intf"), interface.path.as_path()));
    }
    keys
}

/// Read every source file's modification time, before anything is parsed.
pub fn collect_source_mtimes(build_state: &mut BuildCommandState) {
    let mtimes: Vec<(String, i64)> = build_state
        .modules
        .par_iter()
        .flat_map_iter(|(module_name, module)| {
            let package = build_state.get_package(&module.package_name).expect("package");
            source_keys(module_name, module)
                .into_iter()
                .filter_map(|(key, path)| {
                    mtime(&package.path.join(path)).map(|time| (key, state_db::nanos_from_time(time)))
                })
                .collect::<Vec<_>>()
        })
        .collect();
    build_state.source_mtimes = mtimes.into_iter().collect();
}

/// Use the recorded module references of every source file that has not
/// changed since it was last parsed, and mark the others for parsing. Run
/// after [`collect_source_mtimes`].
pub fn seed_recorded_deps(build_state: &mut BuildCommandState) {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return;
    };
    let mut seeded = Vec::new();
    let mut to_parse = AHashSet::new();
    for (module_name, module) in build_state.build_state.modules.iter() {
        let keys = source_keys(module_name, module);
        if keys.is_empty() {
            continue;
        }
        let record = previous.packages.get(&module.package_name);
        let recorded: Option<Vec<(String, &SourceDeps)>> = keys
            .iter()
            .map(|(key, _)| {
                let row = record?.state.deps.get(key)?;
                (build_state.source_mtimes.get(key) == Some(&row.mtime)).then(|| (key.clone(), row))
            })
            .collect();
        match recorded {
            Some(rows) => seeded.extend(rows),
            None => {
                to_parse.insert(module_name.clone());
            }
        }
    }
    {
        let mut in_memory_deps = build_state.in_memory_deps.lock().unwrap();
        for (key, row) in seeded {
            in_memory_deps.insert(key, row.deps.iter().cloned().collect());
        }
    }
    for (module_name, module) in build_state.build_state.modules.iter_mut() {
        let parse = to_parse.contains(module_name);
        if let SourceType::SourceFile(source_file) = &mut module.source_type {
            source_file.implementation.parse_dirty = parse;
            if let Some(interface) = source_file.interface.as_mut() {
                interface.parse_dirty = parse;
            }
        }
        module.compile_dirty = parse;
    }
}

/// The modules a compile of `stale` touches: those it compiles and writes,
/// and the support modules it compiles for the registry.
fn modules_to_compile(build_state: &BuildCommandState, stale: &AHashSet<String>) -> AHashSet<String> {
    let mut universe = stale.clone();
    let mut frontier: Vec<String> = stale.iter().cloned().collect();
    while let Some(module_name) = frontier.pop() {
        if let Some(module) = build_state.get_module(&module_name) {
            for dependent in &module.dependents {
                if universe.insert(dependent.clone()) {
                    frontier.push(dependent.clone());
                }
            }
        }
    }
    let plan = build_state
        .incremental_plan
        .as_ref()
        .expect("planned before choosing what to parse");
    let support = support_modules(build_state, &universe, plan);
    universe.extend(support);
    universe
}

/// Parse an incremental build in two rounds: first the source files that
/// changed (the rest of the dependency graph is recorded), then, once the
/// plan is known, the unchanged modules it compiles. Every other module is
/// never parsed. Returns the parse warnings to report.
pub fn parse_and_plan(build_state: &mut BuildCommandState, inc: impl Fn() + Sync) -> anyhow::Result<String> {
    let mut warnings = super::parse::generate_asts(build_state, &inc)?;
    let deleted_modules = build_state.deleted_modules.clone();
    super::deps::get_deps(build_state, &deleted_modules);
    plan(build_state);
    super::compile::mark_modules_with_deleted_deps_dirty(&mut build_state.build_state);
    let stale: AHashSet<String> = build_state
        .modules
        .iter()
        .filter(|(_, module)| module.compile_dirty)
        .map(|(module_name, _)| module_name.clone())
        .collect();
    let needed = modules_to_compile(build_state, &stale);
    {
        let stored_asts = build_state.stored_asts.lock().unwrap();
        let unparsed: Vec<String> = needed
            .into_iter()
            .filter(|module_name| !stored_asts.contains_key(&format!("{module_name}:impl")))
            .collect();
        drop(stored_asts);
        for module_name in unparsed {
            if let Some(module) = build_state.build_state.modules.get_mut(&module_name)
                && let SourceType::SourceFile(source_file) = &mut module.source_type
            {
                source_file.implementation.parse_dirty = true;
                if let Some(interface) = source_file.interface.as_mut() {
                    interface.parse_dirty = true;
                }
            }
        }
    }
    warnings.push_str(&super::parse::generate_asts(build_state, &inc)?);
    // Parsing marks what it parsed for compilation; the plan decides.
    for (module_name, module) in build_state.build_state.modules.iter_mut() {
        module.compile_dirty = stale.contains(module_name);
    }
    warnings.push_str(&restore_unparsed_parse_warnings(build_state));
    Ok(warnings)
}

/// The saved parse warnings of source files this build did not parse:
/// recorded for the next build record and appended to the package log.
/// Returns them for printing.
fn restore_unparsed_parse_warnings(build_state: &BuildCommandState) -> String {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return String::new();
    };
    let stored_asts = build_state.stored_asts.lock().unwrap();
    let mut recorded = build_state.parse_warnings.lock().unwrap();
    let mut restored: Vec<(&String, &String, &String)> = Vec::new();
    for (package_name, record) in &previous.packages {
        for (key, text) in &record.state.parse_warnings {
            let module_name = key.rsplit_once(':').map_or(key.as_str(), |(name, _)| name);
            let still_this_package = build_state
                .modules
                .get(module_name)
                .is_some_and(|module| &module.package_name == package_name);
            if still_this_package && !stored_asts.contains_key(key) && !recorded.contains_key(key) {
                restored.push((package_name, key, text));
            }
        }
    }
    restored.sort();
    let mut all = String::new();
    for (package_name, key, text) in restored {
        if let Some(package) = build_state.get_package(package_name) {
            super::logs::append(package, text);
        }
        recorded.insert(key.clone(), (package_name.clone(), text.clone()));
        all.push_str(text);
    }
    all
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
fn newest_own_input(
    module: &Module,
    package: &Package,
    config_time: Option<SystemTime>,
) -> Option<SystemTime> {
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
            let js_confirmed_at = record.and_then(|record| record.js_confirmed_at(module_name));
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
    use std::time::Duration;

    #[test]
    fn a_record_knows_its_clean_start_and_sources() {
        let started = UNIX_EPOCH + Duration::new(1_700_000_000, 123_456_789);
        let mut state = PackageState::default();
        state.meta.insert(
            state_db::META_BUILD_STARTED_AT.to_string(),
            state_db::nanos_from_time(started).to_string(),
        );
        state
            .meta
            .insert(state_db::META_BUILD_OK.to_string(), "1".to_string());
        state.sources.insert(PathBuf::from("src/A.resi"), "A".to_string());
        state.sources.insert(PathBuf::from("src/A.res"), "A".to_string());
        let record = PackageRecord::new(state.clone());
        assert_eq!(record.clean_build_started_at, Some(started));
        assert_eq!(
            record.sources["A"],
            vec![PathBuf::from("src/A.res"), PathBuf::from("src/A.resi")]
        );

        state
            .meta
            .insert(state_db::META_BUILD_OK.to_string(), "0".to_string());
        assert_eq!(PackageRecord::new(state).clean_build_started_at, None);
    }
}
