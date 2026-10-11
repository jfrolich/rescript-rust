//! Incremental builds for the in-process compiler.
//!
//! In-process builds keep no compiler artifacts on disk, so a new process
//! knows nothing about the previous build except its outputs: the JavaScript
//! files and each package's build record in [`super::state_db`]. Besides
//! timestamps, the record keeps for every module:
//!
//! - the digest of what other modules can read of it (its signature and JS
//!   metadata, see `ModuleRegistry::interface_digest`), and per top-level
//!   item (`rescript_compiler::cmi::item_deps`);
//! - for every unit its compile read (the units the compiler loaded, not the
//!   syntactic dependencies), that unit's digest then, and which of its
//!   items the compile read with their combined digest. The items read come
//!   from the typed tree, closed over the declarations they reach and over
//!   module aliases; `open`, `include` and whole-module uses read all items.
//!
//! A module is stale when its own sources or configuration changed since its
//! JavaScript was written, when a module it references is new, or when an
//! item it read of another unit now has a different digest. A build then
//! compiles in rounds:
//!
//! - the modules to write compile and write their JavaScript;
//! - support modules, their unchanged dependencies, compile without rendering
//!   or writing JavaScript: the registry needs their signatures and backend
//!   metadata, which nothing on disk records;
//! - once a round is done, the modules that read an item that changed are
//!   written in the next round (see [`next_round`]). An edit that keeps a
//!   module's interface recompiles only that module, and one that changes
//!   some items only the modules that read those.
//!
//! Every other module is not compiled, nor parsed. Watch mode keeps the
//! earlier behavior: it compiles every module into memory anyway, and
//! recompiles every transitive dependent of a stale module.
//!
//! The warnings of the previous build are recorded with it and reported again
//! for the modules that are not recompiled, as the build does for any module
//! it does not recompile.

use super::build_types::{BuildCommandState, Module, SourceType};
use super::packages::Package;
use super::state_db::{self, ItemDigests, ModuleRow, PackageState, SourceDeps, UnitReads};
use crate::config::{Config, SourceMapCommand};
use ahash::{AHashMap, AHashSet};
use rayon::prelude::*;
use rescript_compiler::cmi::item_deps;
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
    /// Compile the dependents of a recompiled module only when its interface
    /// digest changed, in rounds (see [`next_round`]), instead of compiling
    /// every transitive dependent.
    pub cutoff: bool,
}

/// A unit's interface digest (its whole-unit item digest) with its item
/// digests.
fn whole_and_items(items: ItemDigests) -> (u64, ItemDigests) {
    (items[item_deps::WHOLE], items)
}

/// The build record to save for `package` after this build.
/// The interface and item digests of registered modules, computed once for
/// a set of lookups.
pub struct UnitDigests {
    registry: rescript_compiler::cmi::persistent_env::ModuleRegistry,
    cache: std::sync::Mutex<AHashMap<String, Option<std::sync::Arc<(u64, ItemDigests)>>>>,
    /// Computed up front for every module (see [`UnitDigests::all`]).
    all: Option<AHashMap<String, std::sync::Arc<(u64, ItemDigests)>>>,
}

impl UnitDigests {
    pub fn new(build_state: &BuildCommandState) -> Self {
        Self {
            registry: build_state.snapshot_module_registry(),
            cache: std::sync::Mutex::new(AHashMap::new()),
            all: None,
        }
    }

    /// The digests of every registered module of the build, computed in
    /// parallel.
    pub fn all(build_state: &BuildCommandState) -> Self {
        let registry = build_state.snapshot_module_registry();
        let all = build_state
            .modules
            .par_iter()
            .filter_map(|(module_name, _)| {
                let digests = whole_and_items(registry.item_digests(module_name)?);
                Some((module_name.clone(), std::sync::Arc::new(digests)))
            })
            .collect::<Vec<_>>()
            .into_iter()
            .collect();
        Self {
            registry,
            cache: std::sync::Mutex::new(AHashMap::new()),
            all: Some(all),
        }
    }

    /// What the inlinable bodies of the items in `resolved` refer to (see
    /// `ModuleRegistry::lambda_reads`), with every module's JS metadata final.
    pub fn lambda_reads(
        &self,
        resolved: &BTreeMap<String, std::collections::BTreeSet<String>>,
    ) -> BTreeMap<String, std::collections::BTreeSet<String>> {
        self.registry.lambda_reads(resolved)
    }

    /// The module's interface encoded for storage.
    pub fn encode(
        &self,
        module_name: &str,
        alias_rewrites: &[(String, rescript_compiler::types::path::Path)],
    ) -> Option<Vec<u8>> {
        self.registry.encode_stored_module(module_name, alias_rewrites)
    }

    /// The module's interface digest and item digests, `None` when it is not
    /// registered.
    pub fn get(&self, module_name: &str) -> Option<std::sync::Arc<(u64, ItemDigests)>> {
        if let Some(all) = &self.all {
            return all.get(module_name).cloned();
        }
        if let Some(known) = self.cache.lock().unwrap().get(module_name) {
            return known.clone();
        }
        let computed = self
            .registry
            .item_digests(module_name)
            .map(|items| std::sync::Arc::new(whole_and_items(items)));
        self.cache
            .lock()
            .unwrap()
            .insert(module_name.to_string(), computed.clone());
        computed
    }
}

pub fn current_record(
    build_state: &BuildCommandState,
    package_name: &str,
    digests: &UnitDigests,
) -> PackageState {
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
    // The interfaces of the modules this build compiled, where they differ
    // from the stored ones (by content: the interface digest leaves out
    // locations, which the stored interface keeps).
    let stored = build_state
        .previous_in_process
        .as_ref()
        .and_then(|previous| previous.packages.get(package_name))
        .map(|record| &record.state.stored_interfaces);
    let alias_rewrites = build_state.module_alias_rewrites.lock().unwrap().clone();
    record.interface_updates = build_state
        .compiled_modules
        .par_iter()
        .filter(|module_name| {
            build_state
                .get_module(module_name)
                .is_some_and(|module| module.package_name == package_name && !module.compile_dirty)
        })
        .filter_map(|module_name| {
            let aliases = alias_rewrites.get(module_name).map(Vec::as_slice).unwrap_or(&[]);
            let data = digests.encode(module_name, aliases)?;
            let hash = blake3::hash(&data);
            let content = u64::from_le_bytes(hash.as_bytes()[..8].try_into().expect("8 bytes"));
            if stored.and_then(|stored| stored.get(module_name)) == Some(&content) {
                return None;
            }
            Some((module_name.clone(), (content, data)))
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect();
    let mut written: AHashMap<&String, WrittenRecord> = build_state
        .modules
        .par_iter()
        .filter(|(_, module)| module.package_name == package_name)
        .filter_map(|(module_name, _)| {
            Some((module_name, written_interface(build_state, module_name, digests)?))
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect();
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
        // A module this build did not write keeps what its last written
        // compile read and published, with the imports this build checked
        // item by item brought up to date.
        let (interface_digest, imports) = match written.remove(module_name) {
            Some(written) => {
                record.reads_updates.insert(module_name.clone(), written.reads);
                record.items_updates.insert(module_name.clone(), written.items);
                (Some(written.digest), Some(written.imports))
            }
            None => recorded_row(build_state, module_name)
                .filter(|_| !build_state.written_modules.contains(module_name))
                .map_or((None, None), |row| {
                    let verified = build_state.verified_imports.lock().unwrap();
                    let imports = row.imports.clone().map(|imports| {
                        imports
                            .into_iter()
                            .map(|(unit, digest)| {
                                let now = verified.get(module_name).and_then(|units| units.get(&unit));
                                let digest = now.copied().unwrap_or(digest);
                                (unit, digest)
                            })
                            .collect()
                    });
                    (row.interface_digest, imports)
                }),
        };
        // A module that is still dirty was stale but not compiled (a failed
        // module, or one depending on it): what it records must not make it
        // look up to date to the next build.
        let invalidated = build_state.invalidated_modules.contains(module_name) || module.compile_dirty;
        let (interface_digest, imports) = if invalidated {
            (None, None)
        } else {
            (interface_digest, imports)
        };
        record.modules.insert(
            module_name.clone(),
            ModuleRow {
                js_confirmed_at: (!invalidated)
                    .then(|| build_state.js_confirmed_at.get(module_name).copied())
                    .flatten(),
                implementation_warnings: source_file.implementation.compile_warnings.clone(),
                interface_warnings: source_file
                    .interface
                    .as_ref()
                    .and_then(|interface| interface.compile_warnings.clone()),
                interface_digest,
                imports,
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
    let plan = build_state
        .incremental_plan
        .as_ref()
        .expect("planned before choosing what to parse");
    let mut universe = stale.clone();
    let mut frontier: Vec<String> = if plan.cutoff {
        Vec::new()
    } else {
        stale.iter().cloned().collect()
    };
    while let Some(module_name) = frontier.pop() {
        if let Some(module) = build_state.get_module(&module_name) {
            for dependent in &module.dependents {
                if universe.insert(dependent.clone()) {
                    frontier.push(dependent.clone());
                }
            }
        }
    }
    let support = support_modules(build_state, &universe, plan);
    // Support modules with a stored interface are loaded, not parsed.
    let loadable = if plan.cutoff {
        stored_loadable(build_state, stale, &support)
    } else {
        AHashSet::new()
    };
    universe.extend(
        support
            .into_iter()
            .filter(|module_name| !loadable.contains(module_name)),
    );
    universe
}

/// Of the support modules of a round, those whose stored interface can
/// stand in for compiling them: modules with a stored interface that are not
/// stale and do not depend, transitively, on a module the round compiles
/// (whose interface may still change). A stored interface is the one the
/// module's last compile published: it holds while the module's sources are
/// unchanged and no item it read changed, which is what not being stale
/// means.
pub fn stored_loadable(
    build_state: &BuildCommandState,
    round: &AHashSet<String>,
    support: &AHashSet<String>,
) -> AHashSet<String> {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return AHashSet::new();
    };
    let downstream = downstream_of(build_state, round);
    support
        .iter()
        .filter(|module_name| {
            let Some(module) = build_state.get_module(module_name) else {
                return false;
            };
            !module.is_mlmap()
                && !module.compile_dirty
                && !downstream.contains(*module_name)
                && !build_state.compiled_modules.contains(*module_name)
                && previous
                    .packages
                    .get(&module.package_name)
                    .is_some_and(|record| record.state.stored_interfaces.contains_key(*module_name))
        })
        .cloned()
        .collect()
}

/// Load the stored interfaces of `modules` into the registry. Returns the
/// modules loaded; any other must be compiled.
pub fn load_stored(build_state: &BuildCommandState, modules: &AHashSet<String>) -> AHashSet<String> {
    if modules.is_empty() {
        return AHashSet::new();
    }
    let mut by_package: AHashMap<&str, Vec<&str>> = AHashMap::new();
    for module_name in modules {
        if let Some(module) = build_state.get_module(module_name) {
            by_package
                .entry(module.package_name.as_str())
                .or_default()
                .push(module_name.as_str());
        }
    }
    let blobs: Vec<(String, Vec<u8>)> = by_package
        .into_iter()
        .collect::<Vec<_>>()
        .into_par_iter()
        .flat_map_iter(
            |(package_name, modules)| match build_state.get_package(package_name) {
                Some(package) => state_db::read_interfaces(package, &modules),
                None => Vec::new(),
            },
        )
        .collect();
    let decoded: Vec<(String, rescript_compiler::cmi::stored_module::StoredModule)> = blobs
        .into_par_iter()
        .filter_map(|(module_name, data)| {
            Some((module_name, rescript_compiler::cmi::stored_module::decode(&data)?))
        })
        .collect();
    let mut loaded = AHashSet::new();
    let mut alias_rewrites = build_state.module_alias_rewrites.lock().unwrap();
    let mut registry = build_state.module_registry.lock().unwrap();
    for (module_name, module) in decoded {
        if !module.alias_rewrites.is_empty() {
            alias_rewrites.insert(module_name.clone(), module.alias_rewrites.clone());
        }
        registry.register_stored_module(&module_name, module);
        loaded.insert(module_name);
    }
    log::debug!(
        "incremental build: loaded {} of {} stored interfaces",
        loaded.len(),
        modules.len()
    );
    loaded
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

/// Parse the modules a later round compiles that this build has not parsed.
/// Their saved parse warnings were already reported, so the parse only
/// records them.
pub fn parse_for_round(
    build_state: &mut BuildCommandState,
    modules: &AHashSet<String>,
) -> anyhow::Result<()> {
    let unparsed: Vec<String> = {
        let stored_asts = build_state.stored_asts.lock().unwrap();
        modules
            .iter()
            .filter(|module_name| !stored_asts.contains_key(&format!("{module_name}:impl")))
            .cloned()
            .collect()
    };
    if unparsed.is_empty() {
        return Ok(());
    }
    for module_name in &unparsed {
        if let Some(module) = build_state.build_state.modules.get_mut(module_name)
            && let SourceType::SourceFile(source_file) = &mut module.source_type
        {
            source_file.implementation.parse_dirty = true;
            if let Some(interface) = source_file.interface.as_mut() {
                interface.parse_dirty = true;
            }
        }
    }
    build_state.parse_warnings_replayed = true;
    let result = super::parse::generate_asts(build_state, || ());
    build_state.parse_warnings_replayed = false;
    result.map(drop)
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

/// Whether incremental planning applies: a fresh build with a record of the
/// previous one.
pub fn applies(build_state: &BuildCommandState) -> bool {
    build_state.previous_in_process.is_some()
        && build_state.dump.is_none()
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

    let cutoff = build_state.build_state.source_map_command != SourceMapCommand::Watch;
    let mut stale = AHashSet::new();
    if cutoff {
        // A module is stale when its own inputs changed, when a module it
        // references is new (a name may now resolve to it), or when a module
        // whose interface its compile read now has a different digest.
        // Dependents of a recompiled module are decided once its new digest
        // is known (see `next_round`).
        let digests = recorded_digests(build_state);
        let mut import_candidates: Vec<(String, Vec<(String, u64)>)> = Vec::new();
        for (module_name, own) in &times {
            let own_stale = !own.recorded
                || !matches!((own.newest_input, own.output), (Some(newest), Some(output)) if newest <= output);
            let row = recorded_row(build_state, module_name);
            let unknown_imports =
                row.is_none_or(|row| row.interface_digest.is_none() || row.imports.is_none());
            let references_new_module = build_state.get_module(module_name).is_some_and(|module| {
                module
                    .deps
                    .iter()
                    .any(|dep| times.get(dep).is_some_and(|times| !times.recorded))
            });
            let import_removed = row.and_then(|row| row.imports.as_ref()).is_some_and(|imports| {
                imports
                    .iter()
                    .any(|(import, _)| !build_state.modules.contains_key(import))
            });
            if own_stale || unknown_imports || references_new_module || import_removed {
                stale.insert(module_name.clone());
                continue;
            }
            let changed: Vec<(String, u64)> = row
                .and_then(|row| row.imports.as_ref())
                .into_iter()
                .flatten()
                .filter_map(|(import, digest)| {
                    let current = *digests.get(import)?;
                    (current != *digest).then(|| (import.clone(), current))
                })
                .collect();
            if !changed.is_empty() {
                import_candidates.push((module_name.clone(), changed));
            }
        }
        // An import's digest changed since the module was compiled (an
        // earlier build stopped before deciding about it): compare the items
        // it read with what the unit's record says now.
        if !import_candidates.is_empty() {
            let mut by_package: AHashMap<&str, Vec<&str>> = AHashMap::new();
            for (_, changed) in &import_candidates {
                for (unit, _) in changed {
                    if let Some(module) = build_state.get_module(unit) {
                        by_package
                            .entry(module.package_name.as_str())
                            .or_default()
                            .push(unit.as_str());
                    }
                }
            }
            let mut recorded_items: AHashMap<String, std::sync::Arc<ItemDigests>> = AHashMap::new();
            for (package_name, mut units) in by_package {
                units.sort();
                units.dedup();
                if let Some(package) = build_state.get_package(package_name) {
                    recorded_items.extend(
                        state_db::read_items(package, &units)
                            .into_iter()
                            .map(|(unit, items)| (unit, std::sync::Arc::new(items))),
                    );
                }
            }
            stale.extend(affected_by_changed_imports(
                build_state,
                std::mem::take(&mut import_candidates),
                &|unit| recorded_items.get(unit).cloned(),
            ));
        }
    } else {
        let mut memo = AHashMap::new();
        let mut visiting = AHashSet::new();
        let mut names: Vec<&String> = times.keys().collect();
        names.sort();
        for module_name in names {
            let own = &times[module_name];
            let newest = newest_closure(module_name, build_state, &times, &mut memo, &mut visiting);
            let up_to_date = own.recorded
                && matches!((newest, own.output), (Some(newest), Some(output)) if newest <= output);
            if !up_to_date {
                stale.insert(module_name.clone());
            }
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
        support_everything: !cutoff,
        cutoff,
    });
}

/// The recorded row of a module, from its package's database.
fn recorded_row<'a>(build_state: &'a BuildCommandState, module_name: &str) -> Option<&'a ModuleRow> {
    let module = build_state.get_module(module_name)?;
    build_state
        .previous_in_process
        .as_ref()?
        .packages
        .get(&module.package_name)?
        .state
        .modules
        .get(module_name)
}

/// Every module's recorded interface digest.
fn recorded_digests(build_state: &BuildCommandState) -> AHashMap<String, u64> {
    let Some(previous) = build_state.previous_in_process.as_ref() else {
        return AHashMap::new();
    };
    previous
        .packages
        .values()
        .flat_map(|record| record.state.modules.iter())
        .filter_map(|(module_name, row)| Some((module_name.clone(), row.interface_digest?)))
        .collect()
}

/// The modules to write in the next round of a cut-off build: those not yet
/// written whose recorded imports include a module that now has a different
/// interface digest. A module's current digest is the registry's when this
/// build registered it, the recorded one otherwise.
pub fn next_round(build_state: &BuildCommandState, written: &AHashSet<String>) -> AHashSet<String> {
    let digests = UnitDigests::new(build_state);
    let mut candidates = Vec::new();
    for (module_name, module) in build_state.modules.iter() {
        if written.contains(module_name) || module.is_mlmap() {
            continue;
        }
        let Some(imports) = recorded_row(build_state, module_name).and_then(|row| row.imports.as_ref())
        else {
            continue;
        };
        let verified = build_state.verified_imports.lock().unwrap();
        let checked = verified.get(module_name);
        // Units this build did not compile are as recorded.
        let changed: Vec<(String, u64)> = imports
            .iter()
            .filter_map(|(import, digest)| {
                let now = digests.get(import)?.0;
                let seen = checked.and_then(|units| units.get(import)).unwrap_or(digest);
                (now != *seen).then(|| (import.clone(), now))
            })
            .collect();
        drop(verified);
        if !changed.is_empty() {
            candidates.push((module_name.clone(), changed));
        }
    }
    affected_by_changed_imports(build_state, candidates, &|unit| {
        digests
            .get(unit)
            .map(|digests| std::sync::Arc::new(digests.1.clone()))
    })
}

/// The modules that depend, transitively, on one of `modules`.
pub fn downstream_of(build_state: &BuildCommandState, modules: &AHashSet<String>) -> AHashSet<String> {
    let mut downstream: AHashSet<String> = AHashSet::new();
    let mut frontier: Vec<&String> = modules.iter().collect();
    while let Some(module_name) = frontier.pop() {
        if let Some(module) = build_state.get_module(module_name) {
            for dependent in &module.dependents {
                if downstream.insert(dependent.clone()) {
                    frontier.push(dependent);
                }
            }
        }
    }
    downstream
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

/// The support modules of a later round: the dependencies of `universe`
/// that this build has not compiled yet.
pub fn round_support(
    build_state: &BuildCommandState,
    universe: &AHashSet<String>,
    compiled: &AHashSet<String>,
) -> AHashSet<String> {
    let mut support = AHashSet::new();
    let mut frontier: Vec<&String> = universe.iter().collect();
    while let Some(module_name) = frontier.pop() {
        let Some(module) = build_state.get_module(module_name) else {
            continue;
        };
        for dep in &module.deps {
            // A namespace map is a no-op in the scheduler, but its members
            // are what a reference through the namespace needs.
            if build_state.get_module(dep).is_some()
                && !universe.contains(dep)
                && !compiled.contains(dep)
                && support.insert(dep.clone())
            {
                frontier.push(dep);
            }
        }
    }
    support
}

/// What a module written by this build read and published, for its record.
struct WrittenRecord {
    digest: u64,
    imports: Vec<(String, u64)>,
    reads: UnitReads,
    items: ItemDigests,
}

fn written_interface(
    build_state: &BuildCommandState,
    module_name: &str,
    digests: &UnitDigests,
) -> Option<WrittenRecord> {
    if !build_state.written_modules.contains(module_name) {
        return None;
    }
    let own = digests.get(module_name)?;
    // What inlinable bodies refer to is added now, with dependencies' JS
    // metadata final (they may publish it after this module compiled).
    let mut read_keys: BTreeMap<String, std::collections::BTreeSet<String>> = {
        let pending = build_state.unit_reads.lock().unwrap();
        match pending.get(module_name) {
            Some(pending) => {
                let mut keys = pending.resolved.clone();
                for (unit, unit_keys) in digests.lambda_reads(&pending.resolved) {
                    keys.entry(unit).or_default().extend(unit_keys);
                }
                for unit in &pending.module_level {
                    keys.entry(unit.clone())
                        .or_default()
                        .insert(item_deps::MODULE_LEVEL.to_string());
                }
                keys
            }
            None => BTreeMap::new(),
        }
    };
    // A unit the compile loaded without a recorded read is read whole.
    for unit in build_state.loaded_units.lock().unwrap().get(module_name)? {
        read_keys.entry(unit.clone()).or_insert_with(|| {
            [item_deps::WHOLE.to_string(), item_deps::MODULE_LEVEL.to_string()]
                .into_iter()
                .collect()
        });
    }
    let mut imports = Vec::new();
    let mut reads = UnitReads::new();
    for (unit, mut keys) in read_keys {
        if unit == module_name || !build_state.modules.contains_key(&unit) {
            continue;
        }
        // The digest of every item covers the others.
        if keys.contains(item_deps::WHOLE) {
            keys = [item_deps::WHOLE.to_string()].into_iter().collect();
        }
        let unit_digests = digests.get(&unit)?;
        let read_digest = item_deps::read_digest(&unit_digests.1, keys.iter());
        imports.push((unit.clone(), unit_digests.0));
        reads.insert(unit, (read_digest, keys.into_iter().collect()));
    }
    Some(WrittenRecord {
        digest: own.0,
        imports,
        reads,
        items: own.1.clone(),
    })
}

/// Of `candidates` (modules with recorded imports whose unit's interface
/// digest is now different), the ones that read an item of those units that
/// changed. For the others, the imports are recorded as verified. `items`
/// gives a unit's current item digests.
fn affected_by_changed_imports(
    build_state: &BuildCommandState,
    candidates: Vec<(String, Vec<(String, u64)>)>,
    items: &dyn Fn(&str) -> Option<std::sync::Arc<ItemDigests>>,
) -> AHashSet<String> {
    let mut by_package: AHashMap<&str, Vec<&str>> = AHashMap::new();
    for (module_name, _) in &candidates {
        if let Some(module) = build_state.get_module(module_name) {
            by_package
                .entry(module.package_name.as_str())
                .or_default()
                .push(module_name.as_str());
        }
    }
    let mut recorded_reads: AHashMap<String, UnitReads> = AHashMap::new();
    for (package_name, modules) in by_package {
        if let Some(package) = build_state.get_package(package_name) {
            recorded_reads.extend(state_db::read_reads(package, &modules));
        }
    }
    let mut affected = AHashSet::new();
    let mut verified = build_state.verified_imports.lock().unwrap();
    for (module_name, changed) in candidates {
        let reads = recorded_reads.get(&module_name);
        let unaffected = changed.iter().all(|(unit, _)| {
            let Some((digest, keys)) = reads.and_then(|reads| reads.get(unit)) else {
                return false;
            };
            let same =
                items(unit).is_some_and(|items| item_deps::read_digest(&items, keys.iter()) == *digest);
            if !same {
                log::debug!("{module_name} recompiles: an item it reads of {unit} changed");
            }
            same
        });
        if unaffected {
            let entry = verified.entry(module_name).or_default();
            for (unit, now) in changed {
                entry.insert(unit, now);
            }
        } else {
            affected.insert(module_name);
        }
    }
    affected
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
