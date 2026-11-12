//! Fresh-build persistence rows, produced while compilation is still running.
//! A signature-ready event is not enough: read digests also depend on final JS
//! metadata. Wait for completion of direct reads, expand inline-body reads,
//! then wait for any additional units before encoding the rows.

use super::build_types::{BuildCommandState, PendingReads, SourceType};
use super::incremental::{self, UnitDigests};
use super::state_db::{self, ModuleRow, PackageState, SourceDeps, StoredInterface};
use ahash::{AHashMap, AHashSet};
use rescript_compiler::binary_ast::Dependencies;
use rescript_compiler::cmi::item_deps::ResolvedReads;
use rescript_compiler::name::Name;
use rescript_compiler::timing::{self, Phase};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::SystemTime;

pub(super) enum PrepEvent {
    Module(ReadInput),
    Outputs { name: String, success: bool },
}

pub(super) struct ReadInput {
    pub success: bool,
    pub name: String,
    pub loaded: Option<AHashSet<Name>>,
    pub pending: Option<PendingReads>,
    pub implementation_warnings: Option<String>,
    pub interface_warnings: Option<String>,
}

struct Source {
    package: String,
    paths: Vec<(String, PathBuf)>,
    gentype_annotations: [bool; 2],
    gentype_declarations_needed: bool,
}

enum ReadStage {
    Direct,
    Expanded(ResolvedReads),
}

struct Waiting {
    input: ReadInput,
    stage: ReadStage,
    remaining: usize,
}

struct PackageWriter {
    package: super::packages::Package,
    seed: Option<(PackageState, Vec<(String, Vec<u8>)>)>,
    record: Option<state_db::TemporaryRecord>,
    remaining: usize,
    outputs_remaining: usize,
    valid: bool,
    previous_outputs: Option<AHashSet<String>>,
    outputs: String,
    publication: Option<std::thread::JoinHandle<bool>>,
}

pub(super) struct FreshRows {
    writers: AHashMap<String, PackageWriter>,
    digests: UnitDigests,
    sources: AHashMap<String, Source>,
    module_packages: AHashMap<String, String>,
    deps: AHashMap<String, Dependencies>,
    mtimes: AHashMap<String, i64>,
    started: Option<SystemTime>,
    packages: AHashMap<String, PackageState>,
    completed: AHashSet<Name>,
    waiting: AHashMap<String, Waiting>,
    waiters: AHashMap<Name, Vec<String>>,
    inputs: Vec<ReadInput>,
}

pub(super) struct FinishedRows {
    pub packages: AHashSet<String>,
    pub deps: AHashMap<String, Dependencies>,
    pub inputs: Vec<ReadInput>,
}

impl FreshRows {
    pub(super) fn new(state: &BuildCommandState) -> Option<Self> {
        // Incremental rounds may replace a dependency's metadata after a
        // dependent completed. Stream only when every source will compile in
        // this pass (including forced full builds with an existing record).
        #[cfg(debug_assertions)]
        if std::env::var_os("RESCRIPT_TEST_FINAL_RECORD").is_some() { return None; }
        if state.check_only
            || state.in_memory_only
            || state
                .previous_in_process
                .as_ref()
                .is_some_and(|p| !p.packages.is_empty())
                && state.modules.values().any(|module|
                    matches!(module.source_type, SourceType::SourceFile(_)) && !module.compile_dirty)
            || !state.module_registry.lock().unwrap().is_empty() && !state.written_modules.is_empty()
        {
            return None;
        }
        let names = state.modules.keys().cloned().collect();
        let digests = UnitDigests::for_preparation(state.snapshot_module_registry(), &names);
        let sources: AHashMap<String, Source> = state
            .modules
            .iter()
            .filter_map(|(name, module)| {
                let SourceType::SourceFile(source) = &module.source_type else {
                    return None;
                };
                let mut paths = vec![(format!("{name}:impl"), source.implementation.path.clone())];
                if let Some(intf) = &source.interface {
                    paths.push((format!("{name}:intf"), intf.path.clone()));
                }
                Some((
                    name.clone(),
                    Source {
                        package: module.package_name.clone(),
                        paths,
                        gentype_annotations: source.gentype_annotations.map(|flag| flag.unwrap_or(true)),
                        gentype_declarations_needed: state.packages[&module.package_name]
                            .config
                            .gentype_config
                            .is_some()
                            && state
                                .gentype_needed
                                .as_ref()
                                .is_none_or(|needed| needed.contains(name)),
                    },
                ))
            })
            .collect();
        let mut packages: AHashMap<String, PackageState> = state
            .packages
            .keys()
            .map(|name| (name.clone(), PackageState::default()))
            .collect();
        for (key, (package, warning)) in state.parse_warnings.lock().unwrap().iter() {
            packages
                .get_mut(package)?
                .parse_warnings
                .insert(key.clone(), warning.clone());
        }
        let source_map_args = super::compiler_info::source_map_args(state);
        let writers = packages.iter_mut().map(|(name, record)| {
            // Snapshot only the metadata/runtime that whole-record replacement
            // must preserve. This runs before compilation; the worker creates
            // and progressively commits only its private file during compilation.
            let package = &state.packages[name];
            record.meta = state_db::read_meta(package).unwrap_or_default();
            let runtime = record.meta.get(state_db::META_RUNTIME_KEY)
                .and_then(|key| state_db::read_runtime_interfaces(&state_db::path(package), key))
                .unwrap_or_default();
            incremental::fill_record_metadata(state, name, record);
            record.meta.insert(state_db::META_BUILD_OK.to_string(), "1".to_string());
            if let Some(entries) = super::compiler_info::recorded_entries(state, package, &source_map_args) {
                record.meta.extend(entries.into_iter().map(|(key, value)| (key.to_string(), value)));
            }
            let outputs = record.meta.get(state_db::META_OUTPUTS).cloned().unwrap_or_default();
            let count = sources.values().filter(|source: &&Source| source.package == *name).count();
            let seed = std::mem::take(record);
            record.partial = true;
            (name.clone(), PackageWriter {
                package: package.clone(), seed: Some((seed, runtime)), record: None,
                remaining: count, outputs_remaining: count, valid: true,
                previous_outputs: state.recorded_outputs.get(name).cloned(), outputs,
                publication: None,
            })
        }).collect();
        Some(Self {
            writers,
            digests,
            sources,
            packages,
            module_packages: state
                .modules
                .iter()
                .map(|(name, m)| (name.clone(), m.package_name.clone()))
                .collect(),
            deps: std::mem::take(&mut *state.in_memory_deps.lock().unwrap()),
            mtimes: state.source_mtimes.clone(),
            started: state.build_run.started_at(),
            completed: AHashSet::new(),
            waiting: AHashMap::new(),
            waiters: AHashMap::new(),
            inputs: Vec::new(),
        })
    }

    /// Create schemas and start transactions on the preparation thread.
    pub(super) fn start(&mut self) {
        for writer in self.writers.values_mut() {
            let (seed, runtime) = writer.seed.take().expect("unstarted writer");
            match state_db::TemporaryRecord::new(&writer.package, &seed, &runtime) {
                Ok(record) => writer.record = Some(record),
                Err(err) => {
                    log::warn!("Could not prepare {}: {err}; falling back to final-state recording", writer.package.name);
                    // Keep processing module events/digests, but exclude this
                    // package from FinishedRows::packages so the final-state
                    // path reconstructs its complete record exactly once.
                    writer.valid = false;
                }
            }
        }
        let empty: Vec<_> = self.writers.iter().filter(|(_, writer)| writer.remaining == 0)
            .map(|(name, _)| name.clone()).collect();
        for name in empty { self.publish_if_ready(&name); }
    }

    fn flush(&mut self, package: &str) {
        let rows = self.packages.get_mut(package).expect("known package");
        let writer = self.writers.get_mut(package).expect("known writer");
        if let Some(record) = &mut writer.record {
            if let Err(err) = record.insert(rows) {
                log::warn!("Could not prepare {package}: {err}; falling back to final-state recording");
                writer.valid = false;
                writer.record = None;
            }
        }
        *rows = PackageState { partial: true, ..PackageState::default() };
    }

    pub(super) fn outputs_complete(&mut self, name: &str, success: bool) {
        let Some(source) = self.sources.get(name) else { return };
        let package = source.package.clone();
        let writer = self.writers.get_mut(&package).expect("known writer");
        writer.outputs_remaining -= 1;
        writer.valid &= success;
        self.publish_if_ready(&package);
    }

    fn publish_if_ready(&mut self, name: &str) {
        let writer = self.writers.get_mut(name).expect("known writer");
        if !writer.valid || writer.remaining != 0 || writer.outputs_remaining != 0 {
            return;
        }
        let Some(record) = writer.record.take() else { return };
        let package = writer.package.clone();
        let previous = writer.previous_outputs.take();
        let outputs = std::mem::take(&mut writer.outputs);
        writer.publication = Some(std::thread::spawn(move || {
            super::clean::remove_obsolete_outputs(&package, previous.as_ref(), &outputs.lines().collect());
            match record.publish(&package) {
                Ok(()) => true,
                Err(err) => {
                    log::warn!("Could not publish {}: {err}", package.name);
                    false
                }
            }
        }));
    }

    pub(super) fn items(&self, name: &str) -> Option<Arc<state_db::ItemDigests>> {
        self.digests.get(name).map(|(_, items)| items)
    }

    pub(super) fn complete(&mut self, input: ReadInput, interface: Option<StoredInterface>) {
        let name = Name::new(&input.name);
        let package = self.module_packages[&input.name].clone();
        self.writers.get_mut(&package).expect("known writer").valid &= input.success;
        self.completed.insert(name);
        if let Some(interface) = interface {
            let package = &self.module_packages[&input.name];
            self.packages
                .get_mut(package)
                .expect("known package")
                .interface_updates
                .insert(input.name.clone(), interface);
        }
        if let Some(source) = self.sources.get(&input.name) {
            let record = self.packages.get_mut(&source.package).expect("known package");
            timing::measure(Phase::RecordSourceRows, || {
                for (_, path) in &source.paths {
                    record.sources.insert(path.clone(), input.name.clone());
                }
            });
            timing::measure(Phase::RecordDependencyRows, || {
                let gentype_declarations = source.gentype_declarations_needed
                    && rescript_compiler::gentype::main::has_type_declarations_for_module(&input.name);
                for (kind, (key, _)) in source.paths.iter().enumerate() {
                    if let (Some(deps), Some(mtime)) = (self.deps.get(key), self.mtimes.get(key)) {
                        let row = SourceDeps {
                            mtime: *mtime,
                            deps: deps.iter().cloned().collect(),
                            gentype_annotations: source.gentype_annotations[kind],
                            gentype_declarations,
                        };
                        let text = timing::measure(Phase::RecordDepsEncode, || row.deps.join("\n"));
                        record.encoded_deps.insert(key.clone(), text);
                        record.deps.insert(key.clone(), row);
                    }
                }
            });
            self.flush(&package);
            self.advance(Waiting {
                input,
                stage: ReadStage::Direct,
                remaining: 0,
            });
        } else {
            self.flush(&package);
            self.inputs.push(input);
        }
        for dependent in self.waiters.remove(&name).unwrap_or_default() {
            let ready = if let Some(job) = self.waiting.get_mut(&dependent) {
                job.remaining -= 1;
                job.remaining == 0
            } else {
                false
            };
            if ready {
                let job = self.waiting.remove(&dependent).expect("ready job");
                self.advance(job);
            }
        }
    }

    fn advance(&mut self, mut job: Waiting) {
        loop {
            // Most imports are already complete. Filter them before building
            // a collection, so a ready module needs neither an allocation nor a
            // duplicate collection of all its read units. Non-project units cannot
            // block this build; memoize that fact as well.
            let mut needs_completion = |name: &Name| {
                if self.completed.contains(name) {
                    false
                } else if self.sources.contains_key(name.as_str()) {
                    true
                } else {
                    self.completed.insert(*name);
                    false
                }
            };
            let mut missing: Vec<Name> =
                match &job.stage {
                    ReadStage::Direct => {
                        job.input
                            .loaded
                            .iter()
                            .flatten()
                            .copied()
                            .chain(job.input.pending.iter().flat_map(|p| {
                                p.resolved.keys().copied().chain(p.module_level.iter().copied())
                            }))
                            .filter(&mut needs_completion)
                            .collect()
                    }
                    ReadStage::Expanded(keys) => keys.keys().copied().filter(&mut needs_completion).collect(),
                };
            // A ready job allocates nothing, including no hash-set seed.
            // The few outstanding units may occur in both loaded and resolved
            // reads; deduplicate before registering one wake-up per unit.
            missing.sort_unstable();
            missing.dedup();
            if !missing.is_empty() {
                job.remaining = missing.len();
                for unit in missing {
                    self.waiters.entry(unit).or_default().push(job.input.name.clone());
                }
                self.waiting.insert(job.input.name.clone(), job);
                return;
            }
            match job.stage {
                ReadStage::Direct => {
                    let Some(loaded) = &job.input.loaded else {
                        self.inputs.push(job.input);
                        return;
                    };
                    job.stage = ReadStage::Expanded(incremental::read_keys(
                        job.input.pending.as_ref(),
                        loaded,
                        &self.digests,
                    ));
                }
                ReadStage::Expanded(keys) => {
                    if let Some(written) =
                        incremental::written_from_keys(&job.input.name, keys, &self.digests)
                    {
                        let source = &self.sources[&job.input.name];
                        let record = self.packages.get_mut(&source.package).expect("known package");
                        let reads = timing::measure(Phase::RecordReadsEncode, || {
                            state_db::encode_reads(&written.reads)
                        });
                        let items = timing::measure(Phase::RecordItemsEncode, || {
                            state_db::encode_items(&written.items)
                        });
                        let imports = timing::measure(Phase::RecordImportsEncode, || {
                            state_db::Imports::new(written.imports).encode().into_owned()
                        });
                        record.encoded_reads.insert(job.input.name.clone(), reads);
                        record.encoded_items.insert(job.input.name.clone(), items);
                        record.modules.insert(
                            job.input.name.clone(),
                            ModuleRow {
                                js_confirmed_at: self.started,
                                implementation_warnings: job.input.implementation_warnings.take(),
                                interface_warnings: job.input.interface_warnings.take(),
                                interface_digest: Some(written.digest),
                                imports: Some(state_db::Imports::from_text(imports)),
                            },
                        );
                    } else {
                        let package = &self.sources[&job.input.name].package;
                        self.writers.get_mut(package).expect("known writer").valid = false;
                    }
                    let package = self.sources[&job.input.name].package.clone();
                    self.flush(&package);
                    self.writers.get_mut(&package).expect("known writer").remaining -= 1;
                    self.publish_if_ready(&package);
                    self.inputs.push(job.input);
                    return;
                }
            }
        }
    }

    pub(super) fn finish(mut self) -> FinishedRows {
        let packages = self.writers.into_iter().filter_map(|(name, writer)| {
            writer.publication.and_then(|handle| handle.join().ok())
                .filter(|success| *success).map(|_| name)
        }).collect();
        self.inputs
            .extend(self.waiting.into_values().map(|job| job.input));
        FinishedRows {
            packages,
            deps: self.deps,
            inputs: self.inputs,
        }
    }
}
