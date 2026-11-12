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

pub(super) struct ReadInput {
    pub name: String,
    pub loaded: Option<AHashSet<Name>>,
    pub pending: Option<PendingReads>,
    pub implementation_warnings: Option<String>,
    pub interface_warnings: Option<String>,
}

struct Source {
    package: String,
    paths: Vec<(String, PathBuf)>,
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

pub(super) struct FreshRows {
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
    pub packages: AHashMap<String, PackageState>,
    pub deps: AHashMap<String, Dependencies>,
    pub inputs: Vec<ReadInput>,
}

impl FreshRows {
    pub(super) fn new(state: &BuildCommandState) -> Option<Self> {
        // Incremental rounds and watch edits may replace a dependency's metadata
        // after a dependent completed. Keep their existing final-state path.
        if state.check_only
            || state.in_memory_only
            || state
                .previous_in_process
                .as_ref()
                .is_some_and(|p| !p.packages.is_empty())
            || !state.module_registry.lock().unwrap().is_empty() && !state.written_modules.is_empty()
        {
            return None;
        }
        let names = state.modules.keys().cloned().collect();
        let digests = UnitDigests::for_preparation(state.snapshot_module_registry(), &names);
        let sources = state
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
        Some(Self {
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

    pub(super) fn items(&self, name: &str) -> Option<Arc<state_db::ItemDigests>> {
        self.digests.get(name).map(|(_, items)| items)
    }

    pub(super) fn complete(&mut self, input: ReadInput, interface: Option<StoredInterface>) {
        let name = Name::new(&input.name);
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
                for (key, _) in &source.paths {
                    if let (Some(deps), Some(mtime)) = (self.deps.get(key), self.mtimes.get(key)) {
                        let row = SourceDeps {
                            mtime: *mtime,
                            deps: deps.iter().cloned().collect(),
                        };
                        let text = timing::measure(Phase::RecordDepsEncode, || row.deps.join("\n"));
                        record.encoded_deps.insert(key.clone(), text);
                        record.deps.insert(key.clone(), row);
                    }
                }
            });
            self.advance(Waiting {
                input,
                stage: ReadStage::Direct,
                remaining: 0,
            });
        } else {
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
            // a set, so a ready module needs neither an allocation nor a full
            // duplicate set of all its read units. Non-project units cannot
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
            let missing: AHashSet<Name> =
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
                    }
                    self.inputs.push(job.input);
                    return;
                }
            }
        }
    }

    pub(super) fn finish(mut self) -> FinishedRows {
        // Errors or unpublished inputs can leave waiting rows. Their raw reads
        // are returned for the conservative final-state path; never publish an
        // incomplete set of precomputed rows as a successful package record.
        let count: usize = self.packages.values().map(|p| p.modules.len()).sum();
        if !self.waiting.is_empty() || count != self.sources.len() {
            self.packages.clear();
        }
        self.inputs
            .extend(self.waiting.into_values().map(|job| job.input));
        FinishedRows {
            packages: self.packages,
            deps: self.deps,
            inputs: self.inputs,
        }
    }
}
