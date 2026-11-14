#![allow(clippy::too_many_arguments)]

mod dependency_cycle;

use super::build_types::*;
use super::incremental::IncrementalPlan;
use super::logs;
use super::packages;
use super::qos;
use crate::config;
use crate::config::Config;
use crate::helpers;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::{Context, Result, anyhow};
use console::style;
use log::{debug, info, trace, warn};
use rayon::prelude::*;
use rescript_compiler::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, InMemoryModuleInfo, ModuleRegistry,
};
use rescript_compiler::cmi::portable_types::{PortablePersStruct, SignaturePublicationMode};
use rescript_compiler::parse_arena::ParseArena;
use rescript_compiler::parser::ast::{Signature, Structure};
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::mpsc;
use std::time::Duration;
use std::time::Instant;
use tracing::{Span, info_span, instrument};

/// Execute js-post-build command for a compiled JavaScript file.
/// The command runs in the directory containing the rescript.json that defines it.
/// The absolute path to the JS file is passed as an argument.
fn execute_post_build_command(cmd: &str, js_file_path: &Path, working_dir: &Path) -> Result<()> {
    let full_command = format!("{} {}", cmd, js_file_path.display());

    let _span = info_span!(
        "build.js_post_build",
        command = %cmd,
        js_file = %js_file_path.display(),
    )
    .entered();

    debug!(
        "Executing js-post-build: {} (in {})",
        full_command,
        working_dir.display()
    );

    let output = if cfg!(target_os = "windows") {
        Command::new("cmd")
            .args(["/C", &full_command])
            .current_dir(working_dir)
            .output()
    } else {
        Command::new("sh")
            .args(["-c", &full_command])
            .current_dir(working_dir)
            .output()
    };

    match output {
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);

            // Always log stdout/stderr - the user explicitly configured this command
            // and likely cares about its output
            if !stdout.is_empty() {
                info!("{}", stdout.trim());
            }
            if !stderr.is_empty() {
                warn!("{}", stderr.trim());
            }

            if !output.status.success() {
                Err(anyhow!(
                    "js-post-build command failed for {}",
                    js_file_path.display()
                ))
            } else {
                Ok(())
            }
        }
        Err(e) => Err(anyhow!("Failed to execute js-post-build command: {}", e)),
    }
}

/// A unit of work in the ready queue. Ordered by `priority` so that the
/// `BinaryHeap` pops the module with the longest remaining critical path first.
#[derive(Debug)]
struct WorkUnit {
    priority: i64,
    module_name: String,
}

impl PartialEq for WorkUnit {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}
impl Eq for WorkUnit {}
impl PartialOrd for WorkUnit {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for WorkUnit {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority)
    }
}

/// Result of a single module compilation, sent from a worker back to the
/// dispatcher on the main thread. Mirrors the tuple shape the wave-based
/// scheduler used to return.
struct CompletionMsg {
    module_name: String,
    result: Result<Option<String>>,
    interface_result: Option<Result<Option<String>>>,
    is_clean: bool,
    is_compiled: bool,
    registry_updates: Vec<PendingRegistryUpdate>,
}

struct PreJsMsg {
    module_name: String,
    pre_js: rescript_compiler::driver::InProcessPreJsCompileResult,
    needed_modules: Vec<String>,
    interface_registry_update: Option<PendingRegistryUpdate>,
    source_abs: PathBuf,
    implementation_path: PathBuf,
    has_interface: bool,
    is_runtime: bool,
    is_clean: bool,
    registry_only: bool,
}

struct SignatureReadyMsg {
    module_name: String,
    fingerprint: u64,
    is_pure: bool,
    registry_updates: Vec<PendingRegistryUpdate>,
}

struct JsMetadataReadyMsg {
    module_name: String,
    registry_updates: Vec<PendingRegistryUpdate>,
}

enum WorkerMsg {
    SignatureReady(SignatureReadyMsg),
    PreJsReady(Box<PreJsMsg>),
    JsMetadataReady(JsMetadataReadyMsg),
    Completed(CompletionMsg),
}

fn pop_ready_js(
    ready_js: &mut Vec<PreJsMsg>,
    waiting_js_by_dep: &AHashMap<String, Vec<String>>,
) -> Option<PreJsMsg> {
    match ready_js.len() {
        0 => None,
        1 => ready_js.pop(),
        len => {
            let mut best_idx = len - 1;
            let mut best_waiters = waiting_js_by_dep
                .get(&ready_js[best_idx].module_name)
                .map_or(0, Vec::len);
            for idx in (0..len - 1).rev() {
                let waiters = waiting_js_by_dep
                    .get(&ready_js[idx].module_name)
                    .map_or(0, Vec::len);
                if waiters > best_waiters {
                    best_idx = idx;
                    best_waiters = waiters;
                }
            }
            Some(ready_js.remove(best_idx))
        }
    }
}

#[derive(Clone)]
struct InProcessSchedulerHooks {
    tx: mpsc::Sender<WorkerMsg>,
    compile_universe: Arc<AHashSet<String>>,
    /// Support modules of an incremental build: compiled for the registry,
    /// without rendering or writing JavaScript (see `incremental`).
    registry_only: Arc<AHashSet<String>>,
}

#[derive(Default)]
struct InProcessSchedulerCounters {
    scheduled_typecheck: usize,
    critical_scheduled: usize,
    scheduled_js: usize,
    signature_ready: usize,
    pre_js_ready: usize,
    completed: usize,
    max_ready_typecheck: usize,
    max_ready_js: usize,
    max_pending_js: usize,
    max_in_flight: usize,
    js_scheduled_while_typecheck_ready: usize,
    blocked_events_with_idle_slots: usize,
    max_idle_slots: usize,
    dispatcher_wait: Duration,
    idle_slot_wait_nanos: u128,
    pending_js_dep_counts: AHashMap<String, usize>,
}

impl InProcessSchedulerCounters {
    fn observe_queues(
        &mut self,
        ready_typecheck: usize,
        ready_js: usize,
        pending_js: usize,
        in_flight: usize,
    ) {
        self.max_ready_typecheck = self.max_ready_typecheck.max(ready_typecheck);
        self.max_ready_js = self.max_ready_js.max(ready_js);
        self.max_pending_js = self.max_pending_js.max(pending_js);
        self.max_in_flight = self.max_in_flight.max(in_flight);
    }

    fn observe_wait(&mut self, wait: Duration, idle_slots: usize) {
        self.dispatcher_wait = self.dispatcher_wait.saturating_add(wait);
        if idle_slots > 0 {
            self.blocked_events_with_idle_slots += 1;
            self.max_idle_slots = self.max_idle_slots.max(idle_slots);
            self.idle_slot_wait_nanos = self
                .idle_slot_wait_nanos
                .saturating_add(wait.as_nanos().saturating_mul(idle_slots as u128));
        }
    }

    fn observe_pending_js_deps<'a>(&mut self, deps: impl IntoIterator<Item = &'a String>) {
        for dep in deps {
            *self.pending_js_dep_counts.entry(dep.clone()).or_default() += 1;
        }
    }

    fn print_report(&self, capacity: usize) {
        eprintln!(
            "[scheduler-counter] capacity={} critical_slots={} scheduled_typecheck={} critical_scheduled={} scheduled_js={} signature_ready={} pre_js_ready={} completed={} js_scheduled_while_typecheck_ready={} max_ready_typecheck={} max_ready_js={} max_pending_js={} max_in_flight={} blocked_events_with_idle_slots={} max_idle_slots={} dispatcher_wait_ms={:.3} idle_slot_wait_ms={:.3}",
            capacity,
            qos::critical_slots(),
            self.scheduled_typecheck,
            self.critical_scheduled,
            self.scheduled_js,
            self.signature_ready,
            self.pre_js_ready,
            self.completed,
            self.js_scheduled_while_typecheck_ready,
            self.max_ready_typecheck,
            self.max_ready_js,
            self.max_pending_js,
            self.max_in_flight,
            self.blocked_events_with_idle_slots,
            self.max_idle_slots,
            duration_ms(self.dispatcher_wait),
            self.idle_slot_wait_nanos as f64 / 1_000_000.0,
        );
        let mut pending_deps = self
            .pending_js_dep_counts
            .iter()
            .collect::<Vec<(&String, &usize)>>();
        pending_deps.sort_by(|(left_name, left_count), (right_name, right_count)| {
            right_count
                .cmp(left_count)
                .then_with(|| left_name.cmp(right_name))
        });
        for (dep, count) in pending_deps.into_iter().take(20) {
            eprintln!("[scheduler-counter] pending_js_dep dep={} count={}", dep, count);
        }
    }
}

#[derive(Clone)]
struct PendingRegistryUpdate {
    module_name: String,
    pers_struct: Option<Arc<PortablePersStruct>>,
    module_info: InMemoryModuleInfo,
}

struct InProcessModuleResult {
    warning: Option<String>,
    registry_updates: Vec<PendingRegistryUpdate>,
}

fn duration_ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn duration_delta(after: Duration, before: Duration) -> Duration {
    after.saturating_sub(before)
}

fn apply_pending_registry_updates(
    build_command_state: &BuildCommandState,
    updates: Vec<PendingRegistryUpdate>,
) {
    if updates.is_empty() {
        return;
    }

    {
        let mut item_digests = build_command_state.published_item_digests.lock().unwrap();
        let mut interfaces = build_command_state.prepared_interfaces.lock().unwrap();
        for update in &updates {
            item_digests.remove(&update.module_name);
            interfaces.remove(&update.module_name);
        }
    }
    let mut registry = build_command_state.module_registry.lock().unwrap();
    for update in updates {
        if let Some(pers_struct) = update.pers_struct {
            registry.register_module_arc(&update.module_name, pers_struct, update.module_info);
        } else {
            registry.insert_module_info(update.module_name, update.module_info);
        }
    }
}

fn apply_signature_ready(build_command_state: &BuildCommandState, msg: SignatureReadyMsg) -> bool {
    apply_pending_registry_updates(build_command_state, msg.registry_updates);
    let generation_before = build_command_state.get_interface_generation(&msg.module_name);
    let generation_after =
        build_command_state.register_in_memory_interface(msg.module_name, msg.fingerprint, msg.is_pure);
    // A first registration in this process is a changed interface:
    // in-process builds keep no `.cmi` to compare against.
    generation_before == Some(generation_after)
}

fn unblock_dependents(
    build_state: &BuildState,
    compile_universe: &AHashSet<String>,
    priorities: &AHashMap<String, i64>,
    pending_deps: &mut AHashMap<String, usize>,
    dirty_set: &mut AHashSet<String>,
    signature_ready: &mut AHashSet<String>,
    ready_heap: &mut BinaryHeap<WorkUnit>,
    module_name: &str,
    is_clean: bool,
) {
    if !signature_ready.insert(module_name.to_string()) {
        return;
    }

    let Some(module) = build_state.get_module(module_name) else {
        return;
    };
    for dep in &module.dependents {
        if !compile_universe.contains(dep) {
            continue;
        }
        if !is_clean {
            dirty_set.insert(dep.clone());
        }
        let count = pending_deps.get_mut(dep).unwrap();
        *count -= 1;
        if *count == 0 && !signature_ready.contains(dep) {
            ready_heap.push(WorkUnit {
                priority: priorities[dep],
                module_name: dep.clone(),
            });
        }
    }
}

/// Estimate module cost from parse-phase source buffers that are already held
/// in memory for `--in-process`. This keeps the scheduler from doing extra
/// filesystem reads while still prioritizing large ready modules over tiny
/// leaf work.
fn compute_module_costs(
    universe: &AHashSet<String>,
    stored_asts: &AHashMap<String, StoredAst>,
) -> AHashMap<String, i64> {
    let mut costs = AHashMap::with_capacity(universe.len());
    for name in universe {
        let impl_key = format!("{name}:impl");
        let intf_key = format!("{name}:intf");
        let mut source_len = 0usize;
        for key in [&impl_key, &intf_key] {
            if let Some(stored) = stored_asts.get(key) {
                source_len = source_len.saturating_add(stored.source_len());
            }
        }
        costs.insert(name.clone(), source_len.max(1) as i64);
    }
    costs
}

struct CompileWarning {
    module_name: String,
    package_name: String,
    warning: String,
}

/// Compute the weighted critical-path priority of every module in the universe:
/// `priority(m) = cost(m) + max(priority(d) for d in in-universe dependents of m)`.
/// Runs a reverse-topological sweep from leaves to roots. Modules stuck in a
/// cycle get priority 0, and the actual cycle is diagnosed later by
/// `dependency_cycle::find` when the dispatcher detects a stall.
fn compute_critical_path_priorities(
    universe: &AHashSet<String>,
    build_state: &BuildState,
    costs: &AHashMap<String, i64>,
) -> AHashMap<String, i64> {
    let mut priorities: AHashMap<String, i64> = AHashMap::with_capacity(universe.len());
    let mut remaining_dependents: AHashMap<String, usize> = AHashMap::with_capacity(universe.len());
    let mut queue: Vec<String> = Vec::new();

    for name in universe {
        let module = build_state.get_module(name).unwrap();
        let count = module.dependents.iter().filter(|d| universe.contains(*d)).count();
        remaining_dependents.insert(name.clone(), count);
        if count == 0 {
            queue.push(name.clone());
        }
    }

    while let Some(name) = queue.pop() {
        let module = build_state.get_module(&name).unwrap();
        let max_dep_priority = module
            .dependents
            .iter()
            .filter(|d| universe.contains(*d))
            .filter_map(|d| priorities.get(d).copied())
            .max()
            .unwrap_or(0);
        priorities.insert(
            name.clone(),
            max_dep_priority + costs.get(&name).copied().unwrap_or(1),
        );

        for dep in &module.deps {
            if !universe.contains(dep) {
                continue;
            }
            if let Some(count) = remaining_dependents.get_mut(dep) {
                *count -= 1;
                if *count == 0 {
                    queue.push(dep.clone());
                }
            }
        }
    }

    for name in universe {
        priorities.entry(name.clone()).or_insert(0);
    }
    priorities
}

fn signature_publication_mode(
    dependents: &AHashSet<String>,
    compile_universe: &AHashSet<String>,
) -> SignaturePublicationMode {
    if dependents.iter().any(|name| compile_universe.contains(name)) {
        SignaturePublicationMode::Eager
    } else {
        SignaturePublicationMode::OnDemand
    }
}

/// Run the short-circuit check or the in-process compile for a single module.
/// Invoked from worker threads inside the dispatcher scope; only reads
/// `BuildState`, never mutates it (except via the `BuildCommandState` mutex
/// used to publish results).
#[allow(clippy::too_many_arguments)]
fn compile_one(
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    registry_snapshot: &ModuleRegistry,
    stored_asts: &AHashMap<String, StoredAst>,
    module_name: &str,
    is_dirty: bool,
    parent_span: Span,
    in_process_hooks: InProcessSchedulerHooks,
    placement: qos::UnitClass,
    publication: SignaturePublicationMode,
) -> WorkerMsg {
    let _placement = qos::UnitPlacementGuard::enter(placement);
    let module = build_state.get_module(module_name).unwrap();
    let package = build_state
        .get_package(&module.package_name)
        .expect("Package not found");
    let _span = if tracing::enabled!(tracing::Level::INFO) {
        info_span!(
            parent: &parent_span,
            "build.compile_file",
            module = %module_name,
            package = %package.name,
            dirty = is_dirty
        )
        .entered()
    } else {
        Span::none().entered()
    };

    if !is_dirty {
        return WorkerMsg::Completed(CompletionMsg {
            module_name: module_name.to_string(),
            result: Ok(None),
            interface_result: Some(Ok(None)),
            is_clean: true,
            is_compiled: false,
            registry_updates: Vec::new(),
        });
    }

    // Run the compiler in-thread. The caller has already staged runtime
    // modules and namespace signatures into the shared registry, and the DAG
    // scheduler guarantees all dependencies of this module are registered
    // before it is dispatched.
    match &module.source_type {
        SourceType::SourceFile(_) => {
            let interface_generation_before = build_command_state.get_interface_generation(module_name);
            let result = compile_module_in_process_to_js_boundary(
                package,
                module,
                module_name,
                registry_snapshot,
                stored_asts,
                build_state,
                build_command_state,
                Some(&in_process_hooks),
                publication,
            );
            let interface_generation_after = build_command_state.get_interface_generation(module_name);
            match result {
                Ok(mut msg) => {
                    let is_clean_interface = interface_generation_before.is_some()
                        && interface_generation_before == interface_generation_after;
                    msg.is_clean = is_clean_interface;
                    WorkerMsg::PreJsReady(Box::new(msg))
                }
                Err(err) => WorkerMsg::Completed(CompletionMsg {
                    module_name: module_name.to_string(),
                    result: Err(err),
                    interface_result: None,
                    is_clean: false,
                    is_compiled: true,
                    registry_updates: Vec::new(),
                }),
            }
        }
        // Namespace signatures are registered before compilation starts; the
        // entry here just marks the mlmap compiled so its members can proceed.
        SourceType::MlMap(_) => WorkerMsg::Completed(CompletionMsg {
            module_name: package.namespace.to_suffix().unwrap(),
            result: Ok(None),
            interface_result: Some(Ok(None)),
            is_clean: false,
            is_compiled: false,
            registry_updates: Vec::new(),
        }),
    }
}

fn collect_stored_warnings_for_modules_not_recompiled(
    build_state: &BuildState,
    recompiled_modules: &AHashSet<String>,
) -> Vec<CompileWarning> {
    // Collect warnings from modules that were not recompiled in this build but still have stored
    // warnings from a previous compilation. This includes ready modules that were in the compile
    // universe but never scheduled because an earlier module failed.
    let mut warnings = Vec::new();
    for (module_name, module) in build_state.modules.iter() {
        if recompiled_modules.contains(module_name) {
            continue;
        }
        if let SourceType::SourceFile(ref source_file) = module.source_type {
            if let Some(ref warning) = source_file.implementation.compile_warnings {
                warnings.push(CompileWarning {
                    module_name: module_name.clone(),
                    package_name: module.package_name.clone(),
                    warning: warning.clone(),
                });
            }
            if let Some(ref interface) = source_file.interface
                && let Some(ref warning) = interface.compile_warnings
            {
                warnings.push(CompileWarning {
                    module_name: module_name.clone(),
                    package_name: module.package_name.clone(),
                    warning: warning.clone(),
                });
            }
        }
    }
    warnings
}

// Warning output should use the same deterministic module-name order whether a
// warning was emitted by this compile pass or replayed from a previous one.
fn append_compile_warnings(
    build_state: &BuildState,
    mut warning_entries: Vec<CompileWarning>,
    compile_warnings: &mut String,
    write_log: bool,
) {
    warning_entries.sort_by(|a, b| a.module_name.cmp(&b.module_name));
    for CompileWarning {
        package_name,
        warning,
        ..
    } in warning_entries
    {
        if let Some(package) = build_state.get_package(&package_name)
            && write_log
        {
            logs::append(package, &warning);
        }
        compile_warnings.push_str(&warning);
    }
}

/// How far a [`compile`] call got across its rounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompileProgress {
    /// No module has failed and the scheduler has not stalled.
    Ok,
    /// A module failed. Its dependents never become ready, so an unfinished
    /// universe is expected and is not reported as a cycle.
    HadErrors,
    /// Nothing was in flight while modules were still waiting and no module
    /// had failed: the remaining modules form a dependency cycle.
    Stalled,
}

#[instrument(name = "build.compile", skip_all)]
pub fn compile(
    build_state: &mut BuildCommandState,
    show_progress: bool,
    inc: impl Fn() + std::marker::Sync,
    set_length: impl Fn(u64),
) -> anyhow::Result<(String, String, usize)> {
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
    let _span = info_span!(
        "build.compile",
        dirty_modules = dirty_modules.len(),
        module_count = build_state.modules.len()
    )
    .entered();
    let compile_parent_span = Span::current();
    let incremental_plan = build_state.incremental_plan.take();
    let has_support_work = incremental_plan
        .as_ref()
        .is_some_and(|plan| *plan == IncrementalPlan::SupportEverything);
    if dirty_modules.is_empty() && !has_support_work {
        set_length(0);
        let mut warnings = String::new();
        append_compile_warnings(
            &build_state.build_state,
            collect_stored_warnings_for_modules_not_recompiled(&build_state.build_state, &AHashSet::new()),
            &mut warnings,
            !build_state.in_memory_only,
        );
        return Ok((String::new(), warnings, 0));
    }

    // Purge deleted/renamed modules from the in-memory registries so stale
    // entries don't remain resolvable in watch mode.
    build_state.purge_deleted_modules(&build_state.build_state.deleted_modules.clone());
    // Registrations can change between builds (watch mode, retries); only
    // digests computed by this build's scheduler are reused.
    build_state.published_item_digests.lock().unwrap().clear();
    build_state.prepared_interfaces.lock().unwrap().clear();
    build_state.clear_gentype_contexts();
    // Worker type stores hold dependency graphs published by this build
    // only; a new build starts every worker from an empty store.
    rescript_compiler::types::thread_store::begin_build();

    // Synthesize namespace module signatures in memory before any source
    // modules are compiled. Source modules may use `-open Namespace`, so the
    // namespace signature must be available in the PersistentEnv first.
    crate::build::phase_mark("compile-start");
    prepare_registry_for_runtime_precompile(build_state);

    // A runtime project supplies its own modules through the normal dependency
    // scheduler (-make-runtime disables implicit Stdlib dependencies). Other
    // projects need runtime interfaces before their modules can compile.
    if build_state.build_state.project_context.current_config.name != "@rescript/runtime" {
        let parent_span = compile_parent_span.clone();
        let pre_compile_result: Result<()> = std::thread::scope(|scope| {
            spawn_runtime_precompile(scope, || {
                let _parent = parent_span.enter();
                pre_compile_runtime_modules_with_mode(
                    &build_state.module_registry,
                    &build_state.build_state.compiler_info.runtime_path,
                    RuntimeStore::of_build(build_state).as_ref(),
                    build_state.check_only,
                    build_state.dump.is_some(),
                    build_state.revoked_snapshots[0],
                )
            })
            .and_then(join_runtime_precompile)
        });
        pre_compile_result?;
    }
    crate::build::phase_mark("runtime-precompile-end");

    // Clear source-fallback paths after pre-compilation.
    build_state
        .module_registry
        .lock()
        .unwrap()
        .set_source_fallback_paths(AHashMap::new());

    // Expand the compile universe: every dirty module plus everything that
    // transitively depends on it.
    // A cut-off build decides the dependents round by round instead.
    let mut compile_universe = dirty_modules.clone();
    let mut frontier = if incremental_plan == Some(IncrementalPlan::Cutoff) {
        Vec::new()
    } else {
        dirty_modules.iter().cloned().collect::<Vec<_>>()
    };
    while !frontier.is_empty() {
        let mut next_frontier = Vec::new();
        for module_name in &frontier {
            let module = build_state.get_module(module_name).unwrap();
            for dependent in &module.dependents {
                if !compile_universe.contains(dependent) {
                    compile_universe.insert(dependent.clone());
                    next_frontier.push(dependent.clone());
                }
            }
        }
        frontier = next_frontier;
    }

    let mut round_registry_only = incremental_plan
        .as_ref()
        .map(|plan| super::incremental::support_modules(build_state, &compile_universe, plan))
        .unwrap_or_default();
    if incremental_plan.is_some() {
        log::debug!(
            "incremental build: compiling {} modules, {} more for their dependencies only",
            compile_universe.len(),
            round_registry_only.len()
        );
    }
    compile_universe.extend(round_registry_only.iter().cloned());
    // A cut-off build compiles in rounds: the dependents of a module whose
    // interface digest changed are compiled in the next round
    // (see `incremental::next_round`).
    let cutoff = incremental_plan == Some(IncrementalPlan::Cutoff);

    let js_writer = JsWriter::spawn();
    let digest_prep = DigestPrep::spawn(build_state.snapshot_module_registry());
    // Bound the jobs handed to rayon so the priority heap still orders work —
    // dumping everything into rayon's queue would defeat #2. Allow one queued
    // job per thread beyond the running ones: a worker that finishes then
    // starts its next job at once instead of idling until this dispatcher
    // has received its message and spawned a replacement.
    // Set per round, by the pool the round compiles in.
    let mut capacity;
    let mut scheduler_counters =
        std::env::var_os("RESCRIPT_SCHEDULER_COUNTERS").map(|_| InProcessSchedulerCounters::default());
    // Critical-path placement: the highest-priority ready typecheck units get
    // performance-core QoS, at most one per performance core at a time.
    let critical_slots = qos::critical_slots();

    let mut results_buffer: Vec<CompletionMsg> = Vec::with_capacity(compile_universe.len());
    let mut progress = CompileProgress::Ok;
    let mut completed_count = 0usize;
    let mut total_universe_count = 0usize;
    let mut all_registry_only: AHashSet<String> = AHashSet::new();
    let mut all_dirty: AHashSet<String> = AHashSet::new();
    let mut compiled_this_build: AHashSet<String> = AHashSet::new();
    let mut failed_this_build: AHashSet<String> = AHashSet::new();
    // Failed modules that did not publish an interface: their dependents
    // cannot compile. (A module whose `.resi` compiled publishes it even when
    // its implementation fails.)
    let mut unpublished_this_build: AHashSet<String> = AHashSet::new();
    let mut round_dirty = dirty_modules;
    let mut round_universe = compile_universe;
    let mut round = 0usize;
    let compile_universe = loop {
        round += 1;
        // Unchanged dependencies with a stored interface are loaded instead
        // of compiled (see `incremental::stored_loadable`).
        if cutoff {
            let loadable =
                super::incremental::stored_loadable(build_state, &round_dirty, &round_registry_only);
            let loaded = super::incremental::load_stored(build_state, &loadable);
            super::incremental::decode_recorded_imports(build_state, &round_dirty, &loaded);
            // A stored interface that did not load: compile the module after
            // all (it was not parsed).
            let unloaded: AHashSet<String> = loadable.difference(&loaded).cloned().collect();
            super::incremental::parse_for_round(build_state, &unloaded)?;
            round_registry_only.retain(|module_name| !loaded.contains(module_name));
            round_universe.retain(|module_name| !loaded.contains(module_name));
            build_state.loaded_modules.extend(loaded);
        }
        // Each module's AST is dropped once the module is compiled (below), so
        // a module compiled by an earlier build (watch mode) or round has to
        // be parsed again before it compiles.
        super::incremental::parse_for_round(build_state, &round_universe)?;
        let registry_only = Arc::new(std::mem::take(&mut round_registry_only));
        let compile_universe_count = round_universe.len();
        total_universe_count += compile_universe_count;
        set_length(total_universe_count as u64);

        let mut stored_asts_snapshot = build_state.take_stored_asts(&round_universe);
        let compile_universe = Arc::new(std::mem::take(&mut round_universe));
        let module_costs = compute_module_costs(&compile_universe, &stored_asts_snapshot);
        let priorities =
            compute_critical_path_priorities(&compile_universe, &build_state.build_state, &module_costs);

        // Count of not-yet-completed in-universe dependencies for each module.
        // Only touched on the main thread.
        let mut pending_deps: AHashMap<String, usize> = compile_universe
            .iter()
            .map(|name| {
                let module = build_state.get_module(name).unwrap();
                let count = module
                    .deps
                    .iter()
                    .filter(|d| compile_universe.contains(*d))
                    .count();
                (name.clone(), count)
            })
            .collect();

        let mut ready_heap: BinaryHeap<WorkUnit> = compile_universe
            .iter()
            .filter(|name| pending_deps[*name] == 0)
            .map(|name| WorkUnit {
                priority: *priorities.get(name).unwrap_or(&0),
                module_name: name.clone(),
            })
            .collect();

        // Dirtiness propagation tracked locally: when a module's cmi changes, its
        // dependents are forced dirty. This mirrors the old `compile_dirty` flag
        // mutation but keeps build_state borrow-free while workers are running.
        let mut dirty_set: AHashSet<String> = std::mem::take(&mut round_dirty);
        dirty_set.extend(registry_only.iter().cloned());

        let build_state_ref: &BuildState = &build_state.build_state;
        let build_command_state_ref: &BuildCommandState = build_state;

        let (tx, rx) = mpsc::channel::<WorkerMsg>();
        // Worker snapshots share the registry's Arc-backed maps. Publishing a
        // dependency updates those shared maps, so a single template snapshot is
        // enough; each worker still clones it before adding local provisional
        // module/interface entries.
        let worker_registry_template = build_state.snapshot_module_registry();

        if round == 1 {
            crate::build::phase_mark("schedule-start");
        }
        let round_results_start = results_buffer.len();
        let mut completed: AHashSet<String> = AHashSet::new();
        let mut signature_ready: AHashSet<String> = AHashSet::new();
        let mut ready_js: Vec<PreJsMsg> = Vec::new();
        let mut pending_js_payloads: AHashMap<String, PreJsMsg> = AHashMap::new();
        let mut pending_js_deps: AHashMap<String, usize> = AHashMap::new();
        let mut waiting_js_by_dep: AHashMap<String, Vec<String>> = AHashMap::new();
        let mut js_metadata_ready: AHashSet<String> = AHashSet::new();
        let mut critical_in_flight: usize = 0;
        let mut critical_modules: AHashSet<String> = AHashSet::new();
        // Without cut-off rounds, a dependent outside the dirty set is
        // skipped when its dependencies are clean. An unchanged signature is
        // not enough for that: dependents also inline the JS metadata
        // (`let flag = true` becoming `false` keeps the signature). So such a
        // module releases its dependents once its metadata is final
        // (`metadata_same`). Cut-off builds compile every module of a round
        // and decide the next round from item digests that cover the metadata.
        let defer_clean_signatures = !cutoff;
        let mut deferred_clean: AHashSet<String> = AHashSet::new();
        let mut metadata_same: AHashMap<String, bool> = AHashMap::new();

        // A round of many modules compiles in the large pool (see
        // `pools::pool_for`).
        capacity = 2 * super::pools::threads_for(compile_universe_count).max(1);
        super::pools::in_place_scope_for(compile_universe_count, |scope| {
            let mut in_flight: usize = 0;
            loop {
                if let Some(counters) = scheduler_counters.as_mut() {
                    counters.observe_queues(
                        ready_heap.len(),
                        ready_js.len(),
                        pending_js_payloads.len(),
                        in_flight,
                    );
                }
                // Keep dispatching work that was already independent of any
                // failed module. Otherwise diagnostics vary with worker count:
                // a warning-producing module may or may not have started before
                // an unrelated error finishes.
                while in_flight < capacity {
                    if let Some(pre_js_msg) = pop_ready_js(&mut ready_js, &waiting_js_by_dep) {
                        if let Some(counters) = scheduler_counters.as_mut() {
                            counters.scheduled_js += 1;
                            if !ready_heap.is_empty() {
                                counters.js_scheduled_while_typecheck_ready += 1;
                            }
                        }
                        let module_name = pre_js_msg.module_name.clone();
                        let tx = tx.clone();
                        let write_tx = js_writer.sender();
                        let inc_ref = &inc;
                        let parent_span = compile_parent_span.clone();
                        let registry_snapshot = worker_registry_template.clone();
                        in_flight += 1;
                        if let Some(counters) = scheduler_counters.as_mut() {
                            counters.observe_queues(
                                ready_heap.len(),
                                ready_js.len(),
                                pending_js_payloads.len(),
                                in_flight,
                            );
                        }
                        let job_tx = tx.clone();
                        let panicked_module = module_name.clone();
                        spawn_job(
                            scope,
                            tx,
                            move || {
                                let msg = finish_in_process_js(
                                    build_state_ref,
                                    build_command_state_ref,
                                    pre_js_msg,
                                    parent_span,
                                    registry_snapshot,
                                    &job_tx,
                                    &write_tx,
                                );
                                if show_progress {
                                    inc_ref();
                                }
                                WorkerMsg::Completed(msg)
                            },
                            move |message| panicked_completion(panicked_module, &message),
                        );
                        trace!("scheduled in-process JS finish for {}", module_name);
                        continue;
                    }
                    let Some(work) = ready_heap.pop() else { break };
                    if let Some(counters) = scheduler_counters.as_mut() {
                        counters.scheduled_typecheck += 1;
                    }
                    let module_name = work.module_name.clone();
                    let is_dirty = dirty_set.contains(&module_name);
                    let publication = signature_publication_mode(
                        &build_state_ref.get_module(&module_name).unwrap().dependents,
                        &compile_universe,
                    );
                    let tx = tx.clone();
                    let inc_ref = &inc;
                    in_flight += 1;
                    let placement = if critical_in_flight < critical_slots {
                        critical_in_flight += 1;
                        critical_modules.insert(module_name.clone());
                        if let Some(counters) = scheduler_counters.as_mut() {
                            counters.critical_scheduled += 1;
                        }
                        qos::UnitClass::Critical
                    } else {
                        qos::UnitClass::Default
                    };
                    if let Some(counters) = scheduler_counters.as_mut() {
                        counters.observe_queues(
                            ready_heap.len(),
                            ready_js.len(),
                            pending_js_payloads.len(),
                            in_flight,
                        );
                    }
                    let registry_snapshot = worker_registry_template.clone();
                    // Hand the worker this module's ASTs: they are freed as soon
                    // as it is compiled, not when the build ends.
                    let module_asts: AHashMap<String, StoredAst> =
                        [format!("{module_name}:impl"), format!("{module_name}:intf")]
                            .into_iter()
                            .filter_map(|key| stored_asts_snapshot.remove(&key).map(|ast| (key, ast)))
                            .collect();
                    let parent_span = compile_parent_span.clone();
                    let in_process_hooks = InProcessSchedulerHooks {
                        tx: tx.clone(),
                        compile_universe: compile_universe.clone(),
                        registry_only: registry_only.clone(),
                    };
                    let panicked_module = module_name.clone();
                    spawn_job(
                        scope,
                        tx,
                        move || {
                            let msg = compile_one(
                                build_state_ref,
                                build_command_state_ref,
                                &registry_snapshot,
                                &module_asts,
                                &module_name,
                                is_dirty,
                                parent_span,
                                in_process_hooks,
                                placement,
                                publication,
                            );
                            if show_progress && matches!(msg, WorkerMsg::Completed(_)) {
                                inc_ref();
                            }
                            msg
                        },
                        move |message| panicked_completion(panicked_module, &message),
                    );
                }

                if in_flight == 0 {
                    if completed.len() < compile_universe_count && progress == CompileProgress::Ok {
                        progress = CompileProgress::Stalled;
                    }
                    break;
                }

                let idle_slots = if ready_heap.is_empty() && ready_js.is_empty() && in_flight < capacity {
                    capacity - in_flight
                } else {
                    0
                };
                let wait_start = scheduler_counters.as_ref().map(|_| Instant::now());
                let Ok(first_msg) = rx.recv() else { break };
                if let (Some(counters), Some(wait_start)) = (scheduler_counters.as_mut(), wait_start) {
                    counters.observe_wait(wait_start.elapsed(), idle_slots);
                }
                let mut worker_messages = vec![first_msg];
                while let Ok(msg) = rx.try_recv() {
                    worker_messages.push(msg);
                }

                for worker_msg in worker_messages {
                    match worker_msg {
                        WorkerMsg::SignatureReady(msg) => {
                            if let Some(counters) = scheduler_counters.as_mut() {
                                counters.signature_ready += 1;
                            }
                            let module_name = msg.module_name.clone();
                            let is_clean = apply_signature_ready(build_command_state_ref, msg);
                            if is_clean && defer_clean_signatures {
                                deferred_clean.insert(module_name);
                                continue;
                            }
                            unblock_dependents(
                                build_state_ref,
                                &compile_universe,
                                &priorities,
                                &mut pending_deps,
                                &mut dirty_set,
                                &mut signature_ready,
                                &mut ready_heap,
                                &module_name,
                                is_clean,
                            );
                        }
                        WorkerMsg::PreJsReady(msg) => {
                            let msg = *msg;
                            if let Some(counters) = scheduler_counters.as_mut() {
                                counters.pre_js_ready += 1;
                            }
                            in_flight -= 1;
                            let module_name = msg.module_name.clone();
                            if critical_modules.remove(&module_name) {
                                critical_in_flight -= 1;
                            }
                            let pending_deps_for_js = msg
                                .needed_modules
                                .iter()
                                .filter(|dep| !completed.contains(*dep) && !js_metadata_ready.contains(*dep))
                                .cloned()
                                .collect::<Vec<_>>();
                            if pending_deps_for_js.is_empty() {
                                ready_js.push(msg);
                            } else {
                                if let Some(counters) = scheduler_counters.as_mut() {
                                    counters.observe_pending_js_deps(pending_deps_for_js.iter());
                                }
                                pending_js_deps.insert(module_name.clone(), pending_deps_for_js.len());
                                for dep in pending_deps_for_js {
                                    waiting_js_by_dep
                                        .entry(dep)
                                        .or_default()
                                        .push(module_name.clone());
                                }
                                pending_js_payloads.insert(module_name, msg);
                            }
                        }
                        WorkerMsg::JsMetadataReady(mut msg) => {
                            apply_pending_registry_updates(
                                build_command_state_ref,
                                std::mem::take(&mut msg.registry_updates),
                            );
                            let ready_name = msg.module_name;
                            js_metadata_ready.insert(ready_name.clone());
                            if defer_clean_signatures {
                                let same = build_command_state_ref.record_published_digest(&ready_name);
                                metadata_same.insert(ready_name.clone(), same);
                                if deferred_clean.remove(&ready_name) {
                                    unblock_dependents(
                                        build_state_ref,
                                        &compile_universe,
                                        &priorities,
                                        &mut pending_deps,
                                        &mut dirty_set,
                                        &mut signature_ready,
                                        &mut ready_heap,
                                        &ready_name,
                                        same,
                                    );
                                }
                            }

                            if let Some(waiters) = waiting_js_by_dep.remove(&ready_name) {
                                for waiter in waiters {
                                    let Some(count) = pending_js_deps.get_mut(&waiter) else {
                                        continue;
                                    };
                                    *count -= 1;
                                    if *count == 0 {
                                        pending_js_deps.remove(&waiter);
                                        if let Some(payload) = pending_js_payloads.remove(&waiter) {
                                            ready_js.push(payload);
                                        }
                                    }
                                }
                            }
                        }
                        WorkerMsg::Completed(mut msg) => {
                            if let Some(counters) = scheduler_counters.as_mut() {
                                counters.completed += 1;
                            }
                            in_flight -= 1;
                            if critical_modules.remove(&msg.module_name) {
                                critical_in_flight -= 1;
                            }
                            apply_pending_registry_updates(
                                build_command_state_ref,
                                std::mem::take(&mut msg.registry_updates),
                            );

                            // Its registration is final: compile is done with it.
                            digest_prep.prepare(msg.module_name.clone());
                            let module_failed = msg.result.is_err()
                                || msg.interface_result.as_ref().is_some_and(|r| r.is_err());
                            if module_failed {
                                progress = CompileProgress::HadErrors;
                            }

                            let finished_name = msg.module_name.clone();
                            let is_clean = if defer_clean_signatures && msg.is_compiled {
                                let same = match metadata_same.get(&finished_name) {
                                    Some(same) => *same,
                                    None => build_command_state_ref.record_published_digest(&finished_name),
                                };
                                msg.is_clean && same && !module_failed
                            } else {
                                msg.is_clean
                            };
                            if deferred_clean.remove(&finished_name) {
                                unblock_dependents(
                                    build_state_ref,
                                    &compile_universe,
                                    &priorities,
                                    &mut pending_deps,
                                    &mut dirty_set,
                                    &mut signature_ready,
                                    &mut ready_heap,
                                    &finished_name,
                                    is_clean,
                                );
                            }
                            completed.insert(finished_name.clone());
                            js_metadata_ready.insert(finished_name.clone());

                            if let Some(waiters) = waiting_js_by_dep.remove(&finished_name) {
                                for waiter in waiters {
                                    let Some(count) = pending_js_deps.get_mut(&waiter) else {
                                        continue;
                                    };
                                    *count -= 1;
                                    if *count == 0 {
                                        pending_js_deps.remove(&waiter);
                                        if let Some(payload) = pending_js_payloads.remove(&waiter) {
                                            ready_js.push(payload);
                                        }
                                    }
                                }
                            }

                            let completed_without_signature =
                                !signature_ready.contains(&finished_name) && !module_failed;
                            if completed_without_signature {
                                unblock_dependents(
                                    build_state_ref,
                                    &compile_universe,
                                    &priorities,
                                    &mut pending_deps,
                                    &mut dirty_set,
                                    &mut signature_ready,
                                    &mut ready_heap,
                                    &finished_name,
                                    is_clean,
                                );
                            }

                            results_buffer.push(msg);
                        }
                    }
                }
                if let Some(counters) = scheduler_counters.as_mut() {
                    counters.observe_queues(
                        ready_heap.len(),
                        ready_js.len(),
                        pending_js_payloads.len(),
                        in_flight,
                    );
                }
            }
        });
        // Close our sender handle so any lingering clones in already-spawned
        // workers don't keep the channel open past the scope.
        drop(tx);
        // Modules this round did not get to (an error stopped it) keep their
        // ASTs for the next build.
        build_state.restore_stored_asts(stored_asts_snapshot);
        completed_count += completed.len();
        for msg in &results_buffer[round_results_start..] {
            let ok = msg.result.is_ok() && !matches!(msg.interface_result, Some(Err(_)));
            if msg.is_compiled && ok {
                compiled_this_build.insert(msg.module_name.clone());
            } else if !ok {
                failed_this_build.insert(msg.module_name.clone());
                let interface_failed = match &msg.interface_result {
                    Some(result) => result.is_err(),
                    None => true,
                };
                if interface_failed {
                    unpublished_this_build.insert(msg.module_name.clone());
                }
            }
        }
        all_registry_only.extend(registry_only.iter().cloned());
        all_dirty.extend(dirty_set);
        if !cutoff || progress == CompileProgress::Stalled {
            break compile_universe;
        }
        let written: AHashSet<String> = compiled_this_build
            .iter()
            .filter(|module_name| !all_registry_only.contains(*module_name))
            .cloned()
            .collect();
        let mut next = super::incremental::next_round(build_state, &written, &compiled_this_build);
        // After errors, still compile the modules a full build would: those
        // that do not depend on a failed module (a failed module is not
        // compiled again).
        if !failed_this_build.is_empty() {
            let blocked = super::incremental::downstream_of(build_state, &unpublished_this_build);
            next.retain(|module_name| {
                !blocked.contains(module_name) && !failed_this_build.contains(module_name)
            });
        }
        if next.is_empty() {
            break compile_universe;
        }
        let mut available = compiled_this_build.clone();
        available.extend(build_state.loaded_modules.iter().cloned());
        round_registry_only = super::incremental::round_support(build_state, &next, &available);
        let loadable = super::incremental::stored_loadable(build_state, &next, &round_registry_only);
        log::debug!(
            "incremental build: round {}: compiling {} modules whose imports changed, {} more for their dependencies only",
            round + 1,
            next.len(),
            round_registry_only.len()
        );
        let mut needed = next.clone();
        needed.extend(round_registry_only.iter().cloned());
        let to_parse: AHashSet<String> = needed.difference(&loadable).cloned().collect();
        super::incremental::parse_for_round(build_state, &to_parse)?;
        all_registry_only.retain(|module_name| !next.contains(module_name));
        results_buffer.retain(|msg| !needed.contains(&msg.module_name));
        round_universe = needed;
        round_dirty = next;
    };
    let registry_only = all_registry_only;
    let dirty_set = all_dirty;
    // A full build does not compile the modules that depend on a failed
    // one, and reports nothing for them: do not replay the warnings of their
    // earlier compile either (they stay recorded, for the builds after).
    let blocked_by_failure = if incremental_plan.is_some() && !failed_this_build.is_empty() {
        super::incremental::downstream_of(build_state, &failed_this_build)
    } else {
        AHashSet::new()
    };
    build_state.compiled_modules.extend(compiled_this_build);
    if let Some(counters) = scheduler_counters.as_ref() {
        counters.print_report(capacity);
    }
    let js_write_failures = js_writer.finish();
    // Every module's last registration is the one its last completion saw:
    // only completing modules register (see `apply_pending_registry_updates`).
    {
        let mut item_digests = build_state.published_item_digests.lock().unwrap();
        let mut interfaces = build_state.prepared_interfaces.lock().unwrap();
        for prepared in digest_prep.finish() {
            match prepared.item_digests {
                Some(items) => item_digests.insert(prepared.module_name.clone(), items),
                None => item_digests.remove(&prepared.module_name),
            };
            match prepared.interface {
                Some(interface) => interfaces.insert(prepared.module_name, interface),
                None => interfaces.remove(&prepared.module_name),
            };
        }
    }

    trace!(
        "compiled {} of the {} modules to check",
        completed_count, total_universe_count,
    );

    let mut compile_errors = String::new();
    let mut compile_warnings = String::new();
    let mut warning_entries = Vec::new();
    let mut num_compiled_modules = 0;

    // Persist propagated dirtiness back onto build_state. Modules that were
    // marked dirty (because a predecessor's cmi changed) but blocked by a
    // failed prerequisite must keep compile_dirty = true so the next
    // incremental build recompiles them.
    // Successful recompiles in the result loop below override this back to
    // false for the modules that actually ran.
    for name in &dirty_set {
        if let Some(module) = build_state.build_state.modules.get_mut(name) {
            module.compile_dirty = true;
        }
    }

    // Sort by module name so the accumulated error/warning strings and the
    // per-package compile.log writes are deterministic across runs, even
    // though modules complete in arbitrary order.
    results_buffer.sort_by(|a, b| a.module_name.cmp(&b.module_name));

    // A module is only dispatched once its dependencies compiled, so a module
    // that (transitively) depends on a failed one is never compiled in a
    // subprocess build. In-process builds can start a dependent early, from
    // its dependency's published interface; drop such results so they are
    // neither reported nor counted, and leave the module dirty.
    let failed: AHashSet<String> = results_buffer
        .iter()
        .filter(|msg| msg.result.is_err() || matches!(msg.interface_result, Some(Err(_))))
        .map(|msg| msg.module_name.clone())
        .collect();
    if !failed.is_empty() {
        let depends_on_failed = |name: &str| {
            let mut stack = vec![name.to_string()];
            let mut seen = AHashSet::new();
            while let Some(current) = stack.pop() {
                let Some(module) = build_state.build_state.modules.get(&current) else {
                    continue;
                };
                for dep in &module.deps {
                    if failed.contains(dep) {
                        return true;
                    }
                    if seen.insert(dep.clone()) {
                        stack.push(dep.clone());
                    }
                }
            }
            false
        };
        let (dropped, kept): (Vec<_>, Vec<_>) = std::mem::take(&mut results_buffer)
            .into_iter()
            .partition(|msg| depends_on_failed(&msg.module_name));
        results_buffer = kept;
        for msg in dropped {
            if msg.is_compiled {
                build_state.compiled_modules.remove(&msg.module_name);
                build_state.invalidated_modules.insert(msg.module_name);
            }
        }
    }

    // These timestamps are used as a compile-generation marker by
    // mark_modules_with_expired_deps_dirty, not as precise wall-clock compile
    // times. All modules successfully compiled in one pass are mutually
    // up-to-date for that pass, so they must receive the same timestamp.

    let mut recompiled_modules = AHashSet::<String>::new();

    for msg in results_buffer {
        let CompletionMsg {
            module_name,
            result,
            interface_result,
            is_compiled,
            ..
        } = msg;

        if is_compiled {
            if !registry_only.contains(&module_name) {
                num_compiled_modules += 1;
            }
            recompiled_modules.insert(module_name.clone());
        }

        let package_name = {
            let module = build_state
                .build_state
                .modules
                .get(&module_name)
                .ok_or_else(|| anyhow!("Module not found"))?;
            module.package_name.clone()
        };
        let package = build_state
            .build_state
            .packages
            .get(&package_name)
            .ok_or_else(|| anyhow!("Package name not found"))?;

        let (compile_warning, compile_error, interface_warning, interface_error) = {
            let module = build_state
                .build_state
                .modules
                .get_mut(&module_name)
                .ok_or_else(|| anyhow!("Module not found"))?;

            let (compile_warning, compile_error) = match module.source_type {
                SourceType::MlMap(ref mut mlmap) => {
                    module.compile_dirty = false;
                    mlmap.parse_dirty = false;
                    (None, None)
                }
                SourceType::SourceFile(ref mut source_file) => match &result {
                    Ok(None) if !is_compiled => (None, None),
                    Ok(Some(err)) => {
                        let warning_text = err.to_string();
                        source_file.implementation.compile_state = CompileState::Warning;
                        source_file.implementation.compile_warnings = Some(warning_text.clone());
                        (Some(warning_text), None)
                    }
                    Ok(None) => {
                        source_file.implementation.compile_state = CompileState::Success;
                        source_file.implementation.compile_warnings = None;
                        (None, None)
                    }
                    Err(err) => {
                        source_file.implementation.compile_state = CompileState::Error;
                        source_file.implementation.compile_warnings = None;
                        (None, Some(err.to_string()))
                    }
                },
            };

            let (interface_warning, interface_error) = if let SourceType::SourceFile(ref mut source_file) =
                module.source_type
            {
                match &interface_result {
                    Some(Ok(None)) if !is_compiled => (None, None),
                    Some(Ok(Some(err))) => {
                        let warning_text = err.to_string();
                        source_file.interface.as_mut().unwrap().compile_state = CompileState::Warning;
                        source_file.interface.as_mut().unwrap().compile_warnings = Some(warning_text.clone());
                        (Some(warning_text), None)
                    }
                    Some(Ok(None)) => {
                        if let Some(interface) = source_file.interface.as_mut() {
                            interface.compile_state = CompileState::Success;
                            interface.compile_warnings = None;
                        }
                        (None, None)
                    }
                    Some(Err(err)) => {
                        source_file.interface.as_mut().unwrap().compile_state = CompileState::Error;
                        source_file.interface.as_mut().unwrap().compile_warnings = None;
                        (None, Some(err.to_string()))
                    }
                    _ => (None, None),
                }
            } else {
                (None, None)
            };

            if result.is_ok() && interface_result.as_ref().is_none_or(|r| r.is_ok()) {
                module.compile_dirty = false;
                if is_compiled && !registry_only.contains(&module_name) {
                    build_state.written_modules.insert(module_name.clone());
                    if let Some(started) = build_state.build_run.started_at() {
                        build_state.js_confirmed_at.insert(module_name.clone(), started);
                    }
                }
            }

            (compile_warning, compile_error, interface_warning, interface_error)
        };

        if let Some(warning) = compile_warning {
            warning_entries.push(CompileWarning {
                module_name: module_name.clone(),
                package_name: package_name.clone(),
                warning,
            });
        }
        if let Some(error) = compile_error {
            if !build_state.in_memory_only {
                logs::append(package, &error);
            }
            compile_errors.push_str(&error);
        }
        if let Some(warning) = interface_warning {
            warning_entries.push(CompileWarning {
                module_name: module_name.clone(),
                package_name: package_name.clone(),
                warning,
            });
        }
        if let Some(error) = interface_error {
            if !build_state.in_memory_only {
                logs::append(package, &error);
            }
            compile_errors.push_str(&error);
        }
    }

    if progress == CompileProgress::Stalled {
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

        let mut touched_packages = AHashSet::<String>::new();
        for module_name in cycle.iter() {
            if let Some(module) = build_state.get_module(module_name)
                && touched_packages.insert(module.package_name.clone())
                && let Some(package) = build_state.get_package(&module.package_name)
                && !build_state.in_memory_only
            {
                logs::append(package, &message);
            }
        }

        compile_errors.push_str(&message);
    }

    // A module whose JS output could not be written must be recompiled next
    // time, exactly as when the write still happened on the worker.
    for (module_name, err) in js_write_failures {
        build_state.js_confirmed_at.remove(&module_name);
        build_state.written_modules.remove(&module_name);
        if let Some(module) = build_state.build_state.modules.get_mut(&module_name) {
            module.compile_dirty = true;
        }
        compile_errors.push_str(&format!("Failed to write JS output for {module_name}: {err:#}\n"));
    }

    // Collect replayed warnings into the same list as fresh warnings so mixed
    // output matches the sorted order used when every module compiles normally.
    warning_entries.extend(
        collect_stored_warnings_for_modules_not_recompiled(&build_state.build_state, &recompiled_modules)
            .into_iter()
            .filter(|warning| !blocked_by_failure.contains(&warning.module_name)),
    );
    append_compile_warnings(
        &build_state.build_state,
        warning_entries,
        &mut compile_warnings,
        !build_state.in_memory_only,
    );

    Ok((compile_errors, compile_warnings, num_compiled_modules))
}

/// Resolved runtime path per project root. Keyed by root so a later project
/// in the same process (watch reinit, tests, tooling) resolves its own.
static RUNTIME_PATH_MEMO: OnceLock<Mutex<AHashMap<PathBuf, PathBuf>>> = OnceLock::new();

pub fn get_runtime_path(package_config: &Config, project_context: &ProjectContext) -> Result<PathBuf> {
    let memo = RUNTIME_PATH_MEMO.get_or_init(Default::default);
    let root = project_context.get_root_path();
    if let Some(p) = memo.lock().unwrap().get(root) {
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

    Ok(memo
        .lock()
        .unwrap()
        .entry(root.to_path_buf())
        .or_insert(resolved)
        .clone())
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
    // Match the parser's root spelling: canonical during builds, caller-supplied
    // for compiler-args consumers such as editor incremental type checking.
    project_root: &Path,
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
    source_map_command: config::SourceMapCommand,
    // Pre-expanded source directories for the current package (used by gentype).
    // Pass an empty slice when unavailable (e.g. the compiler-args CLI command).
    current_package_dirs: &[PathBuf],
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
    let jsx_preserve_args = root_config.get_jsx_preserve_args();
    let source_map_args = root_config.get_source_map_args(source_map_command);
    let bsb_project_root = project_context.get_root_path();
    let dep_paths: Vec<(String, PathBuf)> = if config.gentype_config.is_some() {
        let resolved = packages.as_ref().map(|pkgs| {
            config
                .dependencies
                .iter()
                .flatten()
                .filter_map(|dep| {
                    let name = dep.name();
                    pkgs.get(name).map(|pkg| (name.to_string(), pkg.path.clone()))
                })
                .collect::<Vec<_>>()
        });
        resolved.unwrap_or_default()
    } else {
        Vec::new()
    };
    let gentype_arg = config.get_gentype_args(current_package_dirs, Some(bsb_project_root), &dep_paths);
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
    let project_root_args = vec![
        "-bs-project-root".to_string(),
        project_root.to_string_lossy().to_string(),
    ];

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
                        spec.module.as_str(),
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
        // bsc runs in the package's flat artifact directory, which holds the
        // package's compiled modules (rewatch-ocaml's `-I .`).
        vec!["-I".to_string(), ".".to_string()],
        runtime_path_args,
        dependency_paths,
        jsx_args,
        jsx_module_args,
        jsx_preserve_args,
        source_map_args,
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
        project_root_args,
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
    let normal_deps: Vec<DependentPackage> = config
        .get_dependency_names()
        .into_iter()
        .map(DependentPackage::Normal)
        .collect();

    // We can only access dev dependencies for source_files that are marked as "type":"dev"
    let dev_deps: Vec<DependentPackage> = if is_file_type_dev {
        config
            .get_dev_dependency_names()
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
                    packages::get_build_path(&canonicalized_path)
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

pub(crate) struct InProcessCompilerFlags {
    pub(crate) nopervasives: bool,
    pub(crate) no_version_header: bool,
    pub(crate) check_div_by_zero: bool,
    pub(crate) cross_module_inline: bool,
    pub(crate) no_assert_false: bool,
    pub(crate) noassert: bool,
    /// `Clflags.transparent_modules` (`-no-alias-deps`).
    pub(crate) transparent_modules: bool,
    pub(crate) no_builtin_ppx: bool,
    pub(crate) make_runtime: bool,
    pub(crate) debug: bool,
    pub(crate) jsx_preserve: bool,
    pub(crate) jsx_version: Option<i32>,
    pub(crate) jsx_module: Option<String>,
    pub(crate) experimental_let_unwrap: bool,
    pub(crate) open_modules: Vec<String>,
    pub(crate) warning_specs: Vec<String>,
    pub(crate) warning_error_specs: Vec<String>,
    /// `Clflags.keep_locs` (`-keep-locs`/`-no-keep-locs`, default on).
    pub(crate) keep_locs: bool,
}

impl Default for InProcessCompilerFlags {
    fn default() -> Self {
        Self {
            nopervasives: false,
            no_version_header: false,
            check_div_by_zero: true,
            cross_module_inline: false,
            no_assert_false: false,
            noassert: false,
            transparent_modules: false,
            no_builtin_ppx: false,
            make_runtime: false,
            debug: false,
            jsx_preserve: false,
            jsx_version: None,
            jsx_module: None,
            experimental_let_unwrap: false,
            open_modules: Vec::new(),
            warning_specs: Vec::new(),
            warning_error_specs: Vec::new(),
            keep_locs: true,
        }
    }
}

pub(crate) fn parse_in_process_compiler_flags(flags: &[String]) -> InProcessCompilerFlags {
    let mut parsed = InProcessCompilerFlags::default();
    let mut iter = flags.iter();
    while let Some(flag) = iter.next() {
        match flag.as_str() {
            "-nopervasives" => parsed.nopervasives = true,
            "-bs-no-version-header" => parsed.no_version_header = true,
            "-bs-no-check-div-by-zero" => parsed.check_div_by_zero = false,
            "-bs-cross-module-opt" => parsed.cross_module_inline = true,
            "-bs-noassertfalse" => parsed.no_assert_false = true,
            // OCaml compiler/bsc/rescript_compiler_main.ml:391-392
            // parses -noassert into Clflags.noassert.
            "-noassert" => parsed.noassert = true,
            // compiler/bsc/rescript_compiler_main.ml:325-327.
            "-no-alias-deps" => parsed.transparent_modules = true,
            "-bs-no-builtin-ppx" => parsed.no_builtin_ppx = true,
            "-make-runtime" => parsed.make_runtime = true,
            "-bs-g" => parsed.debug = true,
            "-bs-jsx-preserve" => parsed.jsx_preserve = true,
            // compiler/bsc/rescript_compiler_main.ml:454-458.
            "-keep-locs" => parsed.keep_locs = true,
            "-no-keep-locs" => parsed.keep_locs = false,
            "-bs-jsx" => {
                if let Some(version) = iter.next().and_then(|v| v.parse::<i32>().ok()) {
                    parsed.jsx_version = Some(version);
                }
            }
            "-bs-jsx-module" => {
                if let Some(module) = iter.next() {
                    rescript_compiler::driver::apply_jsx_module_flag(
                        module,
                        &mut parsed.jsx_module,
                        &mut parsed.jsx_version,
                    );
                }
            }
            "-enable-experimental" => {
                if let Some(feature) = iter.next()
                    && feature == "LetUnwrap"
                {
                    parsed.experimental_let_unwrap = true;
                }
            }
            "-open" => {
                if let Some(mod_name) = iter.next() {
                    parsed.open_modules.push(mod_name.clone());
                }
            }
            "-w" => {
                if let Some(spec) = iter.next() {
                    parsed.warning_specs.push(spec.clone());
                }
            }
            "-warn-error" => {
                if let Some(spec) = iter.next() {
                    parsed.warning_error_specs.push(spec.clone());
                }
            }
            _ => {}
        }
    }
    parsed
}

/// Build `CompilerOptions` for an in-process compilation from the package config.
pub(crate) fn build_compiler_options(
    package: &packages::Package,
    module_name: &str,
    source_file_path: &Path,
    build_command_state: &BuildCommandState,
) -> Result<rescript_compiler::driver::CompilerOptions> {
    let build_state = &build_command_state.build_state;
    let is_type_dev = build_state
        .modules
        .get(module_name)
        .is_some_and(|module| module.is_type_dev);
    let key = (package.path.clone(), is_type_dev);
    let cached = build_command_state
        .package_compiler_options
        .lock()
        .unwrap()
        .get(&key)
        .cloned();
    let template = match cached {
        Some(template) => template,
        None => {
            let template = Arc::new(build_package_compiler_options(
                package,
                is_type_dev,
                build_command_state,
            )?);
            build_command_state
                .package_compiler_options
                .lock()
                .unwrap()
                .insert(key, template.clone());
            template
        }
    };
    let mut options = (*template).clone();
    options.gentype_declarations_needed = build_command_state
        .gentype_needed
        .as_ref()
        .is_none_or(|needed| needed.contains(module_name));
    if let Some(dump) = &build_command_state.dump {
        options.dumps = dump.kinds.clone();
    }
    options.typed_trees = build_command_state.typed_trees.clone();

    // Source filename for interface constraint and JS import resolution. OCaml
    // computes output_dir from the package output prefix before rebasing module
    // imports; see compiler/core/js_dump_program.ml:128 and
    // compiler/core/js_name_of_module_id.ml:135-139.
    options.source_filename = Some(
        Path::new(&package.path)
            .join(source_file_path)
            .to_string_lossy()
            .to_string(),
    );
    // Output path and module format for JS import resolution.
    let js_output_targets =
        js_output_targets_for_source(package, source_file_path, build_state.get_root_config());
    options.output_module_format = js_output_targets.first().map(|target| target.module_format);
    options.output_path = js_output_targets.first().map(|target| target.path.clone());
    options.js_output_targets = js_output_targets;
    options.js_package_specs = js_package_specs(build_state.get_root_config());
    options.module_name = Some(module_name.to_string());
    Ok(options)
}

/// The compiler options shared by every module of `package` (and dev-ness).
fn build_package_compiler_options(
    package: &packages::Package,
    is_type_dev: bool,
    build_command_state: &BuildCommandState,
) -> Result<rescript_compiler::driver::CompilerOptions> {
    let build_state = &build_command_state.build_state;
    let root_config = build_state.get_root_config();
    let project_context = &build_state.project_context;

    // Parse package compiler-flags for flags the in-process compiler needs to honor.
    // In the subprocess path, these are passed as raw CLI args to bsc.
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let warning_args = package.config.get_warning_args(package.is_local_dep, None);
    // The root configuration's JSX flags apply to every package, as in the
    // subprocess `bsc` arguments (`compiler_args`) and the in-process parse.
    let parsed_flags = parse_in_process_compiler_flags(
        &[
            root_config.get_jsx_args(),
            root_config.get_jsx_module_args(),
            root_config.get_jsx_preserve_args(),
            bsc_flags,
            warning_args,
        ]
        .concat(),
    );

    // Collect -I paths from all dependencies (same logic as get_dependency_paths)
    let mut include_paths: Vec<PathBuf> = Vec::new();

    // Add the package's own artifact directory
    include_paths.push(package.get_build_path());

    // Add the dependencies' artifact directories
    let dep_names: Vec<&str> = package
        .config
        .dependencies
        .as_ref()
        .map(|d| d.iter().map(|s| s.name()).collect())
        .unwrap_or_default();
    for dep_name in dep_names {
        if let Some(dep_pkg) = build_state.packages.get(dep_name) {
            include_paths.push(dep_pkg.get_build_path());
        }
    }

    // OCaml compiles with `-I` for the package, its dependencies and, for
    // `type: dev` sources, its dev dependencies (`get_dependency_paths`);
    // units of other packages are not visible.
    let mut visible_package_roots = vec![package.path.clone()];
    let visible_deps = package.config.get_dependency_names().into_iter().chain(
        is_type_dev
            .then(|| package.config.get_dev_dependency_names())
            .into_iter()
            .flatten(),
    );
    for dep_name in visible_deps {
        if let Some(dep_pkg) = build_state.packages.get(&dep_name) {
            visible_package_roots.push(dep_pkg.path.clone());
            let dep_include = dep_pkg.get_build_path();
            if !include_paths.contains(&dep_include) {
                include_paths.push(dep_include);
            }
        }
    }

    // Extract JSX version from root config
    let jsx_version = parsed_flags.jsx_version.or_else(|| {
        root_config
            .jsx
            .as_ref()
            .and_then(|jsx| jsx.version)
            .filter(|&v| v == 4)
    });
    let experimental_let_unwrap = parsed_flags.experimental_let_unwrap
        || package
            .config
            .has_experimental_feature(config::ExperimentalFeature::LetUnwrap)
        || root_config.has_experimental_feature(config::ExperimentalFeature::LetUnwrap);

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
    open_modules.extend(parsed_flags.open_modules);

    // Runtime path
    let runtime_path = get_runtime_path(&package.config, project_context).ok();

    let gentype_context = package.config.gentype_config.as_ref().map(|_| {
        build_command_state.gentype_context(&package.path, || {
            // Mirrors the bsc CLI path in compiler/bsc/rescript_compiler_main.ml:300-343:
            // rewatch first materializes the exact -bs-gentype-* flags, then the
            // Rust compiler builds GenTypeConfig.t from that flag stream.
            let current_package_dirs: &[PathBuf] = package.gentype_dirs.as_deref().unwrap_or(&[]);
            let dep_paths: Vec<(String, PathBuf)> = package
                .config
                .dependencies
                .as_ref()
                .map(|deps| {
                    deps.iter()
                        .filter_map(|dep| {
                            let name = dep.name();
                            build_state
                                .packages
                                .get(name)
                                .map(|pkg| (name.to_string(), pkg.path.clone()))
                        })
                        .collect()
                })
                .unwrap_or_default();
            // OCaml bsc wires -bs-project-root into GenTypeConfig.project_root at
            // compiler/bsc/rescript_compiler_main.ml:266-269 before
            // compiler/gentype/GenTypeConfig.ml:124-131 builds Config.t.
            let mut gentype_args = vec![
                "-bs-project-root".to_string(),
                package.path.to_string_lossy().to_string(),
            ];
            gentype_args.extend(package.config.get_gentype_args(
                current_package_dirs,
                Some(project_context.get_root_path()),
                &dep_paths,
            ));
            rescript_compiler::gentype::config::build_config_from_cli_args(
                package.config.get_namespace().to_suffix(),
                &gentype_args,
            )
        })
    });
    let gentype_config = gentype_context.as_ref().map(|context| context.config.clone());
    let gentype_resolver = gentype_context.map(|context| context.resolver.clone());

    let (source_map, source_map_sources_content, source_map_root) =
        match root_config.effective_source_map_mode(build_state.source_map_command) {
            Some(config::SourceMapMode::Linked) => (
                rescript_compiler::js_ir::source_map::SourceMapMode::Linked,
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.sources_content,
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or(false),
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.source_root.clone(),
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or_default(),
            ),
            Some(config::SourceMapMode::Inline) => (
                rescript_compiler::js_ir::source_map::SourceMapMode::Inline,
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.sources_content,
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or(false),
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.source_root.clone(),
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or_default(),
            ),
            Some(config::SourceMapMode::Hidden) => (
                rescript_compiler::js_ir::source_map::SourceMapMode::Hidden,
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.sources_content,
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or(false),
                root_config
                    .source_map
                    .as_ref()
                    .and_then(|value| match value {
                        config::SourceMapConfig::Options(options) => options.source_root.clone(),
                        config::SourceMapConfig::Disabled => None,
                    })
                    .unwrap_or_default(),
            ),
            None => (
                rescript_compiler::js_ir::source_map::SourceMapMode::None,
                false,
                String::new(),
            ),
        };

    Ok(rescript_compiler::driver::CompilerOptions {
        backend: rescript_compiler::bir::shadow::BackendMode::from_env(),
        check_only: build_command_state.check_only,
        include_paths,
        runtime_path,
        open_modules,
        collect_unit_reads: true,
        warning_locations: None,
        warning_specs: parsed_flags.warning_specs,
        warning_error_specs: parsed_flags.warning_error_specs,
        source_map,
        source_map_sources_content,
        source_map_root,
        jsx_version,
        jsx_module: parsed_flags.jsx_module.clone(),
        experimental_let_unwrap,
        jsx_preserve: parsed_flags.jsx_preserve,
        debug: parsed_flags.debug,
        check_div_by_zero: parsed_flags.check_div_by_zero,
        cross_module_inline: parsed_flags.cross_module_inline,
        no_assert_false: parsed_flags.no_assert_false,
        noassert: parsed_flags.noassert,
        transparent_modules: parsed_flags.transparent_modules,
        no_builtin_ppx: parsed_flags.no_builtin_ppx,
        nopervasives: parsed_flags.nopervasives,
        no_version_header: parsed_flags.no_version_header,
        package_name: Some(package.config.name.clone()),
        package_root: Some(package.path.clone()),
        make_runtime: parsed_flags.make_runtime,
        gentype_config,
        gentype_resolver,
        keep_locs: parsed_flags.keep_locs,
        visible_package_roots: Some(visible_package_roots),
        ..Default::default()
    })
}

fn package_spec_to_module_format(spec: &config::PackageSpec) -> rescript_compiler::js_ir::ModuleFormat {
    match &spec.module {
        config::PackageModule::CommonJs => rescript_compiler::js_ir::ModuleFormat::CommonJs,
        config::PackageModule::EsModule => rescript_compiler::js_ir::ModuleFormat::EsModule,
    }
}

fn js_output_path_for_spec(
    package: &packages::Package,
    source_file_path: &Path,
    root_config: &config::Config,
    spec: &config::PackageSpec,
) -> PathBuf {
    let suffix = root_config.get_suffix(spec);
    if spec.in_source {
        let source_abs = helpers::ocaml_absname(&Path::new(&package.path).join(source_file_path));
        helpers::get_source_file_from_rescript_file(&source_abs, &suffix)
    } else {
        let js_relative = helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
        Path::new(&package.path)
            .join("lib")
            .join(spec.get_out_of_source_dir())
            .join(js_relative)
    }
}

/// The `-bs-package-output` specs every package of the build compiles with:
/// the root configuration's, in order.
fn js_package_specs(root_config: &config::Config) -> Vec<rescript_compiler::js_ir::JsPackageSpec> {
    root_config
        .get_package_specs()
        .iter()
        .map(|spec| rescript_compiler::js_ir::JsPackageSpec {
            module_format: package_spec_to_module_format(spec),
            in_source: spec.in_source,
            out_of_source_dir: spec.get_out_of_source_dir(),
            suffix: root_config.get_suffix(spec),
        })
        .collect()
}

pub(crate) fn js_output_targets_for_source(
    package: &packages::Package,
    source_file_path: &Path,
    root_config: &config::Config,
) -> Vec<rescript_compiler::driver::JsOutputTarget> {
    root_config
        .get_package_specs()
        .iter()
        .map(|spec| rescript_compiler::driver::JsOutputTarget {
            path: js_output_path_for_spec(package, source_file_path, root_config, spec),
            module_format: package_spec_to_module_format(spec),
        })
        .collect()
}

fn js_output_suffix_for_registry(root_config: &config::Config) -> Option<String> {
    root_config
        .get_package_specs()
        .first()
        .map(|spec| root_config.get_suffix(spec))
}

/// The package info a module's `.cmj` records (`-bs-package-output`): per
/// root package spec, the module system, the directory its JavaScript goes to
/// relative to the package root, and the suffix.
fn package_outputs(
    package: &packages::Package,
    root_config: &config::Config,
    source_abs: &Path,
) -> Vec<rescript_compiler::cmi::persistent_env::CmjPackageInfo> {
    use rescript_compiler::cmi::persistent_env::{CmjPackageInfo, CmjPackageModuleSystem};
    let package_root = Path::new(&package.path);
    let Ok(source_rel) = source_abs.strip_prefix(package_root) else {
        return Vec::new();
    };
    root_config
        .get_package_specs()
        .iter()
        .map(|spec| {
            let js_path = js_output_path_for_spec(package, source_rel, root_config, spec);
            let dir = js_path
                .parent()
                .and_then(|dir| dir.strip_prefix(package_root).ok())
                .unwrap_or(Path::new(""));
            CmjPackageInfo {
                module_system: match spec.module {
                    config::PackageModule::CommonJs => CmjPackageModuleSystem::CommonJs,
                    config::PackageModule::EsModule => CmjPackageModuleSystem::EsModule,
                },
                path: dir.to_string_lossy().replace('\\', "/"),
                suffix: root_config.get_suffix(spec),
            }
        })
        .collect()
}

/// Compute the same package fields for a decoded snapshot as for a compiled
/// module. O(package spec count + path bytes), once per decoded module.
pub(crate) fn configure_snapshot_module(
    info: &mut InMemoryModuleInfo, package: &packages::Package, root_config: &config::Config,
) {
    info.package_outputs = Arc::new(package_outputs(package, root_config, &info.source_path));
    info.package_name = Some(package.name.clone().into());
    info.package_root = Some(Arc::new(package.path.clone()));
    info.js_output_suffix = js_output_suffix_for_registry(root_config).map(Into::into);
}

#[allow(clippy::too_many_arguments)]
fn in_memory_module_info_for_package(
    package: &packages::Package,
    root_config: &config::Config,
    source_path: PathBuf,
    is_pure: bool,
    cmj_export_constants: AHashMap<String, CmjExportConstant>,
    cmj_export_arities: AHashMap<String, CmjExportArity>,
    cmj_export_lambdas: rescript_compiler::lambda::CmjExportLambdas,
    is_runtime: bool,
) -> InMemoryModuleInfo {
    let package_outputs = package_outputs(package, root_config, &source_path);
    InMemoryModuleInfo::new(source_path, is_pure, cmj_export_constants, is_runtime)
        .with_package_outputs(package_outputs)
        .with_cmj_export_arities(cmj_export_arities)
        .with_cmj_export_lambdas(cmj_export_lambdas)
        .with_package(
            package.name.clone(),
            package.path.clone(),
            js_output_suffix_for_registry(root_config),
        )
}

#[allow(clippy::too_many_arguments)]
fn js_metadata_registry_updates_for_package(
    module_name: &str,
    package: &packages::Package,
    root_config: &config::Config,
    source_abs: PathBuf,
    is_pure: bool,
    cmj_export_constants: AHashMap<String, CmjExportConstant>,
    cmj_export_arities: AHashMap<String, CmjExportArity>,
    cmj_export_lambdas: rescript_compiler::lambda::CmjExportLambdas,
    is_runtime: bool,
    has_interface: bool,
    interface_registry_update: Option<PendingRegistryUpdate>,
    pers_struct: Option<Arc<PortablePersStruct>>,
) -> Vec<PendingRegistryUpdate> {
    let module_info = in_memory_module_info_for_package(
        package,
        root_config,
        source_abs,
        is_pure,
        cmj_export_constants,
        cmj_export_arities,
        cmj_export_lambdas,
        is_runtime,
    );

    if has_interface {
        if let Some(mut update) = interface_registry_update {
            update.module_info = module_info;
            vec![update]
        } else {
            vec![PendingRegistryUpdate {
                module_name: module_name.to_string(),
                pers_struct: None,
                module_info,
            }]
        }
    } else if let Some(ps) = pers_struct {
        vec![PendingRegistryUpdate {
            module_name: module_name.to_string(),
            pers_struct: Some(ps),
            module_info,
        }]
    } else {
        Vec::new()
    }
}

fn send_js_metadata_ready(
    metadata_tx: &mpsc::Sender<WorkerMsg>,
    module_name: String,
    registry_updates: Vec<PendingRegistryUpdate>,
) -> Vec<PendingRegistryUpdate> {
    for update in &registry_updates {
        if let Some(pers) = &update.pers_struct {
            pers.summary();
        }
    }
    match metadata_tx.send(WorkerMsg::JsMetadataReady(JsMetadataReadyMsg {
        module_name,
        registry_updates,
    })) {
        Ok(()) => Vec::new(),
        Err(send_error) => match send_error.0 {
            WorkerMsg::JsMetadataReady(msg) => msg.registry_updates,
            _ => unreachable!("metadata send returned unexpected worker message"),
        },
    }
}

/// Write JS output to the correct location(s) based on package specs.
///
/// In-process builds recompile every module, so leave files whose content is
/// unchanged untouched: bundlers and watchers key off modification times.
fn write_file_creating_parent_on_missing(path: &Path, contents: impl AsRef<[u8]>) -> Result<()> {
    if std::fs::read(path).is_ok_and(|existing| existing == contents.as_ref()) {
        return Ok(());
    }
    match std::fs::write(path, contents.as_ref()) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(path, contents.as_ref())?;
            Ok(())
        }
        Err(err) => Err(err.into()),
    }
}

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
            let source_abs = helpers::ocaml_absname(&Path::new(&package.path).join(source_file_path));
            helpers::get_source_file_from_rescript_file(&source_abs, &suffix)
        } else {
            // Out-of-source: JS goes in lib/js/ or lib/es6/ preserving relative path
            let out_dir = spec.get_out_of_source_dir();
            let js_relative = helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
            Path::new(&package.path)
                .join("lib")
                .join(out_dir)
                .join(js_relative)
        };

        write_file_creating_parent_on_missing(&js_path, js_output)?;
    }
    Ok(())
}

/// Computes the item digests of compiled modules on a thread of its own, as
/// they complete, for recording the build (see `incremental::UnitDigests`):
/// otherwise recording a large build decodes and hashes every signature at
/// the end, when nothing else runs.
struct DigestPrep {
    tx: mpsc::Sender<String>,
    handle: std::thread::JoinHandle<Vec<PreparedRecord>>,
}

/// What [`DigestPrep`] computed of a completed module.
struct PreparedRecord {
    module_name: String,
    item_digests: Option<Arc<super::state_db::ItemDigests>>,
    interface: Option<super::state_db::StoredInterface>,
}

impl DigestPrep {
    /// `registry` shares the build registry's maps, so it sees each module
    /// as registered when [`DigestPrep::prepare`] is called.
    fn spawn(registry: ModuleRegistry) -> Self {
        let (tx, rx) = mpsc::channel::<String>();
        let handle = std::thread::Builder::new()
            .name("digest-prep".to_string())
            .spawn(move || {
                rx.into_iter()
                    .map(|module_name| PreparedRecord {
                        item_digests: registry
                            .item_digests(&module_name)
                            .filter(|items| items.contains_key(rescript_compiler::cmi::item_deps::WHOLE))
                            .map(Arc::new),
                        interface: registry
                            .encode_stored_module_parts(&module_name)
                            .map(|(extras, core)| super::state_db::StoredInterface::new(extras, core)),
                        module_name,
                    })
                    .collect()
            })
            .expect("failed to spawn the digest thread");
        DigestPrep { tx, handle }
    }

    /// Digest `module_name` as registered now.
    fn prepare(&self, module_name: String) {
        // The thread only stops when `finish` drops the sender.
        self.tx.send(module_name).expect("digest thread stopped");
    }

    /// What was prepared, later completions of a module after earlier ones.
    fn finish(self) -> Vec<PreparedRecord> {
        drop(self.tx);
        self.handle
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }
}

/// JS outputs of one module, queued for the writer thread.
struct JsWriteJob {
    module_name: String,
    outputs: Vec<rescript_compiler::driver::JsOutput>,
}

/// Writes compiled JS on one dedicated thread. The kernel serializes file
/// creation in a directory tree, so creating thousands of files from every
/// worker at once spends most of the time contending inside `open`; a single
/// writer does the same work in less total time and keeps the workers on
/// compilation.
struct JsWriter {
    tx: mpsc::Sender<JsWriteJob>,
    handle: std::thread::JoinHandle<Vec<(String, anyhow::Error)>>,
}

impl JsWriter {
    fn spawn() -> Self {
        let (tx, rx) = mpsc::channel::<JsWriteJob>();
        let handle = std::thread::Builder::new()
            .name("js-writer".to_string())
            .spawn(move || {
                let mut failures = Vec::new();
                for job in rx {
                    if let Err(err) = write_js_write_job(&job.outputs) {
                        failures.push((job.module_name, err));
                    }
                }
                failures
            })
            .expect("failed to spawn the JS writer thread");
        JsWriter { tx, handle }
    }

    fn sender(&self) -> mpsc::Sender<JsWriteJob> {
        self.tx.clone()
    }

    /// Wait for every queued write and return the modules whose write failed.
    fn finish(self) -> Vec<(String, anyhow::Error)> {
        drop(self.tx);
        self.handle
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }
}

fn write_js_write_job(js_outputs: &[rescript_compiler::driver::JsOutput]) -> Result<()> {
    for output in js_outputs {
        write_file_creating_parent_on_missing(&output.path, &output.code)?;
        let map_path = PathBuf::from(format!("{}.map", output.path.display()));
        if let Some(source_map) = output.source_map.as_deref() {
            write_file_creating_parent_on_missing(&map_path, source_map)?;
        } else {
            let _ = std::fs::remove_file(map_path);
        }
    }
    Ok(())
}

fn write_compiled_js_outputs(
    js_outputs: &[rescript_compiler::driver::JsOutput],
    fallback_js_output: &str,
    package: &packages::Package,
    source_file_path: &Path,
    root_config: &config::Config,
) -> Result<()> {
    if js_outputs.is_empty() {
        return write_js_output(fallback_js_output, package, source_file_path, root_config);
    }
    write_js_write_job(js_outputs)
}

/// Register namespace module signatures in the PersistentEnv for --in-process mode.
///
/// For each package with a namespace, synthesizes the namespace module's
/// alias signature (e.g., `module Foo = Foo-MyApp`) and registers it in
/// the shared ModuleRegistry so that `-open Namespace` works during compilation.
///
/// This replaces the `compile_mlmap` bsc subprocess call used in file-based modes.
/// Register everything the runtime pre-compilation reads from the registry
/// (namespace signatures and source fallback paths). Both depend only on the
/// discovered packages, so a fresh in-process build can do this before parsing
/// and pre-compile the runtime while source files are parsed.
pub(crate) fn prepare_registry_for_runtime_precompile(build_state: &BuildCommandState) {
    register_namespace_signatures(build_state);
    register_source_fallback_paths(build_state);
}

/// Whether `RESCRIPT_MODULE_TIMINGS` is set; read once per process rather
/// than on every module compile.
fn module_timings_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some())
}

/// Run the runtime pre-compilation `work` on a dedicated large-stack thread
/// in `scope`; join it with [`join_runtime_precompile`].
pub(crate) fn spawn_runtime_precompile<'scope>(
    scope: &'scope std::thread::Scope<'scope, '_>,
    work: impl FnOnce() -> Result<()> + Send + 'scope,
) -> Result<std::thread::ScopedJoinHandle<'scope, Result<()>>> {
    std::thread::Builder::new()
        .name("rewatch-runtime-precompile".to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn_scoped(scope, work)
        .map_err(|err| anyhow!("failed to spawn runtime pre-compilation thread: {err}"))
}

/// Wait for a [`spawn_runtime_precompile`] thread, turning a panic into an error.
pub(crate) fn join_runtime_precompile(handle: std::thread::ScopedJoinHandle<'_, Result<()>>) -> Result<()> {
    handle.join().unwrap_or_else(|panic| {
        Err(anyhow!(
            "runtime pre-compilation panicked: {}",
            panic_message(panic.as_ref(), "unknown")
        ))
    })
}

/// Run a scheduler job on `scope` and send its message on `tx`, also when
/// the job panics. The schedulers count jobs in flight and wait on
/// `rx.recv()` while holding a sender themselves, so a job that unwound
/// without sending would leave the build waiting forever with every thread
/// idle. `on_panic` turns the panic message into the job's failure message.
fn spawn_job<'scope, M: Send + 'scope>(
    scope: &rayon::Scope<'scope>,
    tx: mpsc::Sender<M>,
    job: impl FnOnce() -> M + Send + 'scope,
    on_panic: impl FnOnce(String) -> M + Send + 'scope,
) {
    scope.spawn(move |_| {
        let msg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(job))
            .unwrap_or_else(|panic| on_panic(panic_message(panic.as_ref(), "unknown panic")));
        // The receiver lives for the whole scope.
        let _ = tx.send(msg);
    });
}

/// The failure message of a project module whose worker job panicked.
fn panicked_completion(module_name: String, message: &str) -> WorkerMsg {
    WorkerMsg::Completed(CompletionMsg {
        result: Err(anyhow!("Compilation panicked for {module_name}: {message}")),
        module_name,
        interface_result: None,
        is_clean: false,
        is_compiled: true,
        registry_updates: Vec::new(),
    })
}

/// The message of a caught panic payload, or `unknown` when it carries none.
fn panic_message(panic: &(dyn std::any::Any + Send), unknown: &str) -> String {
    if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = panic.downcast_ref::<&str>() {
        s.to_string()
    } else {
        unknown.to_string()
    }
}

/// The namespace of `package` and its `(short_name, internal_name)` module
/// aliases, as `packages::parse_packages` generates the `.mlmap`.
pub(crate) fn namespace_aliases(package: &packages::Package) -> Option<(String, Vec<(String, String)>)> {
    let namespace_suffix = package.namespace.to_suffix()?;
    let entry = match &package.namespace {
        packages::Namespace::NamespaceWithEntry { namespace: _, entry } => Some(entry.as_str()),
        _ => None,
    };
    let mut module_aliases: Vec<(String, String)> = package
        .source_files
        .as_ref()?
        .keys()
        .map(|path| helpers::file_path_to_module_name(path, &packages::Namespace::NoNamespace))
        // The entry module is not aliased in the namespace.
        .filter(|module_name| entry != Some(module_name.as_str()))
        .filter(|module_name| helpers::is_non_exotic_module_name(module_name))
        .map(|short_name| {
            let internal_name = format!("{}-{}", short_name, namespace_suffix);
            (short_name, internal_name)
        })
        .collect();
    // Source files are a hash map; keep the namespace signature, and so its
    // interface digest, the same from one process to the next.
    module_aliases.sort();
    module_aliases.dedup();
    (!module_aliases.is_empty()).then_some((namespace_suffix, module_aliases))
}

fn register_namespace_signatures(build_state: &BuildCommandState) {
    for (_package_name, package) in build_state.packages.iter() {
        if let Some((namespace_suffix, module_aliases)) = namespace_aliases(package) {
            build_state.register_namespace_in_registry(
                &namespace_suffix,
                &module_aliases,
                package.path.clone(),
                Vec::new(),
            );
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
    // The runtime package ships its sources at its root.
    let runtime_root = &build_state.build_state.compiler_info.runtime_path;
    if let Ok(entries) = std::fs::read_dir(runtime_root) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(ext) = path.extension().and_then(|e| e.to_str())
                && (ext == "res" || ext == "resi")
                && let Some(stem) = path.file_stem().and_then(|s| s.to_str())
            {
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

    build_state
        .module_registry
        .lock()
        .unwrap()
        .set_source_fallback_paths(fallback_paths);
}

#[derive(Debug)]
struct RuntimeInterfaceSource {
    path: PathBuf,
    arena: ParseArena,
    signature: Signature,
}

#[derive(Debug)]
pub(crate) struct RuntimeModuleSource {
    module_name: String,
    res_path: PathBuf,
    res_arena: ParseArena,
    structure: Structure,
    resi: Option<RuntimeInterfaceSource>,
    deps: AHashSet<String>,
}

#[derive(Debug)]
struct RuntimeWorkUnit {
    priority: i64,
    idx: usize,
}

impl PartialEq for RuntimeWorkUnit {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.idx == other.idx
    }
}
impl Eq for RuntimeWorkUnit {}
impl PartialOrd for RuntimeWorkUnit {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for RuntimeWorkUnit {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority
            .cmp(&other.priority)
            .then_with(|| other.idx.cmp(&self.idx))
    }
}

struct RuntimeCompletionMsg {
    idx: usize,
    result: Result<()>,
}

/// Pre-compile all @rescript/runtime modules from their `.res/.resi` sources
/// into the ModuleRegistry before the main compile loop.
///
/// This intentionally does not read `.cmi` or `.cmj`: the runtime package is
/// bootstrapped with the same in-process compiler as user sources, and the
/// resulting portable signatures plus JS metadata become the authoritative
/// registry entries for later project compilation.
///
/// Runs on a dedicated thread with a large stack to handle any remaining
/// source-fallback chains during the pre-compilation itself.
/// A module registry holding the runtime package at `runtime_root`, compiled
/// in memory: what an in-process compile of a single file resolves against.
pub fn runtime_registry(runtime_root: &Path) -> Result<ModuleRegistry> {
    let registry = Mutex::new(ModuleRegistry::new());
    pre_compile_runtime_modules(&registry, runtime_root, None)?;
    Ok(registry.into_inner().unwrap())
}

/// Where a build keeps the runtime's compiled interfaces between processes:
/// the root package's database (see `state_db::read_runtime_interfaces`),
/// and the identity of the compiler that compiled them.
pub(crate) struct RuntimeStore {
    pub db: PathBuf,
    pub compiler_hash: String,
    /// Whether the build may add to the store. A check-only build writes no
    /// files: it reads what a build stored and stores nothing itself.
    pub writable: bool,
}

impl RuntimeStore {
    pub(crate) fn of_build(build_state: &BuildCommandState) -> Option<Self> {
        let root = build_state
            .packages
            .values()
            .find(|package| package.is_root)?;
        Some(Self {
            db: super::state_db::path(root),
            compiler_hash: build_state.compiler_info.bsc_hash.to_hex().to_string(),
            writable: !build_state.check_only,
        })
    }

    /// The key the runtime's interfaces are stored under: a digest of the
    /// compiler, the runtime's configuration and the path, size and
    /// modification time of every runtime source.
    fn key(&self, runtime_root: &Path, runtime_paths: &[(String, PathBuf)]) -> String {
        let mut hasher = blake3::Hasher::new();
        hasher.update(self.compiler_hash.as_bytes());
        hasher.update(runtime_root.as_os_str().as_encoded_bytes());
        for config in ["rescript.json", "bsconfig.json"] {
            if let Ok(contents) = std::fs::read(runtime_root.join(config)) {
                hasher.update(config.as_bytes());
                hasher.update(&contents);
            }
        }
        for (module_name, path) in runtime_paths {
            hasher.update(module_name.as_bytes());
            for source in [path.clone(), path.with_extension("resi")] {
                let Ok(metadata) = std::fs::metadata(&source) else {
                    continue;
                };
                let modified = metadata
                    .modified()
                    .map(super::state_db::nanos_from_time)
                    .unwrap_or(0);
                hasher.update(source.as_os_str().as_encoded_bytes());
                hasher.update(&metadata.len().to_le_bytes());
                hasher.update(&modified.to_le_bytes());
            }
        }
        hasher.finalize().to_hex().to_string()
    }
}

/// Register the runtime interfaces `store` holds for these sources, without
/// decoding their signatures (see `ModuleRegistry::register_stored_lazily`).
/// Returns whether all of them were registered.
fn load_runtime_interfaces(
    registry: &Mutex<ModuleRegistry>,
    store: &RuntimeStore,
    key: &str,
    runtime_paths: &[(String, PathBuf)],
) -> bool {
    let Some(stored) = super::state_db::read_runtime_interfaces(&store.db, key) else {
        return false;
    };
    let mut registry = registry.lock().unwrap();
    let mut registered = 0;
    for (module_name, data) in &stored {
        if registry.register_stored_lazily(module_name, data).is_some() {
            registered += 1;
        }
    }
    registered == stored.len() && registered == runtime_paths.len()
}

/// Store the runtime interfaces just compiled into `registry` (see
/// [`load_runtime_interfaces`]).
fn store_runtime_interfaces(
    registry: &Mutex<ModuleRegistry>,
    store: &RuntimeStore,
    key: &str,
    runtime_modules: &[RuntimeModuleSource],
) {
    if store.writable
        && let Some(interfaces) = encode_runtime_interfaces(registry, runtime_modules)
    {
        super::state_db::write_runtime_interfaces(&store.db, key, &interfaces);
    }
}

/// The runtime modules just compiled into `registry`, encoded as stored
/// modules (see `ModuleRegistry::register_stored_lazily`), by module; `None`
/// when one of them is missing from the registry.
pub(crate) fn encode_runtime_interfaces(
    registry: &Mutex<ModuleRegistry>,
    runtime_modules: &[RuntimeModuleSource],
) -> Option<Vec<(String, Vec<u8>)>> {
    let registry = registry.lock().unwrap();
    runtime_modules
        .iter()
        .map(|module| {
            let data = registry.encode_stored_module(&module.module_name)?;
            Some((module.module_name.clone(), data))
        })
        .collect()
}

pub(crate) fn pre_compile_runtime_modules(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    store: Option<&RuntimeStore>,
) -> Result<()> {
    pre_compile_runtime_modules_with_mode(registry, runtime_root, store, false, false, false)
}

pub(crate) fn pre_compile_runtime_modules_with_mode(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    store: Option<&RuntimeStore>,
    check_only: bool,
    dump: bool,
    snapshot_revoked: bool,
) -> Result<()> {
    let _span = info_span!("build.runtime_precompile").entered();
    let runtime_timing_enabled =
        std::env::var_os("RESCRIPT_RUNTIME_TIMINGS").is_some() || module_timings_enabled();
    let runtime_timing_start = runtime_timing_enabled.then(Instant::now);
    let runtime_timing_before = runtime_timing_enabled.then(rescript_compiler::timing::snapshot);
    let runtime_config = super::snapshot::runtime_config(runtime_root)
        .with_context(|| format!("failed to read runtime config from {}", runtime_root.display()))?;
    // The runtime package ships its sources at its root; its compiled
    // modules would be in its artifact directory, the runtime's `-I`.
    let runtime_path = packages::get_build_path(runtime_root);
    let runtime_paths = runtime_source_paths(runtime_root)?;
    tracing::Span::current().record("runtime_modules", runtime_paths.len());

    if runtime_paths.is_empty() {
        return Ok(());
    }

    let already_registered = {
        let registry = registry.lock().unwrap();
        registry.has_runtime_snapshot() || runtime_paths.iter().all(|(module_name, _)| {
            registry.is_pending_stored(module_name)
                || (registry.module_info_is_runtime(module_name) && registry.has_cached_module(module_name))
        })
    };
    if already_registered {
        return Ok(());
    }

    // The interfaces the last build compiled stand in for compiling the
    // runtime again while its sources and the compiler are the same.
    // The runtime compiled into this executable, when these are its sources.
    if !snapshot_revoked && super::snapshot::register(registry, runtime_root, &runtime_paths, store, dump)? {
        debug!("Registered {} embedded runtime interfaces", runtime_paths.len());
        return Ok(());
    }

    let store_key = store.map(|store| (store, store.key(runtime_root, &runtime_paths)));
    if let Some((store, key)) = &store_key
        && load_runtime_interfaces(registry, store, key, &runtime_paths)
    {
        debug!("Loaded {} stored runtime interfaces", runtime_paths.len());
        return Ok(());
    }

    let runtime_modules = compile_runtime_sources_with_mode(
        registry,
        runtime_root,
        &runtime_path,
        &runtime_config,
        runtime_paths,
        check_only,
    )?;
    if let Some((store, key)) = &store_key {
        store_runtime_interfaces(registry, store, key, &runtime_modules);
    }

    if let (Some(start), Some(before)) = (runtime_timing_start, runtime_timing_before) {
        let after = rescript_compiler::timing::snapshot();
        let wall = start.elapsed();
        let parse = duration_delta(after.parse, before.parse);
        let env_setup = duration_delta(after.env_setup, before.env_setup);
        let typecheck = duration_delta(after.typecheck, before.typecheck);
        let signature_publish = duration_delta(after.signature_publish, before.signature_publish);
        let lambda = duration_delta(after.lambda, before.lambda);
        let lambda_optimization = duration_delta(after.lambda_optimization, before.lambda_optimization);
        let gentype = duration_delta(after.gentype, before.gentype);
        let codegen = duration_delta(after.codegen, before.codegen);
        let recorded = parse
            .saturating_add(env_setup)
            .saturating_add(typecheck)
            .saturating_add(signature_publish)
            .saturating_add(lambda)
            .saturating_add(lambda_optimization)
            .saturating_add(gentype)
            .saturating_add(codegen);
        let overhead = wall.saturating_sub(recorded);
        eprintln!(
            "[runtime-timing] modules={} wall_ms={:.3} parse_ms={:.3} env_setup_ms={:.3} typecheck_ms={:.3} signature_publish_ms={:.3} lambda_ms={:.3} lambda_optimization_ms={:.3} gentype_ms={:.3} codegen_ms={:.3} overhead_ms={:.3}",
            runtime_modules.len(),
            duration_ms(wall),
            duration_ms(parse),
            duration_ms(env_setup),
            duration_ms(typecheck),
            duration_ms(signature_publish),
            duration_ms(lambda),
            duration_ms(lambda_optimization),
            duration_ms(gentype),
            duration_ms(codegen),
            duration_ms(overhead)
        );
    }

    debug!(
        "Compiled {} runtime modules from source into registry",
        runtime_modules.len()
    );
    Ok(())
}

/// Compile the runtime sources `runtime_paths` (module name, `.res` path),
/// which are in `runtime_path`, into `registry`. Returns the compiled modules
/// and the alias rewrites each published.
pub(crate) fn compile_runtime_sources(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_paths: Vec<(String, PathBuf)>,
) -> Result<Vec<RuntimeModuleSource>> {
    compile_runtime_sources_with_mode(
        registry,
        runtime_root,
        runtime_path,
        runtime_config,
        runtime_paths,
        false,
    )
}

pub(crate) fn compile_runtime_sources_with_mode(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_paths: Vec<(String, PathBuf)>,
    check_only: bool,
) -> Result<Vec<RuntimeModuleSource>> {
    let runtime_compile_threads = super::pools::compile_threads().max(2);
    // Runtime module compilation runs inside Rayon workers, so the outer
    // precompile thread stack is not enough for very large runtime IR cleanup.
    let runtime_compile_pool = rayon::ThreadPoolBuilder::new()
        .num_threads(runtime_compile_threads)
        .thread_name(|idx| format!("rewatch-runtime-in-process-{idx}"))
        .stack_size(256 * 1024 * 1024)
        .build()
        .context("failed to create runtime in-process compiler pool")?;
    let let_unwrap = runtime_let_unwrap(runtime_config);
    let mut runtime_modules =
        runtime_compile_pool.install(|| collect_runtime_sources(runtime_paths, let_unwrap))?;
    populate_runtime_deps(&mut runtime_modules);

    seed_runtime_registry(registry, &runtime_modules);
    runtime_compile_pool.install(|| {
        compile_runtime_modules_parallel(
            registry,
            runtime_root,
            runtime_path,
            runtime_config,
            &runtime_modules,
            check_only,
        )
    })?;
    Ok(runtime_modules)
}

fn seed_runtime_registry(registry: &Mutex<ModuleRegistry>, runtime_modules: &[RuntimeModuleSource]) {
    let mut registry = registry.lock().unwrap();
    for module in runtime_modules {
        let fallback_path = module
            .resi
            .as_ref()
            .map(|interface| &interface.path)
            .unwrap_or(&module.res_path)
            .clone();
        registry.insert_source_fallback_path(module.module_name.clone(), fallback_path);

        // Seed runtime metadata for every runtime module up front. This lets
        // JS import resolution classify runtime deps without disk probes even
        // before each module's real signature and cmj metadata are compiled.
        registry.insert_module_info(
            module.module_name.clone(),
            InMemoryModuleInfo::new(module.res_path.clone(), true, AHashMap::new(), true),
        );
    }
}

fn compile_runtime_modules_parallel(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_modules: &[RuntimeModuleSource],
    check_only: bool,
) -> Result<()> {
    let (mut pending_deps, dependents) = runtime_dependency_graph(runtime_modules);
    let priorities = runtime_critical_path_priorities(runtime_modules, &dependents);
    let mut ready_heap: BinaryHeap<RuntimeWorkUnit> = pending_deps
        .iter()
        .enumerate()
        .filter_map(|(idx, count)| {
            (*count == 0).then_some(RuntimeWorkUnit {
                priority: priorities[idx],
                idx,
            })
        })
        .collect();

    let (tx, rx) = mpsc::channel::<RuntimeCompletionMsg>();
    let capacity = rayon::current_num_threads().max(1);
    let worker_registry_template = registry.lock().unwrap().for_worker_snapshot();
    let mut in_flight = 0usize;
    let mut completed = vec![false; runtime_modules.len()];
    let mut completed_count = 0usize;
    let mut first_error: Option<anyhow::Error> = None;

    rayon::in_place_scope(|scope| {
        loop {
            while in_flight < capacity && first_error.is_none() {
                let Some(work) = ready_heap.pop() else { break };
                let idx = work.idx;
                let module = &runtime_modules[idx];
                let registry_snapshot = worker_registry_template.clone();
                let tx = tx.clone();
                in_flight += 1;
                spawn_job(
                    scope,
                    tx,
                    move || RuntimeCompletionMsg {
                        idx,
                        result: compile_runtime_module_from_source(
                            registry,
                            runtime_root,
                            runtime_path,
                            runtime_config,
                            module,
                            registry_snapshot,
                            check_only,
                        ),
                    },
                    move |message| RuntimeCompletionMsg {
                        idx,
                        result: Err(anyhow!(
                            "Compiling runtime module {} panicked: {message}",
                            module.module_name
                        )),
                    },
                );
            }

            if in_flight == 0 {
                break;
            }

            let Ok(msg) = rx.recv() else { break };
            in_flight -= 1;

            if let Err(err) = msg.result {
                if first_error.is_none() {
                    first_error = Some(err);
                }
                continue;
            }

            completed[msg.idx] = true;
            completed_count += 1;

            for &dependent in &dependents[msg.idx] {
                pending_deps[dependent] -= 1;
                if pending_deps[dependent] == 0 && !completed[dependent] {
                    ready_heap.push(RuntimeWorkUnit {
                        priority: priorities[dependent],
                        idx: dependent,
                    });
                }
            }
        }
    });
    drop(tx);

    if let Some(err) = first_error {
        return Err(err);
    }

    if completed_count != runtime_modules.len() {
        compile_runtime_cycle_remainder_serial(
            registry,
            runtime_root,
            runtime_path,
            runtime_config,
            runtime_modules,
            &completed,
            check_only,
        )?;
    }

    Ok(())
}

fn compile_runtime_cycle_remainder_serial(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_modules: &[RuntimeModuleSource],
    completed: &[bool],
    check_only: bool,
) -> Result<()> {
    debug!("runtime dependency graph has a cycle; compiling remaining modules serially");
    let worker_registry_template = registry.lock().unwrap().for_worker_snapshot();
    for idx in runtime_compile_order(runtime_modules) {
        if completed[idx] {
            continue;
        }
        let registry_snapshot = worker_registry_template.clone();
        compile_runtime_module_from_source(
            registry,
            runtime_root,
            runtime_path,
            runtime_config,
            &runtime_modules[idx],
            registry_snapshot,
            check_only,
        )?;
    }
    Ok(())
}

fn compile_runtime_module_from_source(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    module: &RuntimeModuleSource,
    registry_snapshot: ModuleRegistry,
    check_only: bool,
) -> Result<()> {
    let mut options = runtime_compiler_options(
        runtime_root,
        runtime_path,
        &module.module_name,
        &module.res_path,
        runtime_config,
    );

    options.check_only = check_only;
    let mut local_registry = registry_snapshot;
    let has_runtime_interface = module.resi.is_some();
    let mut interface_pers_struct = None;

    if let Some(interface) = &module.resi {
        let intf_result = rescript_compiler::driver::typecheck_preprocessed_signature_in_process(
            &interface.arena,
            &interface.signature,
            &interface.path.to_string_lossy(),
            &module.module_name,
            &options,
            &local_registry,
        )
        .with_context(|| {
            format!(
                "runtime interface typecheck failed for {}",
                interface.path.display()
            )
        })?;

        if let Some(pers_struct) = intf_result.pers_struct {
            local_registry.register_module_arc(
                &module.module_name,
                pers_struct.clone(),
                InMemoryModuleInfo::new(module.res_path.clone(), true, AHashMap::new(), true),
            );
            interface_pers_struct = Some(pers_struct);
        }
    }

    let compile_result = rescript_compiler::driver::compile_preprocessed_structure_in_process(
        &module.res_arena,
        &module.structure,
        &module.res_path.to_string_lossy(),
        &module.module_name,
        &options,
        &local_registry,
        has_runtime_interface,
    )
    .map_err(|err| {
        anyhow!(
            "runtime implementation compile failed for {}: {err:#}",
            module.res_path.display()
        )
    })?;

    let module_info = InMemoryModuleInfo::new(
        module.res_path.clone(),
        compile_result.is_pure,
        compile_result.cmj_export_constants,
        true,
    )
    .with_cmj_export_arities(compile_result.cmj_export_arities)
    .with_cmj_export_lambdas(compile_result.cmj_export_lambdas);

    let mut shared_registry = registry.lock().unwrap();
    if has_runtime_interface {
        // OCaml compiler/ml/typemod.ml:1742-1758 checks the implementation
        // against the already-saved interface `.cmi`; typemod.ml:1779-1787
        // only saves an inferred `.cmi` in the no-interface branch.
        if let Some(pers_struct) = interface_pers_struct {
            shared_registry.register_module_arc(&module.module_name, pers_struct, module_info);
        } else {
            shared_registry.insert_module_info(module.module_name.clone(), module_info);
        }
    } else if let Some(pers_struct) = compile_result.pers_struct {
        shared_registry.register_module_arc(&module.module_name, pers_struct, module_info);
    }

    Ok(())
}

/// List the runtime `.res` sources as `(module name, path)`, sorted by module
/// name.
pub(crate) fn runtime_source_paths(runtime_root: &Path) -> Result<Vec<(String, PathBuf)>> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(runtime_root)
        .with_context(|| format!("failed to read runtime directory {}", runtime_root.display()))?
    {
        let entry = entry.with_context(|| {
            format!(
                "failed to read runtime directory entry in {}",
                runtime_root.display()
            )
        })?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("res") {
            continue;
        }

        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        let Some(module_name) = module_name_from_stem(stem) else {
            continue;
        };
        paths.push((module_name, path));
    }
    paths.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(paths)
}

/// Read and parse the runtime sources (in parallel on the current Rayon
/// pool), keeping the order of `paths`.
fn collect_runtime_sources(
    paths: Vec<(String, PathBuf)>,
    let_unwrap: bool,
) -> Result<Vec<RuntimeModuleSource>> {
    paths
        .into_par_iter()
        .map(|(module_name, path)| {
            let res_source = read_source_latin1(&path)?;
            let (res_arena, structure, mut deps) = parse_runtime_structure(&path, &res_source, let_unwrap)?;
            let resi_path = path.with_extension("resi");
            let resi = if resi_path.exists() {
                let source = read_source_latin1(&resi_path)?;
                let (arena, signature, intf_deps) = parse_runtime_signature(&resi_path, &source, let_unwrap)?;
                deps.extend(intf_deps);
                Some(RuntimeInterfaceSource {
                    path: resi_path,
                    arena,
                    signature,
                })
            } else {
                None
            };

            Ok(RuntimeModuleSource {
                module_name,
                res_path: path,
                res_arena,
                structure,
                resi,
                deps,
            })
        })
        .collect()
}

fn module_name_from_stem(stem: &str) -> Option<String> {
    let mut chars = stem.chars();
    chars
        .next()
        .map(|ch| format!("{}{}", ch.to_uppercase(), chars.as_str()))
}

pub(crate) fn read_source_latin1(path: &Path) -> Result<String> {
    rescript_compiler::timing::measure(rescript_compiler::timing::Phase::Parse, || {
        let bytes =
            std::fs::read(path).with_context(|| format!("failed to read source file {}", path.display()))?;
        Ok(source_bytes_to_latin1(bytes))
    })
}

fn source_bytes_to_latin1(bytes: Vec<u8>) -> String {
    if bytes.is_ascii() {
        String::from_utf8(bytes).expect("ASCII source bytes should always be valid UTF-8")
    } else {
        bytes.into_iter().map(|b| b as char).collect()
    }
}

fn populate_runtime_deps(runtime_modules: &mut [RuntimeModuleSource]) {
    let runtime_names: AHashSet<String> = runtime_modules
        .iter()
        .map(|module| module.module_name.clone())
        .collect();
    let has_pervasives = runtime_names.contains("Pervasives");

    for module in runtime_modules {
        module
            .deps
            .retain(|dep| runtime_names.contains(dep) && dep != &module.module_name);
        if has_pervasives && module.module_name != "Pervasives" {
            module.deps.insert("Pervasives".to_string());
        }
    }
}

/// `let_unwrap` is the runtime package's LetUnwrap setting
/// ([`runtime_let_unwrap`]); a `@@config` flag can also enable it.
pub(crate) fn parse_runtime_signature(
    path: &Path,
    source: &str,
    let_unwrap: bool,
) -> Result<(ParseArena, Signature, AHashSet<String>)> {
    rescript_compiler::timing::measure(rescript_compiler::timing::Phase::Parse, || {
        let filename = path.to_string_lossy();
        let mut parser = rescript_compiler::parser::Parser::new(filename.as_ref(), source);
        let signature = rescript_compiler::parser::module::parse_signature(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "failed to parse runtime interface {} with {} error(s)",
                path.display(),
                parser.diagnostics().len()
            ));
        }
        let let_unwrap = let_unwrap
            || rescript_compiler::driver::extract_file_config_from_signature(&signature, parser.arena())
                .let_unwrap;
        let signature =
            rescript_compiler::binary_ast::ppx::rewrite_signature(&signature, parser.arena_mut(), let_unwrap)
                .map_err(|err| {
                    anyhow!(
                        "runtime interface PPX rewrite failed for {}: {err}",
                        path.display()
                    )
                })?;
        let deps = rescript_compiler::binary_ast::deps::extract_signature_deps(parser.arena(), &signature)
            .into_iter()
            .collect();
        let mut arena = parser.into_arena();
        rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
        Ok((arena, signature, deps))
    })
}

/// `let_unwrap` is the runtime package's LetUnwrap setting
/// ([`runtime_let_unwrap`]); a `@@config` flag can also enable it.
pub(crate) fn parse_runtime_structure(
    path: &Path,
    source: &str,
    let_unwrap: bool,
) -> Result<(ParseArena, Structure, AHashSet<String>)> {
    rescript_compiler::timing::measure(rescript_compiler::timing::Phase::Parse, || {
        let filename = path.to_string_lossy();
        let mut parser = rescript_compiler::parser::Parser::new(filename.as_ref(), source);
        let structure = rescript_compiler::parser::module::parse_structure(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "failed to parse runtime implementation {} with {} error(s)",
                path.display(),
                parser.diagnostics().len()
            ));
        }
        let let_unwrap = let_unwrap
            || rescript_compiler::driver::extract_file_config_from_structure(&structure, parser.arena())
                .let_unwrap;
        let structure =
            rescript_compiler::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut(), let_unwrap)
                .map_err(|err| {
                    anyhow!(
                        "runtime implementation PPX rewrite failed for {}: {err}",
                        path.display()
                    )
                })?;
        let structure =
            rescript_compiler::binary_ast::writer::apply_no_export_config(parser.arena_mut(), structure);
        let deps = rescript_compiler::binary_ast::deps::extract_structure_deps(parser.arena(), &structure)
            .into_iter()
            .collect();
        let mut arena = parser.into_arena();
        rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
        Ok((arena, structure, deps))
    })
}

fn runtime_dependency_graph(runtime_modules: &[RuntimeModuleSource]) -> (Vec<usize>, Vec<Vec<usize>>) {
    let index_by_name: AHashMap<String, usize> = runtime_modules
        .iter()
        .enumerate()
        .map(|(idx, module)| (module.module_name.clone(), idx))
        .collect();
    let mut remaining_dep_count = vec![0usize; runtime_modules.len()];
    let mut dependents = vec![Vec::<usize>::new(); runtime_modules.len()];

    for (idx, module) in runtime_modules.iter().enumerate() {
        for dep in &module.deps {
            if let Some(&dep_idx) = index_by_name.get(dep) {
                remaining_dep_count[idx] += 1;
                dependents[dep_idx].push(idx);
            }
        }
    }

    (remaining_dep_count, dependents)
}

fn runtime_critical_path_priorities(
    runtime_modules: &[RuntimeModuleSource],
    dependents: &[Vec<usize>],
) -> Vec<i64> {
    let order = runtime_compile_order(runtime_modules);
    let mut priorities = vec![1i64; runtime_modules.len()];

    for idx in order.into_iter().rev() {
        let dependent_priority = dependents[idx]
            .iter()
            .map(|dependent| priorities[*dependent])
            .max()
            .unwrap_or(0);
        priorities[idx] = 1 + dependent_priority;
    }

    priorities
}

fn runtime_compile_order(runtime_modules: &[RuntimeModuleSource]) -> Vec<usize> {
    let index_by_name: AHashMap<String, usize> = runtime_modules
        .iter()
        .enumerate()
        .map(|(idx, module)| (module.module_name.clone(), idx))
        .collect();
    let mut remaining_dep_count = vec![0usize; runtime_modules.len()];
    let mut dependents = vec![Vec::<usize>::new(); runtime_modules.len()];

    for (idx, module) in runtime_modules.iter().enumerate() {
        for dep in &module.deps {
            if let Some(&dep_idx) = index_by_name.get(dep) {
                remaining_dep_count[idx] += 1;
                dependents[dep_idx].push(idx);
            }
        }
    }

    let mut ready: Vec<usize> = remaining_dep_count
        .iter()
        .enumerate()
        .filter_map(|(idx, count)| (*count == 0).then_some(idx))
        .collect();
    ready.sort_by(|a, b| {
        runtime_modules[*b]
            .module_name
            .cmp(&runtime_modules[*a].module_name)
    });

    let mut order = Vec::with_capacity(runtime_modules.len());
    while let Some(idx) = ready.pop() {
        order.push(idx);
        for &dependent in &dependents[idx] {
            remaining_dep_count[dependent] -= 1;
            if remaining_dep_count[dependent] == 0 {
                ready.push(dependent);
                ready.sort_by(|a, b| {
                    runtime_modules[*b]
                        .module_name
                        .cmp(&runtime_modules[*a].module_name)
                });
            }
        }
    }

    if order.len() != runtime_modules.len() {
        let mut remaining: Vec<usize> = (0..runtime_modules.len())
            .filter(|idx| !order.contains(idx))
            .collect();
        remaining.sort_by(|a, b| {
            runtime_modules[*a]
                .module_name
                .cmp(&runtime_modules[*b].module_name)
        });
        debug!(
            "runtime source dependency cycle or unresolved dependency among: {}",
            remaining
                .iter()
                .map(|idx| runtime_modules[*idx].module_name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        order.extend(remaining);
    }

    order
}

/// Whether the runtime package enables LetUnwrap, through its compiler flags
/// or its experimental features.
pub(crate) fn runtime_let_unwrap(runtime_config: &config::Config) -> bool {
    let bsc_flags = config::flatten_flags(&runtime_config.compiler_flags);
    parse_in_process_compiler_flags(&bsc_flags).experimental_let_unwrap
        || runtime_config.has_experimental_feature(config::ExperimentalFeature::LetUnwrap)
}

pub(crate) fn runtime_compiler_options(
    runtime_root: &Path,
    runtime_path: &Path,
    module_name: &str,
    source_path: &Path,
    runtime_config: &config::Config,
) -> rescript_compiler::driver::CompilerOptions {
    let bsc_flags = config::flatten_flags(&runtime_config.compiler_flags);
    let mut parsed_flags = parse_in_process_compiler_flags(&bsc_flags);
    if parsed_flags.open_modules.is_empty() {
        parsed_flags.open_modules.push("Pervasives".to_string());
    }

    let js_output_targets: Vec<rescript_compiler::driver::JsOutputTarget> = runtime_config
        .get_package_specs()
        .iter()
        .map(|spec| rescript_compiler::driver::JsOutputTarget {
            path: runtime_root
                .join("lib")
                .join(spec.get_out_of_source_dir())
                .join(format!("{}{}", module_name, runtime_config.get_suffix(spec))),
            module_format: package_spec_to_module_format(spec),
        })
        .collect();
    let output_module_format = js_output_targets.first().map(|target| target.module_format);
    let output_path = js_output_targets.first().map(|target| target.path.clone());

    rescript_compiler::driver::CompilerOptions {
        backend: rescript_compiler::bir::shadow::BackendMode::from_env(),
        include_paths: vec![runtime_path.to_path_buf()],
        runtime_path: Some(runtime_root.to_path_buf()),
        open_modules: parsed_flags.open_modules,
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path,
        output_module_format,
        js_output_targets,
        jsx_version: parsed_flags.jsx_version,
        jsx_module: parsed_flags.jsx_module.clone(),
        experimental_let_unwrap: runtime_let_unwrap(runtime_config),
        jsx_preserve: parsed_flags.jsx_preserve,
        debug: parsed_flags.debug,
        no_version_header: parsed_flags.no_version_header,
        check_div_by_zero: parsed_flags.check_div_by_zero,
        cross_module_inline: parsed_flags.cross_module_inline,
        no_assert_false: parsed_flags.no_assert_false,
        noassert: parsed_flags.noassert,
        transparent_modules: parsed_flags.transparent_modules,
        no_builtin_ppx: parsed_flags.no_builtin_ppx,
        nopervasives: parsed_flags.nopervasives,
        module_name: Some(module_name.to_string()),
        package_name: Some(runtime_config.name.clone()),
        package_root: Some(runtime_root.to_path_buf()),
        make_runtime: parsed_flags.make_runtime,
        keep_locs: parsed_flags.keep_locs,
        skip_js_render: true,
        ..Default::default()
    }
}

/// Compile a single module fully in-process using the Rust compiler.
///
/// This replaces the bsc subprocess path for `--in-process` mode:
/// - Consumes the preprocessed AST already stored by the parse phase
/// - If .resi exists, typechecks the stored interface AST first and registers it
/// - Compiles the stored .res implementation AST
/// - Writes only JS output (no .cmi, .cmj, .cmt, .cmti)
/// - Returns the finalized PersStruct and signature for the caller to
///   update the shared ModuleRegistry.
///
/// Missing stored ASTs are an in-process build invariant violation: the parse
/// phase must have populated them before any module reaches compilation.
///
/// Takes a `&ModuleRegistry` (read-only snapshot from the current wave)
/// instead of a shared mutable `PersistentEnv`. Each call creates its own
/// fresh `PersistentEnv` internally, enabling parallel compilation.
///
/// Returns the user-visible warning state plus registry updates to publish
/// after the worker returns, before dependents are scheduled. Actual compiler
/// failures are returned as errors so the DAG scheduler stops dependents, like
/// the bsc subprocess path does.
fn compile_with_location_retry<T>(
    ast: &StoredAst,
    build: &BuildCommandState,
    options: &rescript_compiler::driver::CompilerOptions,
    mut compile: impl FnMut(&StoredAst, &rescript_compiler::driver::CompilerOptions,
        Option<rescript_compiler::driver::DerivedFallback<'_>>) -> Result<T>,
) -> Result<T> {
    use rescript_compiler::driver::{DerivedPath, LocationRetry};
    // Set up for each tree compiled, `tree` being the parse and `source`
    // what it was parsed from. A check compiles the general form of a unit
    // that has plans as well. A unit with plans gets its general syntax,
    // which the compiler's attempt loop continues on when the checker cannot
    // use a plan; nothing of the abandoned attempt is published.
    let per_tree = |tree: &StoredAst,
                    source: &Arc<super::build_types::ParseSource>,
                    options: &mut rescript_compiler::driver::CompilerOptions| {
        if tree.arena().plans().item_count() == 0 {
            return;
        }
        if options.derived_path == DerivedPath::Check {
            let (source, locations) = (source.clone(), tree.arena().stores_locations());
            options.derived_reference =
                Some(Arc::new(move || super::parse::general_form(&source, locations)));
            options.derived_differences = Some(build.derived_differences.clone());
        }
    };
    let fallback = || derived_fallback(ast, ast.arena().stores_locations());
    let fallback = matches!(ast, StoredAst::Structure(_)).then_some(
        &fallback as rescript_compiler::driver::DerivedFallback<'_>);
    let result = match ast.retry_source() {
        Some(source) if !ast.arena().stores_locations()
            || (options.derived_path == DerivedPath::Check && ast.arena().plans().item_count() > 0) => {
            let mut options = options.clone();
            // A location-free compile places its warnings in a located
            // parse of the same source; it returns
            // `LocationRetry::Warning` when it cannot.
            if !ast.arena().stores_locations() {
                options.warning_locations = Some(warning_locations(source));
            }
            per_tree(ast, source, &mut options);
            compile(ast, &options, fallback)
        }
        _ => compile(ast, options, fallback),
    };
    let local_retry = !ast.arena().stores_locations()
        && matches!(
            &result,
            Err(error) if matches!(
                error.downcast_ref::<LocationRetry>(),
                Some(LocationRetry::Output | LocationRetry::Warning)
            )
        );
    if local_retry {
        // Warning sites and location-valued constants belong to this module.
        // No first-attempt signature or JavaScript has been published.
        log::debug!(
            "Retrying {} with source locations",
            ast.retry_source()
                .map(|source| source.file_path.display().to_string())
                .unwrap_or_default()
        );
        // The located parse keeps no source of its own: its reference is
        // made from the source it was parsed from.
        let located = super::parse::reparse_with_locations(ast)?;
        let mut options = options.clone();
        if let Some(source) = ast.retry_source() {
            per_tree(&located, source, &mut options);
        }
        let fallback = || derived_fallback(ast, true);
        let fallback = matches!(located, StoredAst::Structure(_)).then_some(
            &fallback as rescript_compiler::driver::DerivedFallback<'_>);
        return compile(&located, &options, fallback);
    }
    if !build.parses_with_locations() && result.is_err() {
        // Type errors can quote declarations from dependency interfaces.
        // Rebuild those with locations as well before reporting the error.
        build
            .diagnostic_retry
            .store(true, std::sync::atomic::Ordering::Relaxed);
        return Err(LocationRetry::Diagnostic.into());
    }
    result
}

/// The located parse of `source`, in which a location-free compile of it
/// places its warnings (`CompilerOptions::warning_locations`).
/// Cost now: one Arc reference-count increment and one closure allocation.
/// Cost when called: a source parse/frontend run with location tables. The
/// owned `WarningLocations` API requires the closure to retain `ParseSource`;
/// it cannot borrow the temporary options assembly's reference to that Arc.
fn warning_locations(
    source: &Arc<super::build_types::ParseSource>,
) -> rescript_compiler::driver::WarningLocations {
    let source = source.clone();
    Arc::new(move || super::parse::reparse_arena_with_locations(&source))
}

/// The general syntax of the implementation `ast`
/// (`DerivedFallback`): its source parsed again with
/// derived code as syntax, with locations when `locations` (the tree being
/// compiled has them). Cost: one frontend run, only after fallback is requested.
fn derived_fallback(ast: &StoredAst, locations: bool) -> Result<rescript_compiler::driver::GeneralSyntax<rescript_compiler::parser::ast::Structure>> {
    let StoredAst::Structure(general) = super::parse::reparse_without_plans(ast, locations)? else {
        anyhow::bail!("a parse without plans changed the kind of the unit")
    };
    let warning_locations = match &general.retry_source {
        Some(source) if !general.arena.stores_locations() => Some(warning_locations(source)),
        _ => None,
    };
    let general =
        Arc::try_unwrap(general).map_err(|_| anyhow::anyhow!("a new parse without plans is shared"))?;
    Ok(rescript_compiler::driver::GeneralSyntax {
        arena: general.arena,
        tree: general.structure,
        warning_locations,
    })
}



fn compile_module_in_process_to_js_boundary(
    package: &packages::Package,
    module: &Module,
    module_name: &str,
    registry: &ModuleRegistry,
    stored_asts: &AHashMap<String, StoredAst>,
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    scheduler_hooks: Option<&InProcessSchedulerHooks>,
    publication: SignaturePublicationMode,
) -> Result<PreJsMsg> {
    build_command_state
        .loaded_units
        .lock()
        .unwrap()
        .remove(module_name);
    build_command_state.unit_reads.lock().unwrap().remove(module_name);
    let _span = info_span!(
        "compiler.in_process_module",
        module = %module_name,
        package = %package.name
    )
    .entered();
    let module_timing_enabled = module_timings_enabled();
    let module_timing_start = module_timing_enabled.then(Instant::now);
    let module_timing_guard = module_timing_enabled.then(rescript_compiler::timing::ThreadTimingGuard::start);
    let _counter_guard = rescript_compiler::perf_counters::ModuleCounterGuard::start(module_name);
    let source_file = match &module.source_type {
        SourceType::SourceFile(sf) => sf,
        _ => {
            return Err(anyhow!(
                "in-process JS boundary requested for non-source module {module_name}"
            ));
        } // MlMap handled elsewhere
    };

    let implementation_path = &source_file.implementation.path;
    let has_interface = source_file.interface.is_some();

    // Build compiler options from package config
    let mut options = build_compiler_options(package, module_name, implementation_path, build_command_state)?;
    // An in-memory build writes no outputs: every module only registers.
    let registry_only = build_command_state.in_memory_only
        || scheduler_hooks.is_some_and(|hooks| hooks.registry_only.contains(module_name));
    if registry_only {
        // A support module's outputs are up to date: GenType only registers
        // its type declarations, which modules importing its types read.
        options.gentype_declarations_only = true;
    }
    let root_config = build_state.get_root_config();

    let source_abs = helpers::ocaml_absname(&Path::new(&package.path).join(implementation_path));
    let is_runtime = package.name == "@rescript/runtime";
    let provisional_is_pure = false;
    let provisional_module_info = in_memory_module_info_for_package(
        package,
        root_config,
        source_abs.clone(),
        provisional_is_pure,
        AHashMap::new(),
        AHashMap::new(),
        Default::default(),
        is_runtime,
    );

    // For .resi + .res, we need the .resi to be in the registry before compiling .res.
    // Build a local registry that includes the .resi result (if any).
    let mut local_registry = registry.clone();
    let mut interface_registry_update: Option<PendingRegistryUpdate> = None;
    let mut gentype_interface = None;
    // The interface's warnings, reported before the implementation's (the
    // subprocess path compiles the interface first).
    let mut interface_warnings = String::new();

    // Register this module's metadata in the local registry
    local_registry.insert_module_info(module_name.to_string(), provisional_module_info.clone());

    // Step 1: If .resi exists, typecheck the interface first
    if let Some(interface) = &source_file.interface {
        let _interface_span = info_span!(
            "compiler.in_process_interface",
            module = %module_name,
            path = %interface.path.display()
        )
        .entered();
        let intf_source_abs = helpers::ocaml_absname(&Path::new(&package.path).join(&interface.path));
        let intf_key = format!("{module_name}:intf");
        let intf_result = match stored_asts.get(&intf_key) {
            Some(ast @ StoredAst::Signature(_)) => {
                compile_with_location_retry(ast, build_command_state, &options, |ast, options, _fallback| {
                    let StoredAst::Signature(stored) = ast else {
                        unreachable!("interface retry changed AST kind")
                    };
                    rescript_compiler::driver::typecheck_preprocessed_signature_in_process(
                        &stored.arena,
                        &stored.signature,
                        &intf_source_abs.to_string_lossy(),
                        module_name,
                        options,
                        &local_registry,
                    )
                })
            }
            Some(_) => {
                return Err(anyhow!(
                    "expected signature AST for {}",
                    intf_source_abs.display()
                ));
            }
            None => {
                return Err(anyhow!(
                    "missing stored signature AST for {}",
                    intf_source_abs.display()
                ));
            }
        }
        .map_err(
            |e| match e.downcast::<rescript_compiler::driver::UserDiagnostic>() {
                // A compiler diagnostic is reported as the text bsc prints.
                Ok(diagnostic) => anyhow!("{}", diagnostic.output()),
                Err(e) => anyhow!("Interface typecheck failed for {}: {}", module_name, e),
            },
        );

        let intf_result = match intf_result {
            Ok(r) => r,
            Err(e) => {
                return Err(e);
            }
        };
        interface_warnings = intf_result.warnings;
        if let Some(dump) = &build_command_state.dump {
            dump.write(&package.name, &interface.path, &intf_result.dumps);
        }
        build_command_state.record_loaded_units(
            module_name,
            intf_result.loaded_units,
            PendingReads {
                resolved: local_registry.resolve_signature_reads(intf_result.unit_reads),
                module_level: Vec::new(),
            },
        );

        // Register the .resi's PersStruct in the local registry so the
        // .res compilation can find it for moregen constraints.
        gentype_interface = intf_result.gentype;
        let intf_fingerprint = intf_result
            .pers_struct
            .as_ref()
            .map(|ps| ps.fingerprint)
            .unwrap_or(0);
        if let Some(ps) = intf_result.pers_struct {
            let module_info = provisional_module_info.clone();
            local_registry.register_module_arc(module_name, ps.clone(), module_info.clone());
            interface_registry_update = Some(PendingRegistryUpdate {
                module_name: module_name.to_string(),
                pers_struct: Some(ps),
                module_info,
            });
        } else {
            interface_registry_update = Some(PendingRegistryUpdate {
                module_name: module_name.to_string(),
                pers_struct: None,
                module_info: provisional_module_info.clone(),
            });
        }

        if let Some(hooks) = scheduler_hooks {
            hooks
                .tx
                .send(WorkerMsg::SignatureReady(SignatureReadyMsg {
                    module_name: module_name.to_string(),
                    fingerprint: intf_fingerprint,
                    is_pure: provisional_is_pure,
                    registry_updates: interface_registry_update.iter().cloned().collect::<Vec<_>>(),
                }))
                .map_err(|err| anyhow!("failed to publish interface signature for {module_name}: {err}"))?;
        } else {
            // Register the interface signature in rewatch's in-memory registry.
            build_command_state.register_in_memory_interface(
                module_name.to_string(),
                intf_fingerprint,
                provisional_is_pure,
            );
        }
    }

    // Step 2: Compile the implementation
    let impl_key = format!("{module_name}:impl");
    options.publish_in_process_signature = !has_interface;
    let publish_implementation_signature = scheduler_hooks.is_some() && !has_interface;
    let signature_hooks = scheduler_hooks.cloned();
    let signature_module_name = module_name.to_string();
    let signature_module_info = provisional_module_info.clone();
    let mut signature_hook =
        move |ready: rescript_compiler::driver::InProcessSignatureReady| -> Result<Option<ModuleRegistry>> {
            let Some(hooks) = signature_hooks.as_ref() else {
                return Ok(None);
            };
            // The driver has left the signature-release guard. A leaf has no
            // waiting dependent and needs only stored bytes; release its decoded
            // graphs now instead of retaining them through the remaining phases.
            if publication == SignaturePublicationMode::OnDemand
                && let Some(pers) = &ready.pers_struct
            {
                pers.prepare_for_storage();
            }
            let fingerprint = ready.pers_struct.as_ref().map(|ps| ps.fingerprint).unwrap_or(0);
            let module_info = signature_module_info.clone();
            let registry_updates = if let Some(pers_struct) = ready.pers_struct {
                vec![PendingRegistryUpdate {
                    module_name: signature_module_name.clone(),
                    pers_struct: Some(pers_struct),
                    module_info,
                }]
            } else {
                vec![PendingRegistryUpdate {
                    module_name: signature_module_name.clone(),
                    pers_struct: None,
                    module_info,
                }]
            };
            hooks
                .tx
                .send(WorkerMsg::SignatureReady(SignatureReadyMsg {
                    module_name: signature_module_name.clone(),
                    fingerprint,
                    is_pure: provisional_is_pure,
                    registry_updates,
                }))
                .map_err(|err| {
                    anyhow!(
                        "failed to publish implementation signature for {}: {err}",
                        signature_module_name
                    )
                })?;
            Ok(None)
        };

    let pre_js = {
        let _impl_span = info_span!(
            "compiler.in_process_implementation",
            module = %module_name,
            path = %source_abs.display()
        )
        .entered();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match stored_asts.get(&impl_key) {
                Some(ast @ StoredAst::Structure(_)) => {
                    compile_with_location_retry(ast, build_command_state, &options, |ast, options, fallback| {
                        let StoredAst::Structure(stored) = ast else {
                            unreachable!("implementation retry changed AST kind")
                        };
                        let signature_hook: Option<
                            &mut rescript_compiler::driver::InProcessSignatureReadyHook<'_>,
                        > = if publish_implementation_signature {
                            Some(&mut signature_hook)
                        } else {
                            None
                        };
                        rescript_compiler::driver::compile_preprocessed_structure_in_process_until_js(
                            &stored.arena,
                            &stored.structure,
                            &source_abs.to_string_lossy(),
                            module_name,
                            options,
                            &local_registry,
                            has_interface,
                            gentype_interface.clone(),
                            signature_hook,
                            publication,
                            fallback,
                        )
                    })
                }
                Some(_) => panic!(
                    "in-process invariant violated: expected structure AST for {}, found another AST",
                    source_abs.display()
                ),
                None => panic!(
                    "in-process invariant violated: missing stored structure AST for {}",
                    source_abs.display()
                ),
            }
        }))
    };

    let pre_js = match pre_js {
        Ok(Ok(mut result)) => {
            // What the backend reads besides the type checker: the modules
            // the generated code may require.
            let mut loaded_units = std::mem::take(&mut result.loaded_units);
            let mut reads = PendingReads {
                resolved: local_registry.resolve_signature_reads(std::mem::take(&mut result.unit_reads)),
                module_level: Vec::new(),
            };
            for module_id in &result.possible_required_modules {
                reads.module_level.push(module_id.id.name_atom());
                loaded_units.push(module_id.id.name().to_string());
            }
            build_command_state.record_loaded_units(module_name, loaded_units, reads);
            result.warnings.insert_str(0, &interface_warnings);
            if let Some(dump) = &build_command_state.dump {
                dump.write(
                    &package.name,
                    implementation_path,
                    &std::mem::take(&mut result.dumps),
                );
            }
            result
        }
        Ok(Err(e)) => {
            let e = in_process_compile_error(module_name, e);
            return Err(if interface_warnings.is_empty() {
                e
            } else {
                anyhow!("{interface_warnings}{e}")
            });
        }
        Err(panic) => {
            let msg = panic_message(panic.as_ref(), "unknown panic");
            return Err(anyhow!("Compilation panicked for {}: {}", module_name, msg));
        }
    };

    if let (Some(start), Some(guard)) = (module_timing_start, module_timing_guard.as_ref()) {
        let timings = guard.snapshot();
        let wall = start.elapsed();
        let parse = timings.parse;
        let env_setup = timings.env_setup;
        let typecheck = timings.typecheck;
        let signature_publish = timings.signature_publish;
        let lambda = timings.lambda;
        let lambda_optimization = timings.lambda_optimization;
        let gentype = timings.gentype;
        let codegen = timings.codegen;
        let recorded = timings.recorded();
        let overhead = wall.saturating_sub(recorded);
        eprintln!(
            "[module-timing] module={} package={} wall_ms={:.3} parse_ms={:.3} env_setup_ms={:.3} typecheck_ms={:.3} signature_publish_ms={:.3} lambda_ms={:.3} lambda_optimization_ms={:.3} gentype_ms={:.3} codegen_ms={:.3} overhead_ms={:.3} end_epoch_ms={:.3}",
            module_name,
            package.name,
            duration_ms(wall),
            duration_ms(parse),
            duration_ms(env_setup),
            duration_ms(typecheck),
            duration_ms(signature_publish),
            duration_ms(lambda),
            duration_ms(lambda_optimization),
            duration_ms(gentype),
            duration_ms(codegen),
            duration_ms(overhead),
            // Wall-clock end, so profiler samples can be attributed to one module.
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0.0, |elapsed| elapsed.as_secs_f64() * 1000.0)
        );
    }

    // OCaml finalizes JS output after the backend has dependency `.cmj`
    // metadata for modules it may import or inspect for side effects. The
    // split in-process scheduler publishes signatures early, so dependent
    // type-checking can start before dependency JS metadata is ready; keep JS
    // finalization waiting on the backend-visible module set, not type-only
    // build dependencies.
    let needed_modules = scheduler_hooks
        .map(|hooks| {
            let mut needed = pre_js
                .possible_required_modules
                .iter()
                .map(|module_id| module_id.id.name())
                .filter(|name| *name != module_name && hooks.compile_universe.contains(*name))
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            needed.sort();
            needed.dedup();
            needed
        })
        .unwrap_or_default();

    Ok(PreJsMsg {
        module_name: module_name.to_string(),
        pre_js,
        needed_modules,
        interface_registry_update,
        source_abs,
        implementation_path: implementation_path.to_path_buf(),
        has_interface,
        is_runtime,
        is_clean: false,
        registry_only,
    })
}

fn finish_in_process_js(
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    pre_js_msg: PreJsMsg,
    parent_span: Span,
    registry_snapshot: ModuleRegistry,
    metadata_tx: &mpsc::Sender<WorkerMsg>,
    write_tx: &mpsc::Sender<JsWriteJob>,
) -> CompletionMsg {
    let _placement = qos::UnitPlacementGuard::enter(qos::UnitClass::Background);
    let module_name = pre_js_msg.module_name.clone();
    let is_clean = pre_js_msg.is_clean;
    let result = finish_in_process_js_inner(
        build_state,
        build_command_state,
        pre_js_msg,
        parent_span,
        registry_snapshot,
        metadata_tx,
        write_tx,
    );
    if !build_command_state.parses_with_locations() && result.is_err() {
        build_command_state
            .diagnostic_retry
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let (result, registry_updates) = match result {
        Ok(outcome) => (Ok(outcome.warning), outcome.registry_updates),
        Err(err) => (Err(err), Vec::new()),
    };
    CompletionMsg {
        module_name,
        result,
        interface_result: None,
        is_clean,
        is_compiled: true,
        registry_updates,
    }
}

fn finish_in_process_js_inner(
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    pre_js_msg: PreJsMsg,
    parent_span: Span,
    registry_snapshot: ModuleRegistry,
    metadata_tx: &mpsc::Sender<WorkerMsg>,
    write_tx: &mpsc::Sender<JsWriteJob>,
) -> Result<InProcessModuleResult> {
    let PreJsMsg {
        module_name,
        mut pre_js,
        needed_modules: _,
        interface_registry_update,
        source_abs,
        implementation_path,
        has_interface,
        is_runtime,
        is_clean: _,
        registry_only,
    } = pre_js_msg;
    let module_timing_enabled = module_timings_enabled();
    let module_timing_start = module_timing_enabled.then(Instant::now);
    let module_timing_guard = module_timing_enabled.then(rescript_compiler::timing::ThreadTimingGuard::start);
    let module = build_state.get_module(&module_name).unwrap();
    let package = build_state
        .get_package(&module.package_name)
        .expect("Package not found");
    // The warnings bsc prints to stderr, filtered like the subprocess path.
    let compiler_warnings = std::mem::take(&mut pre_js.warnings);
    let warning = visible_compiler_warnings(&compiler_warnings, package.is_local_dep);
    if build_command_state.check_only {
        // No code is generated: the module keeps the JS metadata of the last
        // build that generated its code (see `recorded_js_metadata`).
        let recorded = super::incremental::recorded_js_metadata(build_command_state, &module_name);
        let (is_pure, constants, arities, lambdas) = match recorded {
            Some(info) => (
                info.is_pure,
                Arc::unwrap_or_clone(info.cmj_export_constants),
                Arc::unwrap_or_clone(info.cmj_export_arities),
                Arc::unwrap_or_clone(info.cmj_export_lambdas),
            ),
            None => (false, AHashMap::new(), AHashMap::new(), Default::default()),
        };
        let module_info = in_memory_module_info_for_package(
            package,
            build_command_state.get_root_config(),
            source_abs,
            is_pure,
            constants,
            arities,
            lambdas,
            is_runtime,
        );
        // The signature is registered already when it was published before
        // this phase; the metadata alone replaces the provisional one.
        let update = match interface_registry_update.filter(|_| has_interface) {
            Some(mut update) => {
                update.module_info = module_info;
                update
            }
            None => PendingRegistryUpdate {
                module_name: module_name.clone(),
                pers_struct: pre_js.pers_struct.filter(|_| !has_interface),
                module_info,
            },
        };
        return Ok(InProcessModuleResult {
            warning,
            registry_updates: send_js_metadata_ready(metadata_tx, module_name, vec![update]),
        });
    }

    // GenType runs once the JavaScript is written (js_implementation.ml:164-171).
    let mut gentype = pre_js.gentype.take();
    let _span = if tracing::enabled!(tracing::Level::INFO) {
        info_span!(
            parent: &parent_span,
            "build.finish_in_process_js",
            module = %module_name,
            package = %package.name,
        )
        .entered()
    } else {
        Span::none().entered()
    };
    let root_config = build_command_state.get_root_config();
    let mut options =
        build_compiler_options(package, &module_name, &implementation_path, build_command_state)?;
    if registry_only {
        // The backend still runs for the metadata dependents read (purity,
        // exported arities and inlinable bodies); only the output is skipped.
        options.skip_js_render = true;
        options.gentype_declarations_only = true;
    }
    let metadata_interface_registry_update = interface_registry_update;
    let mut metadata_registry_updates: Option<Vec<PendingRegistryUpdate>> = None;
    let mut metadata_hook = |metadata: rescript_compiler::driver::InProcessJsMetadataReady| -> Result<()> {
        let module_info = in_memory_module_info_for_package(
            package,
            root_config,
            source_abs.clone(),
            metadata.is_pure,
            metadata.cmj_export_constants,
            metadata.cmj_export_arities,
            metadata.cmj_export_lambdas,
            is_runtime,
        );
        registry_snapshot.prepare_signature_summary(&module_name);
        let registry_updates = vec![PendingRegistryUpdate {
            module_name: module_name.clone(),
            pers_struct: None,
            module_info,
        }];
        metadata_registry_updates = Some(send_js_metadata_ready(
            metadata_tx,
            module_name.clone(),
            registry_updates,
        ));
        Ok(())
    };
    let compile_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rescript_compiler::driver::finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook(
            pre_js,
            &options,
            &registry_snapshot,
            Some(&mut metadata_hook),
        )
    }));
    let mut compile_result = match compile_result {
        Ok(Ok(result)) => result,
        Ok(Err(e)) => {
            return Err(anyhow!("JS compilation failed for {}: {}", module_name, e));
        }
        Err(panic) => {
            let msg = panic_message(panic.as_ref(), "unknown panic");
            return Err(anyhow!("JS compilation panicked for {}: {}", module_name, msg));
        }
    };
    let js_output_count = compile_result.js_outputs.len();

    let registry_updates = metadata_registry_updates.unwrap_or_else(|| {
        let registry_updates = js_metadata_registry_updates_for_package(
            &module_name,
            package,
            root_config,
            source_abs.clone(),
            compile_result.is_pure,
            compile_result.cmj_export_constants.clone(),
            compile_result.cmj_export_arities.clone(),
            compile_result.cmj_export_lambdas.clone(),
            is_runtime,
            has_interface,
            metadata_interface_registry_update,
            compile_result.pers_struct,
        );
        send_js_metadata_ready(metadata_tx, module_name.clone(), registry_updates)
    });

    if registry_only {
        return Ok(InProcessModuleResult {
            warning,
            registry_updates,
        });
    }

    // A configured JS suffix can share the genType path. That write can
    // invalidate the discovery snapshot, so preserve the ordinary probe.
    if let Some(outcome) = gentype.as_mut()
        && let Ok(Some(output)) = &mut outcome.result
        && let rescript_compiler::gentype::main::Output::NoMatch { output_file } = output
        && !compile_result.js_outputs.is_empty()
        && !compile_result.js_outputs.iter().any(|js| js.path == Path::new(output_file))
        && package.gentype_output_absent(Path::new(output_file))
    {
        *output = rescript_compiler::gentype::main::Output::Absent {
            output_file: std::mem::take(output_file),
        };
    }

    let mut write_duration = Duration::default();
    {
        let _write_span = info_span!(
            "compiler.write_js",
            module = %module_name,
            outputs = compile_result.js_outputs.len()
        )
        .entered();
        let write_start = module_timing_enabled.then(Instant::now);
        // A post-build command reads the file, so it must exist before the
        // command runs. Otherwise hand the outputs to the writer thread.
        if package.config.js_post_build.is_some() || compile_result.js_outputs.is_empty() {
            write_compiled_js_outputs(
                &compile_result.js_outputs,
                &compile_result.js_output,
                package,
                &implementation_path,
                root_config,
            )?;
        } else {
            let outputs = std::mem::take(&mut compile_result.js_outputs);
            let job = JsWriteJob {
                module_name: module_name.clone(),
                outputs,
            };
            if let Err(mpsc::SendError(job)) = write_tx.send(job) {
                write_js_write_job(&job.outputs)?;
            }
        }
        if let Some(write_start) = write_start {
            write_duration = write_start.elapsed();
        }
    }

    // GenType prints its notes (Log_.ml:99-104) to bsc's stdout, which
    // rescript-ocaml shows only for a compile that fails, after its stderr
    // (rewatch-ocaml/compiler_scheduler.ml:229-244): a build shows them only
    // with the report of an exception GenType raised.
    rescript_compiler::driver::apply_gentype_outcome_in_build(
        gentype,
        &compiler_warnings,
        &source_abs.to_string_lossy(),
    )
    .map_err(|err| in_process_compile_error(&module_name, err))?;

    if let Some(js_post_build) = &package.config.js_post_build {
        for spec in root_config.get_package_specs() {
            let suffix = root_config.get_suffix(&spec);
            let js_file = if spec.in_source {
                helpers::get_source_file_from_rescript_file(
                    &Path::new(&package.path).join(&implementation_path),
                    &suffix,
                )
            } else {
                let out_dir = spec.get_out_of_source_dir();
                let js_relative = helpers::get_source_file_from_rescript_file(&implementation_path, &suffix);
                Path::new(&package.path)
                    .join("lib")
                    .join(out_dir)
                    .join(js_relative)
            };
            if js_file.exists() {
                execute_post_build_command(&js_post_build.cmd, &js_file, &package.path)?;
            }
        }
    }

    if let (Some(start), Some(guard)) = (module_timing_start, module_timing_guard.as_ref()) {
        let timings = guard.snapshot();
        let wall = start.elapsed();
        let codegen = timings.codegen;
        let overhead = wall.saturating_sub(codegen.saturating_add(write_duration));
        eprintln!(
            "[module-js-timing] module={} package={} wall_ms={:.3} codegen_ms={:.3} write_ms={:.3} overhead_ms={:.3} outputs={} end_epoch_ms={:.3}",
            module_name,
            package.name,
            duration_ms(wall),
            duration_ms(codegen),
            duration_ms(write_duration),
            duration_ms(overhead),
            js_output_count,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0.0, |elapsed| elapsed.as_secs_f64() * 1000.0)
        );
    }

    Ok(InProcessModuleResult {
        warning,
        registry_updates,
    })
}

fn in_process_compile_error(module_name: &str, err: anyhow::Error) -> anyhow::Error {
    match err.downcast::<rescript_compiler::driver::UserDiagnostic>() {
        Ok(diagnostic) => anyhow!("{}", diagnostic.output()),
        Err(err) => anyhow!("Compilation failed for {}: {}", module_name, err),
    }
}

fn visible_compiler_warnings(stderr: &str, is_local_dep: bool) -> Option<String> {
    if !helpers::has_ascii_alphanumeric(stderr) {
        return None;
    }
    if is_local_dep {
        Some(stderr.to_string())
    } else {
        // Warnings from external deps are suppressed by default — users cannot
        // act on them. Preserve the critical deprecations selected below.
        retain_critical_external_warnings(stderr)
    }
}

/// Filter a bsc stderr capture to the warning blocks the user needs to see
/// even when they originate in an external dependency.
///
/// Currently preserved:
/// - Warning 3 deprecations mentioning the legacy `(. ...)` uncurried syntax.
///   These indicate source that parses today but is scheduled for removal, so
///   consumers need to hear about them even when the code isn't theirs.
pub(super) fn retain_critical_external_warnings(stderr: &str) -> Option<String> {
    const UNCURRIED_DOT_MARKER: &str = "`(. ...)` uncurried syntax";
    if !stderr.contains(UNCURRIED_DOT_MARKER) {
        return None;
    }
    // bsc prints each warning as its own block separated by a blank-line pair
    // (three consecutive newlines). On Windows the same stream uses CRLF, so
    // normalize before splitting to keep the block boundary recognizable —
    // otherwise the whole stderr would be treated as a single block and
    // unrelated warnings would leak through alongside the critical one.
    let normalized = stderr.replace("\r\n", "\n");
    let kept: Vec<&str> = normalized
        .split("\n\n\n")
        .filter(|block| block.contains(UNCURRIED_DOT_MARKER))
        .collect();
    if kept.is_empty() {
        None
    } else {
        Some(kept.join("\n\n\n"))
    }
}

pub fn mark_modules_with_deleted_deps_dirty(build_state: &mut BuildState) {
    build_state.modules.iter_mut().for_each(|(_, module)| {
        if !module.deps.is_disjoint(&build_state.deleted_modules) {
            module.compile_dirty = true;
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::packages::{Namespace, Package};
    use crate::config;
    use crate::project_context::ProjectContext;
    use ahash::AHashMap;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::RwLock;
    use std::time::SystemTime;
    use tempfile::TempDir;

    #[test]
    fn signature_publication_uses_only_dependents_in_this_build() {
        let universe = AHashSet::from_iter(["Reader".to_string()]);
        assert_eq!(
            signature_publication_mode(&AHashSet::new(), &universe),
            SignaturePublicationMode::OnDemand,
        );
        let dependents = AHashSet::from_iter(["OtherBuild".to_string()]);
        assert_eq!(
            signature_publication_mode(&dependents, &universe),
            SignaturePublicationMode::OnDemand,
        );
        let dependents = AHashSet::from_iter(["OtherBuild".to_string(), "Reader".to_string()]);
        assert_eq!(
            signature_publication_mode(&dependents, &universe),
            SignaturePublicationMode::Eager,
        );
    }

    /// The runtime's stored interfaces are keyed by the compiler that
    /// encoded them: another compiler's key misses them.
    #[test]
    fn runtime_interfaces_of_another_compiler_are_not_read() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let db = temp_dir.path().join("rescript.sqlite");
        let store = |hash: &str| RuntimeStore {
            db: db.clone(),
            compiler_hash: hash.to_string(),
            writable: true,
        };
        let runtime_root = temp_dir.path().join("runtime");
        fs::create_dir_all(&runtime_root).expect("runtime directory should be created");
        let paths = vec![("Stdlib".to_string(), runtime_root.join("Stdlib.res"))];
        let old_key = store("old").key(&runtime_root, &paths);
        let new_key = store("new").key(&runtime_root, &paths);
        assert_ne!(old_key, new_key);
        super::super::state_db::write_runtime_interfaces(
            &db,
            &old_key,
            &[("Stdlib".to_string(), vec![1, 2, 3])],
        );
        assert!(super::super::state_db::read_runtime_interfaces(&db, &old_key).is_some());
        assert!(super::super::state_db::read_runtime_interfaces(&db, &new_key).is_none());
    }

    /// A job that panics still reports, so a scheduler that waits for every
    /// job in flight while holding a sender itself does not hang.
    #[test]
    fn spawn_job_reports_a_panic_instead_of_hanging() {
        let (done_tx, done_rx) = mpsc::channel();
        std::thread::spawn(move || {
            let (tx, rx) = mpsc::channel::<Result<u32, String>>();
            let mut results = Vec::new();
            rayon::in_place_scope(|scope| {
                let mut in_flight = 0;
                for i in 0..3u32 {
                    in_flight += 1;
                    spawn_job(
                        scope,
                        tx.clone(),
                        move || {
                            if i == 1 {
                                panic!("job {i} failed");
                            }
                            Ok(i)
                        },
                        Err,
                    );
                }
                while in_flight > 0 {
                    let Ok(msg) = rx.recv() else { break };
                    in_flight -= 1;
                    results.push(msg);
                }
            });
            done_tx.send(results).expect("test receiver is alive");
        });
        let mut results = done_rx
            .recv_timeout(Duration::from_secs(30))
            .expect("the scheduler loop hung on a panicked job");
        results.sort();
        assert_eq!(results, vec![Ok(0), Ok(2), Err("job 1 failed".to_string())]);
    }

    #[test]
    fn panicked_completion_fails_the_module_with_the_message() {
        let WorkerMsg::Completed(msg) = panicked_completion("App".to_string(), "boom") else {
            panic!("expected a completion");
        };
        assert_eq!(msg.module_name, "App");
        assert!(msg.is_compiled && !msg.is_clean);
        let err = msg.result.expect_err("a panicked module fails");
        assert_eq!(err.to_string(), "Compilation panicked for App: boom");
    }

    fn test_project_context(root: &Path) -> ProjectContext {
        let config = config::tests::create_config(config::tests::CreateConfigArgs {
            name: "test-root".to_string(),
            bs_deps: vec![],
            build_dev_deps: vec![],
            allowed_dependents: None,
            path: root.to_path_buf(),
        });

        ProjectContext {
            current_config: config,
            monorepo_context: None,
            node_modules_exist_cache: RwLock::new(AHashMap::new()),
            packages_cache: RwLock::new(AHashMap::new()),
        }
    }

    fn test_package(name: &str, path: PathBuf) -> Package {
        Package {
            prebuilt: false,
            check_only: false,
            name: name.to_string(),
            config: config::tests::create_config(config::tests::CreateConfigArgs {
                name: name.to_string(),
                bs_deps: vec![],
                build_dev_deps: vec![],
                allowed_dependents: None,
                path: path.clone(),
            }),
            source_folders: Default::default(),
            source_files: None,
            namespace: Namespace::NoNamespace,
            modules: None,
            path,
            dirs: None,
            gentype_dirs: None,
            gentype_outputs: None,
            is_local_dep: true,
            is_root: true,
        }
    }

    fn test_module(package_name: &str, implementation_warning: Option<&str>) -> Module {
        Module {
            source_type: SourceType::SourceFile(SourceFile {
                gentype_annotations: [None; 2],
                implementation: Implementation {
                    path: PathBuf::from("src/ModuleA.res"),
                    parse_state: ParseState::Success,
                    compile_state: if implementation_warning.is_some() {
                        CompileState::Warning
                    } else {
                        CompileState::Success
                    },
                    last_modified: SystemTime::UNIX_EPOCH,
                    parse_dirty: false,
                    compile_warnings: implementation_warning.map(str::to_string),
                },
                interface: None,
            }),
            deps: Default::default(),
            dependents: Default::default(),
            package_name: package_name.to_string(),
            compile_dirty: false,
            deps_dirty: false,
            is_type_dev: false,
        }
    }

    fn test_build_state(temp_dir: &TempDir, module_name: &str, module: Module) -> BuildState {
        let package = test_package("test-package", temp_dir.path().to_path_buf());
        fs::create_dir_all(package.get_build_path()).expect("build log directory should be created");

        let mut packages = AHashMap::new();
        packages.insert(package.name.clone(), package);

        let compiler = CompilerInfo {
            bsc_path: temp_dir.path().join("bsc"),
            bsc_hash: blake3::hash(b"test-bsc"),
            runtime_path: temp_dir.path().join("runtime"),
        };

        let mut build_state = BuildState::new(
            test_project_context(temp_dir.path()),
            packages,
            compiler,
            config::SourceMapCommand::Build,
        );
        build_state.insert_module(module_name, module);
        logs::initialize(&build_state.packages);
        build_state
    }

    #[test]
    fn successful_local_subprocess_warnings_remain_visible() {
        let warning = "Warning number 26\nunused variable x\n";
        assert_eq!(
            visible_compiler_warnings(warning, true),
            Some(warning.to_string())
        );
    }

    #[test]
    fn retain_critical_external_warnings_returns_none_without_marker() {
        let input = "\n  Warning number 26\n  foo.res:1:1\n\n  unused variable x.\n";
        assert_eq!(retain_critical_external_warnings(input), None);
    }

    #[test]
    fn retain_critical_external_warnings_keeps_uncurried_dot_block() {
        let input = concat!(
            "\n  Warning number 26\n  foo.res:1:1\n\n  unused variable x.\n",
            "\n\n\n  Warning number 3\n  bar.res:5:10\n\n  ",
            "deprecated: The `(. ...)` uncurried syntax is deprecated.\n",
        );
        let kept = retain_critical_external_warnings(input).expect("uncurried-dot warning should survive");
        assert!(kept.contains("`(. ...)` uncurried syntax"));
        assert!(!kept.contains("unused variable"));
    }

    #[test]
    fn retain_critical_external_warnings_handles_crlf_line_endings() {
        // Windows stderr from bsc uses CRLF. Without normalization the "\n\n\n"
        // splitter would find no boundary and return the entire stream, which
        // would effectively disable suppression for external deps on Windows.
        let input = concat!(
            "\r\n  Warning number 26\r\n  foo.res:1:1\r\n\r\n  unused variable x.\r\n",
            "\r\n\r\n\r\n  Warning number 3\r\n  bar.res:5:10\r\n\r\n  ",
            "deprecated: The `(. ...)` uncurried syntax is deprecated.\r\n",
        );
        let kept = retain_critical_external_warnings(input)
            .expect("uncurried-dot warning should survive on Windows too");
        assert!(kept.contains("`(. ...)` uncurried syntax"));
        assert!(!kept.contains("unused variable"));
    }

    #[test]
    fn replays_stored_warning_for_module_that_did_not_recompile() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let build_state = test_build_state(
            &temp_dir,
            "ModuleA",
            test_module("test-package", Some("warning: carried forward\n")),
        );
        let recompiled_modules = Default::default();

        let compile_warnings =
            collect_stored_warnings_for_modules_not_recompiled(&build_state, &recompiled_modules)
                .into_iter()
                .map(|entry| entry.warning)
                .collect::<String>();

        assert_eq!(compile_warnings, "warning: carried forward\n");
    }

    #[test]
    fn replays_stored_warnings_in_module_name_order() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let mut build_state = test_build_state(
            &temp_dir,
            "Zed",
            test_module("test-package", Some("warning: zed\n")),
        );
        build_state.insert_module("Alpha", test_module("test-package", Some("warning: alpha\n")));
        let mut compile_warnings = String::new();
        let recompiled_modules = Default::default();

        append_compile_warnings(
            &build_state,
            collect_stored_warnings_for_modules_not_recompiled(&build_state, &recompiled_modules),
            &mut compile_warnings,
            true,
        );

        assert_eq!(compile_warnings, "warning: alpha\nwarning: zed\n");
    }

    #[test]
    fn appends_fresh_and_stored_warnings_in_shared_module_name_order() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let build_state = test_build_state(
            &temp_dir,
            "ModuleA",
            test_module("test-package", Some("warning: stored\n")),
        );
        let mut compile_warnings = String::new();

        append_compile_warnings(
            &build_state,
            vec![
                CompileWarning {
                    module_name: "Zed".to_string(),
                    package_name: "test-package".to_string(),
                    warning: "warning: fresh\n".to_string(),
                },
                CompileWarning {
                    module_name: "Alpha".to_string(),
                    package_name: "test-package".to_string(),
                    warning: "warning: stored\n".to_string(),
                },
            ],
            &mut compile_warnings,
            true,
        );

        assert_eq!(compile_warnings, "warning: stored\nwarning: fresh\n");
    }

    #[test]
    fn does_not_replay_stored_warning_for_module_that_recompiled() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let build_state = test_build_state(
            &temp_dir,
            "ModuleA",
            test_module("test-package", Some("warning: already emitted\n")),
        );
        let mut recompiled_modules = ahash::AHashSet::new();
        recompiled_modules.insert("ModuleA".to_string());

        let compile_warnings =
            collect_stored_warnings_for_modules_not_recompiled(&build_state, &recompiled_modules)
                .into_iter()
                .map(|entry| entry.warning)
                .collect::<String>();

        assert!(compile_warnings.is_empty());
    }
}
