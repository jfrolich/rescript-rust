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
use anyhow::{Context, Result, anyhow};
use console::style;
use log::{debug, info, trace, warn};
use rayon::prelude::*;
use rescript_compiler::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, InMemoryModuleInfo, ModuleRegistry,
};
use rescript_compiler::cmi::portable_types::PortablePersStruct;
use rescript_compiler::parse_arena::ParseArena;
use rescript_compiler::parser::ast::{Signature, Structure};
use rescript_compiler::types::path::Path as TypePath;
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::mpsc;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;
use tracing::{Span, info_span, instrument};

/// Decode captured compiler output (stdout or stderr) into a String.
///
/// The output is not guaranteed to be valid UTF-8: a code frame can truncate a
/// multi-byte character. Decode lossily so a bad byte becomes a replacement
/// character instead of crashing the build.
fn compiler_output_to_string(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).to_string()
}

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
    PreJsReady(PreJsMsg),
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
}

#[derive(Default)]
struct InProcessSchedulerCounters {
    scheduled_typecheck: usize,
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
            "[scheduler-counter] capacity={} scheduled_typecheck={} scheduled_js={} signature_ready={} pre_js_ready={} completed={} js_scheduled_while_typecheck_ready={} max_ready_typecheck={} max_ready_js={} max_pending_js={} max_in_flight={} blocked_events_with_idle_slots={} max_idle_slots={} dispatcher_wait_ms={:.3} idle_slot_wait_ms={:.3}",
            capacity,
            self.scheduled_typecheck,
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
    alias_rewrites: AHashMap<String, TypePath>,
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

    let mut registry = build_command_state.module_registry.lock().unwrap();
    for update in updates {
        if let Some(pers_struct) = update.pers_struct {
            registry.register_module_arc(
                &update.module_name,
                pers_struct,
                update.module_info,
                update.alias_rewrites,
            );
        } else {
            registry.insert_module_info(update.module_name, update.module_info);
            registry.extend_alias_rewrites(update.alias_rewrites);
        }
    }
}

fn apply_signature_ready(build_command_state: &BuildCommandState, msg: SignatureReadyMsg) -> bool {
    apply_pending_registry_updates(build_command_state, msg.registry_updates);
    let generation_before = build_command_state.get_interface_generation(&msg.module_name);
    let generation_after =
        build_command_state.register_in_memory_interface(msg.module_name, msg.fingerprint, msg.is_pure);
    generation_before.is_some() && generation_before == Some(generation_after)
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
    build_state: &BuildCommandState,
    universe: &AHashSet<String>,
    stored_asts_snapshot: Option<&AHashMap<String, StoredAst>>,
) -> AHashMap<String, i64> {
    fn compute_from_asts(
        universe: &AHashSet<String>,
        stored_asts: &AHashMap<String, StoredAst>,
    ) -> AHashMap<String, i64> {
        let mut costs = AHashMap::with_capacity(universe.len());
        for name in universe {
            let impl_key = format!("{name}:impl");
            let intf_key = format!("{name}:intf");
            let mut source_len = 0usize;
            if let Some(StoredAst::Structure(stored)) = stored_asts.get(&impl_key) {
                source_len = source_len.saturating_add(stored.source_len);
            }
            if let Some(StoredAst::Signature(stored)) = stored_asts.get(&intf_key) {
                source_len = source_len.saturating_add(stored.source_len);
            }
            costs.insert(name.clone(), source_len.max(1) as i64);
        }
        costs
    }

    if let Some(stored_asts) = stored_asts_snapshot {
        return compute_from_asts(universe, stored_asts);
    }

    let stored_asts = build_state.stored_asts.lock().unwrap();
    compute_from_asts(universe, &stored_asts)
}

/// Compute the weighted critical-path priority of every module in the universe:
/// `priority(m) = cost(m) + max(priority(d) for d in in-universe dependents of m)`.
struct CompileWarning {
    module_name: String,
    package_name: String,
    warning: String,
}
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

/// Run the short-circuit check or actual `bsc` invocation for a single module.
/// Invoked from worker threads inside the dispatcher scope; only reads
/// `BuildState`, never mutates it (except via the `BuildCommandState` mutex
/// used by the in-process path to publish results).
fn compile_one(
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    registry_snapshot: &ModuleRegistry,
    stored_asts: Option<&AHashMap<String, StoredAst>>,
    module_name: &str,
    is_dirty: bool,
    warn_error_override: Option<String>,
    subprocess: bool,
    dump_typed_sexp: bool,
    parent_span: Span,
    in_process_hooks: Option<InProcessSchedulerHooks>,
) -> WorkerMsg {
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
            in_process = build_command_state.build_mode().is_in_process(),
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

    // In-process mode: bypass the bsc subprocess entirely and run the Rust
    // compiler in-thread. The caller has already staged runtime modules and
    // namespace signatures into the shared registry, and the DAG scheduler
    // guarantees all dependencies of this module are registered before it
    // is dispatched.
    if build_command_state.build_mode().is_in_process() {
        if let SourceType::SourceFile(_) = &module.source_type {
            let interface_generation_before = build_command_state.get_interface_generation(module_name);
            let result = compile_module_in_process_to_js_boundary(
                package,
                module,
                module_name,
                registry_snapshot,
                stored_asts.expect("in-process compile requires stored AST snapshot"),
                build_state,
                build_command_state,
                in_process_hooks.as_ref(),
            );
            let interface_generation_after = build_command_state.get_interface_generation(module_name);
            return match result {
                Ok(mut msg) => {
                    let is_clean_interface = interface_generation_before.is_some()
                        && interface_generation_before == interface_generation_after;
                    msg.is_clean = is_clean_interface;
                    WorkerMsg::PreJsReady(msg)
                }
                Err(err) => WorkerMsg::Completed(CompletionMsg {
                    module_name: module_name.to_string(),
                    result: Err(err),
                    interface_result: None,
                    is_clean: false,
                    is_compiled: true,
                    registry_updates: Vec::new(),
                }),
            };
        }
    }

    WorkerMsg::Completed(match &module.source_type {
        SourceType::MlMap(_) => {
            // The mlmap is compiled during AST generation; the entry here just
            // marks it compiled so its namespace members can proceed.
            CompletionMsg {
                module_name: package.namespace.to_suffix().unwrap(),
                result: Ok(None),
                interface_result: Some(Ok(None)),
                is_clean: false,
                is_compiled: false,
                registry_updates: Vec::new(),
            }
        }
        SourceType::SourceFile(source_file) => {
            // Construct span + attributes only when a subscriber is listening.
            // Otherwise root_config.get_package_specs() (which clones) and the
            // attribute formatting run per-module on the build hot path.
            let _file_span = if tracing::enabled!(tracing::Level::INFO) {
                let root_config = build_state.get_root_config();
                let specs = root_config.get_package_specs();
                // A package can be built under multiple specs (e.g. ESM + CJS).
                // Report all of them joined by "," instead of silently picking
                // the first — the compile_file span covers work for every spec.
                let suffix = specs
                    .iter()
                    .map(|s| root_config.get_suffix(s))
                    .collect::<Vec<_>>()
                    .join(",");
                let module_system = specs
                    .iter()
                    .map(|s| s.module.as_str())
                    .collect::<Vec<_>>()
                    .join(",");
                let namespace = package.namespace.to_suffix().unwrap_or_default();
                info_span!("build.compile_file", module = %module_name, package = %package.name, suffix, module_system, namespace).entered()
            } else {
                tracing::Span::none().entered()
            };

            let cmi_path = helpers::get_compiler_asset(
                package,
                &package.namespace,
                &source_file.implementation.path,
                "cmi",
            );
            let cmi_digest = helpers::compute_file_hash(Path::new(&cmi_path));

            let interface_result = source_file.interface.as_ref().map(|iface| {
                compile_file(
                    package,
                    &helpers::get_ast_path(&iface.path),
                    module,
                    module_name,
                    true,
                    build_state,
                    warn_error_override.clone(),
                    subprocess,
                    dump_typed_sexp,
                )
            });
            let result = compile_file(
                package,
                &helpers::get_ast_path(&source_file.implementation.path),
                module,
                module_name,
                false,
                build_state,
                warn_error_override,
                subprocess,
                dump_typed_sexp,
            );
            let cmi_digest_after = helpers::compute_file_hash(Path::new(&cmi_path));

            // If the cmi is byte-for-byte unchanged, downstream modules can
            // short-circuit — we check both interface and implementation
            // because e.g. `include MyModule` exposes implementation changes
            // through the cmi even when the .resi is untouched.
            let is_clean_cmi = matches!(
                (cmi_digest, cmi_digest_after),
                (Some(a), Some(b)) if a == b
            );

            CompletionMsg {
                module_name: module_name.to_string(),
                result,
                interface_result,
                is_clean: is_clean_cmi,
                is_compiled: true,
                registry_updates: Vec::new(),
            }
        }
    })
}

/// Extract sexp output from bsc stderr.
/// When -dtyped-sexp-locs is passed, bsc writes the sexp to stderr.
/// The sexp starts with "(structure" or "(signature" and continues to the end.
/// Everything before that is warnings.
/// Returns (warnings, Option<sexp>).
fn extract_warning_prefix_from_sexp_file(path: &Path) -> std::io::Result<String> {
    const MAX_WARNING_BYTES: usize = 16 * 1024 * 1024;

    let file = std::fs::File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut warnings = Vec::new();
    let mut offset = 0_u64;
    let mut at_line_start = true;
    let mut sexp_offset = None;

    loop {
        let buffer = reader.fill_buf()?;
        if buffer.is_empty() {
            break;
        }
        if at_line_start && (buffer.starts_with(b"(structure") || buffer.starts_with(b"(signature")) {
            sexp_offset = Some(offset);
            break;
        }

        let consumed = buffer
            .iter()
            .position(|byte| *byte == b'\n')
            .map_or(buffer.len(), |position| position + 1);
        let remaining = MAX_WARNING_BYTES.saturating_sub(warnings.len());
        warnings.extend_from_slice(&buffer[..consumed.min(remaining)]);
        at_line_start = buffer[consumed - 1] == b'\n';
        reader.consume(consumed);
        offset += consumed as u64;
    }

    if warnings.len() == MAX_WARNING_BYTES {
        warnings.extend_from_slice(b"\n[compiler warning output truncated]\n");
    }

    if let Some(sexp_offset) = sexp_offset.filter(|offset| *offset > 0) {
        let mut source = reader.into_inner();
        source.seek(SeekFrom::Start(sexp_offset))?;
        let parent = path.parent().unwrap_or_else(|| Path::new("."));
        let mut replacement = tempfile::NamedTempFile::new_in(parent)?;
        std::io::copy(&mut source, &mut replacement)?;
        replacement.flush()?;
        replacement.persist(path).map_err(|error| error.error)?;
    }

    Ok(String::from_utf8_lossy(&warnings).into_owned())
}

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
) {
    warning_entries.sort_by(|a, b| a.module_name.cmp(&b.module_name));
    for CompileWarning {
        package_name,
        warning,
        ..
    } in warning_entries
    {
        if let Some(package) = build_state.get_package(&package_name) {
            logs::append(package, &warning);
        }
        compile_warnings.push_str(&warning);
    }
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
        module_count = build_state.modules.len(),
        in_process = build_state.build_mode().is_in_process()
    )
    .entered();
    let compile_parent_span = Span::current();

    // In --in-process mode, purge deleted/renamed modules from the in-memory
    // registries so stale entries don't remain resolvable in watch mode.
    if build_state.build_mode().is_in_process() {
        build_state.purge_deleted_modules(&build_state.build_state.deleted_modules.clone());
        build_state.clear_gentype_contexts();
    }

    // In --in-process mode, synthesize namespace module signatures in memory
    // before any source modules are compiled. Source modules may use `-open Namespace`,
    // so the namespace signature must be available in the PersistentEnv first.
    if build_state.build_mode().is_in_process() {
        register_namespace_signatures(build_state);
        register_source_fallback_paths(build_state);

        // Pre-compile all @rescript/runtime modules into the registry.
        // In in-process mode, the registry is the sole source of truth —
        // no CMI fallback. Every dependency must be in the registry before
        // project modules start compiling, even when @rescript/runtime is
        // also present in the package graph (otherwise implicit Stdlib opens
        // can require modules that the main build graph hasn't reached yet).
        let parent_span = compile_parent_span.clone();
        let pre_compile_result: Result<()> = std::thread::scope(|scope| {
            let handle = std::thread::Builder::new()
                .name("rewatch-runtime-precompile".to_string())
                .stack_size(256 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    let _parent = parent_span.enter();
                    pre_compile_runtime_modules(build_state)
                })
                .map_err(|err| anyhow!("failed to spawn runtime pre-compilation thread: {err}"))?;

            match handle.join() {
                Ok(result) => result,
                Err(panic) => {
                    let msg = if let Some(s) = panic.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = panic.downcast_ref::<&str>() {
                        s.to_string()
                    } else {
                        "unknown".to_string()
                    };
                    Err(anyhow!("runtime pre-compilation panicked: {msg}"))
                }
            }
        });
        pre_compile_result?;

        // Clear source-fallback paths after pre-compilation.
        build_state
            .module_registry
            .lock()
            .unwrap()
            .set_source_fallback_paths(AHashMap::new());
    }

    // Expand the compile universe: every dirty module plus everything that
    // transitively depends on it.
    let mut compile_universe = dirty_modules.clone();
    let mut frontier = dirty_modules.iter().cloned().collect::<Vec<_>>();
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

    let compile_universe_count = compile_universe.len();
    set_length(compile_universe_count as u64);

    let in_process_mode = build_state.build_mode().is_in_process();
    let stored_asts_snapshot = in_process_mode.then(|| build_state.snapshot_stored_asts());
    let compile_universe = Arc::new(compile_universe);
    let module_costs = compute_module_costs(build_state, &compile_universe, stored_asts_snapshot.as_ref());
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
    let mut dirty_set: AHashSet<String> = dirty_modules;

    let warn_error_override = build_state.get_warn_error_override();
    let subprocess = build_state.subprocess();
    let dump_typed_sexp = build_state.dump_typed_sexp();
    let build_state_ref: &BuildState = &build_state.build_state;
    let build_command_state_ref: &BuildCommandState = build_state;

    let (tx, rx) = mpsc::channel::<WorkerMsg>();
    // Bound concurrency to rayon's pool size so the priority heap actually
    // orders work — dumping everything into rayon's deque would defeat #2.
    let capacity = rayon::current_num_threads().max(1);
    // Worker snapshots share the registry's Arc-backed maps. Publishing a
    // dependency updates those shared maps, so a single template snapshot is
    // enough; each worker still clones it before adding local provisional
    // module/interface entries.
    let worker_registry_template = if in_process_mode {
        build_state.snapshot_module_registry()
    } else {
        ModuleRegistry::new()
    };

    let mut completed: AHashSet<String> = AHashSet::new();
    let mut signature_ready: AHashSet<String> = AHashSet::new();
    let mut results_buffer: Vec<CompletionMsg> = Vec::with_capacity(compile_universe_count);
    let mut ready_js: Vec<PreJsMsg> = Vec::new();
    let mut pending_js_payloads: AHashMap<String, PreJsMsg> = AHashMap::new();
    let mut pending_js_deps: AHashMap<String, usize> = AHashMap::new();
    let mut waiting_js_by_dep: AHashMap<String, Vec<String>> = AHashMap::new();
    let mut js_metadata_ready: AHashSet<String> = AHashSet::new();
    let mut has_errors = false;
    let mut stalled = false;
    let mut scheduler_counters = (in_process_mode
        && std::env::var_os("RESCRIPT_SCHEDULER_COUNTERS").is_some())
    .then(InProcessSchedulerCounters::default);

    rayon::in_place_scope(|scope| {
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
            while in_flight < capacity && !has_errors {
                if let Some(pre_js_msg) = pop_ready_js(&mut ready_js, &waiting_js_by_dep) {
                    if let Some(counters) = scheduler_counters.as_mut() {
                        counters.scheduled_js += 1;
                        if !ready_heap.is_empty() {
                            counters.js_scheduled_while_typecheck_ready += 1;
                        }
                    }
                    let module_name = pre_js_msg.module_name.clone();
                    let tx = tx.clone();
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
                    scope.spawn(move |_| {
                        let msg = finish_in_process_js(
                            build_state_ref,
                            build_command_state_ref,
                            pre_js_msg,
                            parent_span,
                            registry_snapshot,
                            &tx,
                        );
                        if show_progress {
                            inc_ref();
                        }
                        let _ = tx.send(WorkerMsg::Completed(msg));
                    });
                    trace!("scheduled in-process JS finish for {}", module_name);
                    continue;
                }
                let Some(work) = ready_heap.pop() else { break };
                if let Some(counters) = scheduler_counters.as_mut() {
                    counters.scheduled_typecheck += 1;
                }
                let module_name = work.module_name.clone();
                let is_dirty = dirty_set.contains(&module_name);
                let warn_override = warn_error_override.clone();
                let tx = tx.clone();
                let inc_ref = &inc;
                in_flight += 1;
                if let Some(counters) = scheduler_counters.as_mut() {
                    counters.observe_queues(
                        ready_heap.len(),
                        ready_js.len(),
                        pending_js_payloads.len(),
                        in_flight,
                    );
                }
                let registry_snapshot = worker_registry_template.clone();
                let stored_asts = stored_asts_snapshot.as_ref();
                let parent_span = compile_parent_span.clone();
                let in_process_hooks = in_process_mode.then(|| InProcessSchedulerHooks {
                    tx: tx.clone(),
                    compile_universe: compile_universe.clone(),
                });
                scope.spawn(move |_| {
                    let msg = compile_one(
                        build_state_ref,
                        build_command_state_ref,
                        &registry_snapshot,
                        stored_asts,
                        &module_name,
                        is_dirty,
                        warn_override,
                        subprocess,
                        dump_typed_sexp,
                        parent_span,
                        in_process_hooks,
                    );
                    if show_progress && matches!(msg, WorkerMsg::Completed(_)) {
                        inc_ref();
                    }
                    // Receiver lives for the full scope, so send cannot fail
                    // unless the dispatcher has already hung up on purpose.
                    let _ = tx.send(msg);
                });
            }

            if in_flight == 0 {
                if !ready_heap.is_empty() {
                    // Errors suppressed new spawns; nothing left to drain.
                    break;
                }
                if completed.len() < compile_universe_count && !has_errors {
                    stalled = true;
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
                        if let Some(counters) = scheduler_counters.as_mut() {
                            counters.pre_js_ready += 1;
                        }
                        in_flight -= 1;
                        let module_name = msg.module_name.clone();
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
                        if in_process_mode {
                            apply_pending_registry_updates(
                                build_command_state_ref,
                                std::mem::take(&mut msg.registry_updates),
                            );
                        }
                        let ready_name = msg.module_name;
                        js_metadata_ready.insert(ready_name.clone());

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
                        if in_process_mode {
                            apply_pending_registry_updates(
                                build_command_state_ref,
                                std::mem::take(&mut msg.registry_updates),
                            );
                        }

                        if msg.result.is_err() || msg.interface_result.as_ref().is_some_and(|r| r.is_err()) {
                            has_errors = true;
                        }

                        let is_clean = msg.is_clean;
                        let finished_name = msg.module_name.clone();
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

                        if in_process_mode {
                            let completed_without_signature =
                                !signature_ready.contains(&finished_name) && !has_errors;
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
                        } else {
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
    if let Some(counters) = scheduler_counters.as_ref() {
        counters.print_report(capacity);
    }
    // Close our sender handle so any lingering clones in already-spawned
    // workers don't keep the channel open past the scope.
    drop(tx);

    trace!(
        "Compiled {} out of {} in the universe",
        completed.len(),
        compile_universe_count,
    );

    let mut compile_errors = String::new();
    let mut compile_warnings = String::new();
    let mut warning_entries = Vec::new();
    let mut num_compiled_modules = 0;

    // Persist propagated dirtiness back onto build_state. Modules that were
    // marked dirty (because a predecessor's cmi changed) but never scheduled
    // — e.g. the first compile error aborted further dispatch — must keep
    // compile_dirty = true so the next incremental build recompiles them.
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
        .filter(|msg| {
            msg.result.is_err() || matches!(msg.interface_result, Some(Err(_)))
        })
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
        results_buffer.retain(|msg| !depends_on_failed(&msg.module_name));
    }

    // These timestamps are used as a compile-generation marker by
    // mark_modules_with_expired_deps_dirty, not as precise wall-clock compile
    // times. All modules successfully compiled in one pass are mutually
    // up-to-date for that pass, so they must receive the same timestamp.
    let compile_timestamp = SystemTime::now();

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
            num_compiled_modules += 1;
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
                module.last_compiled_cmi = Some(compile_timestamp);
                module.last_compiled_cmt = Some(compile_timestamp);
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
            logs::append(package, &error);
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
            logs::append(package, &error);
            compile_errors.push_str(&error);
        }
    }

    if stalled {
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
            {
                logs::append(package, &message);
            }
        }

        compile_errors.push_str(&message);
    }

    // Collect replayed warnings into the same list as fresh warnings so mixed
    // output matches the sorted order used when every module compiles normally.
    warning_entries.extend(collect_stored_warnings_for_modules_not_recompiled(
        &build_state.build_state,
        &recompiled_modules,
    ));
    append_compile_warnings(&build_state.build_state, warning_entries, &mut compile_warnings);

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
    let jsx_mode_args = root_config.get_jsx_mode_args();
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
    let project_root_args = config.get_project_root_args();

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

pub(crate) struct InProcessCompilerFlags {
    pub(crate) nopervasives: bool,
    pub(crate) no_version_header: bool,
    pub(crate) check_div_by_zero: bool,
    pub(crate) cross_module_inline: bool,
    pub(crate) no_assert_false: bool,
    pub(crate) noassert: bool,
    pub(crate) no_builtin_ppx: bool,
    pub(crate) make_runtime: bool,
    pub(crate) debug: bool,
    pub(crate) jsx_preserve: bool,
    pub(crate) jsx_version: Option<i32>,
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
            no_builtin_ppx: false,
            make_runtime: false,
            debug: false,
            jsx_preserve: false,
            jsx_version: None,
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
            "-enable-experimental" => {
                if let Some(feature) = iter.next() {
                    if feature == "LetUnwrap" {
                        parsed.experimental_let_unwrap = true;
                    }
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
fn build_compiler_options(
    package: &packages::Package,
    module_name: &str,
    source_file_path: &Path,
    build_command_state: &BuildCommandState,
) -> Result<rescript_compiler::driver::CompilerOptions> {
    let build_state = &build_command_state.build_state;
    let root_config = build_state.get_root_config();
    let project_context = &build_state.project_context;

    // Parse package compiler-flags for flags the in-process compiler needs to honor.
    // In the subprocess path, these are passed as raw CLI args to bsc.
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let warning_args = package.config.get_warning_args(package.is_local_dep, None);
    let parsed_flags = parse_in_process_compiler_flags(&[bsc_flags, warning_args].concat());

    // Collect -I paths from all dependencies (same logic as get_dependency_paths)
    let mut include_paths: Vec<PathBuf> = Vec::new();

    // Add the package's own lib/ocaml directory
    include_paths.push(package.get_ocaml_build_path());

    // Add dependency lib/ocaml paths
    let dep_names: Vec<&str> = package
        .config
        .dependencies
        .as_ref()
        .map(|d| d.iter().map(|s| s.name()).collect())
        .unwrap_or_default();
    for dep_name in dep_names {
        if let Some(dep_pkg) = build_state.packages.get(dep_name) {
            include_paths.push(dep_pkg.get_ocaml_build_path());
        }
    }

    // OCaml compiles with `-I` for the package, its dependencies and, for
    // `type: dev` sources, its dev dependencies (`get_dependency_paths`);
    // units of other packages are not visible.
    let is_type_dev = build_state
        .modules
        .get(module_name)
        .is_some_and(|module| module.is_type_dev);
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
            let dep_include = dep_pkg.get_ocaml_build_path();
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

    // Source filename for interface constraint and JS import resolution. OCaml
    // computes output_dir from the package output prefix before rebasing module
    // imports; see compiler/core/js_dump_program.ml:128 and
    // compiler/core/js_name_of_module_id.ml:135-139.
    let source_filename = Some(
        Path::new(&package.path)
            .join(source_file_path)
            .to_string_lossy()
            .to_string(),
    );

    // Output path and module format for JS import resolution.
    let js_output_targets = js_output_targets_for_source(package, source_file_path, root_config);
    let output_module_format = js_output_targets.first().map(|target| target.module_format);
    let output_path = js_output_targets.first().map(|target| target.path.clone());
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
            let mut gentype_args = package.config.get_project_root_args();
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
        include_paths,
        runtime_path,
        open_modules,
        warning_specs: parsed_flags.warning_specs,
        warning_error_specs: parsed_flags.warning_error_specs,
        source_filename,
        output_path,
        output_module_format,
        js_output_targets,
        source_map,
        source_map_sources_content,
        source_map_root,
        jsx_version,
        experimental_let_unwrap,
        jsx_preserve: parsed_flags.jsx_preserve,
        debug: parsed_flags.debug,
        check_div_by_zero: parsed_flags.check_div_by_zero,
        cross_module_inline: parsed_flags.cross_module_inline,
        no_assert_false: parsed_flags.no_assert_false,
        noassert: parsed_flags.noassert,
        no_builtin_ppx: parsed_flags.no_builtin_ppx,
        nopervasives: parsed_flags.nopervasives,
        no_version_header: parsed_flags.no_version_header,
        module_name: Some(module_name.to_string()),
        package_name: Some(package.config.name.clone()),
        make_runtime: parsed_flags.make_runtime,
        gentype_config,
        gentype_resolver,
        typed_artifacts: Some(std::sync::Arc::new(typed_artifact_output(package, source_file_path))),
        keep_locs: parsed_flags.keep_locs,
        visible_package_roots: Some(visible_package_roots),
        ..Default::default()
    })
}

/// Where editor tooling expects the typed artifacts of a module: next to the
/// `.ast` under `lib/bs`, plus a flat copy in `lib/ocaml` (the same files the
/// bsc subprocess path copies after compiling).
fn typed_artifact_output(
    package: &packages::Package,
    source_file_path: &Path,
) -> rescript_compiler::driver::TypedArtifactOutput {
    let build_path = package.get_build_path();
    let dir = source_file_path.parent().unwrap_or_else(|| Path::new(""));
    let basename = helpers::file_path_to_compiler_asset_basename(source_file_path, &package.namespace);
    rescript_compiler::driver::TypedArtifactOutput {
        output_prefix: build_path.join(dir).join(basename),
        copy_dirs: vec![package.get_ocaml_build_path()],
        builddir: build_path.to_string_lossy().into_owned(),
        args: std::env::args().collect(),
    }
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
        let source_abs = Path::new(&package.path).join(source_file_path);
        helpers::get_source_file_from_rescript_file(&source_abs, &suffix)
    } else {
        let js_relative = helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
        Path::new(&package.path)
            .join("lib")
            .join(spec.get_out_of_source_dir())
            .join(js_relative)
    }
}

fn js_output_targets_for_source(
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

fn in_memory_module_info_for_package(
    package: &packages::Package,
    root_config: &config::Config,
    source_path: PathBuf,
    is_pure: bool,
    cmj_export_constants: AHashMap<String, CmjExportConstant>,
    cmj_export_arities: AHashMap<String, CmjExportArity>,
    hoisted_exports: Vec<rescript_compiler::lambda::HoistedExport>,
    is_runtime: bool,
) -> InMemoryModuleInfo {
    InMemoryModuleInfo::new(source_path, is_pure, cmj_export_constants, is_runtime)
        .with_cmj_export_arities(cmj_export_arities)
        .with_cmj_hoisted_exports(hoisted_exports)
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
    hoisted_exports: Vec<rescript_compiler::lambda::HoistedExport>,
    is_runtime: bool,
    has_interface: bool,
    interface_registry_update: Option<PendingRegistryUpdate>,
    pers_struct: Option<PortablePersStruct>,
    new_alias_rewrites: AHashMap<String, TypePath>,
) -> Vec<PendingRegistryUpdate> {
    let module_info = in_memory_module_info_for_package(
        package,
        root_config,
        source_abs,
        is_pure,
        cmj_export_constants,
        cmj_export_arities,
        hoisted_exports,
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
                alias_rewrites: AHashMap::new(),
            }]
        }
    } else if let Some(ps) = pers_struct {
        vec![PendingRegistryUpdate {
            module_name: module_name.to_string(),
            pers_struct: Some(Arc::new(ps)),
            module_info,
            alias_rewrites: new_alias_rewrites,
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
fn write_file_creating_parent_on_missing(path: &Path, contents: impl AsRef<[u8]>) -> Result<()> {
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
            let source_abs = Path::new(&package.path).join(source_file_path);
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

/// Register namespace module signatures in the PersistentEnv for --in-process mode.
///
/// For each package with a namespace, synthesizes the namespace module's
/// alias signature (e.g., `module Foo = Foo-MyApp`) and registers it in
/// the shared ModuleRegistry so that `-open Namespace` works during compilation.
///
/// This replaces the `compile_mlmap` bsc subprocess call used in file-based modes.
fn register_namespace_signatures(build_state: &BuildCommandState) {
    for (_package_name, package) in build_state.packages.iter() {
        let namespace_suffix = match package.namespace.to_suffix() {
            Some(suffix) => suffix,
            None => continue, // No namespace for this package
        };

        let entry = match &package.namespace {
            packages::Namespace::NamespaceWithEntry { namespace: _, entry } => Some(entry.as_str()),
            _ => None,
        };

        // Build the list of (short_name, internal_name) alias pairs.
        // This mirrors the logic in packages::parse_packages that calls gen_mlmap.
        let source_files = match &package.source_files {
            Some(sf) => sf,
            None => continue,
        };

        let module_aliases: Vec<(String, String)> = source_files
            .keys()
            .map(|path| helpers::file_path_to_module_name(path, &packages::Namespace::NoNamespace))
            .filter(|module_name| {
                // Exclude the entry module (it's not aliased in the namespace)
                if let Some(entry) = entry {
                    module_name != entry
                } else {
                    true
                }
            })
            .filter(|module_name| helpers::is_non_exotic_module_name(module_name))
            .map(|short_name| {
                let internal_name = format!("{}-{}", short_name, namespace_suffix);
                (short_name, internal_name)
            })
            .collect();

        if !module_aliases.is_empty() {
            build_state.register_namespace_in_registry(
                &namespace_suffix,
                &module_aliases,
                package.path.clone(),
            );
            // Editor tooling reads the namespace unit from lib/bs like the
            // bsc-compiled `.mlmap` (js_implementation.ml:207-226).
            let mut sorted_aliases = module_aliases.clone();
            sorted_aliases.sort();
            let build_path = package.get_build_path();
            let output = rescript_compiler::driver::TypedArtifactOutput {
                output_prefix: build_path.join(&namespace_suffix),
                copy_dirs: vec![package.get_ocaml_build_path()],
                builddir: build_path.to_string_lossy().into_owned(),
                args: std::env::args().collect(),
            };
            if let Err(err) = rescript_compiler::driver::save_namespace_typed_artifacts(
                &namespace_suffix,
                &sorted_aliases,
                &output,
            ) {
                log::warn!("Could not write namespace artifacts for {namespace_suffix}: {err}");
            }
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
    let runtime_path = build_state
        .build_state
        .compiler_info
        .runtime_path
        .join("lib")
        .join("ocaml");
    if let Ok(entries) = std::fs::read_dir(runtime_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
                if ext == "res" || ext == "resi" {
                    if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
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
struct RuntimeModuleSource {
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
fn pre_compile_runtime_modules(build_state: &BuildCommandState) -> Result<()> {
    let _span = info_span!("build.runtime_precompile").entered();
    let runtime_timing_enabled = std::env::var_os("RESCRIPT_RUNTIME_TIMINGS").is_some()
        || std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some();
    let runtime_timing_start = runtime_timing_enabled.then(Instant::now);
    let runtime_timing_before = runtime_timing_enabled.then(rescript_compiler::timing::snapshot);
    let runtime_root = &build_state.build_state.compiler_info.runtime_path;
    let runtime_config = packages::read_config(runtime_root)
        .with_context(|| format!("failed to read runtime config from {}", runtime_root.display()))?;
    let runtime_path = runtime_root.join("lib").join("ocaml");
    let mut runtime_modules = collect_runtime_sources(&runtime_path)?;
    tracing::Span::current().record("runtime_modules", runtime_modules.len());

    if runtime_modules.is_empty() {
        return Ok(());
    }

    let already_registered = {
        let registry = build_state.module_registry.lock().unwrap();
        runtime_modules.iter().all(|module| {
            registry.module_info_is_runtime(&module.module_name)
                && registry.has_cached_module(&module.module_name)
        })
    };
    if already_registered {
        return Ok(());
    }

    populate_runtime_deps(&mut runtime_modules);

    seed_runtime_registry(build_state, &runtime_modules);
    let runtime_compile_threads = rayon::current_num_threads().max(2);
    // Runtime module compilation runs inside Rayon workers, so the outer
    // precompile thread stack is not enough for very large runtime IR cleanup.
    let runtime_compile_pool = rayon::ThreadPoolBuilder::new()
        .num_threads(runtime_compile_threads)
        .thread_name(|idx| format!("rewatch-runtime-in-process-{idx}"))
        .stack_size(256 * 1024 * 1024)
        .build()
        .context("failed to create runtime in-process compiler pool")?;
    runtime_compile_pool.install(|| {
        compile_runtime_modules_parallel(
            build_state,
            runtime_root,
            &runtime_path,
            &runtime_config,
            &runtime_modules,
        )
    })?;

    if let (Some(start), Some(before)) = (runtime_timing_start, runtime_timing_before) {
        let after = rescript_compiler::timing::snapshot();
        let wall = start.elapsed();
        let parse = duration_delta(after.parse, before.parse);
        let typecheck = duration_delta(after.typecheck, before.typecheck);
        let lambda = duration_delta(after.lambda, before.lambda);
        let lambda_optimization = duration_delta(after.lambda_optimization, before.lambda_optimization);
        let gentype = duration_delta(after.gentype, before.gentype);
        let codegen = duration_delta(after.codegen, before.codegen);
        let recorded = parse
            .saturating_add(typecheck)
            .saturating_add(lambda)
            .saturating_add(lambda_optimization)
            .saturating_add(gentype)
            .saturating_add(codegen);
        let overhead = wall.saturating_sub(recorded);
        eprintln!(
            "[runtime-timing] modules={} wall_ms={:.3} parse_ms={:.3} typecheck_ms={:.3} lambda_ms={:.3} lambda_optimization_ms={:.3} gentype_ms={:.3} codegen_ms={:.3} overhead_ms={:.3}",
            runtime_modules.len(),
            duration_ms(wall),
            duration_ms(parse),
            duration_ms(typecheck),
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

fn seed_runtime_registry(build_state: &BuildCommandState, runtime_modules: &[RuntimeModuleSource]) {
    let mut registry = build_state.module_registry.lock().unwrap();
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
    build_state: &BuildCommandState,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_modules: &[RuntimeModuleSource],
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
    let worker_registry_template = build_state.snapshot_module_registry();
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
                scope.spawn(move |_| {
                    let result = compile_runtime_module_from_source(
                        build_state,
                        runtime_root,
                        runtime_path,
                        runtime_config,
                        module,
                        registry_snapshot,
                    );
                    let _ = tx.send(RuntimeCompletionMsg { idx, result });
                });
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
            build_state,
            runtime_root,
            runtime_path,
            runtime_config,
            runtime_modules,
            &completed,
        )?;
    }

    Ok(())
}

fn compile_runtime_cycle_remainder_serial(
    build_state: &BuildCommandState,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    runtime_modules: &[RuntimeModuleSource],
    completed: &[bool],
) -> Result<()> {
    debug!("runtime dependency graph has a cycle; compiling remaining modules serially");
    let worker_registry_template = build_state.snapshot_module_registry();
    for idx in runtime_compile_order(runtime_modules) {
        if completed[idx] {
            continue;
        }
        let registry_snapshot = worker_registry_template.clone();
        compile_runtime_module_from_source(
            build_state,
            runtime_root,
            runtime_path,
            runtime_config,
            &runtime_modules[idx],
            registry_snapshot,
        )?;
    }
    Ok(())
}

fn compile_runtime_module_from_source(
    build_state: &BuildCommandState,
    runtime_root: &Path,
    runtime_path: &Path,
    runtime_config: &config::Config,
    module: &RuntimeModuleSource,
    registry_snapshot: ModuleRegistry,
) -> Result<()> {
    let options = runtime_compiler_options(
        runtime_root,
        runtime_path,
        &module.module_name,
        &module.res_path,
        runtime_config,
    );

    let mut local_registry = registry_snapshot;
    let has_runtime_interface = module.resi.is_some();
    let mut interface_pers_struct = None;
    let mut interface_alias_rewrites = AHashMap::new();

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

        interface_alias_rewrites = intf_result.new_alias_rewrites;
        if let Some(pers_struct) = intf_result.pers_struct {
            let pers_struct = Arc::new(pers_struct);
            local_registry.register_module_arc(
                &module.module_name,
                pers_struct.clone(),
                InMemoryModuleInfo::new(module.res_path.clone(), true, AHashMap::new(), true),
                interface_alias_rewrites.clone(),
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
    .with_cmj_hoisted_exports(compile_result.hoisted_exports);

    let mut shared_registry = build_state.module_registry.lock().unwrap();
    if has_runtime_interface {
        // OCaml compiler/ml/typemod.ml:1742-1758 checks the implementation
        // against the already-saved interface `.cmi`; typemod.ml:1779-1787
        // only saves an inferred `.cmi` in the no-interface branch. Keep
        // implementation-local module aliases out of the published registry.
        if let Some(pers_struct) = interface_pers_struct {
            shared_registry.register_module_arc(
                &module.module_name,
                pers_struct,
                module_info,
                interface_alias_rewrites,
            );
        } else {
            shared_registry.insert_module_info(module.module_name.clone(), module_info);
            shared_registry.extend_alias_rewrites(interface_alias_rewrites);
        }
    } else if let Some(pers_struct) = compile_result.pers_struct {
        shared_registry.register_module(
            &module.module_name,
            pers_struct,
            module_info,
            compile_result.new_alias_rewrites,
        );
    }

    Ok(())
}

fn collect_runtime_sources(runtime_path: &Path) -> Result<Vec<RuntimeModuleSource>> {
    let mut runtime_modules = Vec::new();
    for entry in std::fs::read_dir(runtime_path)
        .with_context(|| format!("failed to read runtime directory {}", runtime_path.display()))?
    {
        let entry = entry.with_context(|| {
            format!(
                "failed to read runtime directory entry in {}",
                runtime_path.display()
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

        let res_source = read_source_latin1(&path)?;
        let (res_arena, structure, mut deps) = parse_runtime_structure(&path, &res_source)?;
        let resi_path = path.with_extension("resi");
        let resi = if resi_path.exists() {
            let source = read_source_latin1(&resi_path)?;
            let (arena, signature, intf_deps) = parse_runtime_signature(&resi_path, &source)?;
            deps.extend(intf_deps);
            Some(RuntimeInterfaceSource {
                path: resi_path,
                arena,
                signature,
            })
        } else {
            None
        };

        runtime_modules.push(RuntimeModuleSource {
            module_name,
            res_path: path,
            res_arena,
            structure,
            resi,
            deps,
        });
    }

    runtime_modules.sort_by(|a, b| a.module_name.cmp(&b.module_name));
    Ok(runtime_modules)
}

fn module_name_from_stem(stem: &str) -> Option<String> {
    let mut chars = stem.chars();
    chars
        .next()
        .map(|ch| format!("{}{}", ch.to_uppercase(), chars.as_str()))
}

fn read_source_latin1(path: &Path) -> Result<String> {
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

fn parse_runtime_signature(path: &Path, source: &str) -> Result<(ParseArena, Signature, AHashSet<String>)> {
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
        let signature = rescript_compiler::binary_ast::ppx::rewrite_signature(&signature, parser.arena_mut())
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

fn parse_runtime_structure(path: &Path, source: &str) -> Result<(ParseArena, Structure, AHashSet<String>)> {
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
        let structure = rescript_compiler::binary_ast::ppx::rewrite_structure(&structure, parser.arena_mut())
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

fn runtime_compiler_options(
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
        include_paths: vec![runtime_path.to_path_buf()],
        runtime_path: Some(runtime_root.to_path_buf()),
        open_modules: parsed_flags.open_modules,
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path,
        output_module_format,
        js_output_targets,
        jsx_version: parsed_flags.jsx_version,
        experimental_let_unwrap: parsed_flags.experimental_let_unwrap
            || runtime_config.has_experimental_feature(config::ExperimentalFeature::LetUnwrap),
        jsx_preserve: parsed_flags.jsx_preserve,
        debug: parsed_flags.debug,
        no_version_header: parsed_flags.no_version_header,
        check_div_by_zero: parsed_flags.check_div_by_zero,
        cross_module_inline: parsed_flags.cross_module_inline,
        no_assert_false: parsed_flags.no_assert_false,
        noassert: parsed_flags.noassert,
        no_builtin_ppx: parsed_flags.no_builtin_ppx,
        nopervasives: parsed_flags.nopervasives,
        module_name: Some(module_name.to_string()),
        package_name: Some(runtime_config.name.clone()),
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
fn compile_module_in_process_to_js_boundary(
    package: &packages::Package,
    module: &Module,
    module_name: &str,
    registry: &ModuleRegistry,
    stored_asts: &AHashMap<String, StoredAst>,
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    scheduler_hooks: Option<&InProcessSchedulerHooks>,
) -> Result<PreJsMsg> {
    let _span = info_span!(
        "compiler.in_process_module",
        module = %module_name,
        package = %package.name
    )
    .entered();
    let module_timing_enabled = std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some();
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
    let root_config = build_state.get_root_config();

    let source_abs = Path::new(&package.path).join(implementation_path);
    let is_runtime = package.name == "@rescript/runtime";
    let provisional_is_pure = false;
    let provisional_module_info = in_memory_module_info_for_package(
        package,
        root_config,
        source_abs.clone(),
        provisional_is_pure,
        AHashMap::new(),
        AHashMap::new(),
        Vec::new(),
        is_runtime,
    );

    // For .resi + .res, we need the .resi to be in the registry before compiling .res.
    // Build a local registry that includes the .resi result (if any).
    let mut local_registry = registry.clone();
    let mut interface_registry_update: Option<PendingRegistryUpdate> = None;
    let mut gentype_ignore_interface = false;
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
        let intf_source_abs = Path::new(&package.path).join(&interface.path);
        let intf_key = format!("{module_name}:intf");
        let intf_result = match stored_asts.get(&intf_key) {
            Some(StoredAst::Signature(stored)) => {
                rescript_compiler::driver::typecheck_preprocessed_signature_in_process(
                    &stored.arena,
                    &stored.signature,
                    &intf_source_abs.to_string_lossy(),
                    module_name,
                    &options,
                    &local_registry,
                )
            }
            Some(StoredAst::Structure(_)) => panic!(
                "in-process invariant violated: expected signature AST for {}, found structure AST",
                intf_source_abs.display()
            ),
            None => panic!(
                "in-process invariant violated: missing stored signature AST for {}",
                intf_source_abs.display()
            ),
        }
        .map_err(|e| match e.downcast::<rescript_compiler::driver::UserDiagnostic>() {
            // A compiler diagnostic is reported as the text bsc prints.
            Ok(diagnostic) => anyhow!("{}", diagnostic.output()),
            Err(e) => anyhow!("Interface typecheck failed for {}: {}", module_name, e),
        });

        let intf_result = match intf_result {
            Ok(r) => r,
            Err(e) => {
                return Err(e);
            }
        };
        interface_warnings = intf_result.warnings;

        // Register the .resi's PersStruct in the local registry so the
        // .res compilation can find it for moregen constraints.
        gentype_ignore_interface = intf_result.gentype_ignore_interface;
        let intf_fingerprint = intf_result
            .pers_struct
            .as_ref()
            .map(|ps| ps.fingerprint)
            .unwrap_or(0);
        let intf_alias_rewrites = intf_result.new_alias_rewrites;
        if let Some(ps) = intf_result.pers_struct {
            let ps = Arc::new(ps);
            let module_info = provisional_module_info.clone();
            local_registry.register_module_arc(
                module_name,
                ps.clone(),
                module_info.clone(),
                intf_alias_rewrites.clone(),
            );
            interface_registry_update = Some(PendingRegistryUpdate {
                module_name: module_name.to_string(),
                pers_struct: Some(ps),
                module_info,
                alias_rewrites: intf_alias_rewrites,
            });
        } else {
            interface_registry_update = Some(PendingRegistryUpdate {
                module_name: module_name.to_string(),
                pers_struct: None,
                module_info: provisional_module_info.clone(),
                alias_rewrites: intf_alias_rewrites,
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
            let fingerprint = ready.pers_struct.as_ref().map(|ps| ps.fingerprint).unwrap_or(0);
            let module_info = signature_module_info.clone();
            let registry_updates = if let Some(pers_struct) = ready.pers_struct {
                vec![PendingRegistryUpdate {
                    module_name: signature_module_name.clone(),
                    pers_struct: Some(Arc::new(pers_struct)),
                    module_info,
                    alias_rewrites: ready.new_alias_rewrites,
                }]
            } else {
                vec![PendingRegistryUpdate {
                    module_name: signature_module_name.clone(),
                    pers_struct: None,
                    module_info,
                    alias_rewrites: ready.new_alias_rewrites,
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
                Some(StoredAst::Structure(stored)) => {
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
                        &options,
                        &local_registry,
                        has_interface,
                        gentype_ignore_interface,
                        signature_hook,
                    )
                }
                Some(StoredAst::Signature(_)) => panic!(
                    "in-process invariant violated: expected structure AST for {}, found signature AST",
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
            result.warnings.insert_str(0, &interface_warnings);
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
            let msg = if let Some(s) = panic.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic".to_string()
            };
            return Err(anyhow!("Compilation panicked for {}: {}", module_name, msg));
        }
    };

    if let (Some(start), Some(guard)) = (module_timing_start, module_timing_guard.as_ref()) {
        let timings = guard.snapshot();
        let wall = start.elapsed();
        let parse = timings.parse;
        let typecheck = timings.typecheck;
        let lambda = timings.lambda;
        let lambda_optimization = timings.lambda_optimization;
        let gentype = timings.gentype;
        let codegen = timings.codegen;
        let recorded = parse
            .saturating_add(typecheck)
            .saturating_add(lambda)
            .saturating_add(lambda_optimization)
            .saturating_add(gentype)
            .saturating_add(codegen);
        let overhead = wall.saturating_sub(recorded);
        eprintln!(
            "[module-timing] module={} package={} wall_ms={:.3} parse_ms={:.3} typecheck_ms={:.3} lambda_ms={:.3} lambda_optimization_ms={:.3} gentype_ms={:.3} codegen_ms={:.3} overhead_ms={:.3}",
            module_name,
            package.name,
            duration_ms(wall),
            duration_ms(parse),
            duration_ms(typecheck),
            duration_ms(lambda),
            duration_ms(lambda_optimization),
            duration_ms(gentype),
            duration_ms(codegen),
            duration_ms(overhead)
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
    })
}

fn finish_in_process_js(
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
    pre_js_msg: PreJsMsg,
    parent_span: Span,
    registry_snapshot: ModuleRegistry,
    metadata_tx: &mpsc::Sender<WorkerMsg>,
) -> CompletionMsg {
    let module_name = pre_js_msg.module_name.clone();
    let is_clean = pre_js_msg.is_clean;
    let result = finish_in_process_js_inner(
        build_state,
        build_command_state,
        pre_js_msg,
        parent_span,
        registry_snapshot,
        metadata_tx,
    );
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
    } = pre_js_msg;
    let module_timing_enabled = std::env::var_os("RESCRIPT_MODULE_TIMINGS").is_some();
    let module_timing_start = module_timing_enabled.then(Instant::now);
    let module_timing_guard = module_timing_enabled.then(rescript_compiler::timing::ThreadTimingGuard::start);
    let module = build_state.get_module(&module_name).unwrap();
    let package = build_state
        .get_package(&module.package_name)
        .expect("Package not found");
    // The warnings bsc prints to stderr, filtered like the subprocess path.
    let warning = visible_compiler_warnings(&std::mem::take(&mut pre_js.warnings), package.is_local_dep);
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
    let options = build_compiler_options(package, &module_name, &implementation_path, build_command_state)?;
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
            metadata.hoisted_exports,
            is_runtime,
        );
        let registry_updates = vec![PendingRegistryUpdate {
            module_name: module_name.clone(),
            pers_struct: None,
            module_info,
            alias_rewrites: AHashMap::new(),
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
    drop(metadata_hook);
    let compile_result = match compile_result {
        Ok(Ok(result)) => result,
        Ok(Err(e)) => {
            return Err(anyhow!("JS compilation failed for {}: {}", module_name, e));
        }
        Err(panic) => {
            let msg = if let Some(s) = panic.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic".to_string()
            };
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
            compile_result.hoisted_exports.clone(),
            is_runtime,
            has_interface,
            metadata_interface_registry_update,
            compile_result.pers_struct,
            compile_result.new_alias_rewrites,
        );
        send_js_metadata_ready(metadata_tx, module_name.clone(), registry_updates)
    });

    let mut write_duration = Duration::default();
    {
        let _write_span = info_span!(
            "compiler.write_js",
            module = %module_name,
            outputs = compile_result.js_outputs.len()
        )
        .entered();
        let write_start = module_timing_enabled.then(Instant::now);
        write_compiled_js_outputs(
            &compile_result.js_outputs,
            &compile_result.js_output,
            package,
            &implementation_path,
            root_config,
        )?;
        if let Some(write_start) = write_start {
            write_duration = write_start.elapsed();
        }
    }

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
            "[module-js-timing] module={} package={} wall_ms={:.3} codegen_ms={:.3} write_ms={:.3} overhead_ms={:.3} outputs={}",
            module_name,
            package.name,
            duration_ms(wall),
            duration_ms(codegen),
            duration_ms(write_duration),
            duration_ms(overhead),
            js_output_count
        );
    }

    Ok(InProcessModuleResult {
        warning,
        registry_updates,
    })
}

fn compile_file(
    package: &packages::Package,
    ast_path: &Path,
    module: &Module,
    module_name: &str,
    is_interface: bool,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    subprocess: bool,
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
    // `gentype_dirs` is populated once during package discovery, so we just
    // borrow the cached slice here (empty when gentype is off).
    let current_package_dirs: &[PathBuf] = package.gentype_dirs.as_deref().unwrap_or(&[]);
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
        build_state.source_map_command,
        current_package_dirs,
    )?;

    // --dump-typed-sexp: add -dtyped-sexp to bsc invocation
    if dump_typed_sexp {
        to_mjs_args.push("-dtyped-sexp".to_string());
    }

    let cwd = build_path_abs
        .canonicalize()
        .map(StrippedVerbatimPath::to_stripped_verbatim_path)
        .ok()
        .unwrap();

    // --subprocess: run bsc as subprocess with timeout (non-fatal on crash/timeout).
    // This REPLACES the normal bsc call — only one bsc runs per compile_file.
    if subprocess {
        // Redirect stderr to sexp file when dump_typed_sexp is set
        let sexp_file = if dump_typed_sexp {
            let path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
            if let Some(parent) = path.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            Some(std::fs::File::create(&path).map_err(|e| anyhow!("Failed to create sexp file: {e}"))?)
        } else {
            None
        };

        match Command::new(&compiler_info.bsc_path)
            .current_dir(&cwd)
            .args(&to_mjs_args)
            .stdout(std::process::Stdio::null())
            .stderr(match sexp_file {
                Some(f) => std::process::Stdio::from(f),
                None => std::process::Stdio::piped(),
            })
            .spawn()
        {
            Ok(mut child) => {
                // Drain piped stderr while the compiler is running. Waiting with try_wait while a
                // full pipe blocks the child would otherwise turn ordinary diagnostics into a
                // misleading timeout.
                let stderr_reader = child.stderr.take().map(|mut stderr| {
                    std::thread::spawn(move || {
                        let mut bytes = Vec::new();
                        stderr.read_to_end(&mut bytes).map(|_| bytes)
                    })
                });
                let timeout = std::time::Duration::from_secs(30);
                let start = std::time::Instant::now();
                let mut timed_out = false;
                let mut wait_error = None;
                let exit_status = loop {
                    match child.try_wait() {
                        Ok(Some(status)) => break Some(status),
                        Ok(None) if start.elapsed() > timeout => {
                            let _ = child.kill();
                            let _ = child.wait();
                            timed_out = true;
                            break None;
                        }
                        Ok(None) => std::thread::sleep(std::time::Duration::from_millis(50)),
                        Err(error) => {
                            let _ = child.kill();
                            let _ = child.wait();
                            wait_error = Some(error);
                            break None;
                        }
                    }
                };
                let stderr = match stderr_reader {
                    Some(reader) => reader
                        .join()
                        .map_err(|_| anyhow!("bsc stderr reader thread panicked"))??,
                    None => Vec::new(),
                };

                if timed_out {
                    if dump_typed_sexp {
                        // Truncate the sexp file (partial output is invalid)
                        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                        let _ = std::fs::write(&sexp_path, "");
                    }
                    let msg = format!(
                        "Timeout ({:.0}s) compiling `{module_name}`",
                        timeout.as_secs_f64()
                    );
                    log::warn!("{}", msg);
                    return Ok(Some(msg));
                }
                if let Some(error) = wait_error {
                    let msg = format!("bsc subprocess failed while waiting for `{module_name}`: {error}");
                    log::warn!("{msg}");
                    return Ok(Some(msg));
                }
                if let Some(status) = exit_status.filter(|status| !status.success()) {
                    let diagnostics = if dump_typed_sexp {
                        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                        std::fs::read_to_string(&sexp_path).unwrap_or_default()
                    } else {
                        String::from_utf8_lossy(&stderr).into_owned()
                    };

                    // An exit without a code represents a crash (for example, termination by a
                    // signal). Subprocess mode deliberately keeps crashes nonfatal.
                    if status.code().is_none() {
                        let msg = format!("bsc subprocess crashed for `{module_name}`: {diagnostics}");
                        log::warn!("{msg}");
                        return Ok(Some(msg));
                    }

                    return Err(anyhow!(if diagnostics.is_empty() {
                        format!("bsc exited with {status} compiling `{module_name}`")
                    } else {
                        diagnostics
                    }));
                }

                let warnings = if dump_typed_sexp {
                    let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                    extract_warning_prefix_from_sexp_file(&sexp_path).unwrap_or_default()
                } else {
                    compiler_output_to_string(&stderr)
                };
                return Ok(visible_compiler_warnings(&warnings, package.is_local_dep));
            }
            Err(e) => {
                log::warn!("Failed to spawn bsc subprocess: {e}");
            }
        }
        return Ok(None);
    }

    // Normal mode: run bsc via Command::output()
    // When generating sexp, redirect stderr directly to file to avoid buffering
    // huge output in memory (e.g., Icon.res produces 882MB of sexp).
    let sexp_file = if dump_typed_sexp {
        let path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        Some(std::fs::File::create(&path).map_err(|e| anyhow!("Failed to create sexp file: {e}"))?)
    } else {
        None
    };

    let to_mjs = Command::new(&compiler_info.bsc_path)
        .current_dir(&cwd)
        .args(to_mjs_args)
        .stderr(match sexp_file {
            Some(f) => std::process::Stdio::from(f),
            None => std::process::Stdio::piped(),
        })
        .output();

    match to_mjs {
        Ok(x) if !x.status.success() => {
            let stderr = if dump_typed_sexp {
                // stderr was redirected to file — read error from there
                let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
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
            let raw_stderr = compiler_output_to_string(&x.stderr);

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

                    let mut source_map = source.clone().into_os_string();
                    source_map.push(".map");
                    let source_map = PathBuf::from(source_map);
                    let mut destination_map = destination.clone().into_os_string();
                    destination_map.push(".map");
                    let destination_map = PathBuf::from(destination_map);

                    if source_map.exists() {
                        let _ = std::fs::copy(&source_map, &destination_map)
                            .expect("copying source map file failed");
                    } else {
                        let _ = std::fs::remove_file(&destination_map);
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
                    // Determine the correct JS file path based on in-source setting:
                    // - in-source: true  -> next to the source file (e.g., src/Foo.js)
                    // - in-source: false -> in lib/<module>/ directory (e.g., lib/es6/src/Foo.js)
                    let js_file = if spec.in_source {
                        helpers::get_source_file_from_rescript_file(
                            &Path::new(&package.path).join(path),
                            &root_config.get_suffix(&spec),
                        )
                    } else {
                        helpers::get_source_file_from_rescript_file(
                            &Path::new(&package.path)
                                .join("lib")
                                .join(spec.get_out_of_source_dir())
                                .join(path),
                            &root_config.get_suffix(&spec),
                        )
                    };

                    if js_file.exists() {
                        // Fail the build if post-build command fails (matches bsb behavior with &&)
                        // Run in the package's directory (where rescript.json is defined)
                        execute_post_build_command(&js_post_build.cmd, &js_file, &package.path)?;
                    }
                }
            }

            Ok(visible_compiler_warnings(&err, package.is_local_dep))
        }
    }
}

/// An in-process compile failure. A compiler diagnostic is reported as the
/// text bsc prints, like the subprocess path does.
fn in_process_compile_error(module_name: &str, err: anyhow::Error) -> anyhow::Error {
    match err.downcast::<rescript_compiler::driver::UserDiagnostic>() {
        Ok(diagnostic) => anyhow!("{}", diagnostic.output()),
        Err(err) => anyhow!("Compilation failed for {}: {}", module_name, err),
    }
}

fn visible_compiler_warnings(stderr: &str, is_local_dep: bool) -> Option<String> {
    if !helpers::contains_ascii_characters(stderr) {
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
                        match (module.last_compiled_cmt, module.last_compiled_cmi) {
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

    // The compiler can write a code frame that truncates a multi-byte character, so the
    // captured output is not always valid UTF-8. Decoding it must not panic.
    #[test]
    fn compiler_output_to_string_handles_invalid_utf8() {
        // 0xe2 0x80 is the start of an em dash (U+2014); the third byte is missing.
        let truncated = [b'W', b'a', b'r', b'n', b'i', b'n', b'g', b' ', 0xe2, 0x80];
        let decoded = compiler_output_to_string(&truncated);
        assert!(decoded.starts_with("Warning "));
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
            is_local_dep: true,
            is_root: true,
        }
    }

    fn test_module(package_name: &str, implementation_warning: Option<&str>) -> Module {
        Module {
            source_type: SourceType::SourceFile(SourceFile {
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
            last_compiled_cmi: None,
            last_compiled_cmt: None,
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
    fn typed_sexp_warning_prefix_is_removed_without_buffering_the_sexp() {
        let temp_dir = tempfile::tempdir().expect("temp directory should be created");
        let path = temp_dir.path().join("Module.sexp");
        let warning = "Warning number 26\nunused variable x\n";
        let sexp_body = "x".repeat(4 * 1024 * 1024);
        let sexp = format!("(structure\n{sexp_body})\n");
        let mut contents = warning.as_bytes().to_vec();
        contents.extend_from_slice(sexp.as_bytes());
        fs::write(&path, contents).expect("mixed compiler output should be written");

        let extracted =
            extract_warning_prefix_from_sexp_file(&path).expect("warning prefix should be extracted");

        assert_eq!(extracted, warning);
        assert_eq!(
            fs::metadata(&path).expect("sexp should remain").len(),
            sexp.len() as u64
        );
        let mut file = fs::File::open(&path).expect("sexp should open");
        let mut prefix = [0_u8; 10];
        file.read_exact(&mut prefix).expect("sexp prefix should read");
        assert_eq!(&prefix, b"(structure");
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
