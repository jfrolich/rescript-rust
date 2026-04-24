#![allow(clippy::too_many_arguments)]

mod dependency_cycle;

use super::build_types::*;
use super::logs;
use super::packages;
use crate::config;
use crate::config::Config;
use rescript_compiler::cmi::persistent_env::{
    InMemoryModuleInfo, ModuleRegistry, PersistentEnv, read_cmj_module_metadata,
};
use crate::helpers;
use crate::helpers::StrippedVerbatimPath;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::{Result, anyhow};
use console::style;
use log::{debug, info, trace, warn};
use rayon::prelude::*;
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::mpsc;
use std::time::SystemTime;

/// Execute js-post-build command for a compiled JavaScript file.
/// The command runs in the directory containing the rescript.json that defines it.
/// The absolute path to the JS file is passed as an argument.
fn execute_post_build_command(cmd: &str, js_file_path: &Path, working_dir: &Path) -> Result<()> {
    let full_command = format!("{} {}", cmd, js_file_path.display());

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
}

/// Compute the critical-path priority of every module in the universe:
/// `priority(m) = 1 + max(priority(d) for d in in-universe dependents of m)`.
/// Runs a reverse-topological sweep from leaves to roots. Modules stuck in a
/// cycle get priority 0, and the actual cycle is diagnosed later by
/// `dependency_cycle::find` when the dispatcher detects a stall.
fn compute_critical_path_priorities(
    universe: &AHashSet<String>,
    build_state: &BuildState,
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
        priorities.insert(name.clone(), max_dep_priority + 1);

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
    module_name: &str,
    is_dirty: bool,
    warn_error_override: Option<String>,
    subprocess: bool,
    dump_typed_sexp: bool,
) -> CompletionMsg {
    let module = build_state.get_module(module_name).unwrap();
    let package = build_state
        .get_package(&module.package_name)
        .expect("Package not found");

    if !is_dirty {
        return CompletionMsg {
            module_name: module_name.to_string(),
            result: Ok(None),
            interface_result: Some(Ok(None)),
            is_clean: true,
            is_compiled: false,
        };
    }

    // In-process mode: bypass the bsc subprocess entirely and run the Rust
    // compiler in-thread. The caller has already staged runtime modules and
    // namespace signatures into the shared registry, and the DAG scheduler
    // guarantees all dependencies of this module are registered before it
    // is dispatched.
    if build_command_state.build_mode().is_in_process() {
        if let SourceType::SourceFile(_) = &module.source_type {
            let interface_generation_before =
                build_command_state.get_interface_generation(module_name);
            let result = compile_module_in_process(
                package,
                module,
                module_name,
                registry_snapshot,
                build_state,
                build_command_state,
            );
            let interface_generation_after =
                build_command_state.get_interface_generation(module_name);
            let is_clean_interface = matches!(&result, Ok(None))
                && interface_generation_before.is_some()
                && interface_generation_before == interface_generation_after;
            return CompletionMsg {
                module_name: module_name.to_string(),
                result,
                interface_result: None,
                is_clean: is_clean_interface,
                is_compiled: true,
            };
        }
    }

    match &module.source_type {
        SourceType::MlMap(_) => {
            // The mlmap is compiled during AST generation; the entry here just
            // marks it compiled so its namespace members can proceed.
            CompletionMsg {
                module_name: package.namespace.to_suffix().unwrap(),
                result: Ok(None),
                interface_result: Some(Ok(None)),
                is_clean: false,
                is_compiled: false,
            }
        }
        SourceType::SourceFile(source_file) => {
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
            }
        }
    }
}

/// Extract sexp output from bsc stderr.
/// When -dtyped-sexp-locs is passed, bsc writes the sexp to stderr.
/// The sexp starts with "(structure" or "(signature" and continues to the end.
/// Everything before that is warnings.
/// Returns (warnings, Option<sexp>).
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

    // In --in-process mode, purge deleted/renamed modules from the in-memory
    // registries so stale entries don't remain resolvable in watch mode.
    if build_state.build_mode().is_in_process() {
        build_state.purge_deleted_modules(&build_state.build_state.deleted_modules.clone());
    }

    // In --in-process mode, synthesize namespace module signatures in memory
    // before any source modules are compiled. Source modules may use `-open Namespace`,
    // so the namespace signature must be available in the PersistentEnv first.
    if build_state.build_mode().is_in_process() {
        register_namespace_signatures(build_state);
        register_source_fallback_paths(build_state);
        // Pre-compile all @rescript/runtime modules into the registry.
        // In in-process mode, the registry is the sole source of truth —
        // no CMI fallback. Every dependency must be in the registry.
        let pre_compile_result = std::thread::scope(|scope| {
            let handle = std::thread::Builder::new()
                .name("rewatch-runtime-precompile".to_string())
                .stack_size(64 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    pre_compile_runtime_modules(build_state);
                });

            match handle {
                Ok(handle) => handle.join().map_err(|panic| {
                    if let Some(s) = panic.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = panic.downcast_ref::<&str>() {
                        s.to_string()
                    } else {
                        "unknown".to_string()
                    }
                }),
                Err(err) => Err(format!("failed to spawn runtime pre-compilation thread: {err}")),
            }
        });
        if let Err(msg) = pre_compile_result {
            eprintln!("Warning: runtime pre-compilation panicked: {}", msg);
        }
        // Clear source-fallback paths after pre-compilation.
        build_state
            .module_registry
            .lock()
            .unwrap()
            .source_fallback_paths
            .clear();
    }

    // Expand the compile universe: every dirty module plus everything that
    // transitively depends on it.
    let mut compile_universe = dirty_modules.clone();
    let mut frontier = compile_universe.clone();
    loop {
        let mut dependents: AHashSet<String> = AHashSet::new();
        for module_name in frontier.iter() {
            dependents.extend(build_state.get_module(module_name).unwrap().dependents.clone());
        }
        frontier = dependents
            .difference(&compile_universe)
            .cloned()
            .collect::<AHashSet<String>>();
        if frontier.is_empty() {
            break;
        }
        compile_universe.extend(frontier.iter().cloned());
    }

    let compile_universe_count = compile_universe.len();
    set_length(compile_universe_count as u64);

    let priorities = compute_critical_path_priorities(&compile_universe, &build_state.build_state);

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

    // Snapshot the registry once before the scope. The DAG scheduler only
    // dispatches a module once all its dependencies have completed, so their
    // registrations have already been published to the shared registry —
    // but workers need a lock-free view, so each worker gets a snapshot taken
    // at spawn time. (Taking one per spawn is cheap vs. type-checking.)
    let in_process_mode = build_state.build_mode().is_in_process();

    let (tx, rx) = mpsc::channel::<CompletionMsg>();
    // Bound concurrency to rayon's pool size so the priority heap actually
    // orders work — dumping everything into rayon's deque would defeat #2.
    let capacity = rayon::current_num_threads().max(1);

    let mut completed: AHashSet<String> = AHashSet::new();
    let mut results_buffer: Vec<CompletionMsg> = Vec::with_capacity(compile_universe_count);
    let mut has_errors = false;
    let mut stalled = false;

    rayon::in_place_scope(|scope| {
        let mut in_flight: usize = 0;
        loop {
            while in_flight < capacity && !has_errors {
                let Some(work) = ready_heap.pop() else { break };
                let module_name = work.module_name.clone();
                let is_dirty = dirty_set.contains(&module_name);
                let warn_override = warn_error_override.clone();
                let tx = tx.clone();
                let inc_ref = &inc;
                in_flight += 1;
                // Take a per-spawn snapshot of the registry so workers have
                // a stable view including any deps that published registry
                // entries before this module was unblocked. Subprocess mode
                // ignores the snapshot.
                let registry_snapshot: ModuleRegistry = if in_process_mode {
                    build_state.snapshot_module_registry()
                } else {
                    ModuleRegistry::new()
                };
                scope.spawn(move |_| {
                    let msg = compile_one(
                        build_state_ref,
                        build_command_state_ref,
                        &registry_snapshot,
                        &module_name,
                        is_dirty,
                        warn_override,
                        subprocess,
                        dump_typed_sexp,
                    );
                    if show_progress {
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

            let Ok(msg) = rx.recv() else { break };
            in_flight -= 1;

            if msg.result.is_err() || msg.interface_result.as_ref().is_some_and(|r| r.is_err()) {
                has_errors = true;
            }

            let is_clean = msg.is_clean;
            let finished_name = msg.module_name.clone();
            completed.insert(finished_name.clone());
            results_buffer.push(msg);

            // Look up dependents from the node the scheduler scheduled under —
            // for mlmap, compile_one returns the namespace suffix, which is the
            // key modules use to refer to the namespace entry.
            let dependents = build_state.get_module(&finished_name).unwrap().dependents.clone();

            for dep in &dependents {
                if !compile_universe.contains(dep) {
                    continue;
                }
                if !is_clean {
                    dirty_set.insert(dep.clone());
                }
                let count = pending_deps.get_mut(dep).unwrap();
                *count -= 1;
                if *count == 0 && !completed.contains(dep) {
                    ready_heap.push(WorkUnit {
                        priority: priorities[dep],
                        module_name: dep.clone(),
                    });
                }
            }
        }
    });
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
                module.last_compiled_cmi = Some(SystemTime::now());
                module.last_compiled_cmt = Some(SystemTime::now());
            }

            (compile_warning, compile_error, interface_warning, interface_error)
        };

        if let Some(warning) = compile_warning {
            logs::append(package, &warning);
            compile_warnings.push_str(&warning);
        }
        if let Some(error) = compile_error {
            logs::append(package, &error);
            compile_errors.push_str(&error);
        }
        if let Some(warning) = interface_warning {
            logs::append(package, &warning);
            compile_warnings.push_str(&warning);
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

    // Collect warnings from modules that were not recompiled in this build
    // but still have stored warnings from a previous compilation.
    // This ensures warnings are not lost during incremental builds in watch mode.
    for (module_name, module) in build_state.modules.iter() {
        if compile_universe.contains(module_name) {
            continue;
        }
        if let SourceType::SourceFile(ref source_file) = module.source_type {
            let package = build_state.get_package(&module.package_name);
            if let Some(ref warning) = source_file.implementation.compile_warnings {
                if let Some(package) = package {
                    logs::append(package, warning);
                }
                compile_warnings.push_str(warning);
            }
            if let Some(ref interface) = source_file.interface
                && let Some(ref warning) = interface.compile_warnings
            {
                if let Some(package) = package {
                    logs::append(package, warning);
                }
                compile_warnings.push_str(warning);
            }
        }
    }

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

/// Build `CompilerOptions` for an in-process compilation from the package config.
fn build_compiler_options(
    package: &packages::Package,
    module_name: &str,
    source_file_path: &Path,
    build_state: &BuildState,
) -> Result<rescript_compiler::driver::CompilerOptions> {
    let root_config = build_state.get_root_config();
    let project_context = &build_state.project_context;

    // Parse package compiler-flags for flags the in-process compiler needs to honor.
    // In the subprocess path, these are passed as raw CLI args to bsc.
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let mut nopervasives = false;
    let mut flag_open_modules: Vec<String> = Vec::new();
    {
        let mut iter = bsc_flags.iter();
        while let Some(flag) = iter.next() {
            match flag.as_str() {
                "-nopervasives" => nopervasives = true,
                "-open" => {
                    if let Some(mod_name) = iter.next() {
                        flag_open_modules.push(mod_name.clone());
                    }
                }
                _ => {} // Other flags (-nostdlib, -make-runtime, etc.) are not needed in-process
            }
        }
    }

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


    // Add dev dependency paths if the module is type:dev
    // (omitted for simplicity in first cut; can be added later)

    // Extract JSX version from root config
    let jsx_version = root_config
        .jsx
        .as_ref()
        .and_then(|jsx| jsx.version)
        .filter(|&v| v == 4);

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
    open_modules.extend(flag_open_modules);

    // Runtime path
    let runtime_path = get_runtime_path(&package.config, project_context).ok();

    // Source filename for interface constraint resolution
    let source_filename = Some(source_file_path.to_string_lossy().to_string());

    // Output path for JS import resolution
    let output_path = root_config.get_package_specs().first().map(|spec| {
        let suffix = root_config.get_suffix(spec);
        if spec.in_source {
            let source_abs = Path::new(&package.path).join(source_file_path);
            helpers::get_source_file_from_rescript_file(&source_abs, &suffix)
        } else {
            let js_relative =
                helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
            Path::new(&package.path)
                .join("lib")
                .join(spec.get_out_of_source_dir())
                .join(js_relative)
        }
    });

    Ok(rescript_compiler::driver::CompilerOptions {
        include_paths,
        runtime_path,
        open_modules,
        source_filename,
        output_path,
        jsx_version,
        nopervasives,
        module_name: Some(module_name.to_string()),
        ..Default::default()
    })
}

/// Write JS output to the correct location(s) based on package specs.
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
            let js_relative =
                helpers::get_source_file_from_rescript_file(source_file_path, &suffix);
            Path::new(&package.path)
                .join("lib")
                .join(out_dir)
                .join(js_relative)
        };

        if let Some(parent) = js_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&js_path, js_output)?;
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
            packages::Namespace::NamespaceWithEntry {
                namespace: _,
                entry,
            } => Some(entry.as_str()),
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
            .map(|path| {
                helpers::file_path_to_module_name(path, &packages::Namespace::NoNamespace)
            })
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
            build_state.register_namespace_in_registry(&namespace_suffix, &module_aliases);
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
        .source_fallback_paths = fallback_paths;
}

/// Pre-compile all @rescript/runtime modules into the ModuleRegistry before the
/// main compile loop. This eliminates source-fallback recursion during parallel
/// compilation: without pre-compilation, every module that implicitly needs
/// Pervasives (via `-open Pervasives`) would trigger recursive source-fallback
/// type-checking, creating deep stack frames that overflow worker thread stacks.
///
/// After this step, all runtime modules (Pervasives, Js, Belt, etc.) are in the
/// registry and found directly without any source-fallback.
///
/// Runs on a dedicated thread with a large stack to handle any remaining
/// source-fallback chains during the pre-compilation itself.
fn pre_compile_runtime_modules(build_state: &BuildCommandState) {
    let runtime_root = &build_state.build_state.compiler_info.runtime_path;
    // Runtime .res sources live in lib/ocaml/ alongside the .cmi/.cmj files
    let runtime_path = runtime_root.join("lib").join("ocaml");

    // Collect all runtime .res files and check for .resi siblings
    let mut runtime_modules: Vec<(String, PathBuf, Option<PathBuf>)> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&runtime_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("res") {
                continue;
            }
            if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                let module_name = {
                    let mut chars = stem.chars();
                    match chars.next() {
                        None => continue,
                        Some(ch) => format!("{}{}", ch.to_uppercase(), chars.as_str()),
                    }
                };
                let resi_path = path.with_extension("resi");
                let has_resi = resi_path.exists();
                runtime_modules.push((
                    module_name,
                    path.clone(),
                    if has_resi { Some(resi_path) } else { None },
                ));
            }
        }
    }

    if runtime_modules.is_empty() {
        return;
    }

    // Sort for deterministic compilation order.
    // Put Pervasives first since everything depends on it.
    runtime_modules.sort_by(|a, b| {
        let a_priority = if a.0 == "Pervasives" { 0 } else { 1 };
        let b_priority = if b.0 == "Pervasives" { 0 } else { 1 };
        a_priority.cmp(&b_priority).then_with(|| a.0.cmp(&b.0))
    });

    let module_count = runtime_modules.len();
    let source_paths: AHashMap<String, PathBuf> = runtime_modules
        .iter()
        .map(|(module_name, res_path, _)| (module_name.clone(), res_path.clone()))
        .collect();

    rescript_compiler::ident::Ident::set_current_time(999);
    let id_gen = rescript_compiler::context::IdGenerator::with_start_stamp(999);
    let _predef_stamp = id_gen.next_stamp();
    let type_ctx = rescript_compiler::types::TypeContext::new(&id_gen);
    type_ctx.set_load_paths(vec![runtime_path.clone()]);

    let mut pers_env = PersistentEnv::new();
    pers_env.set_load_path(vec![runtime_path.clone()]);

    let mut loaded = 0;
    for (module_name, _, _) in &runtime_modules {
        if pers_env.find_pers_struct(module_name, &type_ctx).is_some() {
            loaded += 1;
        } else {
            debug!("Runtime CMI load failed for {}", module_name);
        }
    }

    let (mut portables, alias_rewrites) = pers_env.extract_all_cached_modules(&type_ctx);
    let mut registry = build_state.module_registry.lock().unwrap();
    registry.alias_rewrites.extend(alias_rewrites);

    let mut registered = 0;
    for (module_name, portable) in portables.drain() {
        let source_path = source_paths
            .get(&module_name)
            .cloned()
            .unwrap_or_else(|| runtime_path.join(format!("{module_name}.res")));
        let cmj_metadata = read_cmj_module_metadata(&runtime_path.join(format!("{module_name}.cmj")));
        registry.register_module(
            &module_name,
            portable,
            InMemoryModuleInfo {
                source_path,
                is_pure: cmj_metadata
                    .as_ref()
                    .map(|metadata| metadata.is_pure)
                    .unwrap_or(true),
                cmj_export_constants: cmj_metadata
                    .map(|metadata| metadata.export_constants)
                    .unwrap_or_default(),
                is_runtime: true,
            },
            AHashMap::new(),
        );
        registered += 1;
    }

    debug!(
        "Pre-loaded {}/{} runtime CMIs into registry ({} cached modules)",
        loaded, module_count, registered
    );
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
/// Returns Ok(None) on success, Ok(Some(warning)) on success with warnings,
/// Err on failure.
fn compile_module_in_process(
    package: &packages::Package,
    module: &Module,
    module_name: &str,
    registry: &ModuleRegistry,
    build_state: &BuildState,
    build_command_state: &BuildCommandState,
) -> Result<Option<String>> {
    let source_file = match &module.source_type {
        SourceType::SourceFile(sf) => sf,
        _ => return Ok(None), // MlMap handled elsewhere
    };

    let implementation_path = &source_file.implementation.path;
    let has_interface = source_file.interface.is_some();
    let root_config = build_command_state.get_root_config();

    // Build compiler options from package config
    let options =
        build_compiler_options(package, module_name, implementation_path, build_state)?;

    let source_abs = Path::new(&package.path).join(implementation_path);
    let is_runtime = package.name == "@rescript/runtime";
    let provisional_is_pure = true;

    // For .resi + .res, we need the .resi to be in the registry before compiling .res.
    // Build a local registry that includes the .resi result (if any).
    let mut local_registry = registry.clone();

    // Register this module's metadata in the local registry
    local_registry.module_info.insert(
        module_name.to_string(),
        rescript_compiler::cmi::persistent_env::InMemoryModuleInfo {
            source_path: source_abs.clone(),
            is_pure: provisional_is_pure,
            cmj_export_constants: AHashMap::new(),
            is_runtime,
        },
    );

    // Step 1: If .resi exists, typecheck the interface first
    if let Some(interface) = &source_file.interface {
        let intf_source_abs = Path::new(&package.path).join(&interface.path);
        let intf_key = format!("{module_name}:intf");
        let intf_result = match build_command_state.get_stored_ast(&intf_key) {
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
        .map_err(|e| anyhow!("Interface typecheck failed for {}: {}", module_name, e));

        let intf_result = match intf_result {
            Ok(r) => r,
            Err(e) => {
                let warning = format!("{}", e);
                eprintln!("{}", warning);
                return Ok(Some(warning));
            }
        };

        // Register the .resi's PersStruct in the local registry so the
        // .res compilation can find it for moregen constraints.
        let intf_fingerprint = intf_result
            .pers_struct
            .as_ref()
            .map(|ps| ps.fingerprint)
            .unwrap_or(0);
        if let Some(ps) = intf_result.pers_struct {
            local_registry
                .cached_modules
                .insert(module_name.to_string(), Arc::new(ps.clone()));
            // Update the shared registry with the .resi result
            build_command_state.update_module_registry(
                module_name,
                ps,
                source_abs.clone(),
                provisional_is_pure,
                AHashMap::new(),
                is_runtime,
                intf_result.new_alias_rewrites,
            );
        }

        // Register the interface signature in rewatch's in-memory registry
        build_command_state.register_in_memory_interface(
            module_name.to_string(),
            intf_result.signature,
            intf_fingerprint,
            provisional_is_pure,
        );
    }

    // Step 2: Compile the implementation
    let impl_key = format!("{module_name}:impl");
    let compile_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match build_command_state.get_stored_ast(&impl_key) {
            Some(StoredAst::Structure(stored)) => {
                rescript_compiler::driver::compile_preprocessed_structure_in_process(
                    &stored.arena,
                    &stored.structure,
                    &source_abs.to_string_lossy(),
                    module_name,
                    &options,
                    &local_registry,
                    has_interface,
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
    }));

    let compile_result = match compile_result {
        Ok(Ok(result)) => result,
        Ok(Err(e)) => {
            // Return as a warning, not an error. The module won't produce JS
            // output but the build should continue for other modules.
            let warning = format!("Compilation failed for {}: {}", module_name, e);
            eprintln!("{}", warning);
            return Ok(Some(warning));
        }
        Err(panic) => {
            let msg = if let Some(s) = panic.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic".to_string()
            };
            // Return as a warning, not an error. The module won't produce JS
            // output but the build should continue for other modules.
            let warning = format!("Compilation panicked for {}: {}", module_name, msg);
            eprintln!("{}", warning);
            return Ok(Some(warning));
        }
    };

    // Update the shared registry with the implementation's PersStruct
    let impl_fingerprint = compile_result
        .pers_struct
        .as_ref()
        .map(|ps| ps.fingerprint)
        .unwrap_or(0);
    let is_pure = compile_result.is_pure;
    let cmj_export_constants = compile_result.cmj_export_constants.clone();
    if let Some(ps) = compile_result.pers_struct {
        build_command_state.update_module_registry(
            module_name,
            ps,
            source_abs.clone(),
            is_pure,
            cmj_export_constants,
            is_runtime,
            compile_result.new_alias_rewrites,
        );
    }

    // Register the implementation's inferred signature if no .resi
    if !has_interface {
        build_command_state.register_in_memory_interface(
            module_name.to_string(),
            compile_result.signature,
            impl_fingerprint,
            is_pure,
        );
    }

    // Step 3: Write only JS output (no compiler assets)
    write_js_output(
        &compile_result.js_output,
        package,
        implementation_path,
        root_config,
    )?;

    // Execute js-post-build command if configured
    if let Some(js_post_build) = &package.config.js_post_build {
        for spec in root_config.get_package_specs() {
            let suffix = root_config.get_suffix(&spec);
            let js_file = if spec.in_source {
                helpers::get_source_file_from_rescript_file(
                    &Path::new(&package.path).join(implementation_path),
                    &suffix,
                )
            } else {
                let out_dir = spec.get_out_of_source_dir();
                let js_relative =
                    helpers::get_source_file_from_rescript_file(implementation_path, &suffix);
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

    Ok(None)
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
                let timeout = std::time::Duration::from_secs(30);
                let start = std::time::Instant::now();
                let mut timed_out = false;
                let mut exit_status = None;
                loop {
                    match child.try_wait() {
                        Ok(Some(status)) => {
                            exit_status = Some(status);
                            break;
                        }
                        Ok(None) if start.elapsed() > timeout => {
                            let _ = child.kill();
                            let _ = child.wait();
                            timed_out = true;
                            break;
                        }
                        Ok(None) => {
                            std::thread::sleep(std::time::Duration::from_millis(50))
                        }
                        Err(_) => break,
                    }
                }

                if timed_out {
                    if dump_typed_sexp {
                        // Truncate the sexp file (partial output is invalid)
                        let sexp_path = ocaml_build_path_abs.join(format!("{basename}.sexp"));
                        let _ = std::fs::write(&sexp_path, "");
                    }
                    let msg = format!("Timeout ({:.0}s) compiling `{module_name}`", timeout.as_secs_f64());
                    log::warn!("{}", msg);
                    return Ok(Some(msg));
                } else if exit_status.is_some_and(|s| !s.success()) {
                    log::warn!("bsc subprocess crashed for `{module_name}`");
                }
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
            let raw_stderr = String::from_utf8_lossy(&x.stderr).to_string();

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

            if helpers::contains_ascii_characters(&err) {
                if package.is_local_dep {
                    Ok(Some(err))
                } else {
                    // Warnings from external deps are suppressed by default —
                    // users can't act on them. A small allow-list of critical
                    // deprecations still gets through so breakage signals are
                    // visible (and can be reported upstream).
                    Ok(retain_critical_external_warnings(&err))
                }
            } else {
                Ok(None)
            }
        }
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
                        match (module.last_compiled_cmt, module.last_compiled_cmt) {
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
}
