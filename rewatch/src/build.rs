pub mod build_types;
pub mod clean;
pub mod compile;
pub mod compiler_info;
pub mod deps;
pub mod incremental;
pub mod logs;
pub mod namespaces;
pub mod packages;
pub mod parse;
pub mod plan;
pub mod pools;
pub mod qos;
pub mod state_db;
pub mod tooling;

use self::parse::parser_args;
use crate::build::compile::mark_modules_with_deleted_deps_dirty;
use crate::build::compiler_info::{CompilerCheckResult, write_compiler_info};
use crate::config::SourceMapCommand;
use crate::helpers::emojis::*;
use crate::helpers::{self};
use crate::lock::{LockKind, drop_lock, get_lock_or_exit};
use crate::project_context::ProjectContext;
use anyhow::{Context, Result, anyhow};
use build_types::*;
use console::style;
use indicatif::{ProgressBar, ProgressStyle};
use log::log_enabled;
use serde::Serialize;
use std::fmt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use tracing::{info_span, instrument};

fn is_dirty(module: &Module) -> bool {
    match module.source_type {
        SourceType::SourceFile(SourceFile {
            implementation: Implementation {
                parse_dirty: true, ..
            },
            ..
        }) => true,
        SourceType::SourceFile(SourceFile {
            interface: Some(Interface {
                parse_dirty: true, ..
            }),
            ..
        }) => true,
        SourceType::SourceFile(_) => false,
        SourceType::MlMap(MlMap {
            parse_dirty: dirty, ..
        }) => dirty,
    }
}

/// Mark every module for parsing and compilation. Namespace maps are not
/// reparsed: they are not source files, and a build that has to compile every
/// module does not otherwise report them as parsed.
fn mark_modules_dirty(build_state: &mut BuildCommandState) {
    for module in build_state.modules.values_mut() {
        module.compile_dirty = true;
        match &mut module.source_type {
            SourceType::SourceFile(source_file) => {
                source_file.implementation.parse_dirty = true;
                if let Some(interface) = &mut source_file.interface {
                    interface.parse_dirty = true;
                }
            }
            SourceType::MlMap(_) => {}
        }
    }
}

#[derive(Serialize, Debug, Clone)]
struct CompilerArgs {
    pub compiler_args: Vec<String>,
    pub parser_args: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilationOutcome {
    Clean,
    Warnings,
}

fn has_output(output: &str) -> bool {
    helpers::has_ascii_alphanumeric(output)
}

fn has_config_warnings(build_state: &BuildCommandState) -> bool {
    build_state.packages.iter().any(|(_, package)| {
        package.is_local_dep
            && (!package.config.get_unsupported_fields().is_empty()
                || !package.config.get_unknown_fields().is_empty())
    })
}

pub fn format_finished_compilation_message(
    compilation_kind: Option<&str>,
    outcome: CompilationOutcome,
    duration: Duration,
) -> String {
    let compilation_kind = compilation_kind
        .map(|kind| format!("{kind} "))
        .unwrap_or_default();
    let (status, warning_suffix) = match outcome {
        CompilationOutcome::Clean => (CHECKMARK, ""),
        CompilationOutcome::Warnings => (WARNING, " with warnings"),
    };

    format!(
        "{LINE_CLEAR}{status}Finished {compilation_kind}compilation{warning_suffix} in {:.2}s",
        duration.as_secs_f64()
    )
}

#[instrument(name = "rewatch.compiler_args", skip_all, fields(file_path = %rescript_file_path.display()))]
pub fn get_compiler_args(rescript_file_path: &Path) -> Result<String> {
    let filename = &helpers::get_abs_path(rescript_file_path);
    let current_package = helpers::get_abs_path(
        &helpers::get_nearest_config(rescript_file_path).context("Couldn't find package root")?,
    );
    let project_context = ProjectContext::new(&current_package)?;

    let is_type_dev = match filename.strip_prefix(&current_package) {
        Err(_) => false,
        Ok(relative_path) => project_context
            .current_config
            .find_is_type_dev_for_path(relative_path),
    };

    // make PathBuf from package root and get the relative path for filename
    let relative_filename = filename.strip_prefix(&current_package).with_context(|| {
        format!(
            "{} is not inside package {}",
            filename.display(),
            current_package.display()
        )
    })?;

    let file_path = current_package.join(filename);
    let contents = helpers::read_file(&file_path).context("Error reading file")?;

    let (ast_path, parser_args) = parser_args(
        &project_context,
        &project_context.current_config,
        relative_filename,
        &contents,
        /* is_local_dep */ true,
        /* warn_error_override */ None,
    )?;
    let is_interface = filename.to_string_lossy().ends_with('i');
    let has_interface = if is_interface {
        true
    } else {
        let mut interface_filename = filename.to_string_lossy().to_string();
        interface_filename.push('i');
        PathBuf::from(&interface_filename).exists()
    };
    let compiler_args = compile::compiler_args(
        &project_context.current_config,
        &ast_path,
        relative_filename,
        is_interface,
        has_interface,
        &project_context,
        &None,
        is_type_dev,
        true,
        None, // No warn_error_override for compiler-args command
        SourceMapCommand::Build,
        &[], // Source dirs not available outside full build; gentype falls back to defaults.
    )?;

    let result = serde_json::to_string_pretty(&CompilerArgs {
        compiler_args,
        parser_args,
    })?;

    Ok(result)
}

/// The content hash of the executable at `path`. Hashing the whole binary
/// (tens of megabytes) on every build is a noticeable part of a small
/// rebuild, so the hash is kept in a file in the temporary directory with the
/// executable's size, modification and change times and inode, and reused
/// while those are the same (replacing or rewriting the binary changes them).
fn executable_hash(path: &Path) -> Option<blake3::Hash> {
    let metadata = std::fs::metadata(path).ok()?;
    let mut stamp = format!(
        "{}\n{}\n{}",
        path.display(),
        metadata.len(),
        metadata
            .modified()
            .ok()
            .map(state_db::nanos_from_time)
            .unwrap_or(0)
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        stamp.push_str(&format!(
            "\n{}\n{}.{}",
            metadata.ino(),
            metadata.ctime(),
            metadata.ctime_nsec()
        ));
    }
    let cache = std::env::temp_dir().join(format!(
        "rescript-exe-{}.hash",
        &blake3::hash(path.as_os_str().as_encoded_bytes()).to_hex()[..16]
    ));
    if let Ok(cached) = std::fs::read_to_string(&cache)
        && let Some((cached_stamp, hash)) = cached.rsplit_once('\n')
        && cached_stamp == stamp
        && let Ok(hash) = blake3::Hash::from_hex(hash)
    {
        return Some(hash);
    }
    let hash = helpers::compute_file_hash(path)?;
    let tmp = cache.with_extension(format!("tmp{}", std::process::id()));
    if std::fs::write(&tmp, format!("{stamp}\n{}", hash.to_hex())).is_ok() {
        let _ = std::fs::rename(&tmp, &cache);
    }
    Some(hash)
}

pub fn get_compiler_info(project_context: &ProjectContext) -> Result<CompilerInfo> {
    // Builds compile with the compiler linked into this executable, so its
    // identity invalidates previous builds.
    let bsc_path = std::env::current_exe()
        .and_then(|path| path.canonicalize())
        .context("Could not resolve the rescript executable")?;
    let bsc_hash = executable_hash(&bsc_path).ok_or(anyhow!(
        "Failed to compute bsc hash for {}",
        bsc_path.to_string_lossy()
    ))?;
    let runtime_path = compile::get_runtime_path(&project_context.current_config, project_context)?;
    Ok(CompilerInfo {
        bsc_path,
        bsc_hash,
        runtime_path,
    })
}

#[allow(clippy::too_many_arguments)]
#[instrument(name = "build.initialize", skip_all)]
pub fn initialize_build(
    default_timing: Option<Duration>,
    filter: &Option<regex::Regex>,
    show_progress: bool,
    path: &Path,
    plain_output: bool,
    warn_error: Option<String>,
    prod: bool,
    features: Option<Vec<String>>,
    source_map_command: SourceMapCommand,
) -> Result<BuildCommandState> {
    let _span = info_span!(
        "build.initialize",
        working_dir = %path.display(),
        prod
    )
    .entered();
    let project_context = ProjectContext::new(path)?;
    let timing_clean_start = Instant::now();
    // Hashing the compiler binary is independent of package discovery, so
    // overlap the two.
    let (compiler, packages) = std::thread::scope(|scope| {
        let compiler = scope.spawn(|| get_compiler_info(&project_context));
        let packages = packages::make(filter, &project_context, show_progress, prod, features.as_ref());
        let compiler = compiler
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        (compiler, packages)
    });
    let compiler = compiler?;
    let packages = packages?;
    phase_mark("init:packages-make");

    let source_map_args = project_context
        .get_root_config()
        .get_source_map_args(source_map_command);
    // Read before `verify_compiler_info` may clean a package's build state.
    let metas = compiler_info::read_metas(&packages);
    let recorded_outputs = clean::recorded_outputs(&metas);
    let compiler_check =
        compiler_info::verify_compiler_info_with(&packages, &compiler, &source_map_args, &metas);

    if !packages::validate_packages_dependencies(&packages) {
        return Err(anyhow!("Failed to validate package dependencies"));
    }

    let mut build_state = BuildCommandState::new(
        path.to_path_buf(),
        project_context,
        packages,
        compiler,
        warn_error,
        features,
        source_map_command,
    );
    phase_mark("init:validate");
    build_state.recorded_outputs = recorded_outputs;
    packages::parse_packages(&mut build_state)?;
    phase_mark("init:parse-packages");

    let (diff_cleanup, total_cleanup) = clean::cleanup_previous_in_process_build(&mut build_state);
    phase_mark("init:read-compile-state");
    phase_mark("init:cleanup-previous");
    let timing_clean_total = timing_clean_start.elapsed();

    if show_progress {
        if plain_output {
            if let CompilerCheckResult::CleanedPackagesDueToCompiler = compiler_check {
                // Snapshot-friendly output (no progress prefixes or emojis)
                println!("Cleaned previous build due to compiler update");
            }
            println!("Cleaned {diff_cleanup}/{total_cleanup}")
        } else {
            if let CompilerCheckResult::CleanedPackagesDueToCompiler = compiler_check {
                println!(
                    "{}{} {}Cleaned previous build due to compiler update",
                    LINE_CLEAR,
                    style("[1/3]").bold().dim(),
                    SWEEP
                );
            }
            println!(
                "{}{} {}Cleaned {}/{} in {:.2}s",
                LINE_CLEAR,
                style("[1/3]").bold().dim(),
                SWEEP,
                diff_cleanup,
                total_cleanup,
                default_timing.unwrap_or(timing_clean_total).as_secs_f64()
            );
        }
    }

    Ok(build_state)
}

fn format_step(current: usize, total: usize) -> console::StyledObject<String> {
    style(format!("[{current}/{total}]")).bold().dim()
}

#[derive(Debug, Clone)]
pub enum IncrementalBuildErrorKind {
    SourceFileParseError,
    CompileError(Option<String>),
}

#[derive(Debug, Clone)]
pub struct IncrementalBuildError {
    pub plain_output: bool,
    pub kind: IncrementalBuildErrorKind,
}

impl fmt::Display for IncrementalBuildError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.kind {
            IncrementalBuildErrorKind::SourceFileParseError => {
                if self.plain_output {
                    write!(f, "{LINE_CLEAR}  Could not parse Source Files",)
                } else {
                    write!(f, "{LINE_CLEAR}  {CROSS}Could not parse Source Files",)
                }
            }
            IncrementalBuildErrorKind::CompileError(Some(e)) => {
                if self.plain_output {
                    write!(f, "{LINE_CLEAR}  Failed to Compile. Error: {e}",)
                } else {
                    write!(f, "{LINE_CLEAR}  {CROSS}Failed to Compile. Error: {e}",)
                }
            }
            IncrementalBuildErrorKind::CompileError(None) => {
                if self.plain_output {
                    write!(f, "{LINE_CLEAR}  Failed to Compile. See Errors Above",)
                } else {
                    write!(f, "{LINE_CLEAR}  {CROSS}Failed to Compile. See Errors Above",)
                }
            }
        }
    }
}

pub fn with_build_lock<T>(path: &Path, f: impl FnOnce() -> T) -> T {
    let build_folder = path.to_string_lossy().to_string();
    let _lock = get_lock_or_exit(LockKind::Build, &build_folder);
    let result = f();
    let _lock = drop_lock(LockKind::Build, &build_folder);
    result
}

#[instrument(name = "build.incremental", skip_all, fields(module_count = build_state.modules.len()))]
pub fn incremental_build(
    build_state: &mut BuildCommandState,
    default_timing: Option<Duration>,
    initial_build: bool,
    show_progress: bool,
    only_incremental: bool,
    plain_output: bool,
) -> Result<CompilationOutcome, IncrementalBuildError> {
    let build_folder = build_state.root_folder.clone();
    with_build_lock(&build_folder, || {
        incremental_build_without_lock(
            build_state,
            default_timing,
            initial_build,
            show_progress,
            only_incremental,
            plain_output,
        )
    })
}

// `build` needs to lock before initialization because initialization mutates previous
// build artifacts. Keep the compile body separate so it can run under that wider lock.
/// Print a wall-clock phase marker when RESCRIPT_BUILD_PHASES is set.
pub fn phase_mark(label: &str) {
    if std::env::var_os("RESCRIPT_BUILD_PHASES").is_some() {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs_f64() * 1000.0)
            .unwrap_or(0.0);
        eprintln!("[build-phase] {label} epoch_ms={now:.3}");
    }
}

#[instrument(name = "build.incremental.unlocked", skip_all, fields(module_count = build_state.modules.len()))]
pub fn incremental_build_without_lock(
    build_state: &mut BuildCommandState,
    default_timing: Option<Duration>,
    initial_build: bool,
    show_progress: bool,
    only_incremental: bool,
    plain_output: bool,
) -> Result<CompilationOutcome, IncrementalBuildError> {
    let phase_timing_enabled = rescript_compiler::timing::enabled();
    if phase_timing_enabled {
        rescript_compiler::timing::reset();
    }
    let compiler_counters_enabled = rescript_compiler::perf_counters::enabled();
    if compiler_counters_enabled {
        rescript_compiler::perf_counters::reset();
    }
    logs::initialize(&build_state.packages);
    build_state.build_started_at = Some(std::time::SystemTime::now());
    build_state.last_build_ok = false;
    build_state.stopped_at_parse = false;
    build_state.invalidated_modules.clear();

    // A fresh in-process build has nothing compiled in memory, so every
    // module compiles (in-process builds keep no artifacts on disk).
    let fresh_in_process = build_state.module_registry.lock().unwrap().is_empty();
    // A fresh in-process build compiles only what changed since the JavaScript
    // was written (see `incremental`). It still parses every module: the
    // dependency graph comes from the parse.
    let incremental =
        fresh_in_process && !build_state.diagnostic_locations && incremental::applies(build_state);
    if incremental
        && build_state.build_state.source_map_command == SourceMapCommand::Build
        && incremental::everything_up_to_date(build_state)
    {
        for module in build_state.build_state.modules.values_mut() {
            module.compile_dirty = false;
        }
        let parse_warnings = incremental::restore_parse_warnings(build_state);
        // Nothing compiles; this reports the restored warnings.
        let compile_warnings = compile::compile(build_state, false, || (), |_| ())
            .map(|(_, warnings, _)| warnings)
            .unwrap_or_default();
        logs::finalize(&build_state.packages);
        if show_progress {
            if plain_output {
                println!("Compiled 0 modules")
            } else {
                println!(
                    "{}{} {}Compiled 0 modules, everything is up to date",
                    LINE_CLEAR,
                    format_step(2, 3),
                    SWORDS,
                );
            }
        }
        let has_parse_warnings = has_output(&parse_warnings);
        if has_parse_warnings {
            eprintln!("{}", &parse_warnings);
        }
        let has_compile_warnings = has_output(&compile_warnings);
        if has_compile_warnings {
            eprintln!("{}", &compile_warnings);
        }
        if initial_build {
            log_config_warnings(build_state);
        }
        write_compiler_info(build_state);
        build_state.last_build_ok = true;
        print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);
        return Ok(
            if has_parse_warnings
                || has_compile_warnings
                || (initial_build && has_config_warnings(build_state))
            {
                CompilationOutcome::Warnings
            } else {
                CompilationOutcome::Clean
            },
        );
    }
    if fresh_in_process {
        incremental::collect_source_mtimes(build_state);
    }
    if incremental {
        incremental::seed_recorded_deps(build_state);
    } else if fresh_in_process {
        mark_modules_dirty(build_state);
    }

    let num_dirty_modules = build_state.modules.values().filter(|m| is_dirty(m)).count() as u64;
    let pb = if !plain_output && show_progress {
        ProgressBar::new(num_dirty_modules)
    } else {
        ProgressBar::hidden()
    };
    let mut current_step = if only_incremental { 1 } else { 2 };
    let total_steps = if only_incremental { 2 } else { 3 };
    pb.set_style(
        ProgressStyle::with_template(&format!(
            "{} {}Parsing... {{spinner}} {{pos}}/{{len}} {{msg}}",
            format_step(current_step, total_steps),
            PARSE
        ))
        .unwrap(),
    );

    phase_mark("parse-start");
    let timing_parse_start = Instant::now();
    let timing_ast = Instant::now();
    let result_asts = if fresh_in_process {
        // The runtime pre-compilation only needs the registry and the runtime
        // sources, so run it while the project sources are parsed. `compile`
        // later finds the runtime already registered and skips it.
        compile::prepare_registry_for_runtime_precompile(build_state);
        let registry = std::mem::take(&mut build_state.module_registry);
        let runtime_root = build_state.build_state.compiler_info.runtime_path.clone();
        let runtime_store = compile::RuntimeStore::of_build(build_state);
        let (result_asts, precompile_result) = std::thread::scope(|scope| {
            let handle = compile::spawn_runtime_precompile(scope, || {
                let result =
                    compile::pre_compile_runtime_modules(&registry, &runtime_root, runtime_store.as_ref());
                phase_mark("runtime-precompile-done");
                result
            });
            let result_asts = if incremental {
                incremental::parse_and_plan(build_state, || pb.inc(1))
            } else {
                parse::generate_asts(build_state, || pb.inc(1))
            };
            phase_mark("parse-asts-done");
            let precompile_result = handle.and_then(compile::join_runtime_precompile);
            (result_asts, precompile_result)
        });
        build_state.module_registry = registry;
        phase_mark("runtime-precompile-joined");
        if let Err(err) = precompile_result
            && result_asts.is_ok()
        {
            logs::finalize(&build_state.packages);
            pb.finish();
            print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);
            return Err(IncrementalBuildError {
                kind: IncrementalBuildErrorKind::CompileError(Some(err.to_string())),
                plain_output,
            });
        }
        result_asts
    } else {
        parse::generate_asts(build_state, || pb.inc(1))
    };
    let timing_ast_elapsed = timing_ast.elapsed();

    let parse_warnings = match result_asts {
        Ok(warnings) => {
            pb.finish();
            warnings
        }
        Err(err) => {
            let _error_span = info_span!("build.parse_error").entered();
            build_state.stopped_at_parse = true;
            logs::finalize(&build_state.packages);

            if !plain_output && show_progress {
                eprintln!(
                    "{}{} {}Error parsing source files in {:.2}s",
                    LINE_CLEAR,
                    format_step(current_step, total_steps),
                    CROSS,
                    default_timing.unwrap_or(timing_ast_elapsed).as_secs_f64()
                );
                pb.finish();
            }

            eprintln!("{}", &err);
            print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);

            return Err(IncrementalBuildError {
                kind: IncrementalBuildErrorKind::SourceFileParseError,
                plain_output,
            });
        }
    };
    phase_mark("parse-end");
    let deleted_modules = build_state.deleted_modules.clone();
    deps::get_deps(build_state, &deleted_modules);
    phase_mark("deps-end");
    let timing_parse_total = timing_parse_start.elapsed();
    // An incremental build parses in two rounds; report what it parsed.
    let num_dirty_modules = if incremental {
        build_state
            .stored_asts
            .lock()
            .unwrap()
            .keys()
            .filter(|key| key.ends_with(":impl"))
            .count() as u64
    } else {
        num_dirty_modules
    };

    if show_progress {
        if plain_output {
            println!("Parsed {num_dirty_modules} source files")
        } else {
            println!(
                "{}{} {}Parsed {} source files in {:.2}s",
                LINE_CLEAR,
                format_step(current_step, total_steps),
                PARSE,
                num_dirty_modules,
                default_timing.unwrap_or(timing_parse_total).as_secs_f64()
            );
        }
    }
    let has_parse_warnings = has_output(&parse_warnings);

    mark_modules_with_deleted_deps_dirty(&mut build_state.build_state);
    current_step += 1;

    //print all the compile_dirty modules
    if log_enabled!(log::Level::Trace) {
        for (module_name, module) in build_state.modules.iter() {
            if module.compile_dirty {
                println!("compile dirty: {module_name}");
            }
        }
    };

    let start_compiling = Instant::now();
    let pb = if !plain_output && show_progress {
        ProgressBar::new(build_state.modules.len().try_into().unwrap())
    } else {
        ProgressBar::hidden()
    };
    pb.set_style(
        ProgressStyle::with_template(&format!(
            "{} {}Compiling... {{spinner}} {{pos}}/{{len}} {{msg}}",
            format_step(current_step, total_steps),
            SWORDS
        ))
        .unwrap(),
    );

    let (compile_errors, compile_warnings, num_compiled_modules) = compile::compile(
        build_state,
        show_progress,
        || pb.inc(1),
        |size| pb.set_length(size),
    )
    .map_err(|e| {
        let _error_span = info_span!("build.compile_error").entered();
        print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);

        IncrementalBuildError {
            kind: IncrementalBuildErrorKind::CompileError(Some(e.to_string())),
            plain_output,
        }
    })?;

    if build_state
        .diagnostic_retry
        .swap(false, std::sync::atomic::Ordering::Relaxed)
    {
        pb.finish_and_clear();
        // No first-pass diagnostic escapes. Discard the speculative registry
        // and recompile its dependencies too: inclusion/type errors can quote
        // a declaration in another module, not just the failing source file.
        build_state.diagnostic_locations = true;
        *build_state.module_registry.lock().unwrap() =
            rescript_compiler::cmi::persistent_env::ModuleRegistry::new();
        build_state.stored_asts.lock().unwrap().clear();
        build_state.in_memory_interfaces.lock().unwrap().clear();
        build_state.loaded_units.lock().unwrap().clear();
        build_state.unit_reads.lock().unwrap().clear();
        build_state.verified_imports.lock().unwrap().clear();
        build_state.incremental_plan = None;
        build_state.previous_in_process = None;
        build_state.loaded_modules.clear();
        build_state.compiled_modules.clear();
        build_state.parse_warnings_replayed = false;
        mark_modules_dirty(build_state);
        let result = incremental_build_without_lock(
            build_state,
            default_timing,
            initial_build,
            show_progress,
            only_incremental,
            plain_output,
        );
        build_state.diagnostic_locations = false;
        return result;
    }

    if has_parse_warnings {
        eprintln!("{}", &parse_warnings);
    }
    let compile_duration = start_compiling.elapsed();
    phase_mark("compile-end");

    logs::finalize(&build_state.packages);
    pb.finish();
    if !compile_errors.is_empty() {
        let _error_span = info_span!("build.compile_error").entered();
        if show_progress {
            if plain_output {
                eprintln!("Compiled {num_compiled_modules} modules")
            } else {
                eprintln!(
                    "{}{} {}Compiled {} modules in {:.2}s",
                    LINE_CLEAR,
                    format_step(current_step, total_steps),
                    CROSS,
                    num_compiled_modules,
                    default_timing.unwrap_or(compile_duration).as_secs_f64()
                );
            }
        }
        if has_output(&compile_warnings) {
            let _warning_span = info_span!("build.compile_warning").entered();
            eprintln!("{}", &compile_warnings);
        }
        if initial_build {
            log_config_warnings(build_state);
        }
        if has_output(&compile_errors) {
            eprintln!("{}", &compile_errors);
        }

        print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);
        Err(IncrementalBuildError {
            kind: IncrementalBuildErrorKind::CompileError(None),
            plain_output,
        })
    } else {
        let has_compile_warnings = has_output(&compile_warnings);
        let has_config_warning_output = initial_build && has_config_warnings(build_state);
        let outcome = if has_parse_warnings || has_compile_warnings || has_config_warning_output {
            CompilationOutcome::Warnings
        } else {
            CompilationOutcome::Clean
        };

        if show_progress {
            if plain_output {
                println!("Compiled {num_compiled_modules} modules")
            } else {
                println!(
                    "{}{} {}Compiled {} modules in {:.2}s",
                    LINE_CLEAR,
                    format_step(current_step, total_steps),
                    SWORDS,
                    num_compiled_modules,
                    default_timing.unwrap_or(compile_duration).as_secs_f64()
                );
            }
        }

        if has_compile_warnings {
            eprintln!("{}", &compile_warnings);
        }
        if initial_build {
            log_config_warnings(build_state);
        }

        // Write per-package compiler metadata to `lib/bs/compiler-info.json` (idempotent)
        write_compiler_info(build_state);
        phase_mark("compiler-info-end");

        print_compiler_reports(phase_timing_enabled, compiler_counters_enabled);
        build_state.last_build_ok = true;
        Ok(outcome)
    }
}

fn print_compiler_reports(phase_timing_enabled: bool, compiler_counters_enabled: bool) {
    if phase_timing_enabled {
        rescript_compiler::timing::print_report();
    }
    if compiler_counters_enabled {
        rescript_compiler::perf_counters::print_report();
    }
}

fn log_config_warnings(build_state: &BuildCommandState) {
    let mut packages: Vec<_> = build_state.packages.values().collect();
    packages.sort_by(|a, b| a.name.cmp(&b.name));
    packages.iter().for_each(|package| {
        let deprecations = package.config.get_deprecations();
        if !deprecations.is_empty() {
            // External consumers can't fix deprecations themselves, so we
            // point them at the package's issue tracker when we can find one.
            let issue_tracker_url = if package.is_local_dep {
                None
            } else {
                crate::build::packages::read_issue_tracker_url(&package.path)
            };
            log_deprecations(&package.name, deprecations, issue_tracker_url.as_deref());
        }

        if package.is_local_dep {
            package
                .config
                .get_unsupported_fields()
                .iter()
                .for_each(|field| log_unsupported_config_field(&package.name, field));

            package
                .config
                .get_unknown_fields()
                .iter()
                .for_each(|field| log_unknown_config_field(&package.name, field));
        }
    });
}

fn log_deprecations(
    package_name: &str,
    deprecations: &[crate::config::DeprecationWarning],
    issue_tracker_url: Option<&str>,
) {
    let mut message = format!(
        "Package '{package_name}' uses deprecated config (support will be removed in a future version):"
    );
    for deprecation in deprecations {
        let line = match deprecation {
            crate::config::DeprecationWarning::BsconfigJson => {
                "  - filename 'bsconfig.json' — rename to 'rescript.json'"
            }
            crate::config::DeprecationWarning::BsDependencies => {
                "  - field 'bs-dependencies' — use 'dependencies' instead"
            }
            crate::config::DeprecationWarning::BsDevDependencies => {
                "  - field 'bs-dev-dependencies' — use 'dev-dependencies' instead"
            }
            crate::config::DeprecationWarning::BscFlags => {
                "  - field 'bsc-flags' — use 'compiler-flags' instead"
            }
            crate::config::DeprecationWarning::CjsModule => {
                "  - module 'cjs' in package-specs — use 'commonjs' instead"
            }
            crate::config::DeprecationWarning::Es6Module => {
                "  - module 'es6' in package-specs — use 'esmodule' instead"
            }
        };
        message.push('\n');
        message.push_str(line);
    }
    if let Some(url) = issue_tracker_url {
        message.push_str(&format!("\nPlease report this to the package maintainer: {url}"));
    }
    eprintln!("\n{}", style(message).yellow());
}

fn log_unsupported_config_field(package_name: &str, field_name: &str) {
    let warning = format!(
        "The field '{field_name}' found in the package config of '{package_name}' is not supported by ReScript 12's new build system."
    );
    eprintln!("\n{}", style(warning).yellow());
}

fn log_unknown_config_field(package_name: &str, field_name: &str) {
    let warning = format!(
        "Unknown field '{field_name}' found in the package config of '{package_name}'. This option will be ignored."
    );
    eprintln!("\n{}", style(warning).yellow());
}

#[allow(clippy::too_many_arguments)]
#[instrument(name = "rewatch.build", skip_all, fields(working_dir = %path.display()))]
pub fn build(
    filter: &Option<regex::Regex>,
    path: &Path,
    show_progress: bool,
    no_timing: bool,
    plain_output: bool,
    warn_error: Option<String>,
    prod: bool,
    features: Option<Vec<String>>,
    dump: Option<DumpRequest>,
) -> Result<BuildCommandState> {
    let _span = info_span!(
        "rewatch.build",
        working_dir = %path.display(),
        prod
    )
    .entered();
    let default_timing: Option<std::time::Duration> = if no_timing {
        Some(std::time::Duration::new(0.0 as u64, 0.0 as u32))
    } else {
        None
    };
    let timing_total = Instant::now();
    phase_mark("build-start");
    with_build_lock(path, || {
        let mut build_state = initialize_build(
            default_timing,
            filter,
            show_progress,
            path,
            plain_output,
            warn_error,
            prod,
            features,
            crate::config::SourceMapCommand::Build,
        )
        .with_context(|| "Could not initialize build")?;
        build_state.dump = dump;

        match incremental_build_without_lock(
            &mut build_state,
            default_timing,
            true,
            show_progress,
            false,
            plain_output,
        ) {
            Ok(result) => {
                if !plain_output && show_progress {
                    let timing_total_elapsed = timing_total.elapsed();
                    println!(
                        "\n{}",
                        format_finished_compilation_message(
                            None,
                            result,
                            default_timing.unwrap_or(timing_total_elapsed),
                        )
                    );
                }
                clean::cleanup_after_build(&build_state);
                phase_mark("cleanup-end");
                Ok(build_state)
            }
            Err(e) => {
                clean::cleanup_after_build(&build_state);
                Err(anyhow!("Incremental build failed. Error: {e}"))
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fs2::FileExt;
    use std::fs;
    use std::fs::OpenOptions;
    use std::process;
    use std::sync::mpsc;
    use std::thread;
    use tempfile::TempDir;

    #[test]
    fn with_build_lock_holds_lock_while_running_work() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path();
        let build_lock_path = project_folder.join("lib").join(LockKind::Build.file_name());

        let result = with_build_lock(project_folder, || {
            assert!(
                build_lock_path.exists(),
                "build lock should be held while guarded work runs"
            );
            42
        });

        assert_eq!(result, 42);
        assert!(
            !build_lock_path.exists(),
            "build lock should be removed after guarded work finishes"
        );
    }

    #[test]
    fn with_build_lock_drops_lock_after_error_result() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path();
        let build_lock_path = project_folder.join("lib").join(LockKind::Build.file_name());

        let result: Result<(), &str> = with_build_lock(project_folder, || Err("failed"));

        assert_eq!(result, Err("failed"));
        assert!(
            !build_lock_path.exists(),
            "build lock should be removed after guarded work returns an error"
        );
    }

    #[test]
    fn build_waits_for_lock_before_initializing() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().to_path_buf();
        let lib_dir = project_folder.join("lib");
        let build_lock_path = lib_dir.join(LockKind::Build.file_name());
        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(&build_lock_path, process::id().to_string()).expect("lockfile should be written");
        let active_guard = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(lib_dir.join(".build.lock.guard"))
            .expect("guard file should open");
        active_guard
            .lock_exclusive()
            .expect("active build should hold advisory lock");

        let (sender, receiver) = mpsc::channel();
        let build_project_folder = project_folder.clone();
        let build_thread = thread::spawn(move || {
            // This temp project has no config, so initialization would fail immediately
            // if `build` did not wait for the lock first.
            let result = build(
                &None,
                &build_project_folder,
                false,
                true,
                true,
                None,
                false,
                None,
                None,
            );
            sender.send(result.is_err()).expect("result should be sent");
        });

        assert!(
            receiver.recv_timeout(Duration::from_millis(250)).is_err(),
            "build should wait for build.lock before running initialization"
        );

        drop(active_guard);
        fs::remove_file(&build_lock_path).expect("lockfile should be removed");
        assert!(
            receiver
                .recv_timeout(Duration::from_secs(5))
                .expect("build should finish after lock is removed")
        );
        build_thread.join().expect("build thread should complete");
    }

    #[test]
    fn formats_successful_completion_message() {
        assert_eq!(
            format_finished_compilation_message(None, CompilationOutcome::Clean, Duration::from_millis(1500),),
            format!("{LINE_CLEAR}{}Finished compilation in 1.50s", CHECKMARK)
        );
    }

    #[test]
    fn formats_warning_completion_message() {
        assert_eq!(
            format_finished_compilation_message(
                Some("incremental"),
                CompilationOutcome::Warnings,
                Duration::from_millis(1500),
            ),
            format!(
                "{LINE_CLEAR}{}Finished incremental compilation with warnings in 1.50s",
                WARNING
            )
        );
    }
}
