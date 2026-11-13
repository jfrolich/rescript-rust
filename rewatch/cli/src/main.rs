mod snapshot;

use anyhow::Result;
use console::Term;
use log::LevelFilter;
use std::{io::Write, path::Path};

#[cfg(feature = "alloc-stats")]
mod alloc_stats;

// Intentional rewatch performance choice: clean and in-process builds allocate
// many short-lived graph nodes and compiler artifacts, and mimalloc has been a
// measurable win for that workload. Keep this separate from compiler parity
// work; it must not change generated typedtree/lambda/JS output.
#[cfg(not(feature = "alloc-stats"))]
#[global_allocator]
static GLOBAL_ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

// The `alloc-stats` feature counts allocations on top of mimalloc; see
// `alloc_stats.rs` and `scripts/perf/README.md`.
#[cfg(feature = "alloc-stats")]
#[global_allocator]
static GLOBAL_ALLOCATOR: alloc_stats::CountingAlloc = alloc_stats::CountingAlloc;

use rescript::{
    build, cli, cmd, format,
    lock::{LockKind, drop_lock, get_clean_lock_or_exit, get_lock_or_exit},
    telemetry, watcher,
};

/// The registry `rescript bsc` compiles against. The file compile finds
/// other units' `.cmi` files in its `-I` directories; in process, an `-I`
/// directory that is a package's `lib/rescript` compiles that package (with its
/// dependencies) into memory instead, leaving its files alone, and the
/// runtime is compiled otherwise.
fn bsc_registry(
    runtime_path: &Path,
    include_dirs: &[std::path::PathBuf],
) -> anyhow::Result<rescript_compiler::cmi::persistent_env::ModuleRegistry> {
    let runtime = std::fs::canonicalize(runtime_path).ok();
    let mut packages = Vec::new();
    for dir in include_dirs {
        // `lib/rescript` need not exist yet: the build writes it.
        if !dir.ends_with("lib/rescript") {
            continue;
        }
        let Some(Ok(package)) = dir.parent().and_then(Path::parent).map(std::fs::canonicalize) else {
            continue;
        };
        if Some(&package) != runtime.as_ref()
            && (package.join("rescript.json").exists() || package.join("bsconfig.json").exists())
        {
            packages.push(package);
        }
    }
    match packages.as_slice() {
        [] => rescript::build::compile::runtime_registry(runtime_path),
        [package] => build::plan::build_in_memory(package)
            .map_err(|err| anyhow::anyhow!("bsc: building {} failed:\n{err:#}", package.display())),
        _ => Err(anyhow::anyhow!(
            "bsc: at most one package's lib/rescript can be an -I directory in process"
        )),
    }
}

fn main() {
    #[cfg(feature = "alloc-stats")]
    alloc_stats::start();
    // The runtime the build script compiled (see `cli/build.rs`).
    build::snapshot::install(include_bytes!(concat!(env!("OUT_DIR"), "/runtime.bin")));
    // Hidden test commands: run the linked compiler one file at a time, as
    // the parity scripts compare it against the OCaml reference compiler.
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("bsc") => {
            configure_rayon_for_in_process();
            rescript_compiler::cli::bsc::main(
                args.collect(),
                Some(Box::new(|runtime_path, include_dirs| {
                    let runtime_path = runtime_path
                        .or_else(|| std::env::var_os("RESCRIPT_RUNTIME").map(Into::into))
                        .ok_or_else(|| anyhow::anyhow!("bsc: pass -runtime-path or set RESCRIPT_RUNTIME"))?;
                    bsc_registry(&runtime_path, &include_dirs)
                })),
            );
            std::process::exit(0);
        }
        Some("snapshot") => {
            configure_rayon_for_in_process();
            if let Err(error) = snapshot::run(args.collect()) {
                eprintln!("{error:#}");
                std::process::exit(1);
            }
            return;
        }
        Some("res-parser") => {
            rescript_compiler::cli::res_parser::main(args.collect());
            std::process::exit(0);
        }
        _ => {}
    }
    rescript::build::phase_mark("main");
    rescript_compiler::hash_seed::install_thread_local_hash_seeds();
    let telemetry_guard = telemetry::init_telemetry();
    let otel_enabled = telemetry_guard.otel_enabled();
    let exit_code = match run_main(otel_enabled) {
        Ok(status) => status,
        Err(err) => {
            eprintln!("{:#}", err);
            1
        }
    };
    rescript::build::phase_mark("run-main-end");
    drop(telemetry_guard);
    #[cfg(feature = "alloc-stats")]
    alloc_stats::finish();
    std::process::exit(exit_code);
}

/// Run the command; its exit status on success.
fn run_main(otel_enabled: bool) -> Result<i32> {
    let cli = cli::parse_with_default().unwrap_or_else(|err| err.exit());

    let log_level_filter = cli.verbose.log_level_filter();

    if !otel_enabled {
        let stdout_logger = env_logger::Builder::new()
            .format(write_log_record)
            .filter_level(log_level_filter)
            .target(env_logger::fmt::Target::Stdout)
            .build();

        let stderr_logger = env_logger::Builder::new()
            .format(write_log_record)
            .filter_level(log_level_filter)
            .target(env_logger::fmt::Target::Stderr)
            .build();

        log::set_max_level(log_level_filter);
        log::set_boxed_logger(Box::new(SplitLogger {
            stdout: stdout_logger,
            stderr: stderr_logger,
        }))
        .expect("Failed to initialize logger");
    }

    let is_tty: bool = Term::stdout().is_term() && Term::stderr().is_term();
    let plain_output = !is_tty;

    // Show progress messages (e.g. "Finished compilation") as long as logging is at Info level
    // or more verbose. This way `-v` and `-vv` add debug output without suppressing progress.
    let show_progress = log_level_filter >= LevelFilter::Info;

    match cli.command {
        cli::Command::BuildReference {
            folder,
            bsc,
            prod,
            ppx,
        } => {
            let mut ppx_overrides = Vec::new();
            for spec in ppx {
                let Some((name, executable)) = spec.split_once('=') else {
                    anyhow::bail!("--ppx expects SPEC=EXECUTABLE, got {spec}");
                };
                ppx_overrides.push((name.to_string(), std::fs::canonicalize(executable)?));
            }
            // The plan parses and prepares every module in process, like
            // `build`: give its Rayon workers and this thread the same stack.
            configure_rayon_for_in_process();
            let built = run_with_in_process_stack(|| {
                build::plan::build_reference(Path::new(&folder), Path::new(&bsc), prod, &ppx_overrides)
            })?;
            if !built {
                std::process::exit(1);
            }
            Ok(0)
        }
        cli::Command::CompilerArgs { path } => {
            println!("{}", build::get_compiler_args(Path::new(&path))?);
            Ok(0)
        }
        cli::Command::Build(build_args) => {
            let features = build_args.features.parsed();
            configure_rayon_for_in_process();
            let build_result = run_with_in_process_stack(|| {
                build::build(
                    &build_args.filter,
                    Path::new(&build_args.folder as &str),
                    show_progress,
                    build_args.no_timing,
                    plain_output,
                    (*build_args.warn_error).clone(),
                    build_args.prod,
                    features,
                    build_args
                        .dump_dir
                        .clone()
                        .map(|dir| rescript::build::build_types::DumpRequest {
                            kinds: build_args.dump.clone(),
                            dir,
                        }),
                    build_args.check_only,
                )
            });
            match build_result {
                Err(e) => Err(e),
                Ok(build_state) => {
                    if let Some(args_after_build) = (*build_args.after_build).clone() {
                        drop(build_state);
                        cmd::run(args_after_build)?;
                    } else {
                        // `rescript build` is a one-shot command and `main` exits
                        // immediately after this match. Dropping the full build graph
                        // walks every package/module/AST and shows up in clean-build
                        // wall time; let the OS reclaim it at process exit instead.
                        std::mem::forget(build_state);
                    }
                    Ok(0)
                }
            }
        }
        cli::Command::Watch(watch_args) => {
            let features = watch_args.features.parsed();
            configure_rayon_for_in_process();
            let _lock = get_lock_or_exit(LockKind::Watch, &watch_args.folder);
            let watch_result = run_with_in_process_stack(|| {
                watcher::start(
                    &watch_args.filter,
                    show_progress,
                    &watch_args.folder,
                    (*watch_args.after_build).clone(),
                    plain_output,
                    (*watch_args.warn_error).clone(),
                    watch_args.clear_screen,
                    watch_args.prod,
                    features,
                )
            });
            // 0, or 128 plus the number of the signal that stopped it.
            watch_result
        }
        cli::Command::Clean { folder, prod } => {
            // The watch lock first, as `rescript watch` takes it: a watcher
            // keeps reading the artifacts the clean removes.
            let _watch_lock = get_clean_lock_or_exit(&folder);
            let _lock = get_lock_or_exit(LockKind::Build, &folder);
            let result = build::clean::clean(folder.as_ref(), show_progress, plain_output, prod);
            let _ = drop_lock(LockKind::Build, &folder);
            let _ = drop_lock(LockKind::Watch, &folder);

            result.map(|()| 0)
        }
        cli::Command::Format { stdin, check, files } => format::format(stdin, check, files).map(|()| 0),
        cli::Command::Doc { paths } => {
            let cwd = std::env::current_dir()?;
            configure_rayon_for_in_process();
            match run_with_in_process_stack(|| build::tooling::doc(&cwd, &paths, plain_output)) {
                Ok(docs) => {
                    std::io::stdout().write_all(&docs)?;
                    Ok(0)
                }
                Err(err) => {
                    eprintln!("{err:#}");
                    Ok(1)
                }
            }
        }
        cli::Command::Analysis { args } => {
            let cwd = std::env::current_dir()?;
            std::process::exit(rescript::tooling_server::run_client(&cwd, &args))
        }
    }
}

fn configure_rayon_for_in_process() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(rescript::build::pools::global_threads())
        .thread_name(|index| format!("rewatch-in-process-worker-{index}"))
        .stack_size(IN_PROCESS_STACK_SIZE)
        .build_global()
        .expect("failed to configure in-process Rayon worker pool");
}

const IN_PROCESS_STACK_SIZE: usize = rescript::build::pools::STACK_SIZE;

fn run_with_in_process_stack<T, F>(f: F) -> T
where
    T: Send,
    F: FnOnce() -> T + Send,
{
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .name("rewatch-in-process-main".to_string())
            .stack_size(IN_PROCESS_STACK_SIZE)
            .spawn_scoped(scope, f)
            .expect("failed to spawn in-process build thread");
        match handle.join() {
            Ok(result) => result,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

/// A log record as printed: verbose logs are labeled inline (`debug: …`,
/// `trace: …`, as rewatch-ocaml's `Output.log`), the others on a line of
/// their own (`WARN:`).
fn write_log_record(buf: &mut env_logger::fmt::Formatter, record: &log::Record) -> std::io::Result<()> {
    match record.level() {
        log::Level::Debug => writeln!(buf, "debug: {}", record.args()),
        log::Level::Trace => writeln!(buf, "trace: {}", record.args()),
        level => writeln!(buf, "{level}:\n{}", record.args()),
    }
}

struct SplitLogger {
    stdout: env_logger::Logger,
    stderr: env_logger::Logger,
}

impl log::Log for SplitLogger {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        self.stdout.enabled(metadata) || self.stderr.enabled(metadata)
    }

    fn log(&self, record: &log::Record) {
        match record.level() {
            log::Level::Error | log::Level::Warn => self.stderr.log(record),
            _ => self.stdout.log(record),
        }
    }

    fn flush(&self) {
        self.stdout.flush();
        self.stderr.flush();
    }
}
