use anyhow::Result;
use console::Term;
use log::LevelFilter;
use std::{io::Write, path::Path};

#[global_allocator]
// Intentional rewatch performance choice: clean and in-process builds allocate
// many short-lived graph nodes and compiler artifacts, and mimalloc has been a
// measurable win for that workload. Keep this separate from compiler parity
// work; it must not change generated typedtree/lambda/JS output.
static GLOBAL_ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rescript::{
    build, cli, cmd, format,
    lock::{LockKind, drop_lock, get_lock_or_exit},
    telemetry, watcher,
};

/// The registry `rescript bsc` compiles against. The file compile finds
/// other units' `.cmi` files in its `-I` directories; in process, an `-I`
/// directory that is a package's `lib/ocaml` compiles that package (with its
/// dependencies) into memory instead, leaving its files alone, and the
/// runtime is compiled otherwise.
fn bsc_registry(
    runtime_path: &Path,
    include_dirs: &[std::path::PathBuf],
) -> anyhow::Result<rescript_compiler::cmi::persistent_env::ModuleRegistry> {
    let runtime = std::fs::canonicalize(runtime_path).ok();
    let mut packages = Vec::new();
    for dir in include_dirs {
        // `lib/ocaml` need not exist yet: the build writes it.
        if !dir.ends_with("lib/ocaml") {
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
            "bsc: at most one package's lib/ocaml can be an -I directory in process"
        )),
    }
}

fn main() {
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
        Ok(()) => 0,
        Err(err) => {
            eprintln!("{:#}", err);
            1
        }
    };
    rescript::build::phase_mark("run-main-end");
    drop(telemetry_guard);
    std::process::exit(exit_code);
}

fn run_main(otel_enabled: bool) -> Result<()> {
    let cli = cli::parse_with_default().unwrap_or_else(|err| err.exit());

    let log_level_filter = cli.verbose.log_level_filter();

    if !otel_enabled {
        let stdout_logger = env_logger::Builder::new()
            .format(|buf, record| writeln!(buf, "{}:\n{}", record.level(), record.args()))
            .filter_level(log_level_filter)
            .target(env_logger::fmt::Target::Stdout)
            .build();

        let stderr_logger = env_logger::Builder::new()
            .format(|buf, record| writeln!(buf, "{}:\n{}", record.level(), record.args()))
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
        cli::Command::BuildReference { folder, bsc, prod } => {
            if !build::plan::build_reference(Path::new(&folder), Path::new(&bsc), prod)? {
                std::process::exit(1);
            }
            Ok(())
        }
        cli::Command::CompilerArgs { path } => {
            println!("{}", build::get_compiler_args(Path::new(&path))?);
            Ok(())
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
                    Ok(())
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
            match watch_result {
                Err(e) => Err(e),
                Ok(_) => Ok(()),
            }
        }
        cli::Command::Clean { folder, prod } => {
            let _lock = get_lock_or_exit(LockKind::Build, &folder);
            let result = build::clean::clean(folder.as_ref(), show_progress, plain_output, prod);
            let _ = drop_lock(LockKind::Build, &folder);

            result
        }
        cli::Command::Format { stdin, check, files } => format::format(stdin, check, files),
        cli::Command::Analysis { args } => {
            let cwd = std::env::current_dir()?;
            std::process::exit(rescript::tooling_server::run_client(&cwd, &args))
        }
    }
}

fn configure_rayon_for_in_process() {
    let mut builder = rayon::ThreadPoolBuilder::new();
    if std::env::var_os("RAYON_NUM_THREADS").is_none() {
        builder = builder.num_threads(default_in_process_threads());
    }
    builder
        .thread_name(|index| format!("rewatch-in-process-worker-{index}"))
        .stack_size(IN_PROCESS_STACK_SIZE)
        .build_global()
        .expect("failed to configure in-process Rayon worker pool");
}

fn default_in_process_threads() -> usize {
    let logical = num_cpus::get().max(1);
    let target = logical.saturating_mul(8).div_ceil(5);
    let scaling_cap = logical.saturating_add(8);
    // In-process compilation publishes signatures before JS is emitted so
    // dependents can type-check early. Those workers can later block before JS
    // while waiting for dependency cmj metadata, so a CPU-sized pool leaves
    // runnable modules stranded behind parked workers. A small oversubscription
    // keeps that overlap, while a scaling cap avoids limiting larger builders
    // to the core count of this development machine.
    target.min(scaling_cap)
}

const IN_PROCESS_STACK_SIZE: usize = 256 * 1024 * 1024;

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
