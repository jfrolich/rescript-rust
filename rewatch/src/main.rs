use anyhow::Result;
use console::Term;
use log::LevelFilter;
use std::{io::Write, path::Path};

#[global_allocator]
static GLOBAL_ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rescript::{
    build, cli, cmd, format,
    lock::{LockKind, drop_lock, get_lock_or_exit},
    telemetry, watcher,
};

fn main() {
    let telemetry_guard = telemetry::init_telemetry();
    let otel_enabled = telemetry_guard.otel_enabled();
    let exit_code = match run_main(otel_enabled) {
        Ok(()) => 0,
        Err(err) => {
            eprintln!("{:#}", err);
            1
        }
    };
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
        cli::Command::CompilerArgs { path } => {
            println!("{}", build::get_compiler_args(Path::new(&path))?);
            Ok(())
        }
        cli::Command::Build(build_args) => {
            let features = build_args.features.parsed();
            let build_mode = match cli::resolve_build_mode(*build_args.rust, build_args.in_process.in_process)
            {
                Ok(mode) => mode,
                Err(err) => {
                    return Err(anyhow::anyhow!(err));
                }
            };
            configure_rayon_for_in_process(build_mode);
            let build_result = run_with_in_process_stack(build_mode, || {
                build::build(
                    &build_args.filter,
                    Path::new(&build_args.folder as &str),
                    show_progress,
                    build_args.no_timing,
                    true, // create_sourcedirs is now always enabled
                    plain_output,
                    (*build_args.warn_error).clone(),
                    build_mode,
                    build_args.subprocess.subprocess,
                    build_args.dump_typed_sexp_arg.dump_typed_sexp,
                    build_args.prod,
                    features,
                )
            });
            match build_result {
                Err(e) => Err(e),
                Ok(_) => {
                    if let Some(args_after_build) = (*build_args.after_build).clone() {
                        cmd::run(args_after_build)
                    }
                    Ok(())
                }
            }
        }
        cli::Command::Watch(watch_args) => {
            let features = watch_args.features.parsed();
            let build_mode = match cli::resolve_build_mode(*watch_args.rust, watch_args.in_process.in_process)
            {
                Ok(mode) => mode,
                Err(err) => {
                    return Err(anyhow::anyhow!(err));
                }
            };
            configure_rayon_for_in_process(build_mode);
            let _lock = get_lock_or_exit(LockKind::Watch, &watch_args.folder);
            let watch_result = run_with_in_process_stack(build_mode, || {
                watcher::start(
                    &watch_args.filter,
                    show_progress,
                    &watch_args.folder,
                    (*watch_args.after_build).clone(),
                    true, // create_sourcedirs is now always enabled
                    plain_output,
                    (*watch_args.warn_error).clone(),
                    build_mode,
                    watch_args.subprocess.subprocess,
                    watch_args.dump_typed_sexp_arg.dump_typed_sexp,
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
            let result = build::clean::clean(Path::new(&folder as &str), show_progress, plain_output, prod);
            let _lock = drop_lock(LockKind::Build, &folder);

            result
        }
        cli::Command::Format { stdin, check, files } => format::format(stdin, check, files),
    }
}

fn configure_rayon_for_in_process(build_mode: rescript::build::build_types::BuildMode) {
    if build_mode.is_in_process() {
        rayon::ThreadPoolBuilder::new()
            .thread_name(|index| format!("rewatch-in-process-worker-{index}"))
            .stack_size(IN_PROCESS_STACK_SIZE)
            .build_global()
            .expect("failed to configure in-process Rayon worker pool");
    }
}

// compiler-rust/src/bin/bsc.rs:119 uses a 512 MB subprocess stack for one
// compiler invocation. In-process builds run the same pipeline in several
// workers, so keep more headroom than the old 256 MB worker stack without
// multiplying subprocess-sized stacks across the whole build.
const IN_PROCESS_STACK_SIZE: usize = 384 * 1024 * 1024;

fn run_with_in_process_stack<T, F>(build_mode: rescript::build::build_types::BuildMode, f: F) -> T
where
    T: Send,
    F: FnOnce() -> T + Send,
{
    if !build_mode.is_in_process() {
        return f();
    }

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
