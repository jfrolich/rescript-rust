//! The Rust `bsc` command line.
//!
//! It mirrors the OCaml `bsc` driver (rescript_compiler_main.ml):
//! - `-bs-ast` runs the frontend and writes the binary `.ast` file
//! - otherwise it compiles a .res/.resi (or .ast) file through the Rust
//!   pipeline, writing JS (`-o` or `-bs-package-output`) and any requested
//!   `-d*` dumps
//! - `-bs-ns`, `-bs-package-name`, include paths, warnings, PPX and genType
//!   flags configure that pipeline
//!
//! Unrecognized flags are ignored.

use crate::binary_ast::{
    deps, write_signature_ast_current_with_extra_deps_and_builtin_ppx,
    write_structure_ast_current_with_extra_deps_and_builtin_ppx,
};
use crate::cmi::cmi_format;
use crate::driver::{
    CompilerOptions, UserDiagnostic, compile_file_to_js_with_options, enable_cli_cleanup_skip,
    error_extension_to_anyhow, run_implementation_frontend, run_interface_frontend,
    typecheck_interface_file,
};
use crate::js_ir::ModuleFormat;
use crate::js_ir::source_map::SourceMapMode;
use crate::parser::{Parser, code_frame, module, sexp_locs};
use crate::source_text::latin1_bytes_to_string;
use anyhow::{Context, Result, anyhow};
use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

/// Auto-detect the runtime path based on the executable's location.
/// Mirrors OCaml's runtime_package.ml default_path logic.
fn default_runtime_path() -> Option<PathBuf> {
    let exe = env::current_exe().ok()?;
    let dir = exe.parent()?;
    let components: Vec<_> = dir.components().collect();
    let len = components.len();

    if len < 4 {
        return None;
    }

    // Check case 1: npm installation
    // bin: node_modules/@rescript/{platform}/bin
    // runtime: node_modules/@rescript/runtime
    let last = components[len - 1].as_os_str().to_str().unwrap_or("");
    let third = components[len - 3].as_os_str().to_str().unwrap_or("");
    let fourth = components[len - 4].as_os_str().to_str().unwrap_or("");

    if last == "bin" && third == "@rescript" && fourth == "node_modules" {
        let base: PathBuf = components[..len - 4].iter().collect();
        let runtime = base.join("node_modules").join("@rescript").join("runtime");
        if runtime.exists() {
            return Some(runtime);
        }
    }

    // Case 2: local development — walk up from exe dir looking for packages/@rescript/runtime.
    // This handles various layouts:
    //   OCaml: _build/install/default/bin/bsc (4 levels)
    //   Rust:  compiler-rust/target/debug/bsc (3 levels)
    let mut search_dir = dir.to_path_buf();
    for _ in 0..6 {
        let runtime = search_dir
            .join("packages")
            .join("@rescript")
            .join("runtime");
        if runtime.exists() {
            return Some(runtime);
        }
        if !search_dir.pop() {
            break;
        }
    }

    None
}

#[derive(Default, Debug)]
struct Options {
    ignore_parse_errors: bool,
    formatted: bool,
    bs_ast: bool,
    absname: bool,
    debug: bool,
    dump_lambda: bool,
    dump_parsetree_sexp_locs: bool,
    dump_typed_sexp: bool,
    dump_typed_sexp_locs: bool,
    dump_lambda_sexp: bool,
    dump_lambda_sexp_locs: bool,
    output: Option<PathBuf>,
    package_outputs: Vec<String>,
    source_map: SourceMapMode,
    source_map_sources_content: bool,
    source_map_root: String,
    namespace: Option<String>,
    module_name: Option<String>,
    input: Option<PathBuf>,
    include_paths: Vec<PathBuf>,
    runtime_path: Option<PathBuf>,
    package_name: Option<String>,
    open_modules: Vec<String>,
    warning_specs: Vec<String>,
    warning_error_specs: Vec<String>,
    jsx_version: Option<i32>,
    jsx_module: Option<String>,
    experimental_let_unwrap: bool,
    jsx_preserve: bool,
    nopervasives: bool,
    no_version_header: bool,
    no_check_div_by_zero: bool,
    cross_module_inline: bool,
    no_assert_false: bool,
    noassert: bool,
    transparent_modules: bool,
    no_builtin_ppx: bool,
    builtin_spice_ppx: bool,
    gentype: bool,
    gentype_flags: crate::gentype::config::FlagState,
    make_runtime: bool,
    read_cmi: bool,
    color_mode: code_frame::ColorMode,
}

impl Options {
    fn has_dump_output(&self) -> bool {
        self.dump_lambda
            || self.dump_typed_sexp
            || self.dump_typed_sexp_locs
            || self.dump_lambda_sexp
            || self.dump_lambda_sexp_locs
    }
}

/// Builds the module registry an in-process compile resolves other units
/// in, from the runtime package path (`-runtime-path` or the default) and the
/// `-I` directories.
pub type RegistryProvider = Box<
    dyn FnOnce(Option<PathBuf>, Vec<PathBuf>) -> Result<crate::cmi::persistent_env::ModuleRegistry>
        + Send,
>;

/// Run `bsc` with `args` (without the program name); never returns.
///
/// With `registry`, source files compile in process against it and no
/// `.cmi`/`.cmj` file is read or written; `.ast` input is not supported.
pub fn main(args: Vec<String>, registry: Option<RegistryProvider>) {
    crate::hash_seed::install_thread_local_hash_seeds();
    // Spawn the compiler in a thread with a large stack to avoid stack overflow
    // on deeply nested type structures in CMI files
    let builder = std::thread::Builder::new()
        .name("compiler".into())
        .stack_size(512 * 1024 * 1024); // 512MB

    let handler = builder
        .spawn(|| {
            enable_cli_cleanup_skip();
            let result = run(args, registry);
            crate::perf_counters::print_report();
            match result {
                Ok(()) => {
                    let _ = std::io::stdout().flush();
                    let _ = std::io::stderr().flush();
                    std::process::exit(0);
                }
                Err(err) => {
                    if let Some(diagnostic) = err.downcast_ref::<UserDiagnostic>() {
                        eprint!("{}", diagnostic.output());
                        let _ = std::io::stderr().flush();
                        std::process::exit(diagnostic.exit_code());
                    }
                    eprintln!("{err}");
                    let _ = std::io::stderr().flush();
                    std::process::exit(1);
                }
            }
        })
        .expect("Failed to spawn compiler thread");

    let Err(payload) = handler.join();
    if let Some(report) = crate::misc::uncaught_exception_report(&*payload) {
        // OCaml's runtime report for an uncaught exception.
        eprintln!("{report}");
        let _ = std::io::stderr().flush();
        std::process::exit(2);
    }
    panic!("Compiler thread panicked: {payload:?}");
}

/// rescript_compiler_main.ml:168-182 `format_file`.
fn format_file(input: &str, output: Option<&Path>, ignore_parse_errors: bool) -> Result<()> {
    let is_res = input.ends_with(".res") || input.ends_with(".resi");
    if !is_res {
        return Err(
            UserDiagnostic::new(format!("bsc: don't know what to do with {input}\n"), 2).into(),
        );
    }
    let source = fs::read(input).with_context(|| input.to_string())?;
    let (report, formatted) =
        crate::driver::format_source_with(&source, input, ignore_parse_errors);
    if !report.is_empty() {
        eprint!("{report}");
    }
    let Some(formatted) = formatted else {
        let _ = std::io::stderr().flush();
        std::process::exit(1);
    };
    match output {
        None => {
            std::io::stdout().write_all(&formatted)?;
        }
        Some(path) => fs::write(path, &formatted)?,
    }
    Ok(())
}

fn run(args: Vec<String>, registry: Option<RegistryProvider>) -> Result<()> {
    let mut opts = Options {
        // OCaml compiler/bsc/rescript_compiler_main.ml:494 sets
        // `Clflags.color := Some Always` before parsing command-line flags.
        color_mode: code_frame::ColorMode::Always,
        ..Options::default()
    };
    let mut args = args.into_iter().peekable();

    while let Some(arg) = args.next() {
        if arg.starts_with('-') {
            match arg.as_str() {
                "-bs-ast" => opts.bs_ast = true,
                "-bs-g" => opts.debug = true,
                "-drawlambda" => opts.dump_lambda = true,
                "-dparsetree-sexp-locs" => opts.dump_parsetree_sexp_locs = true,
                "-dtyped-sexp" => opts.dump_typed_sexp = true,
                "-dtyped-sexp-locs" => opts.dump_typed_sexp_locs = true,
                "-dlambda-sexp" => opts.dump_lambda_sexp = true,
                "-dlambda-sexp-locs" => opts.dump_lambda_sexp_locs = true,
                "-o" | "-output" => {
                    if let Some(val) = args.next() {
                        opts.output = Some(PathBuf::from(val));
                    }
                }
                "-bs-source-map" => {
                    let value = args
                        .next()
                        .ok_or_else(|| anyhow!("-bs-source-map requires a value"))?;
                    opts.source_map = match value.to_ascii_lowercase().as_str() {
                        "linked" => SourceMapMode::Linked,
                        "inline" => SourceMapMode::Inline,
                        "hidden" => SourceMapMode::Hidden,
                        "false" | "none" => SourceMapMode::None,
                        _ => {
                            return Err(anyhow!(
                                "Unsupported sourceMap value: {value}. Expected linked, inline, hidden, false, or none"
                            ));
                        }
                    };
                }
                "-bs-source-map-sources-content" => {
                    let value = args.next().ok_or_else(|| {
                        anyhow!("-bs-source-map-sources-content requires a value")
                    })?;
                    opts.source_map_sources_content = match value.as_str() {
                        "true" => true,
                        "false" => false,
                        _ => return Err(anyhow!("Expected true or false, got {value}")),
                    };
                }
                "-bs-source-map-root" => {
                    opts.source_map_root = args
                        .next()
                        .ok_or_else(|| anyhow!("-bs-source-map-root requires a value"))?;
                }
                "-bs-package-output" => {
                    if let Some(val) = args.next() {
                        opts.package_outputs.push(val);
                    }
                }
                "-bs-ns" => {
                    // js_packages_state.ml:38-42: OCaml's `-bs-ns` also sets
                    // `dont_record_crc_unit`.
                    if let Some(val) = args.next() {
                        opts.namespace = Some(val);
                    }
                }
                "-bs-module-name" => {
                    if let Some(val) = args.next() {
                        opts.module_name = Some(val);
                    }
                }
                "-impl" | "-intf" => {
                    if let Some(val) = args.next() {
                        opts.input = Some(PathBuf::from(val));
                    }
                }
                "-I" => {
                    if let Some(val) = args.next() {
                        opts.include_paths.push(PathBuf::from(val));
                    }
                }
                "-runtime-path" => {
                    if let Some(val) = args.next() {
                        opts.runtime_path = Some(PathBuf::from(val));
                    }
                }
                "-bs-package-name" => {
                    if let Some(val) = args.next() {
                        opts.package_name = Some(val);
                    }
                }
                "-open" => {
                    if let Some(val) = args.next() {
                        opts.open_modules.push(val);
                    }
                }
                "-bs-jsx" => {
                    if let Some(val) = args.next() {
                        opts.jsx_version = val.parse::<i32>().ok();
                    }
                }
                "-bs-jsx-module" => {
                    if let Some(val) = args.next() {
                        crate::driver::apply_jsx_module_flag(
                            &val,
                            &mut opts.jsx_module,
                            &mut opts.jsx_version,
                        );
                    }
                }
                "-enable-experimental" => {
                    if let Some(val) = args.next() {
                        if val == "LetUnwrap" {
                            opts.experimental_let_unwrap = true;
                        }
                    }
                }
                "-bs-jsx-preserve" => opts.jsx_preserve = true,
                "-bs-no-version-header" => opts.no_version_header = true,
                "-bs-no-check-div-by-zero" => opts.no_check_div_by_zero = true,
                "-bs-cross-module-opt" => opts.cross_module_inline = true,
                "-bs-noassertfalse" => opts.no_assert_false = true,
                // OCaml compiler/bsc/rescript_compiler_main.ml:391-392
                // parses -noassert into Clflags.noassert.
                "-noassert" => opts.noassert = true,
                "-bs-no-builtin-ppx" => opts.no_builtin_ppx = true,
                // Run the configured in-process Spice mapper, as rewatch does
                // when a project selects the Spice PPX (used for profiling).
                "-bs-builtin-spice-ppx" => opts.builtin_spice_ppx = true,
                "-bs-gentype" => opts.gentype = true,
                // -bs-project-root and the -bs-gentype-* flags, mirroring
                // compiler/bsc/rescript_compiler_main.ml:266-270 and :300-343.
                flag if opts.gentype_flags.apply(flag, || args.next()) => {}
                "-w" => {
                    if let Some(val) = args.next() {
                        opts.warning_specs.push(val);
                    }
                }
                "-warn-error" => {
                    if let Some(val) = args.next() {
                        opts.warning_error_specs.push(val);
                    }
                }
                "-ppx" => {
                    if let Some(val) = args.next() {
                        if val.contains("spice") {
                            opts.builtin_spice_ppx = true;
                        } else {
                            eprintln!("External PPXs are no longer supported: {val}");
                            std::process::exit(2);
                        }
                    }
                }
                "-color" => {
                    if let Some(val) = args.next() {
                        if let Some(mode) = code_frame::parse_color_mode(&val) {
                            opts.color_mode = mode;
                        }
                    }
                }
                "-bs-jsx-mode" | "-ppxopt" => {
                    // Consume the next argument if present (value flags).
                    let _ = args.next();
                }
                "-bs-read-cmi" => opts.read_cmi = true,
                "-no-alias-deps" => opts.transparent_modules = true,
                "-absname" => opts.absname = true,
                "-bs-no-implicit-stdlib"
                | "-unsafe"
                | "-bs-super-errors"
                | "-bs-stop-after-cmj"
                | "-bs-no-check-cmi" => {
                    // Boolean flags - no argument to consume
                }
                // rescript_compiler_main.ml:440-450
                "-ignore-parse-errors" | "-editor-mode" => opts.ignore_parse_errors = true,
                "-format" => {
                    let file = args
                        .next()
                        .ok_or_else(|| anyhow!("-format requires a file"))?;
                    code_frame::set_color_mode(opts.color_mode);
                    format_file(&file, opts.output.as_deref(), opts.ignore_parse_errors)?;
                    opts.formatted = true;
                }
                "-make-runtime" => opts.make_runtime = true,
                "-nopervasives" => opts.nopervasives = true,
                // Unknown flags are ignored; a value that follows one is
                // taken as the input file.
                _ => {}
            }
        } else {
            opts.input = Some(PathBuf::from(arg));
        }
    }

    if opts.input.is_none() && opts.formatted {
        return Ok(());
    }
    let input = opts
        .input
        .clone()
        .ok_or_else(|| anyhow!("Missing input file"))?;
    // rescript_compiler_main.ml:43-48 `set_abs_input_name`.
    let input = if opts.absname && input.is_relative() {
        absolute_cwd_path(&input)
    } else {
        input
    };
    code_frame::set_color_mode(opts.color_mode);

    if opts.bs_ast {
        // `-bs-ast` runs the whole frontend (parser warnings, external and
        // builtin PPXs, JSX) before writing, like OCaml
        // compiler/core/js_implementation.ml:172-186.
        return generate_ast(
            &input,
            opts.output,
            opts.dump_parsetree_sexp_locs,
            &CompilerOptions {
                warning_specs: opts.warning_specs.clone(),
                warning_error_specs: opts.warning_error_specs.clone(),
                jsx_version: opts.jsx_version,
                jsx_module: opts.jsx_module.clone(),
                experimental_let_unwrap: opts.experimental_let_unwrap,
                jsx_preserve: opts.jsx_preserve,
                no_builtin_ppx: opts.no_builtin_ppx,
                spice_ppx: opts.builtin_spice_ppx,
                ..CompilerOptions::default()
            },
        );
    }

    let ext = input.extension().and_then(|s| s.to_str()).unwrap_or("");
    if let Some(registry) = registry {
        if matches!(ext, "cmi" | "ast" | "iast") {
            return Err(UserDiagnostic::new(
                format!(
                    "bsc: {} input needs the file-based compiler\n",
                    input.display()
                ),
                2,
            )
            .into());
        }
        let runtime_path = opts.runtime_path.clone().or_else(default_runtime_path);
        let include_dirs = opts.include_paths.clone();
        let registry = registry(runtime_path, include_dirs)?;
        // Building the registry compiles other units in process, which sets
        // the color mode and prints reports; a fresh `bsc` has done neither.
        code_frame::set_color_mode(opts.color_mode);
        code_frame::reset_color_setup();
        return compile_in_process(&input, &opts, registry);
    }
    if ext == "cmi" {
        return read_cmi_input(&input);
    }

    let from_ast = ext == "ast" || ext == "iast";
    let source_path = if from_ast {
        read_ast_source_path(&input)?
    } else {
        input
    };

    let is_interface = source_path
        .extension()
        .and_then(|s| s.to_str())
        .is_some_and(|ext| ext == "resi" || ext == "mli");

    // Auto-detect runtime path if not explicitly provided
    let runtime_path = opts.runtime_path.clone().or_else(default_runtime_path);
    let package_output = opts
        .package_outputs
        .first()
        .and_then(|spec| parse_package_output(spec));

    let compiler_opts = CompilerOptions {
        checker: crate::driver::CheckerChoice::from_env(),
        derived_census: CompilerOptions::derived_census_from_env(),
        derived_path: crate::driver::DerivedPath::from_env(),
        derived_reference: None,
        derived_differences: None,
        backend: crate::bir::shadow::BackendMode::from_env(),
        signature_check: crate::cmi::signature_check::SignatureCheck::from_env(),
        js_printer: crate::emit::PrinterMode::from_env(),
        check_only: false,
        typed_trees: None,
        dump_lambda: opts.dump_lambda,
        dump_typed_sexp: opts.dump_typed_sexp,
        dump_typed_sexp_locs: opts.dump_typed_sexp_locs,
        dump_lambda_sexp: opts.dump_lambda_sexp,
        dump_lambda_sexp_locs: opts.dump_lambda_sexp_locs,
        include_paths: opts.include_paths.clone(),
        runtime_path,
        open_modules: opts.open_modules.clone(),
        collect_unit_reads: false,
        warning_locations: None,
        warning_specs: opts.warning_specs.clone(),
        warning_error_specs: opts.warning_error_specs.clone(),
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path: opts.output.clone(),
        output_module_format: package_output
            .as_ref()
            .map(|(module_format, _, _)| *module_format),
        js_output_targets: Vec::new(),
        source_map: opts.source_map,
        source_map_sources_content: opts.source_map_sources_content,
        source_map_root: opts.source_map_root.clone(),
        jsx_version: opts.jsx_version,
        jsx_module: opts.jsx_module.clone(),
        experimental_let_unwrap: opts.experimental_let_unwrap,
        jsx_preserve: opts.jsx_preserve,
        debug: opts.debug,
        no_version_header: opts.no_version_header,
        check_div_by_zero: !opts.no_check_div_by_zero,
        cross_module_inline: opts.cross_module_inline,
        no_assert_false: opts.no_assert_false,
        noassert: opts.noassert,
        transparent_modules: opts.transparent_modules,
        no_builtin_ppx: opts.no_builtin_ppx,
        spice_ppx: opts.builtin_spice_ppx,
        nopervasives: opts.nopervasives,
        module_name: opts.module_name.clone(),
        package_name: opts.package_name.clone(),
        package_root: (!opts.gentype_flags.project_root.is_empty())
            .then(|| PathBuf::from(&opts.gentype_flags.project_root)),
        make_runtime: opts.make_runtime,
        assume_compiled_interface: opts.read_cmi,
        gentype_config: opts.gentype.then(|| {
            std::sync::Arc::new(crate::gentype::config::build_config_from_flags(
                opts.namespace.clone(),
                opts.gentype_flags.clone(),
            ))
        }),
        gentype_resolver: None,
        gentype_declarations_only: false,
        gentype_declarations_needed: true,
        js_package_specs: Vec::new(),
        capture_intermediates: false,
        dumps: Vec::new(),
        skip_js_render: false,
        publish_in_process_signature: true,
        frontend_already_reported: from_ast,
        visible_package_roots: None,
        keep_locs: true,
    };

    if is_interface {
        // Interface files (.resi) don't produce JS output
        typecheck_interface_file(&source_path, &compiler_opts)?;
        Ok(())
    } else {
        write_outputs(&source_path, &compiler_opts, &opts)
    }
}

/// Compile a source file in process against `registry`: write its
/// JavaScript like the file compile, and print its warnings and the requested
/// `-d...` dumps to stderr.
fn compile_in_process(
    source_path: &Path,
    opts: &Options,
    mut registry: crate::cmi::persistent_env::ModuleRegistry,
) -> Result<()> {
    use crate::driver::DumpKind;
    let bytes = fs::read(source_path)
        .with_context(|| format!("Failed to read {}", source_path.display()))?;
    let source = latin1_bytes_to_string(bytes);
    let filename = source_path.to_string_lossy().into_owned();
    let module_name = opts
        .module_name
        .clone()
        .unwrap_or_else(|| crate::driver::module_name_from_source_filename(&filename));
    let is_interface = source_path
        .extension()
        .and_then(|s| s.to_str())
        .is_some_and(|ext| ext == "resi" || ext == "mli");

    let mut options = CompilerOptions {
        include_paths: opts.include_paths.clone(),
        open_modules: opts.open_modules.clone(),
        warning_specs: opts.warning_specs.clone(),
        warning_error_specs: opts.warning_error_specs.clone(),
        source_filename: Some(filename.clone()),
        source_map: opts.source_map,
        source_map_sources_content: opts.source_map_sources_content,
        source_map_root: opts.source_map_root.clone(),
        jsx_version: opts.jsx_version,
        jsx_module: opts.jsx_module.clone(),
        experimental_let_unwrap: opts.experimental_let_unwrap,
        jsx_preserve: opts.jsx_preserve,
        debug: opts.debug,
        no_version_header: opts.no_version_header,
        check_div_by_zero: !opts.no_check_div_by_zero,
        cross_module_inline: opts.cross_module_inline,
        no_assert_false: opts.no_assert_false,
        noassert: opts.noassert,
        transparent_modules: opts.transparent_modules,
        no_builtin_ppx: opts.no_builtin_ppx,
        spice_ppx: opts.builtin_spice_ppx,
        nopervasives: opts.nopervasives,
        module_name: opts.module_name.clone(),
        package_name: opts.package_name.clone(),
        package_root: (!opts.gentype_flags.project_root.is_empty())
            .then(|| PathBuf::from(&opts.gentype_flags.project_root)),
        gentype_config: opts.gentype.then(|| {
            std::sync::Arc::new(crate::gentype::config::build_config_from_flags(
                opts.namespace.clone(),
                opts.gentype_flags.clone(),
            ))
        }),
        ..CompilerOptions::default()
    };
    for (requested, kind) in [
        (opts.dump_typed_sexp, DumpKind::TypedTree),
        (opts.dump_typed_sexp_locs, DumpKind::TypedTreeLocs),
        (opts.dump_lambda, DumpKind::RawLambda),
        (opts.dump_lambda_sexp, DumpKind::Lambda),
        (opts.dump_lambda_sexp_locs, DumpKind::LambdaLocs),
    ] {
        if requested {
            options.dumps.push(kind);
        }
    }

    let print_dumps = |dumps: &[(DumpKind, String)]| {
        let mut stderr = io::stderr();
        for (_, text) in dumps {
            let bytes: Vec<u8> = text.chars().map(|c| c as u32 as u8).collect();
            let _ = stderr.write_all(&bytes);
        }
    };

    crate::perf_counters::begin_cli_unit();
    if is_interface {
        let result = crate::driver::typecheck_interface_source_in_process(
            &source,
            &filename,
            &module_name,
            &options,
            &registry,
        )?;
        eprint!("{}", result.warnings);
        print_dumps(&result.dumps);
        return Ok(());
    }

    // The file compile reads the interface's `.cmi`; in process, type the
    // sibling `.resi` and publish its signature as the build does. Its
    // warnings belong to the interface compile, so they are not printed.
    let interface_path = source_path.with_extension("resi");
    let has_interface = opts.read_cmi && interface_path.is_file();
    let mut gentype_interface = None;
    if has_interface {
        let bytes = fs::read(&interface_path)
            .with_context(|| format!("Failed to read {}", interface_path.display()))?;
        let interface_source = latin1_bytes_to_string(bytes);
        let mut interface_options = options.clone();
        interface_options.dumps.clear();
        interface_options.source_filename = Some(interface_path.to_string_lossy().into_owned());
        let interface = crate::driver::typecheck_interface_source_in_process(
            &interface_source,
            &interface_path.to_string_lossy(),
            &module_name,
            &interface_options,
            &registry,
        )?;
        gentype_interface = interface.gentype;
        if let Some(pers_struct) = interface.pers_struct {
            registry.register_module_arc(
                &module_name,
                pers_struct,
                crate::cmi::persistent_env::InMemoryModuleInfo::new(
                    source_path.to_path_buf(),
                    true,
                    Default::default(),
                    false,
                ),
            );
        }
    }

    // Where the JavaScript goes, as for the file compile.
    let mut targets = Vec::new();
    if let Some(out) = &opts.output {
        options.output_path = Some(out.clone());
        targets.push(crate::driver::JsOutputTarget {
            path: out.clone(),
            module_format: if out.extension().is_some_and(|ext| ext == "mjs") {
                ModuleFormat::EsModule
            } else {
                ModuleFormat::CommonJs
            },
        });
    } else {
        for spec in &opts.package_outputs {
            if let Some((module_format, dir, suffix)) = parse_package_output(spec) {
                targets.push(crate::driver::JsOutputTarget {
                    path: package_output_path(
                        &opts.gentype_flags.project_root,
                        source_path,
                        &dir,
                        &suffix,
                    ),
                    module_format,
                });
            }
        }
    }
    options.js_output_targets = targets.clone();

    crate::perf_counters::begin_cli_unit();
    let result = crate::driver::compile_source_in_process(
        &source,
        &filename,
        &module_name,
        &options,
        &registry,
        has_interface,
        gentype_interface,
    )?;
    eprint!("{}", result.warnings);
    // OCaml prints the requested dumps and still emits the JavaScript.
    print_dumps(&result.dumps);
    if targets.is_empty() {
        print!("{}", result.js_output);
        print!(
            "{}",
            crate::driver::apply_gentype_outcome(result.gentype, "", &filename)?
        );
        return Ok(());
    }
    for output in &result.js_outputs {
        if let Some(parent) = output.path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&output.path, &output.code)?;
    }
    print!(
        "{}",
        crate::driver::apply_gentype_outcome(result.gentype, "", &filename)?
    );
    Ok(())
}

fn read_cmi_input(input: &Path) -> Result<()> {
    let filename = input.to_string_lossy();
    match cmi_format::read_cmi(&filename) {
        Ok(_cmi) => Ok(()),
        Err(cmi_format::CmiError::Io(err)) => Err(err).with_context(|| filename.to_string()),
        Err(err) => Err(UserDiagnostic::new(format_cmi_error_report(&err), 2).into()),
    }
}

fn format_cmi_error_report(err: &cmi_format::CmiError) -> String {
    format!("\n  We've found a bug for you!\n  _none_\n\n  {err}\n\n")
}

fn generate_ast(
    input: &Path,
    output: Option<PathBuf>,
    dump_parsetree_sexp_locs: bool,
    options: &CompilerOptions,
) -> Result<()> {
    // Read file as raw bytes, converting each byte to a char (Latin-1 encoding).
    // This matches OCaml's byte-level string handling where each byte is a character.
    // In Latin-1 mode, char offset == original byte offset, which is critical for
    // correct position tracking in the scanner and correct UTF-16 offset calculations
    // for multi-byte UTF-8 sequences (e.g., emoji characters).
    let bytes = fs::read(input).with_context(|| format!("Failed to read {}", input.display()))?;
    let source = latin1_bytes_to_string(bytes);

    // Use the original path as provided (matching OCaml's behavior)
    // OCaml does not canonicalize paths - it uses them as-is
    let source_path = input.to_string_lossy().to_string();

    let filename = input.to_string_lossy().to_string();

    // Determine if this is an interface (.resi) or implementation (.res)
    let is_interface = input
        .extension()
        .and_then(|s| s.to_str())
        .is_some_and(|ext| ext == "resi" || ext == "mli");

    // Determine output path and extension
    // Note: OCaml ignores the -o extension for interface files, always using .iast
    let out_path = match output {
        Some(path) => {
            if is_interface {
                path.with_extension("iast")
            } else {
                path
            }
        }
        None => {
            if is_interface {
                input.with_extension("iast")
            } else {
                input.with_extension("ast")
            }
        }
    };

    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent)?;
    }

    // Stored ASTs must contain syntax, not process-local derived plans.
    let options = &CompilerOptions {
        derived_path: crate::driver::DerivedPath::General,
        ..options.clone()
    };
    let mut parser = Parser::new(&filename, &source);
    let mut frontend_output = String::new();
    let warnings_are_fatal;

    if is_interface {
        let signature = module::parse_signature(&mut parser);
        let frontend = run_interface_frontend(
            &mut parser,
            signature,
            &source,
            &filename,
            options,
            &mut frontend_output,
        );
        eprint!("{frontend_output}");
        let frontend = frontend?;
        warnings_are_fatal = frontend.warnings_fatal;

        if dump_parsetree_sexp_locs {
            let mut stderr = std::io::stderr();
            sexp_locs::print_signature(&frontend.signature, parser.arena(), &mut stderr);
            let _ = stderr.write_all(b"\n");
        }

        if let Some(extension) =
            deps::signature_error_extension(parser.arena(), &frontend.signature)
        {
            return Err(error_extension_to_anyhow(
                parser.arena(),
                &source,
                &filename,
                &extension,
            ));
        }
        // The frontend already applied the builtin PPX.
        write_signature_ast_current_with_extra_deps_and_builtin_ppx(
            &out_path,
            &source_path,
            parser.arena_mut(),
            &frontend.signature,
            &[],
            false,
        )
        .with_context(|| format!("Failed to write {}", out_path.display()))?;
    } else {
        let structure = module::parse_structure(&mut parser);
        let frontend = run_implementation_frontend(
            &mut parser,
            structure,
            &source,
            &filename,
            options,
            &mut frontend_output,
        );
        eprint!("{frontend_output}");
        let frontend = frontend?;
        warnings_are_fatal = frontend.warnings_fatal;

        if dump_parsetree_sexp_locs {
            let mut stderr = std::io::stderr();
            sexp_locs::print_structure(&frontend.structure, parser.arena(), &mut stderr);
            let _ = stderr.write_all(b"\n");
        }

        if let Some(extension) =
            deps::structure_error_extension(parser.arena(), &frontend.structure)
        {
            return Err(error_extension_to_anyhow(
                parser.arena(),
                &source,
                &filename,
                &extension,
            ));
        }
        // The frontend already applied the builtin PPX.
        write_structure_ast_current_with_extra_deps_and_builtin_ppx(
            &out_path,
            &source_path,
            parser.arena_mut(),
            &frontend.structure,
            &[],
            false,
        )
        .with_context(|| format!("Failed to write {}", out_path.display()))?;
    }

    if warnings_are_fatal {
        return Err(UserDiagnostic::new(String::new(), 2).into());
    }
    Ok(())
}

fn read_ast_source_path(ast_path: &Path) -> Result<PathBuf> {
    let content =
        fs::read(ast_path).with_context(|| format!("Failed to read {}", ast_path.display()))?;

    if content.len() < 5 {
        return Err(anyhow!("Invalid .ast file: too small"));
    }

    // `Binary_ast.read_header` (compiler/depends/binary_ast.ml): a header
    // whose source path has no newline after it is damaged, as when a killed
    // build cut the file short.
    let header = crate::binary_ast::header::read_header(&content)
        .ok_or_else(|| anyhow!("Invalid .ast file: missing source path"))?;
    let path_bytes = crate::binary_ast::header::header_source(&content, &header);
    let path_str = String::from_utf8_lossy(path_bytes);

    if path_str.is_empty() {
        return Err(anyhow!("Invalid .ast file: empty source path"));
    }

    Ok(PathBuf::from(path_str.into_owned()))
}

fn write_outputs(
    source_path: &Path,
    compiler_opts: &CompilerOptions,
    opts: &Options,
) -> Result<()> {
    if opts.has_dump_output() {
        let js = compile_file_to_js_with_options(source_path, compiler_opts)?;
        write_precompiled_outputs(source_path, &js, opts)?;
        return maybe_process_gentype(source_path, opts);
    }

    if let Some(out) = &opts.output {
        let mut output_opts = compiler_opts.clone();
        output_opts.output_path = Some(out.clone());
        let js = compile_file_to_js_with_options(source_path, &output_opts)?;
        if let Some(parent) = out.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(out, js)?;
        return maybe_process_gentype(source_path, opts);
    }

    if !opts.package_outputs.is_empty() {
        for spec in &opts.package_outputs {
            if let Some((format, dir, suffix)) = parse_package_output(spec) {
                let out_path = package_output_path(
                    &opts.gentype_flags.project_root,
                    source_path,
                    &dir,
                    &suffix,
                );
                let mut output_opts = compiler_opts.clone();
                output_opts.output_path = Some(out_path.clone());
                output_opts.output_module_format = Some(format);
                let js = compile_file_to_js_with_options(source_path, &output_opts)?;
                if let Some(parent) = out_path.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(out_path, js)?;
            }
        }
        return maybe_process_gentype(source_path, opts);
    }

    let mut output_opts = compiler_opts.clone();
    output_opts.output_path = None;
    output_opts.output_module_format = None;
    let js = compile_file_to_js_with_options(source_path, &output_opts)?;
    print!("{js}");
    maybe_process_gentype(source_path, opts)
}

fn path_without_extension(path: &Path) -> PathBuf {
    let mut path = path.to_path_buf();
    path.set_extension("");
    path
}

fn gentype_output_prefix(source_path: &Path, opts: &Options) -> PathBuf {
    match &opts.output {
        Some(output) => path_without_extension(output),
        None => path_without_extension(source_path),
    }
}

fn uncapitalize_ascii_filename(path: &Path) -> Option<PathBuf> {
    let file_name = path.file_name()?.to_str()?;
    let mut chars = file_name.chars();
    let first = chars.next()?;
    let lowered = first.to_ascii_lowercase().to_string() + chars.as_str();
    Some(path.with_file_name(lowered))
}

fn gentype_cmt_file_for_output_prefix(output_prefix: &Path) -> Option<PathBuf> {
    // Mirrors compiler/gentype/Paths.ml:get_cmt_file for the output.cmt path
    // passed by compiler/core/js_implementation.ml after code generation.
    let path_cmt = output_prefix.with_extension("cmt");
    if path_cmt.extension().and_then(|ext| ext.to_str()) != Some("cmt") {
        return None;
    }

    let path_cmt_lower_case = uncapitalize_ascii_filename(&path_cmt)?;
    let path_cmti = output_prefix.with_extension("cmti");
    let path_cmti_lower_case = path_cmt_lower_case.with_extension("cmti");

    [
        path_cmti_lower_case,
        path_cmti,
        path_cmt_lower_case,
        path_cmt,
    ]
    .into_iter()
    .find(|candidate| candidate.exists())
}

fn maybe_process_gentype(source_path: &Path, opts: &Options) -> Result<()> {
    if !opts.gentype {
        return Ok(());
    }

    let output_prefix = gentype_output_prefix(source_path, opts);
    let Some(cmt_file) = gentype_cmt_file_for_output_prefix(&output_prefix) else {
        return Ok(());
    };

    check_gentype_cmt_file(&cmt_file)
}

fn check_gentype_cmt_file(cmt_file: &Path) -> Result<()> {
    // Cmt_format.read_cmt raises Cmt_format.Error(Not_a_typedtree _) when the
    // selected file contains a compiled interface without typedtree data.
    const CMT_MAGIC: &[u8; 12] = b"Caml1999T039";
    const CMI_MAGIC: &[u8] = crate::cmi::cmi_format::CMI_MAGIC;

    let data = fs::read(cmt_file).with_context(|| cmt_file.display().to_string())?;
    if data.len() < CMT_MAGIC.len() {
        return Ok(());
    }

    let magic = &data[..CMT_MAGIC.len()];
    if magic == CMT_MAGIC {
        return Ok(());
    }

    if magic.starts_with(CMI_MAGIC) {
        let _ = io::stdout().flush();
        return Err(UserDiagnostic::new(
            "Fatal error: exception Cmt_format.Error(_)\n".to_string(),
            2,
        )
        .into());
    }

    print!(
        "  Error loading {}\n\n  It looks like you might have stale compilation artifacts.\n  Try to clean and rebuild.\n\n",
        gentype_display_path(cmt_file).display()
    );
    let _ = io::stdout().flush();
    Err(UserDiagnostic::new(
        "Fatal error: exception File \"compiler/gentype/gentype_main.ml\", line 89, characters 4-10: Assertion failed\n".to_string(),
        2,
    )
    .into())
}

fn gentype_display_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        return path.to_path_buf();
    }

    match env::current_dir() {
        Ok(cwd) => cwd.join(path),
        Err(_) => path.to_path_buf(),
    }
}

fn write_precompiled_outputs(source_path: &Path, js: &str, opts: &Options) -> Result<()> {
    if let Some(out) = &opts.output {
        if let Some(parent) = out.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(out, js)?;
        return Ok(());
    }

    if !opts.package_outputs.is_empty() {
        for spec in &opts.package_outputs {
            if let Some((_format, dir, suffix)) = parse_package_output(spec) {
                let out_path = package_output_path(
                    &opts.gentype_flags.project_root,
                    source_path,
                    &dir,
                    &suffix,
                );
                if let Some(parent) = out_path.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(out_path, js)?;
            }
        }
        return Ok(());
    }

    let out = source_path.with_extension("js");
    if let Some(parent) = out.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(out, js)?;
    Ok(())
}

fn parse_package_output(spec: &str) -> Option<(ModuleFormat, String, String)> {
    let parts = spec.split(':').collect::<Vec<_>>();
    // OCaml compiler/core/js_packages_info.ml:177-193 parses
    // `-bs-package-output` as `[path]`, `[module_system:path]`, or
    // `[module_system:path:suffix]`, defaulting the one-part form to ESModule.
    match parts.as_slice() {
        [dir] => Some((
            ModuleFormat::EsModule,
            (*dir).to_string(),
            ".js".to_string(),
        )),
        [module_system, dir] => Some((
            parse_module_format(module_system)?,
            (*dir).to_string(),
            ".js".to_string(),
        )),
        [module_system, dir, suffix] => Some((
            parse_module_format(module_system)?,
            (*dir).to_string(),
            (*suffix).to_string(),
        )),
        _ => None,
    }
}

fn parse_module_format(module_system: &str) -> Option<ModuleFormat> {
    // OCaml compiler/core/js_packages_info.ml:96-100 recognizes the same
    // module-system names in `module_system_of_string`.
    match module_system {
        "commonjs" => Some(ModuleFormat::CommonJs),
        "esmodule" => Some(ModuleFormat::EsModule),
        _ => None,
    }
}

/// ext_path.ml:91-106 `absolute_cwd_path`: join with the working directory and
/// drop `.`/`..` components lexically.
fn absolute_cwd_path(path: &Path) -> PathBuf {
    let joined = env::current_dir().unwrap_or_default().join(path);
    let mut out = PathBuf::new();
    for component in joined.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// lam_compile_main.ml:487-495: package outputs go to
/// `Ext_path.package_dir () // path // basename`, where `package_dir` is the
/// `-bs-project-root` directory. Without a project root (which OCaml rejects)
/// the directory stays relative to the working directory.
///
/// lam_compile_main.ml:484-492 uses the output-prefix basename, not the
/// capitalized module identity. `Ext_namespace.change_ext_ns_suffix`
/// (ext_namespace.ml:33-35) strips only the last namespace suffix.
fn package_output_path(
    project_root: &str,
    source_path: &Path,
    directory: &str,
    suffix: &str,
) -> PathBuf {
    let stem = source_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Module");
    let basename = stem.rsplit_once('-').map_or(stem, |(base, _)| base);
    let directory = if project_root.is_empty() {
        PathBuf::from(directory)
    } else {
        // `Filename.concat` appends even an absolute `path`.
        Path::new(project_root).join(directory.trim_start_matches('/'))
    };
    directory.join(format!("{basename}{suffix}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `bsc X.ast` takes the source path from the AST's header, read like
    /// `Binary_ast.read_header`: a path without its newline is damaged, and
    /// an empty one is not a source. Files are removed one by one, and the
    /// directory only when empty.
    #[test]
    fn ast_input_source_path_follows_the_header_contract() {
        let dir = std::env::temp_dir().join(format!("bsc-ast-header-{}", std::process::id()));
        fs::create_dir(&dir).expect("fresh test directory");
        let cases: [(&str, &[u8], Result<&str, &str>); 6] = [
            (
                "Whole.ast",
                b"\x00\x00\x00\x09\nBelt\nJs\n/src/A.res\n\x84\x95",
                Ok("/src/A.res"),
            ),
            (
                "LastByte.ast",
                b"\x00\x00\x00\x01\n/src/A.res\n",
                Ok("/src/A.res"),
            ),
            (
                "Unterminated.ast",
                b"\x00\x00\x00\x01\n/src/A.res",
                Err("missing source path"),
            ),
            (
                "Negative.ast",
                b"\xff\xff\xff\xff\nA\n/a.res\n",
                Err("missing source path"),
            ),
            (
                "Empty.ast",
                b"\x00\x00\x00\x01\n\n",
                Err("empty source path"),
            ),
            ("Short.ast", b"\x00\x00", Err("too small")),
        ];
        let mut outcomes = Vec::new();
        for (name, contents, _) in &cases {
            let path = dir.join(name);
            fs::write(&path, contents).expect("write AST");
            outcomes.push(read_ast_source_path(&path).map_err(|error| error.to_string()));
            fs::remove_file(&path).expect("remove AST");
        }
        fs::remove_dir(&dir).expect("remove empty test directory");
        for ((name, _, expected), outcome) in cases.iter().zip(outcomes) {
            match (expected, outcome) {
                (Ok(source), Ok(path)) => assert_eq!(path, PathBuf::from(source), "{name}"),
                (Err(message), Err(error)) => {
                    assert!(error.contains(message), "{name}: {error}")
                }
                (expected, outcome) => panic!("{name}: expected {expected:?}, got {outcome:?}"),
            }
        }
    }

    #[test]
    fn package_outputs_preserve_source_case_and_strip_namespace_suffix() {
        for (source, expected) in [
            ("src/lower_case.res", "out/lower_case.mjs"),
            ("src/mixedCase.res", "out/mixedCase.mjs"),
            ("src/UpperCase.res", "out/UpperCase.mjs"),
            ("src/lower_case-Namespace.res", "out/lower_case.mjs"),
            ("src/first-part-Namespace.res", "out/first-part.mjs"),
        ] {
            assert_eq!(
                package_output_path("", Path::new(source), "out", ".mjs"),
                Path::new(expected)
            );
        }
    }

    #[test]
    fn package_outputs_are_relative_to_the_project_root() {
        assert_eq!(
            package_output_path("/proj", Path::new("src/A.ast"), "src", ".res.js"),
            Path::new("/proj/src/A.res.js")
        );
        assert_eq!(
            package_output_path("/proj", Path::new("src/A.ast"), "lib/es6/src", ".js"),
            Path::new("/proj/lib/es6/src/A.js")
        );
    }
}
