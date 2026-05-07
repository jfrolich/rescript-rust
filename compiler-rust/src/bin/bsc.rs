//! Minimal Rust bsc replacement.
//!
//! This is a lightweight CLI that supports:
//! - `-bs-ast` parsing (produces a simple .ast file)
//! - compiling a .res/.resi (or .ast) file to JS using the Rust pipeline
//! - `-bs-package-output` for determining output directories
//! - `-bs-ns` for namespace suffix in module names
//!
//! All other flags are accepted and ignored.

use anyhow::{Context, Result, anyhow};
use rescript_compiler::binary_ast::{
    ppx, write_signature_ast_current, write_structure_ast_current,
};
use rescript_compiler::driver::{
    CompilerOptions, compile_file_to_js_with_options, enable_cli_cleanup_skip,
    typecheck_interface_file,
};
use rescript_compiler::js_ir::ModuleFormat;
use rescript_compiler::parser::{Parser, module, sexp_locs};
use rescript_compiler::source_text::latin1_bytes_to_string;
use std::env;
use std::fs;
use std::io::Write;
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
    //   Rust:  compiler-rust/target/release/bsc (3 levels)
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
    bs_ast: bool,
    debug: bool,
    dump_lambda: bool,
    dump_parsetree_sexp_locs: bool,
    dump_typed_sexp: bool,
    dump_typed_sexp_locs: bool,
    dump_lambda_sexp: bool,
    dump_lambda_sexp_locs: bool,
    output: Option<PathBuf>,
    package_outputs: Vec<String>,
    namespace: Option<String>,
    module_name: Option<String>,
    input: Option<PathBuf>,
    include_paths: Vec<PathBuf>,
    runtime_path: Option<PathBuf>,
    package_name: Option<String>,
    open_modules: Vec<String>,
    jsx_version: Option<i32>,
    experimental_let_unwrap: bool,
    jsx_preserve: bool,
    nopervasives: bool,
    no_version_header: bool,
    no_check_div_by_zero: bool,
    cross_module_inline: bool,
    no_assert_false: bool,
    make_runtime: bool,
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

fn main() {
    // Spawn the compiler in a thread with a large stack to avoid stack overflow
    // on deeply nested type structures in CMI files
    let builder = std::thread::Builder::new()
        .name("compiler".into())
        .stack_size(512 * 1024 * 1024); // 512MB

    let handler = builder
        .spawn(|| {
            enable_cli_cleanup_skip();
            match run() {
                Ok(()) => {
                    let _ = std::io::stdout().flush();
                    let _ = std::io::stderr().flush();
                    std::process::exit(0);
                }
                Err(err) => {
                    eprintln!("{err}");
                    let _ = std::io::stderr().flush();
                    std::process::exit(1);
                }
            }
        })
        .expect("Failed to spawn compiler thread");

    handler.join().expect("Compiler thread panicked");
}

fn run() -> Result<()> {
    let mut opts = Options::default();
    let mut args = env::args().skip(1).peekable();

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
                "-bs-package-output" => {
                    if let Some(val) = args.next() {
                        opts.package_outputs.push(val);
                    }
                }
                "-bs-ns" => {
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
                "-w" | "-warn-error" | "-color" | "-bs-jsx-mode" | "-pp" | "-ppx" | "-ppxopt" => {
                    // Consume the next argument if present (value flags).
                    let _ = args.next();
                }
                "-absname"
                | "-bs-read-cmi"
                | "-no-alias-deps"
                | "-bs-no-implicit-stdlib"
                | "-unsafe"
                | "-bs-super-errors"
                | "-bs-stop-after-cmj"
                | "-bs-no-check-cmi" => {
                    // Boolean flags - no argument to consume
                }
                "-make-runtime" => opts.make_runtime = true,
                "-nopervasives" => opts.nopervasives = true,
                _ => {
                    // Unknown flag: ignore, but if it looks like a value flag, try to skip.
                }
            }
        } else {
            opts.input = Some(PathBuf::from(arg));
        }
    }

    let input = opts
        .input
        .clone()
        .ok_or_else(|| anyhow!("Missing input file"))?;

    if opts.bs_ast {
        return generate_ast(&input, opts.output, opts.dump_parsetree_sexp_locs);
    }

    let ext = input.extension().and_then(|s| s.to_str()).unwrap_or("");
    let source_path = if ext == "ast" || ext == "iast" {
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
        dump_lambda: opts.dump_lambda,
        dump_typed_sexp: opts.dump_typed_sexp,
        dump_typed_sexp_locs: opts.dump_typed_sexp_locs,
        dump_lambda_sexp: opts.dump_lambda_sexp,
        dump_lambda_sexp_locs: opts.dump_lambda_sexp_locs,
        include_paths: opts.include_paths.clone(),
        runtime_path,
        open_modules: opts.open_modules.clone(),
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path: opts.output.clone(),
        output_module_format: package_output
            .as_ref()
            .map(|(module_format, _, _)| *module_format),
        js_output_targets: Vec::new(),
        jsx_version: opts.jsx_version,
        experimental_let_unwrap: opts.experimental_let_unwrap,
        jsx_preserve: opts.jsx_preserve,
        debug: opts.debug,
        no_version_header: opts.no_version_header,
        check_div_by_zero: !opts.no_check_div_by_zero,
        cross_module_inline: opts.cross_module_inline,
        no_assert_false: opts.no_assert_false,
        nopervasives: opts.nopervasives,
        module_name: opts.module_name.clone(),
        package_name: opts.package_name.clone(),
        make_runtime: opts.make_runtime,
        capture_intermediates: false,
        skip_js_render: false,
        publish_in_process_signature: true,
    };

    if is_interface {
        // Interface files (.resi) don't produce JS output
        typecheck_interface_file(&source_path, &compiler_opts)?;
        Ok(())
    } else {
        write_outputs(&source_path, &compiler_opts, &opts)
    }
}

fn generate_ast(
    input: &Path,
    output: Option<PathBuf>,
    dump_parsetree_sexp_locs: bool,
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

    let mut parser = Parser::new(filename, &source);

    if is_interface {
        // Parse signature (interface file)
        let signature = module::parse_signature(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }

        if dump_parsetree_sexp_locs {
            let rewritten = ppx::rewrite_signature(&signature, parser.arena_mut())
                .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;
            let mut stderr = std::io::stderr();
            sexp_locs::print_signature(&rewritten, parser.arena(), &mut stderr);
            let _ = stderr.write_all(b"\n");
        }

        write_signature_ast_current(&out_path, &source_path, parser.arena_mut(), &signature)
            .with_context(|| format!("Failed to write {}", out_path.display()))?;
    } else {
        // Parse structure (implementation file)
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }

        if dump_parsetree_sexp_locs {
            let rewritten = ppx::rewrite_structure(&structure, parser.arena_mut())
                .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;
            let mut stderr = std::io::stderr();
            sexp_locs::print_structure(&rewritten, parser.arena(), &mut stderr);
            let _ = stderr.write_all(b"\n");
        }

        write_structure_ast_current(&out_path, &source_path, parser.arena_mut(), &structure)
            .with_context(|| format!("Failed to write {}", out_path.display()))?;
    }

    Ok(())
}

fn read_ast_source_path(ast_path: &Path) -> Result<PathBuf> {
    let content =
        fs::read(ast_path).with_context(|| format!("Failed to read {}", ast_path.display()))?;

    if content.len() < 5 {
        return Err(anyhow!("Invalid .ast file: too small"));
    }

    // Read the dependency section size (4 bytes, big-endian)
    let dep_size = u32::from_be_bytes([content[0], content[1], content[2], content[3]]) as usize;

    // Skip past the dependency section to get to the source path
    let path_start = 4 + dep_size;
    if path_start >= content.len() {
        return Err(anyhow!("Invalid .ast file: missing source path"));
    }

    // Read until newline to get the source path
    let path_end = content[path_start..]
        .iter()
        .position(|&b| b == b'\n')
        .map(|pos| path_start + pos)
        .unwrap_or(content.len());

    let path_bytes = &content[path_start..path_end];
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
        return write_precompiled_outputs(source_path, &js, opts);
    }

    if let Some(out) = &opts.output {
        let mut output_opts = compiler_opts.clone();
        output_opts.output_path = Some(out.clone());
        let js = compile_file_to_js_with_options(source_path, &output_opts)?;
        if let Some(parent) = out.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(out, js)?;
        return Ok(());
    }

    if !opts.package_outputs.is_empty() {
        for spec in &opts.package_outputs {
            if let Some((format, dir, suffix)) = parse_package_output(spec) {
                let module_name = module_name_for_file(
                    source_path,
                    opts.namespace.as_deref(),
                    opts.module_name.as_deref(),
                );
                let out_path = Path::new(&dir).join(format!("{module_name}{suffix}"));
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
        return Ok(());
    }

    let out = source_path.with_extension("js");
    let mut output_opts = compiler_opts.clone();
    output_opts.output_path = Some(out.clone());
    output_opts.output_module_format = None;
    let js = compile_file_to_js_with_options(source_path, &output_opts)?;
    if let Some(parent) = out.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(out, js)?;
    Ok(())
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
                let module_name = module_name_for_file(
                    source_path,
                    opts.namespace.as_deref(),
                    opts.module_name.as_deref(),
                );
                let out_path = Path::new(&dir).join(format!("{module_name}{suffix}"));
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

fn module_name_for_file(path: &Path, ns: Option<&str>, override_name: Option<&str>) -> String {
    if let Some(name) = override_name {
        return name.to_string();
    }
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Module");
    let base = if let Some(ns) = ns {
        if ns.is_empty() {
            stem.to_string()
        } else {
            format!("{stem}-{ns}")
        }
    } else {
        stem.to_string()
    };
    capitalize(&base)
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
