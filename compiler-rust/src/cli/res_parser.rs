//! ReScript Parser CLI
//!
//! This CLI provides a drop-in replacement for the OCaml `res_parser` CLI,
//! enabling the Rust parser to run the existing syntax tests.
//!
//! Uses the same single-dash CLI format as the OCaml parser for compatibility.
//!
//! Usage:
//!   res_parser_rust [options] <file>
//!
//! Options:
//!   -print <format>         Output format: ml, res, sexp, sexp-locs, sexp-locs-ppx, sexp0-locs, binary, binary0, ast, comments, tokens
//!   -recover                Enable error recovery mode
//!   -interface              Parse as interface file
//!   -width <n>              Line width for printer (default: 100)
//!   -jsx-version <n>        JSX version (3 or 4)
//!   -jsx-module <mod>       JSX module (default: react)
//!   -test-ast-conversion    Test AST conversion roundtrip (parsetree -> parsetree0 -> parsetree)

use crate::binary_ast::{Marshal, MarshalWriter, mapper_from0, mapper_to0, ppx};
use crate::location::Position;
use crate::parse_arena::ParseArena;
use crate::parser::{
    Comment, Parser, ParserWarning, Scanner, SignatureItem, Structure, code_frame, jsx_ppx,
    ml_printer, module, printer, sexp, sexp_locs, sexp_locs0,
};
use crate::source_text::latin1_bytes_to_string;
use clap::Parser as ClapParser;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process;

/// A Write adapter that collects UTF-8 output and stores it as chars in a String.
/// When the ML printer writes chars as UTF-8, this captures them and stores the
/// decoded chars, preserving the original Latin-1 encoding from the source.
struct StringWriter(String);

impl StringWriter {
    fn new() -> Self {
        StringWriter(String::new())
    }

    fn into_string(self) -> String {
        self.0
    }
}

impl Write for StringWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // buf contains UTF-8 encoded bytes from write! macro
        // Convert back to a &str (which is what was originally written)
        match std::str::from_utf8(buf) {
            Ok(s) => {
                self.0.push_str(s);
                Ok(buf.len())
            }
            Err(_) => {
                // Fallback: treat as Latin-1 bytes
                for &b in buf {
                    self.0.push(b as char);
                }
                Ok(buf.len())
            }
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// ReScript Parser CLI - for testing purposes only
#[derive(ClapParser, Debug)]
#[command(name = "res_parser_rust")]
#[command(about = "ReScript parser CLI for testing - matches OCaml res_parser interface")]
struct Args {
    /// Input file to parse
    file: PathBuf,

    /// Output format: ml, res, sexp, ast, comments, tokens (default: res)
    #[arg(short = 'p', long = "print", default_value = "res")]
    print: String,

    /// Enable error recovery mode
    #[arg(short = 'r', long = "recover")]
    recover: bool,

    /// Parse as interface file (.resi)
    #[arg(short = 'i', long = "interface")]
    interface: bool,

    /// Line width for printer
    #[arg(short = 'w', long = "width", default_value = "100")]
    width: usize,

    /// JSX version (3 or 4)
    #[arg(long = "jsx-version", default_value = "-1")]
    jsx_version: i32,

    /// JSX module
    #[arg(long = "jsx-module", default_value = "react")]
    jsx_module: String,

    /// Test AST conversion
    #[arg(long = "test-ast-conversion")]
    test_ast_conversion: bool,
}

/// Convert OCaml-style single-dash long options to GNU-style double-dash options.
/// This allows the same CLI to work with scripts written for the OCaml parser.
/// e.g., "-print" -> "--print", "-recover" -> "--recover"
fn normalize_args(args: Vec<String>) -> Vec<String> {
    std::iter::once("res_parser".to_string())
        .chain(args)
        .map(|arg| {
            // Convert OCaml-style options to GNU-style
            match arg.as_str() {
                "-print" => "--print".to_string(),
                "-recover" => "--recover".to_string(),
                "-interface" => "--interface".to_string(),
                "-width" => "--width".to_string(),
                "-jsx-version" => "--jsx-version".to_string(),
                "-jsx-module" => "--jsx-module".to_string(),
                "-test-ast-conversion" => "--test-ast-conversion".to_string(),
                _ => arg,
            }
        })
        .collect()
}

/// Run the parser CLI with `args` (without the program name); never returns.
pub fn main(args: Vec<String>) {
    // Parse on a thread with a large stack, like `bsc`, so deeply nested input
    // does not overflow the default main-thread stack.
    let handle = std::thread::Builder::new()
        .name("res_parser".into())
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(args))
        .expect("failed to spawn parser thread");
    if handle.join().is_err() {
        process::exit(2);
    }
}

fn run(args: Vec<String>) {
    let args = Args::parse_from(normalize_args(args));

    // Read file as raw bytes, converting each byte to a char (Latin-1 encoding).
    // This preserves the original byte sequence through the compilation pipeline,
    // allowing the final output to convert back to bytes with `c as u8`.
    // This approach handles both ASCII and UTF-8 files correctly because:
    // - Each byte becomes a char with code point 0-255
    // - The ML printer's escape_string function properly escapes bytes > 127
    // - The output conversion `c as u8` recovers the original bytes
    let source = match fs::read(&args.file) {
        Ok(bytes) => latin1_bytes_to_string(bytes),
        Err(e) => {
            eprintln!("Error reading file {:?}: {}", args.file, e);
            process::exit(1);
        }
    };

    let filename = args.file.to_string_lossy().to_string();

    // res_cli.ml:96-98: the tokens target bypasses parsing and scans the file
    // as it is.
    if args.print == "tokens" {
        print_tokens(&source, &filename, &mut io::stdout());
        return;
    }

    // res_cli.ml:79-82: the res target keeps the line endings of a CRLF
    // file, like bsc -format; the source is parsed as it is.
    let newline = crate::parser::line_endings::newline(&source);

    // Determine if we're parsing an interface
    let is_interface = args.interface || filename.ends_with(".resi") || filename.ends_with(".mli");

    let mut parser = Parser::new(&filename, &source);

    // Parse structure or signature
    if is_interface {
        let signature = module::parse_signature(&mut parser);

        // OCaml compiler/syntax/src/res_core.ml:292-300 reports deprecated
        // uncurried-dot syntax through Location.prerr_warning, which writes
        // to stderr.
        print_parser_warnings(&parser, &source, &filename, &mut io::stderr());

        // Print diagnostics if any
        let has_parse_errors = parser.has_errors();
        if has_parse_errors {
            print_diagnostics(&parser, &source, &filename, &mut io::stdout());
            if !args.recover {
                process::exit(1);
            }
        }

        let signature = if has_parse_errors {
            signature
        } else {
            // res_cli.ml:305-317: the parsetree0 round trip runs before the
            // JSX transform.
            let signature = if args.test_ast_conversion {
                let tree0 = mapper_to0::map_signature(parser.arena_mut(), &signature);
                mapper_from0::map_signature(parser.arena_mut(), &tree0).unwrap_or_else(|error| {
                    eprintln!("{error}");
                    std::process::exit(2)
                })
            } else {
                signature
            };
            // Apply JSX PPX transformation and emit JSX preprocessor warnings.
            let (signature, jsx_warnings) = match jsx_ppx::transform_signature_with_warnings_result(
                signature,
                args.jsx_version,
                &args.jsx_module,
                parser.arena_mut(),
            ) {
                Ok(result) => result,
                Err(err) => {
                    eprintln!("{err}");
                    process::exit(1);
                }
            };
            print_jsx_preprocessor_warnings(&source, &filename, &jsx_warnings, &mut io::stderr());
            signature
        };

        // Print in requested format
        match args.print.as_str() {
            "ml" => {
                // Capture ML output using StringWriter, then convert chars to Latin-1 bytes.
                // This preserves the original file bytes through the round-trip.
                let mut writer = StringWriter::new();
                ml_printer::print_signature_ml(&signature, parser.arena(), &mut writer);
                let output = writer.into_string();
                let _ = io::stdout().write_all(&latin1_bytes(&output));
            }
            "res" => print_signature_res(
                &signature,
                parser.comments().to_vec(),
                newline,
                parser.arena_mut(),
                &mut io::stdout(),
            ),
            "sexp" => sexp::print_signature(parser.arena(), &signature, &mut io::stdout()),
            "sexp-locs" => {
                sexp_locs::print_signature(&signature, parser.arena(), &mut io::stdout())
            }
            "sexp-locs-ppx" => {
                if has_parse_errors {
                    sexp_locs::print_signature(&signature, parser.arena(), &mut io::stdout());
                } else {
                    // res_cli.ml:129-132 runs `Bs_builtin_ppx.mapper`: its
                    // warnings go to stderr as it maps, before any error.
                    // `res_parser` has no `-enable-experimental`, so LetUnwrap
                    // is off.
                    let (rewritten, warnings) =
                        ppx::rewrite_signature_with_warnings(&signature, parser.arena_mut(), false);
                    eprint!(
                        "{}",
                        crate::driver::format_ppx_warnings(
                            parser.arena(),
                            &source,
                            &filename,
                            &warnings
                        )
                    );
                    let rewritten = match rewritten {
                        Ok(rewritten) => rewritten,
                        Err(e) => {
                            eprintln!("PPX rewrite failed: {e}");
                            process::exit(1);
                        }
                    };
                    sexp_locs::print_signature(&rewritten, parser.arena(), &mut io::stdout());
                }
            }
            "sexp0-locs" => {
                let sig0 = mapper_to0::map_signature(parser.arena_mut(), &signature);
                sexp_locs0::print_signature(parser.arena(), &sig0, &mut io::stdout());
            }
            "ast" => print_signature_ast(&signature, &mut io::stdout()),
            "binary" => {
                // OCaml -print binary format (current parsetree):
                // 1. Magic: "ResIntf01317" (raw string, not marshaled) for interfaces
                // 2. Marshaled filename (using output_value)
                // 3. Marshaled signature (using output_value)

                // Write magic
                let _ = io::stdout().write_all(b"ResIntf01317");

                // Marshal filename
                let mut w = MarshalWriter::new();
                filename.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());

                // Marshal signature
                let mut w = MarshalWriter::new();
                w.set_arena(parser.arena());
                signature.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());
            }
            "binary0" => {
                // Parsetree0 binary format (frozen PPX-compatible format):
                // Same layout as binary but with parsetree0 types

                // Convert to parsetree0
                let sig0 = mapper_to0::map_signature(parser.arena_mut(), &signature);

                // Write magic
                let _ = io::stdout().write_all(b"ResIntf01317");

                // Marshal filename
                let mut w = MarshalWriter::new();
                filename.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());

                // Marshal parsetree0 signature
                let mut w = MarshalWriter::new();
                w.set_arena(parser.arena());
                sig0.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());
            }
            "comments" => print_comments(&parser, &mut io::stdout()),
            "tokens" => print_tokens(&source, &filename, &mut io::stdout()),
            _ => {
                eprintln!("Unknown print format: {}", args.print);
                process::exit(1);
            }
        }
    } else {
        let structure = module::parse_structure(&mut parser);

        // OCaml compiler/syntax/src/res_core.ml:292-300 reports deprecated
        // uncurried-dot syntax through Location.prerr_warning, which writes
        // to stderr.
        print_parser_warnings(&parser, &source, &filename, &mut io::stderr());

        // Print diagnostics if any
        let has_parse_errors = parser.has_errors();
        if has_parse_errors {
            print_diagnostics(&parser, &source, &filename, &mut io::stdout());
            if !args.recover {
                process::exit(1);
            }
        }

        let structure = if has_parse_errors {
            structure
        } else {
            // res_cli.ml:305-317: the parsetree0 round trip runs before the
            // JSX transform.
            let structure = if args.test_ast_conversion {
                let tree0 = mapper_to0::map_structure(parser.arena_mut(), &structure);
                mapper_from0::map_structure(parser.arena_mut(), &tree0).unwrap_or_else(|error| {
                    eprintln!("{error}");
                    std::process::exit(2)
                })
            } else {
                structure
            };
            // Apply JSX PPX transformation and emit JSX preprocessor warnings.
            let (structure, jsx_warnings) = match jsx_ppx::transform_structure_with_warnings_result(
                structure,
                args.jsx_version,
                &args.jsx_module,
                parser.arena_mut(),
            ) {
                Ok(result) => result,
                Err(err) => {
                    eprintln!("{err}");
                    process::exit(1);
                }
            };
            print_jsx_preprocessor_warnings(&source, &filename, &jsx_warnings, &mut io::stderr());
            structure
        };

        // Print in requested format
        match args.print.as_str() {
            "ml" => {
                // Capture ML output using StringWriter, then convert chars to Latin-1 bytes.
                // This preserves the original file bytes through the round-trip.
                let mut writer = StringWriter::new();
                ml_printer::print_structure_ml(&structure, parser.arena(), &mut writer);
                let output = writer.into_string();
                let _ = io::stdout().write_all(&latin1_bytes(&output));
            }
            "res" => {
                let output = printer::print_structure_with_comments(
                    &structure,
                    parser.comments().to_vec(),
                    newline,
                    parser.arena_mut(),
                );
                if !output.is_empty() {
                    // Convert Latin-1 chars back to bytes to preserve original file encoding
                    let _ = io::stdout().write_all(&latin1_bytes(&output));
                }
            }
            "sexp" => sexp::print_structure(parser.arena(), &structure, &mut io::stdout()),
            "sexp-locs" => {
                sexp_locs::print_structure(&structure, parser.arena(), &mut io::stdout())
            }
            "sexp-locs-ppx" => {
                if has_parse_errors {
                    sexp_locs::print_structure(&structure, parser.arena(), &mut io::stdout());
                } else {
                    // res_cli.ml:161-165 runs `Bs_builtin_ppx.mapper`, as on
                    // the interface path above.
                    let (rewritten, warnings) =
                        ppx::rewrite_structure_with_warnings(&structure, parser.arena_mut(), false);
                    eprint!(
                        "{}",
                        crate::driver::format_ppx_warnings(
                            parser.arena(),
                            &source,
                            &filename,
                            &warnings
                        )
                    );
                    let rewritten = match rewritten {
                        Ok(rewritten) => rewritten,
                        Err(e) => {
                            eprintln!("PPX rewrite failed: {e}");
                            process::exit(1);
                        }
                    };
                    sexp_locs::print_structure(&rewritten, parser.arena(), &mut io::stdout());
                }
            }
            "sexp0-locs" => {
                let str0 = mapper_to0::map_structure(parser.arena_mut(), &structure);
                sexp_locs0::print_structure(parser.arena(), &str0, &mut io::stdout());
            }
            "ast" => print_structure_ast(&structure, &mut io::stdout()),
            "binary" => {
                // OCaml -print binary format (current parsetree):
                // 1. Magic: "ResImpl01317" (raw string, not marshaled) for implementations
                // 2. Marshaled filename (using output_value)
                // 3. Marshaled structure (using output_value)

                // Write magic
                let _ = io::stdout().write_all(b"ResImpl01317");

                // Marshal filename
                let mut w = MarshalWriter::new();
                filename.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());

                // Marshal structure
                let mut w = MarshalWriter::new();
                w.set_arena(parser.arena());
                structure.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());
            }
            "binary0" => {
                // Parsetree0 binary format (frozen PPX-compatible format):
                // Same layout as binary but with parsetree0 types

                // Convert to parsetree0
                let str0 = mapper_to0::map_structure(parser.arena_mut(), &structure);

                // Write magic
                let _ = io::stdout().write_all(b"ResImpl01317");

                // Marshal filename
                let mut w = MarshalWriter::new();
                filename.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());

                // Marshal parsetree0 structure
                let mut w = MarshalWriter::new();
                w.set_arena(parser.arena());
                str0.marshal(&mut w);
                let _ = io::stdout().write_all(&w.finish());
            }
            "comments" => print_comments(&parser, &mut io::stdout()),
            "tokens" => print_tokens(&source, &filename, &mut io::stdout()),
            _ => {
                eprintln!("Unknown print format: {}", args.print);
                process::exit(1);
            }
        }
    }
}

/// Print parser diagnostics in OCaml-compatible format
fn print_diagnostics(parser: &Parser<'_>, source: &str, filename: &str, out: &mut impl Write) {
    for diag in parser.diagnostics() {
        // OCaml uses explain_with_source to detect old syntax like |> and [|...|]
        let error_msg = code_frame::format_error(
            filename,
            source,
            &diag.start_pos,
            &diag.end_pos,
            &diag.explain_with_source(Some(source)),
        );
        let _ = out.write_all(error_msg.as_bytes());
    }
}

fn print_parser_warnings(parser: &Parser<'_>, source: &str, filename: &str, out: &mut impl Write) {
    for warning in parser.warnings() {
        print_parser_warning(source, filename, warning, out);
    }
}

fn print_parser_warning(
    source: &str,
    filename: &str,
    warning: &ParserWarning,
    out: &mut impl Write,
) {
    print_warning_frame(
        source,
        filename,
        warning.number(),
        &warning.start_pos,
        &warning.end_pos,
        warning.message(),
        out,
    );
}

fn print_jsx_preprocessor_warnings(
    source: &str,
    filename: &str,
    warnings: &[jsx_ppx::JsxPreprocessorWarning],
    out: &mut impl Write,
) {
    for warning in warnings {
        let (number, message) = if warning.deprecated {
            (3, format!("deprecated: {}", warning.message))
        } else {
            (22, warning.message.clone())
        };
        print_warning_frame(
            source,
            filename,
            number,
            &warning.start_pos,
            &warning.end_pos,
            &message,
            out,
        );
    }
}

/// A warning with its location and code frame, as `Location.prerr_warning`
/// prints it.
fn print_warning_frame(
    source: &str,
    filename: &str,
    number: impl std::fmt::Display,
    start_pos: &Position,
    end_pos: &Position,
    message: impl std::fmt::Display,
    out: &mut impl Write,
) {
    let use_color = code_frame::should_enable_color();
    let _ = writeln!(out);
    if use_color {
        let _ = writeln!(out, "  \x1b[1;33mWarning number {number}\x1b[0m");
    } else {
        let _ = writeln!(out, "  Warning number {number}");
    }
    let location = code_frame::format_location(filename, start_pos, end_pos);
    let location = if use_color {
        code_frame::colorize_location(&location)
    } else {
        location
    };
    let _ = writeln!(out, "  {}", location);
    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "{}",
        code_frame::print_warning(source, start_pos, end_pos)
    );
    let _ = writeln!(out, "  {message}");
    let _ = writeln!(out);
}

/// Printer output holds the source bytes as Latin-1 characters; write each
/// character back as one byte.
fn latin1_bytes(output: &str) -> Vec<u8> {
    output.chars().map(|c| c as u8).collect()
}

/// Print comments from parser
fn print_comments(parser: &Parser<'_>, out: &mut impl Write) {
    for comment in parser.comments() {
        let _ = writeln!(out, "{:?}", comment);
    }
}

/// Print tokens from source
fn print_tokens(source: &str, filename: &str, out: &mut impl Write) {
    // Create a temporary arena to intern the filename
    let mut arena = ParseArena::new();
    let filename_idx = arena.intern_string(filename);
    let mut scanner = Scanner::new(filename_idx, source);
    loop {
        let result = scanner.scan();
        let start_col = result.start_pos.cnum - result.start_pos.bol;
        let end_col = result.end_pos.cnum - result.end_pos.bol;
        let _ = writeln!(
            out,
            "{:?} @ {}:{}-{}:{}",
            result.token,
            result.start_pos.line,
            start_col + 1,
            result.end_pos.line,
            end_col + 1
        );
        if matches!(result.token, crate::parser::Token::Eof) {
            break;
        }
    }
}

// ============================================================================
// ReScript Printer
// ============================================================================

fn print_signature_res(
    signature: &[SignatureItem],
    comments: Vec<Comment>,
    newline: &str,
    arena: &mut ParseArena,
    out: &mut impl Write,
) {
    // Use printer to print signature
    let output = printer::print_signature_with_comments(signature, comments, newline, arena);
    if !output.is_empty() {
        // Convert Latin-1 chars back to bytes to preserve original file encoding
        let _ = out.write_all(&latin1_bytes(&output));
    }
}

// ============================================================================
// AST Debug Printer
// ============================================================================

fn print_structure_ast(structure: &Structure, out: &mut impl Write) {
    let _ = writeln!(out, "{:#?}", structure);
}

fn print_signature_ast(signature: &[SignatureItem], out: &mut impl Write) {
    let _ = writeln!(out, "{:#?}", signature);
}
