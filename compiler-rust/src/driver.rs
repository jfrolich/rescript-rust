//! Compiler driver utilities.
//!
//! This module wires together parsing, type-checking, Lambda conversion, and
//! JS IR codegen to produce JavaScript output.

use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};

use crate::binary_ast::ppx;
use crate::cmi::persistent_env::PersistentEnv;
use crate::context::IdGenerator;
use crate::binary_ast::spice_ppx;
use crate::js_ir::printer::print_program;
use crate::lambda::compile::LambdaCompiler;
use crate::lambda::convert::LambdaConverter;
use crate::parser::{module, Parser};
use crate::types::sexp_typedtree::{print_typed_structure, print_typed_structure_with_locs, print_typed_signature, print_typed_signature_with_locs};
use crate::types::{initial_env, type_structure, transl_signature, TypeCheckContext, TypeContext};

/// Compiler options that can be passed to the driver.
#[derive(Default, Clone)]
pub struct CompilerOptions {
    /// Print the Lambda IR to stderr (like OCaml's -drawlambda)
    pub dump_lambda: bool,
    /// Print the typed tree as sexp to stderr (like OCaml's -dtyped-sexp)
    pub dump_typed_sexp: bool,
    /// Print the typed tree as sexp with locations to stderr (like OCaml's -dtyped-sexp-locs)
    pub dump_typed_sexp_locs: bool,
    /// Print the Lambda IR as sexp to stderr (like OCaml's -dlambda-sexp)
    pub dump_lambda_sexp: bool,
    /// Print the Lambda IR as sexp with locations to stderr (like OCaml's -dlambda-sexp-locs)
    pub dump_lambda_sexp_locs: bool,
    /// Include paths for finding .cmi files (from -I flags)
    pub include_paths: Vec<PathBuf>,
    /// Runtime package path (from -runtime-path flag)
    /// Used to locate stdlib CMIs at {runtime_path}/lib/ocaml/
    pub runtime_path: Option<PathBuf>,
}

/// Compile ReScript source to JavaScript.
pub fn compile_source_to_js(source: &str, filename: &str) -> Result<String> {
    compile_source_to_js_with_options(source, filename, &CompilerOptions::default())
}

/// Compile ReScript source to JavaScript with options.
pub fn compile_source_to_js_with_options(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<String> {
    // Parse
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!("Parse failed with {} error(s)", parser.diagnostics().len()));
    }
    let structure = spice_ppx::expand_structure(&structure, parser.arena_mut());

    // Expand extension points (%%raw, %raw, %re, %%private) without touching externals
    let structure = ppx::expand_extensions(&structure, parser.arena_mut());

    // Rewrite expressions: desugar pipe (->), setter (#=), property access (##),
    // await, tagged templates, and encode externals. This matches OCaml's bs_builtin_ppx.
    let structure = ppx::rewrite_structure(&structure, parser.arena_mut());

    // Type check
    let id_gen = IdGenerator::new();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    pers_env.set_load_path(build_load_path(options));
    load_pervasives(&mut pers_env, &mut env, &type_ctx);

    // Store persistent env in the type check context for module resolution
    tctx.set_persistent_env(pers_env);

    let (typed_structure, _env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure(parser.arena(), &type_ctx, &typed_structure, &mut stderr);
    }
    if options.dump_typed_sexp_locs {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure_with_locs(parser.arena(), &type_ctx, &typed_structure, &mut stderr);
    }

    // Typedtree -> Lambda
    let mut converter = LambdaConverter::new(parser.arena());
    let lambda = converter.convert_structure(&typed_structure);

    // Print Lambda IR if requested
    if options.dump_lambda {
        eprintln!("{}", crate::lambda::print::LambdaPrinter::new(&lambda));
    }

    // Print Lambda sexp if requested
    if options.dump_lambda_sexp {
        use std::io::Write;
        let mut stderr = std::io::stderr();
        let _ = crate::lambda::sexp_lambda::print_lambda(&lambda, &mut stderr);
        let _ = stderr.flush();
    }
    if options.dump_lambda_sexp_locs {
        use std::io::Write;
        let mut stderr = std::io::stderr();
        let _ = crate::lambda::sexp_lambda::print_lambda_with_locs(&lambda, &mut stderr);
        let _ = stderr.flush();
    }

    // Lambda -> JS IR
    let mut compiler = LambdaCompiler::new();
    let program = compiler.compile_program(&lambda);

    // JS IR -> JS source
    Ok(print_program(&program))
}

/// Type-check an interface file and dump typed sexp if requested.
/// Interface files (.resi) don't produce JS output, only .cmi files.
pub fn typecheck_interface_source(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<()> {
    // Parse as signature
    let mut parser = Parser::new(filename, source);
    let signature = module::parse_signature(&mut parser);
    if parser.has_errors() {
        return Err(anyhow!("Parse failed with {} error(s)", parser.diagnostics().len()));
    }

    // Type check
    let id_gen = IdGenerator::new();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    let mut env = initial_env(&type_ctx);

    // Load Pervasives and extend the initial environment
    let mut pers_env = PersistentEnv::new();
    pers_env.set_load_path(build_load_path(options));
    load_pervasives(&mut pers_env, &mut env, &type_ctx);

    tctx.set_persistent_env(pers_env);

    let typed_signature = transl_signature(&mut tctx, &env, parser.arena(), &signature)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let mut stderr = std::io::stderr();
        let _ = print_typed_signature(parser.arena(), &type_ctx, &typed_signature, &mut stderr);
    }
    if options.dump_typed_sexp_locs {
        let mut stderr = std::io::stderr();
        let _ = print_typed_signature_with_locs(parser.arena(), &type_ctx, &typed_signature, &mut stderr);
    }

    Ok(())
}

/// Type-check an interface file and dump typed sexp if requested.
pub fn typecheck_interface_file(
    path: &std::path::Path,
    options: &CompilerOptions,
) -> Result<()> {
    let bytes = std::fs::read(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;
    let source: String = bytes.iter().map(|&b| b as char).collect();
    let filename = path.to_string_lossy();
    typecheck_interface_source(&source, &filename, options)
}

/// Compile a file to JavaScript.
pub fn compile_file_to_js(path: &std::path::Path) -> Result<String> {
    compile_file_to_js_with_options(path, &CompilerOptions::default())
}

/// Compile a file to JavaScript with options.
pub fn compile_file_to_js_with_options(
    path: &std::path::Path,
    options: &CompilerOptions,
) -> Result<String> {
    // Read file as raw bytes, converting each byte to a char (Latin-1 encoding).
    // This matches OCaml's byte-level string handling where each byte is a character.
    // In Latin-1 mode, char offset == original byte offset, which is critical for
    // correct position tracking in the scanner.
    let bytes = std::fs::read(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;
    let source: String = bytes.iter().map(|&b| b as char).collect();
    let filename = path.to_string_lossy();
    compile_source_to_js_with_options(&source, &filename, options)
}

/// Build the load path from compiler options.
///
/// Matches OCaml's `res_compmisc.ml:init_path()`:
/// - Expands `-I` directories
/// - Appends `{runtime_path}/lib/ocaml` as the stdlib directory (unless no_stdlib)
fn build_load_path(options: &CompilerOptions) -> Vec<PathBuf> {
    let mut paths = options.include_paths.clone();
    if let Some(ref runtime_path) = options.runtime_path {
        let stdlib_dir = runtime_path.join("lib").join("ocaml");
        paths.push(stdlib_dir);
    }
    paths
}

/// Load the Pervasives and Stdlib modules into the initial environment.
///
/// This is equivalent to OCaml's `res_compmisc.ml:initial_env()` which loads
/// Pervasives.cmi and Stdlib.cmi and opens them into the environment.
fn load_pervasives<'a>(pers_env: &mut PersistentEnv, env: &mut Env, ctx: &'a TypeContext<'a>) {
    use crate::ident::Ident;

    // Try to load and open Pervasives (matches OCaml: open_implicit_module "Pervasives")
    if pers_env.open_module("Pervasives", env, ctx) {
        // Also add Pervasives as a module in the environment
        if let Some(md) = pers_env.get_module_declaration("Pervasives", ctx) {
            env.add_module(Ident::create_persistent("Pervasives"), md);
        }
    }

    // Try to load and open Stdlib (matches OCaml: open_implicit_module "Stdlib")
    if pers_env.open_module("Stdlib", env, ctx) {
        if let Some(md) = pers_env.get_module_declaration("Stdlib", ctx) {
            env.add_module(Ident::create_persistent("Stdlib"), md);
        }
    }
}

use crate::types::env::Env;
