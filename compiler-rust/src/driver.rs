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
use crate::parser::ast::{
    Attribute, Constant, Expression, ModuleExpr, ModuleExprDesc, Payload, Structure,
    StructureItemDesc,
};
use crate::parser::{jsx_ppx, module, Parser};
use crate::types::sexp_typedtree::{print_typed_structure, print_typed_structure_with_locs, print_typed_signature, print_typed_signature_with_locs};
use crate::types::{initial_env, type_structure, transl_signature, TypeCheckContext, TypeContext};

fn has_react_component_attr(attrs: &[Attribute], arena: &crate::parse_arena::ParseArena) -> bool {
    attrs.iter().any(|attr| {
        matches!(
            arena.get_string(attr.0.txt),
            "react.component" | "jsx.component"
        )
    })
}

fn has_react_component_with_props_attr(
    attrs: &[Attribute],
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    attrs.iter().any(|attr| {
        matches!(
            arena.get_string(attr.0.txt),
            "react.componentWithProps" | "jsx.componentWithProps"
        )
    })
}

fn expression_has_string_literal(expr: &Expression, value: &str) -> bool {
    use crate::parser::ast::ExpressionDesc;

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(s, _)) => s == value,
        ExpressionDesc::Pexp_constant(_) => false,
        ExpressionDesc::Pexp_let(_, bindings, body) => {
            bindings
                .iter()
                .any(|vb| expression_has_string_literal(&vb.pvb_expr, value))
                || expression_has_string_literal(body, value)
        }
        ExpressionDesc::Pexp_fun { default, rhs, .. } => {
            default
                .as_ref()
                .is_some_and(|e| expression_has_string_literal(e, value))
                || expression_has_string_literal(rhs, value)
        }
        ExpressionDesc::Pexp_apply { funct, args, .. } => {
            expression_has_string_literal(funct, value)
                || args
                    .iter()
                    .any(|(_, arg)| expression_has_string_literal(arg, value))
        }
        ExpressionDesc::Pexp_match(scrutinee, cases) | ExpressionDesc::Pexp_try(scrutinee, cases) => {
            expression_has_string_literal(scrutinee, value)
                || cases.iter().any(|case| {
                    case.pc_guard
                        .as_ref()
                        .is_some_and(|g| expression_has_string_literal(g, value))
                        || expression_has_string_literal(&case.pc_rhs, value)
                })
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            items.iter().any(|item| expression_has_string_literal(item, value))
        }
        ExpressionDesc::Pexp_construct(_, arg) | ExpressionDesc::Pexp_variant(_, arg) => arg
            .as_ref()
            .is_some_and(|arg| expression_has_string_literal(arg, value)),
        ExpressionDesc::Pexp_record(fields, base) => {
            fields
                .iter()
                .any(|field| expression_has_string_literal(&field.expr, value))
                || base
                    .as_ref()
                    .is_some_and(|base| expression_has_string_literal(base, value))
        }
        ExpressionDesc::Pexp_field(expr, _)
        | ExpressionDesc::Pexp_assert(expr)
        | ExpressionDesc::Pexp_await(expr)
        | ExpressionDesc::Pexp_newtype(_, expr)
        | ExpressionDesc::Pexp_constraint(expr, _)
        | ExpressionDesc::Pexp_coerce(expr, _, _)
        | ExpressionDesc::Pexp_send(expr, _) => expression_has_string_literal(expr, value),
        ExpressionDesc::Pexp_setfield(lhs, _, rhs)
        | ExpressionDesc::Pexp_sequence(lhs, rhs)
        | ExpressionDesc::Pexp_while(lhs, rhs) => {
            expression_has_string_literal(lhs, value) || expression_has_string_literal(rhs, value)
        }
        ExpressionDesc::Pexp_ifthenelse(cond, then_expr, else_expr) => {
            expression_has_string_literal(cond, value)
                || expression_has_string_literal(then_expr, value)
                || else_expr
                    .as_ref()
                    .is_some_and(|else_expr| expression_has_string_literal(else_expr, value))
        }
        ExpressionDesc::Pexp_for(_, start, end, _, body) => {
            expression_has_string_literal(start, value)
                || expression_has_string_literal(end, value)
                || expression_has_string_literal(body, value)
        }
        ExpressionDesc::Pexp_letmodule(_, module_expr, body) => {
            module_expr_has_config_string(module_expr, value)
                || expression_has_string_literal(body, value)
        }
        ExpressionDesc::Pexp_pack(module_expr) => module_expr_has_config_string(module_expr, value),
        ExpressionDesc::Pexp_letexception(_, body) | ExpressionDesc::Pexp_open(_, _, body) => {
            expression_has_string_literal(body, value)
        }
        ExpressionDesc::Pexp_extension((_, payload)) => payload_has_string_literal(payload, value),
        ExpressionDesc::Pexp_ident(_) | ExpressionDesc::Pexp_jsx_element(_) => false,
    }
}

fn payload_has_string_literal(payload: &Payload, value: &str) -> bool {
    match payload {
        Payload::PStr(items) => items.iter().any(|item| match &item.pstr_desc {
            StructureItemDesc::Pstr_eval(expr, _) => expression_has_string_literal(expr, value),
            StructureItemDesc::Pstr_attribute((_, nested_payload)) => {
                payload_has_string_literal(nested_payload, value)
            }
            _ => false,
        }),
        Payload::PPat(pat, guard) => {
            pattern_has_string_literal(pat, value)
                || guard
                    .as_ref()
                    .is_some_and(|guard| expression_has_string_literal(guard, value))
        }
        Payload::PTyp(_) | Payload::PSig(_) => false,
    }
}

fn pattern_has_string_literal(pat: &crate::parser::ast::Pattern, value: &str) -> bool {
    use crate::parser::ast::PatternDesc;

    match &pat.ppat_desc {
        PatternDesc::Ppat_constant(Constant::String(s, _)) => s == value,
        PatternDesc::Ppat_alias(inner, _)
        | PatternDesc::Ppat_constraint(inner, _)
        | PatternDesc::Ppat_exception(inner)
        | PatternDesc::Ppat_open(_, inner) => pattern_has_string_literal(inner, value),
        PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
            items.iter().any(|item| pattern_has_string_literal(item, value))
        }
        PatternDesc::Ppat_construct(_, Some(arg)) | PatternDesc::Ppat_variant(_, Some(arg)) => {
            pattern_has_string_literal(arg, value)
        }
        PatternDesc::Ppat_or(lhs, rhs) => {
            pattern_has_string_literal(lhs, value) || pattern_has_string_literal(rhs, value)
        }
        PatternDesc::Ppat_record(rows, _) => rows
            .iter()
            .any(|row| pattern_has_string_literal(&row.pat, value)),
        PatternDesc::Ppat_extension((_, payload)) => payload_has_string_literal(payload, value),
        _ => false,
    }
}

fn module_expr_has_config_string(module_expr: &ModuleExpr, value: &str) -> bool {
    match &module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => structure_has_config_string(structure, value),
        ModuleExprDesc::Pmod_functor(_, _, body) => module_expr_has_config_string(body, value),
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_has_config_string(lhs, value) || module_expr_has_config_string(rhs, value)
        }
        ModuleExprDesc::Pmod_constraint(inner, module_type) => {
            module_expr_has_config_string(inner, value)
                || module_type_has_config_string(module_type, value)
        }
        _ => false,
    }
}

fn module_type_has_config_string(
    module_type: &crate::parser::ast::ModuleType,
    value: &str,
) -> bool {
    use crate::parser::ast::ModuleTypeDesc;

    match &module_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(sig_items) => sig_items.iter().any(|item| match &item.psig_desc
        {
            crate::parser::ast::SignatureItemDesc::Psig_attribute((_, payload)) => {
                payload_has_string_literal(payload, value)
            }
            _ => false,
        }),
        ModuleTypeDesc::Pmty_functor(_, param, body) => {
            param
                .as_ref()
                .is_some_and(|param| module_type_has_config_string(param, value))
                || module_type_has_config_string(body, value)
        }
        ModuleTypeDesc::Pmty_with(inner, _) => module_type_has_config_string(inner, value),
        _ => false,
    }
}

fn structure_has_config_string(structure: &Structure, value: &str) -> bool {
    structure.iter().any(|item| match &item.pstr_desc {
        StructureItemDesc::Pstr_attribute(attr) => payload_has_string_literal(&attr.1, value),
        StructureItemDesc::Pstr_module(mb) => module_expr_has_config_string(&mb.pmb_expr, value),
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_has_config_string(&mb.pmb_expr, value)),
        StructureItemDesc::Pstr_include(incl) => module_expr_has_config_string(&incl.pincl_mod, value),
        _ => false,
    })
}

fn is_async_component_expr(expr: &Expression) -> bool {
    use crate::parser::ast::ExpressionDesc;

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun { is_async, .. } => *is_async,
        ExpressionDesc::Pexp_constraint(inner, _) => is_async_component_expr(inner),
        ExpressionDesc::Pexp_apply { args, .. } => args
            .iter()
            .any(|(_, arg)| is_async_component_expr(arg)),
        ExpressionDesc::Pexp_sequence(_, inner) => is_async_component_expr(inner),
        _ => false,
    }
}

fn module_expr_has_async_component(
    module_expr: &ModuleExpr,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match &module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => structure_has_async_component(structure, arena),
        ModuleExprDesc::Pmod_functor(_, _, body) => module_expr_has_async_component(body, arena),
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_has_async_component(lhs, arena)
                || module_expr_has_async_component(rhs, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, _) => module_expr_has_async_component(inner, arena),
        _ => false,
    }
}

fn structure_has_async_component(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    structure.iter().any(|item| match &item.pstr_desc {
        StructureItemDesc::Pstr_value(_, bindings) => bindings.iter().any(|vb| {
            has_react_component_attr(&vb.pvb_attributes, arena)
                && is_async_component_expr(&vb.pvb_expr)
        }),
        StructureItemDesc::Pstr_module(mb) => module_expr_has_async_component(&mb.pmb_expr, arena),
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_has_async_component(&mb.pmb_expr, arena)),
        StructureItemDesc::Pstr_include(incl) => module_expr_has_async_component(&incl.pincl_mod, arena),
        _ => false,
    })
}

fn module_expr_needs_jsx_rewrite(module_expr: &ModuleExpr, arena: &crate::parse_arena::ParseArena) -> bool {
    match &module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => structure_needs_jsx_rewrite(structure, arena),
        ModuleExprDesc::Pmod_functor(_, _, body) => module_expr_needs_jsx_rewrite(body, arena),
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_needs_jsx_rewrite(lhs, arena) || module_expr_needs_jsx_rewrite(rhs, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, _) => module_expr_needs_jsx_rewrite(inner, arena),
        _ => false,
    }
}

fn structure_needs_jsx_rewrite(structure: &Structure, arena: &crate::parse_arena::ParseArena) -> bool {
    structure.iter().any(|item| match &item.pstr_desc {
        // External @react.component declarations need JSX PPX lowering.
        StructureItemDesc::Pstr_primitive(vd) => has_react_component_attr(&vd.pval_attributes, arena),
        StructureItemDesc::Pstr_value(_, bindings) => bindings.iter().any(|vb| {
            has_react_component_attr(&vb.pvb_attributes, arena)
                || has_react_component_with_props_attr(&vb.pvb_attributes, arena)
        }),
        StructureItemDesc::Pstr_module(mb) => module_expr_needs_jsx_rewrite(&mb.pmb_expr, arena),
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_needs_jsx_rewrite(&mb.pmb_expr, arena)),
        StructureItemDesc::Pstr_include(incl) => module_expr_needs_jsx_rewrite(&incl.pincl_mod, arena),
        _ => false,
    })
}

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

    // Source fallback path: only run JSX rewrite when the file enables `-bs-jsx`,
    // and skip known-unstable async component lowering in this path.
    let jsx_enabled = structure_has_config_string(&structure, "-bs-jsx");
    let has_async_component = structure_has_async_component(&structure, parser.arena());
    let structure = if jsx_enabled
        && !has_async_component
        && structure_needs_jsx_rewrite(&structure, parser.arena())
    {
        jsx_ppx::transform_structure(structure, 4, parser.arena_mut())
    } else {
        structure
    };

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
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
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
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
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
