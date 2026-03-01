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
    Attribute, Constant, Expression, ModuleExpr, ModuleExprDesc, Payload, Signature, Structure,
    SignatureItemDesc, StructureItemDesc,
};
use crate::parser::{jsx_ppx, module, Parser};
use crate::types::sexp_typedtree::{
    print_typed_signature, print_typed_signature_with_locs, print_typed_structure,
    print_typed_structure_with_locs,
};
use crate::types::{
    TypeCheckContext, TypeContext, initial_env, transl_signature, type_structure,
};

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

fn expression_has_string_literal(
    expr: &Expression,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::ExpressionDesc as ED;

    match &*expr.pexp_desc {
        ED::Pexp_constant(c) => matches!(&**c, Constant::String(s, _) if s == value),
        ED::Pexp_let(inner) => {
            let (_, bindings, body) = &**inner;
            bindings
                .iter()
                .any(|vb| expression_has_string_literal(arena.get_expr(vb.pvb_expr), value, arena))
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_fun(inner) => {
            let crate::parser::ast::PexpFun { default, rhs, .. } = &**inner;
            default
                .as_ref()
                .is_some_and(|e| expression_has_string_literal(arena.get_expr(*e), value, arena))
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_apply(inner) => {
            let crate::parser::ast::PexpApply { funct, args, .. } = &**inner;
            expression_has_string_literal(arena.get_expr(*funct), value, arena)
                || args
                    .iter()
                    .any(|(_, arg)| expression_has_string_literal(arena.get_expr(*arg), value, arena))
        }
        ED::Pexp_match(inner) | ED::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            expression_has_string_literal(arena.get_expr(*scrutinee), value, arena)
                || cases.iter().any(|case| {
                    case.pc_guard
                        .as_ref()
                        .is_some_and(|g| {
                            expression_has_string_literal(arena.get_expr(*g), value, arena)
                        })
                        || expression_has_string_literal(arena.get_expr(case.pc_rhs), value, arena)
                })
        }
        ED::Pexp_tuple(items) | ED::Pexp_array(items) => items
            .iter()
            .any(|item| expression_has_string_literal(arena.get_expr(*item), value, arena)),
        ED::Pexp_construct(_, arg) => arg
            .as_ref()
            .is_some_and(|arg| expression_has_string_literal(arena.get_expr(*arg), value, arena)),
        ED::Pexp_variant(inner) => {
            let (_, arg) = &**inner;
            arg.as_ref()
                .is_some_and(|arg| expression_has_string_literal(arena.get_expr(*arg), value, arena))
        }
        ED::Pexp_record(inner) => {
            let (fields, base) = &**inner;
            fields
                .iter()
                .any(|field| expression_has_string_literal(arena.get_expr(field.expr), value, arena))
                || base
                    .as_ref()
                    .is_some_and(|base| expression_has_string_literal(arena.get_expr(*base), value, arena))
        }
        ED::Pexp_field(expr, _)
        | ED::Pexp_assert(expr)
        | ED::Pexp_await(expr) => expression_has_string_literal(arena.get_expr(*expr), value, arena),
        ED::Pexp_newtype(inner) => {
            let (_, expr) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_constraint(inner) => {
            let (expr, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_coerce(inner) => {
            let (expr, _, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_send(inner) => {
            let (expr, _) = &**inner;
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        ED::Pexp_setfield(inner) => {
            let (lhs, _, rhs) = &**inner;
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_sequence(lhs, rhs) | ED::Pexp_while(lhs, rhs) => {
            expression_has_string_literal(arena.get_expr(*lhs), value, arena)
                || expression_has_string_literal(arena.get_expr(*rhs), value, arena)
        }
        ED::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            expression_has_string_literal(arena.get_expr(*cond), value, arena)
                || expression_has_string_literal(arena.get_expr(*then_expr), value, arena)
                || else_expr
                    .as_ref()
                    .is_some_and(|else_expr| {
                        expression_has_string_literal(arena.get_expr(*else_expr), value, arena)
                    })
        }
        ED::Pexp_for(inner) => {
            let (_, start, end, _, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*start), value, arena)
                || expression_has_string_literal(arena.get_expr(*end), value, arena)
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_letmodule(inner) => {
            let (_, module_expr, body) = &**inner;
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
                || expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_pack(module_expr) => {
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
        }
        ED::Pexp_letexception(inner) => {
            let (_, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_open(inner) => {
            let (_, _, body) = &**inner;
            expression_has_string_literal(arena.get_expr(*body), value, arena)
        }
        ED::Pexp_extension(inner) => {
            let (_, payload) = &**inner;
            payload_has_string_literal(payload, value, arena)
        }
        ED::Pexp_ident(_) | ED::Pexp_jsx_element(_) => false,
    }
}

fn payload_has_string_literal(
    payload: &Payload,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match payload {
        Payload::PStr(items) => items.iter().any(|item| match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, _) = &**inner;
                expression_has_string_literal(arena.get_expr(*expr), value, arena)
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                payload_has_string_literal(&attr.1, value, arena)
            }
            _ => false,
        }),
        Payload::PPat(inner) => {
            let (pat, guard) = &**inner;
            pattern_has_string_literal(arena.get_pat(*pat), value, arena)
                || guard
                    .as_ref()
                    .is_some_and(|guard| {
                        expression_has_string_literal(arena.get_expr(*guard), value, arena)
                    })
        }
        Payload::PTyp(_) | Payload::PSig(_) => false,
    }
}

fn pattern_has_string_literal(
    pat: &crate::parser::ast::Pattern,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::PatternDesc as PD;

    match &*pat.ppat_desc {
        PD::Ppat_constant(c) => matches!(&**c, Constant::String(s, _) if s == value),
        PD::Ppat_alias(inner, _)
        | PD::Ppat_exception(inner)
        | PD::Ppat_open(_, inner) => pattern_has_string_literal(arena.get_pat(*inner), value, arena),
        PD::Ppat_constraint(inner) => {
            let (inner_pat, _) = &**inner;
            pattern_has_string_literal(arena.get_pat(*inner_pat), value, arena)
        }
        PD::Ppat_tuple(items) | PD::Ppat_array(items) => items
            .iter()
            .any(|item| pattern_has_string_literal(arena.get_pat(*item), value, arena)),
        PD::Ppat_construct(_, Some(arg)) => {
            pattern_has_string_literal(arena.get_pat(*arg), value, arena)
        }
        PD::Ppat_variant(inner) => {
            let (_, arg) = &**inner;
            arg.as_ref()
                .is_some_and(|arg| pattern_has_string_literal(arena.get_pat(*arg), value, arena))
        }
        PD::Ppat_or(lhs, rhs) => {
            pattern_has_string_literal(arena.get_pat(*lhs), value, arena)
                || pattern_has_string_literal(arena.get_pat(*rhs), value, arena)
        }
        PD::Ppat_record(inner) => {
            let (rows, _) = &**inner;
            rows.iter()
                .any(|row| pattern_has_string_literal(arena.get_pat(row.pat), value, arena))
        }
        PD::Ppat_extension(inner) => {
            let (_, payload) = &**inner;
            payload_has_string_literal(payload, value, arena)
        }
        _ => false,
    }
}

fn module_expr_has_config_string(
    module_expr: &ModuleExpr,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match &*module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => {
            structure_has_config_string(structure, value, arena)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, param, body) = &**inner;
            param
                .as_ref()
                .is_some_and(|param| {
                    module_type_has_config_string(arena.get_mod_type(*param), value, arena)
                })
                || module_expr_has_config_string(arena.get_mod_expr(*body), value, arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_has_config_string(arena.get_mod_expr(*lhs), value, arena)
                || module_expr_has_config_string(arena.get_mod_expr(*rhs), value, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, module_type) => {
            module_expr_has_config_string(arena.get_mod_expr(*inner), value, arena)
                || module_type_has_config_string(arena.get_mod_type(*module_type), value, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr) => {
            expression_has_string_literal(arena.get_expr(*expr), value, arena)
        }
        _ => false,
    }
}

fn module_type_has_config_string(
    module_type: &crate::parser::ast::ModuleType,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    use crate::parser::ast::ModuleTypeDesc as MTD;

    match &*module_type.pmty_desc {
        MTD::Pmty_signature(sig_items) => sig_items.iter().any(|item| match &*item.psig_desc {
            crate::parser::ast::SignatureItemDesc::Psig_attribute(attr) => {
                payload_has_string_literal(&attr.1, value, arena)
            }
            _ => false,
        }),
        MTD::Pmty_functor(inner) => {
            let (_, param, body) = &**inner;
            param
                .as_ref()
                .is_some_and(|param| {
                    module_type_has_config_string(arena.get_mod_type(*param), value, arena)
                })
                || module_type_has_config_string(arena.get_mod_type(*body), value, arena)
        }
        MTD::Pmty_with(inner) => {
            let (inner_mty, _) = &**inner;
            module_type_has_config_string(arena.get_mod_type(*inner_mty), value, arena)
        }
        MTD::Pmty_typeof(module_expr) => {
            module_expr_has_config_string(arena.get_mod_expr(*module_expr), value, arena)
        }
        _ => false,
    }
}

fn structure_has_config_string(
    structure: &Structure,
    value: &str,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    structure.iter().any(|item| match &*item.pstr_desc {
        StructureItemDesc::Pstr_attribute(attr) => payload_has_string_literal(&attr.1, value, arena),
        StructureItemDesc::Pstr_module(mb) => {
            module_expr_has_config_string(arena.get_mod_expr(mb.pmb_expr), value, arena)
        }
        StructureItemDesc::Pstr_recmodule(mbs) => mbs.iter().any(|mb| {
            module_expr_has_config_string(arena.get_mod_expr(mb.pmb_expr), value, arena)
        }),
        StructureItemDesc::Pstr_include(incl) => {
            module_expr_has_config_string(arena.get_mod_expr(incl.pincl_mod), value, arena)
        }
        _ => false,
    })
}



fn module_expr_needs_jsx_rewrite(
    module_expr: &ModuleExpr,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    match &*module_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(structure) => structure_needs_jsx_rewrite(structure, arena),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, _, body) = &**inner;
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*body), arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*lhs), arena)
                || module_expr_needs_jsx_rewrite(arena.get_mod_expr(*rhs), arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, _) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(*inner), arena)
        }
        _ => false,
    }
}

fn structure_needs_jsx_rewrite(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> bool {
    structure.iter().any(|item| match &*item.pstr_desc {
        // External @react.component declarations need JSX PPX lowering.
        StructureItemDesc::Pstr_primitive(vd) => has_react_component_attr(&vd.pval_attributes, arena),
        StructureItemDesc::Pstr_value(inner) => { let (_, bindings) = &**inner; bindings.iter().any(|vb| {
            has_react_component_attr(&vb.pvb_attributes, arena)
                || has_react_component_with_props_attr(&vb.pvb_attributes, arena)
        })},
        StructureItemDesc::Pstr_module(mb) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(mb.pmb_expr), arena)
        }
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_needs_jsx_rewrite(arena.get_mod_expr(mb.pmb_expr), arena)),
        StructureItemDesc::Pstr_include(incl) => {
            module_expr_needs_jsx_rewrite(arena.get_mod_expr(incl.pincl_mod), arena)
        }
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
    /// Source filename for interface constraint propagation.
    /// When set, after type_structure, checks for a matching .cmi and
    /// unifies implementation value types with interface types.
    pub source_filename: Option<String>,
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
        return Err(anyhow!(
            "Parse failed with {} error(s)",
            parser.diagnostics().len()
        ));
    }
    // Source fallback path: only run JSX rewrite when the file enables `-bs-jsx`.
    let jsx_enabled = structure_has_config_string(&structure, "-bs-jsx", parser.arena());
    let structure = if jsx_enabled
        && structure_needs_jsx_rewrite(&structure, parser.arena())
    {
        jsx_ppx::transform_structure(structure, 4, parser.arena_mut())
    } else {
        structure
    };

    let structure = spice_ppx::expand_structure(&structure, parser.arena_mut())
        .map_err(|e| anyhow!("Spice PPX expansion failed: {e}"))?;

    // Expand extension points (%%raw, %raw, %re, %%private) without touching externals
    let structure = ppx::expand_extensions(&structure, parser.arena_mut());

    // Rewrite expressions: desugar pipe (->), setter (#=), property access (##),
    // await, tagged templates, and encode externals. This matches OCaml's bs_builtin_ppx.
    let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

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

    let (typed_structure, _final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    // Print typed tree if requested
    if options.dump_typed_sexp {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure(parser.arena(), &type_ctx, &typed_structure, &mut stderr);
    }
    if options.dump_typed_sexp_locs {
        let mut stderr = std::io::stderr();
        let _ = print_typed_structure_with_locs(
            parser.arena(),
            &type_ctx,
            &typed_structure,
            &mut stderr,
        );
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
    let bytes =
        std::fs::read(path).with_context(|| format!("Failed to read {}", path.display()))?;
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

/// Type-check a ReScript source file and write the typed tree as sexp to a writer.
/// This reuses the parse -> ppx -> typecheck pipeline but skips codegen.
/// For structure files (.res), writes `(structure ...)`.
/// For signature files (.resi), writes `(signature ...)`.
pub fn typecheck_and_dump_sexp<W: std::io::Write>(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    let is_interface = filename.ends_with(".resi");

    if is_interface {
        // Parse as signature
        let mut parser = Parser::new(filename, source);
        let signature = module::parse_signature(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }

        // Type check
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        load_pervasives(&mut pers_env, &mut env, &type_ctx);
        tctx.set_persistent_env(pers_env);

        let typed_signature = transl_signature(&mut tctx, &env, parser.arena(), &signature)
            .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        print_typed_signature_with_locs(parser.arena(), &type_ctx, &typed_signature, writer)
            .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;
    } else {
        // Parse as structure
        let mut parser = Parser::new(filename, source);
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            return Err(anyhow!(
                "Parse failed with {} error(s)",
                parser.diagnostics().len()
            ));
        }

        let jsx_enabled = structure_has_config_string(&structure, "-bs-jsx", parser.arena());
        let structure = if jsx_enabled
            && structure_needs_jsx_rewrite(&structure, parser.arena())
        {
            jsx_ppx::transform_structure(structure, 4, parser.arena_mut())
        } else {
            structure
        };

        let structure = spice_ppx::expand_structure(&structure, parser.arena_mut())
            .map_err(|e| anyhow!("Spice PPX expansion failed: {e}"))?;
        let structure = ppx::expand_extensions(&structure, parser.arena_mut());
        let structure = ppx::rewrite_structure(&structure, parser.arena_mut())
            .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

        // Type check
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
        let mut env = initial_env(&type_ctx);

        let mut pers_env = PersistentEnv::new();
        let load_path = build_load_path(options);
        type_ctx.set_load_paths(load_path.clone());
        pers_env.set_load_path(load_path);
        load_pervasives(&mut pers_env, &mut env, &type_ctx);
        tctx.set_persistent_env(pers_env);

        let (typed_structure, _final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
            .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        print_typed_structure_with_locs(parser.arena(), &type_ctx, &typed_structure, writer)
            .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;
    }

    Ok(())
}

// NOTE: Interface constraint propagation (apply_interface_constraints) was
// investigated and found unviable at the current stage. The approach of
// unifying impl types with .resi CMI types after type_structure causes:
// 1. Crashes on auto-generated CMIs (fixed by .resi check)
// 2. Regressions on other tests (-2 parity, +40 hunks) due to unwanted
//    type modifications through shared non-generic nodes
// 3. Doesn't reach the target (reasonReact's actionless) because all
//    types in Rust are fully generalized (Tvar at GENERIC_LEVEL),
//    so instance() creates copies that don't propagate back
// Root cause: Rust's level management differs from OCaml's — module-internal
// Tvars get generalized to GENERIC_LEVEL when they shouldn't.
// OCaml's generalize_structure/value_restriction keeps them at var_level,
// and the link direction from unify preserves the low level through Tlink chains.

/// Per-file configuration overrides extracted from `@@config({flags: [...]})`.
#[derive(Debug, Default)]
pub struct FileConfigOverrides {
    pub let_unwrap: bool,
    pub jsx_version: Option<i32>,
}

fn parse_config_flags(flags: &[String]) -> FileConfigOverrides {
    let mut overrides = FileConfigOverrides::default();
    let mut i = 0;
    while i < flags.len() {
        match flags[i].as_str() {
            "-enable-experimental" => {
                if i + 1 < flags.len() && flags[i + 1] == "LetUnwrap" {
                    overrides.let_unwrap = true;
                    i += 2;
                    continue;
                }
            }
            "-bs-jsx" => {
                if i + 1 < flags.len() {
                    if let Ok(v) = flags[i + 1].parse::<i32>() {
                        overrides.jsx_version = Some(v);
                    }
                    i += 2;
                    continue;
                }
            }
            _ => {}
        }
        i += 1;
    }
    overrides
}

fn extract_flags_from_config_payload(
    payload: &Payload,
    arena: &crate::parse_arena::ParseArena,
) -> Vec<String> {
    use crate::parser::ast::ExpressionDesc as ED;
    use crate::parser::longident::Longident;
    let mut result = Vec::new();
    if let Payload::PStr(items) = payload {
        for item in items.iter() {
            if let StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc {
                let (expr_idx, _attrs) = &**inner;
                let expr = arena.get_expr(*expr_idx);
                if let ED::Pexp_record(inner) = &*expr.pexp_desc {
                    let (fields, _spread) = &**inner;
                    for field in fields {
                        let lid = arena.get_longident(field.lid.txt);
                        let is_flags = match lid {
                            Longident::Lident(str_idx) => arena.get_string(*str_idx) == "flags",
                            _ => false,
                        };
                        if is_flags {
                            let field_expr = arena.get_expr(field.expr);
                            if let ED::Pexp_array(elements) = &*field_expr.pexp_desc {
                                for elem_idx in elements.iter() {
                                    let elem = arena.get_expr(*elem_idx);
                                    if let ED::Pexp_constant(c) = &*elem.pexp_desc {
                                        if let Constant::String(s, _) = &**c {
                                            result.push(s.to_string());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    result
}

/// Extract `@@config({flags: [...]})` overrides from a parsed structure.
pub fn extract_file_config_from_structure(
    structure: &Structure,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    for item in structure {
        if let StructureItemDesc::Pstr_attribute(attr) = &*item.pstr_desc {
            let name = arena.get_string(attr.0.txt);
            if name == "config" {
                let flags = extract_flags_from_config_payload(&attr.1, arena);
                if !flags.is_empty() {
                    return parse_config_flags(&flags);
                }
            }
        }
    }
    FileConfigOverrides::default()
}

/// Extract `@@config({flags: [...]})` overrides from a parsed signature.
pub fn extract_file_config_from_signature(
    signature: &Signature,
    arena: &crate::parse_arena::ParseArena,
) -> FileConfigOverrides {
    for item in signature {
        if let SignatureItemDesc::Psig_attribute(attr) = &*item.psig_desc {
            let name = arena.get_string(attr.0.txt);
            if name == "config" {
                let flags = extract_flags_from_config_payload(&attr.1, arena);
                if !flags.is_empty() {
                    return parse_config_flags(&flags);
                }
            }
        }
    }
    FileConfigOverrides::default()
}

/// Typecheck a stored structure AST (from parse phase) and dump sexp.
/// Applies remaining PPX passes (spice, expand_extensions, rewrite_structure) before typechecking.
pub fn typecheck_stored_structure_and_dump_sexp<W: std::io::Write>(
    mut arena: crate::parse_arena::ParseArena,
    structure: Structure,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    // Reset counter: the arena was already used during binary AST writing
    // (write_structure_ast_current_with_extra_deps → rewrite_structure), which
    // expanded %%private items and incremented local_module_counter.
    // OCaml starts fresh for each bsc invocation, so we reset to match.
    arena.reset_local_module_counter();

    let jsx_enabled = structure_has_config_string(&structure, "-bs-jsx", &arena);
    let structure = if jsx_enabled
        && structure_needs_jsx_rewrite(&structure, &arena)
    {
        jsx_ppx::transform_structure(structure, 4, &mut arena)
    } else {
        structure
    };

    let structure = spice_ppx::expand_structure(&structure, &mut arena)
        .map_err(|e| anyhow!("Spice PPX expansion failed: {e}"))?;
    let structure = ppx::expand_extensions(&structure, &mut arena);
    let structure = ppx::rewrite_structure(&structure, &mut arena)
        .map_err(|e| anyhow!("PPX rewrite failed: {e}"))?;

    let id_gen = IdGenerator::new();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    load_pervasives(&mut pers_env, &mut env, &type_ctx);
    tctx.set_persistent_env(pers_env);

    let (typed_structure, _final_env) = type_structure(&mut tctx, &env, &arena, &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    print_typed_structure_with_locs(&arena, &type_ctx, &typed_structure, writer)
        .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;

    Ok(())
}

/// Typecheck a stored signature AST (from parse phase) and dump sexp.
pub fn typecheck_stored_signature_and_dump_sexp<W: std::io::Write>(
    arena: crate::parse_arena::ParseArena,
    signature: Signature,
    options: &CompilerOptions,
    writer: &mut W,
) -> Result<()> {
    let id_gen = IdGenerator::new();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
    let mut env = initial_env(&type_ctx);

    let mut pers_env = PersistentEnv::new();
    let load_path = build_load_path(options);
    type_ctx.set_load_paths(load_path.clone());
    pers_env.set_load_path(load_path);
    load_pervasives(&mut pers_env, &mut env, &type_ctx);
    tctx.set_persistent_env(pers_env);

    let typed_signature = transl_signature(&mut tctx, &env, &arena, &signature)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    print_typed_signature_with_locs(&arena, &type_ctx, &typed_signature, writer)
        .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;

    Ok(())
}
