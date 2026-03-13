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
    /// Additional modules opened implicitly from `-open` flags.
    pub open_modules: Vec<String>,
    /// Source filename for interface constraint propagation.
    /// When set, after type_structure, checks for a matching .cmi and
    /// unifies implementation value types with interface types.
    pub source_filename: Option<String>,
    /// JSX version from CLI `-bs-jsx` (e.g. 4). When set, enables JSX PPX rewrite.
    pub jsx_version: Option<i32>,
}

fn jsx_version_for_structure(
    structure: &Structure,
    options: &CompilerOptions,
    arena: &crate::parse_arena::ParseArena,
) -> Option<i32> {
    options
        .jsx_version
        .or_else(|| structure_has_config_string(structure, "-bs-jsx", arena).then_some(4))
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
    let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
    let structure = if let Some(jsx_version) = jsx_version {
        if structure_needs_jsx_rewrite(&structure, parser.arena()) {
            jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
        } else {
            structure
        }
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
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);

    // Store persistent env in the type check context for module resolution
    tctx.set_persistent_env(pers_env);

    let (typed_structure, final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    // Apply interface constraints: moregen linking for non-generic Tvars.
    // OCaml's Includemod.compunit -> moregeneral -> moregen links weak (non-generic)
    // type variables from value-restricted expressions to the corresponding types
    // from the .resi interface. This happens BEFORE sexp serialization.
    apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options);

    // OCaml's type_implementation_more calls normalize_signature ONLY when there
    // is no .resi file (Mli_exists branch skips it). Match this behavior:
    // normalize sorts Tvariant row fields and Tobject field chains alphabetically.
    let has_resi = options.source_filename.as_ref().is_some_and(|f| {
        f.ends_with(".res") && std::path::Path::new(&format!("{}i", f)).exists()
    });
    if !has_resi {
        normalize_signature_types(&type_ctx, &typed_structure, &final_env);
    }

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
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);

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
fn load_pervasives<'a>(
    pers_env: &mut PersistentEnv,
    env: &mut Env,
    ctx: &'a TypeContext<'a>,
    open_modules: &[String],
) {
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

    // Apply explicit `-open` modules in argument order.
    for module_name in open_modules {
        if pers_env.open_module(module_name, env, ctx) {
            if let Some(md) = pers_env.get_module_declaration(module_name, ctx) {
                env.add_module(Ident::create_persistent(module_name), md);
            }
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
        load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
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

        let jsx_version = jsx_version_for_structure(&structure, options, parser.arena());
        let structure = if let Some(jsx_version) = jsx_version {
            if structure_needs_jsx_rewrite(&structure, parser.arena()) {
                jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
            } else {
                structure
            }
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
        load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
        tctx.set_persistent_env(pers_env);

        let (typed_structure, _final_env) = type_structure(&mut tctx, &env, parser.arena(), &structure)
            .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

        apply_moregen_constraints(&mut tctx, &type_ctx, &typed_structure, options);

        print_typed_structure_with_locs(parser.arena(), &type_ctx, &typed_structure, writer)
            .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;
    }

    Ok(())
}

/// Apply moregen-like interface constraints: link non-generic Tvars in the
/// implementation to corresponding types from the .resi interface.
///
/// This matches OCaml's Includemod.compunit -> moregeneral -> moregen mechanism.
/// OCaml runs this after type_structure but before sexp serialization. The key
/// insight is that value-restricted expressions (like `basicComponent("interop")`)
/// produce non-generic Tvars that `instance()` returns by identity. When moregen
/// links these shared Tvars to interface types, ALL references update.
fn apply_moregen_constraints(
    tctx: &mut TypeCheckContext<'_>,
    type_ctx: &TypeContext<'_>,
    typed_structure: &crate::types::typedtree::Structure,
    options: &CompilerOptions,
) {
    use crate::types::type_expr::TypeExprRef;
    use crate::types::decl::SignatureItem;

    let source_file = match &options.source_filename {
        Some(f) => f,
        None => return,
    };

    // Only apply when a .resi file exists
    if !source_file.ends_with(".res") {
        return;
    }
    let resi_file = format!("{}i", source_file);
    if !std::path::Path::new(&resi_file).exists() {
        return;
    }

    // Extract module name from source filename
    let module_name = std::path::Path::new(source_file)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_string());
    let module_name = match module_name {
        Some(n) => n,
        None => return,
    };

    // Load the RAW interface signature from CMI (without path substitution).
    // OCaml's ps_sig retains raw Pident paths; path substitution happens lazily
    // in components_of_module_maker, not on the sig used for moregen.
    // Using raw paths ensures moregen_link propagates Pident (local) paths
    // instead of Pdot (module-qualified) paths to the implementation.
    let iface_sig = {
        let pers = match &mut tctx.persistent_env {
            Some(p) => p,
            None => return,
        };
        // Temporarily add source dir to load path
        let source_dir = std::path::Path::new(source_file).parent()
            .map(|d| d.to_path_buf())
            .unwrap_or_else(|| PathBuf::from("."));
        let already_in_path = pers.load_path_contains(&source_dir);
        if !already_in_path {
            pers.add_load_path(source_dir.clone());
        }
        // Ensure the module is loaded first (for side effects like registering types)
        let _ = pers.find_pers_struct(&module_name, type_ctx);
        // Then read raw sig without path substitution for moregen
        let result = pers.read_raw_sig(&module_name, type_ctx);
        match result {
            Some(sig) => sig,
            None => return,
        }
    };

    // Build a map from value name -> interface type
    let mut iface_val_types: std::collections::HashMap<String, TypeExprRef> =
        std::collections::HashMap::new();
    for item in &iface_sig {
        if let SignatureItem::SigValue(id, vd) = item {
            iface_val_types.insert(id.name().to_string(), vd.val_type);
        }
    }

    // Walk top-level implementation structure items and match with interface.
    // Also recurse into modules to find inner non-generic Tvars.
    let mut debug = Vec::new();

    // Debug: dump all top-level binding names and types
    debug.push(format!("TOTAL TOP-LEVEL ITEMS: {}", typed_structure.str_items.len()));
    for item in &typed_structure.str_items {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in bindings {
                    let name = extract_pat_name(&binding.vb_pat);
                    debug.push(format!("TOP-LEVEL VALUE: {:?}", name));
                    if name.as_deref() == Some("wrapJsForReason") {
                        debug.push(format!("=== wrapJsForReason pat_type={:?} level={}",
                            binding.vb_pat.pat_type, type_ctx.get_level(type_ctx.repr(binding.vb_pat.pat_type))));
                        dump_all_tvars(type_ctx, binding.vb_pat.pat_type, &mut debug, &mut std::collections::HashSet::new(), 0);
                    }
                }
            }
            crate::types::typedtree::StructureItemDesc::Tstr_module(mb) => {
                debug.push(format!("TOP-LEVEL MODULE: {}", mb.mb_name.txt));
            }
            _ => {
                debug.push(format!("TOP-LEVEL OTHER"));
            }
        }
    }

    moregen_link_structure(type_ctx, typed_structure, &iface_val_types, &mut debug);
    if !debug.is_empty() {
        use std::io::Write;
        let debug_file = format!("/tmp/moregen_debug_{}.txt", module_name);
        let mut f = std::fs::File::create(&debug_file).unwrap();
        for line in &debug {
            writeln!(f, "{}", line).unwrap();
        }
    }
}

fn moregen_link_structure(
    type_ctx: &TypeContext<'_>,
    structure: &crate::types::typedtree::Structure,
    iface_val_types: &std::collections::HashMap<String, crate::types::type_expr::TypeExprRef>,
    debug: &mut Vec<String>,
) {
    for item in &structure.str_items {
        match &item.str_desc {
            crate::types::typedtree::StructureItemDesc::Tstr_value(_, bindings) => {
                for binding in bindings {
                    let name = extract_pat_name(&binding.vb_pat);
                    if let Some(ref name) = name {
                        if let Some(&iface_ty) = iface_val_types.get(name) {
                            debug.push(format!("moregen_link: {} impl={:?} iface={:?}",
                                name, binding.vb_pat.pat_type, iface_ty));
                            let iface_inst = crate::types::ctype::instance(type_ctx, iface_ty);
                            moregen_link(type_ctx, binding.vb_pat.pat_type, iface_inst,
                                &mut std::collections::HashSet::new(), debug);
                        } else {
                            debug.push(format!("no iface match: {}", name));
                        }
                    }
                }
            }
            crate::types::typedtree::StructureItemDesc::Tstr_module(mb) => {
                moregen_link_mod_expr(type_ctx, &mb.mb_expr, iface_val_types, debug);
            }
            _ => {}
        }
    }
}

fn moregen_link_mod_expr(
    type_ctx: &TypeContext<'_>,
    mod_expr: &crate::types::typedtree::ModuleExpr,
    iface_val_types: &std::collections::HashMap<String, crate::types::type_expr::TypeExprRef>,
    debug: &mut Vec<String>,
) {
    match &mod_expr.mod_desc {
        crate::types::typedtree::ModuleExprDesc::Tmod_structure(s) => {
            moregen_link_structure(type_ctx, s, iface_val_types, debug);
        }
        crate::types::typedtree::ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
            moregen_link_mod_expr(type_ctx, inner, iface_val_types, debug);
        }
        _ => {}
    }
}

fn dump_all_tvars(
    ctx: &TypeContext<'_>,
    ty: crate::types::type_expr::TypeExprRef,
    debug: &mut Vec<String>,
    seen: &mut std::collections::HashSet<crate::types::type_expr::TypeExprRef>,
    depth: usize,
) {
    use crate::types::type_expr::{TypeDesc, GENERIC_LEVEL};
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }
    let level = ctx.get_level(ty);
    let desc = ctx.get_desc(ty);
    let indent = "  ".repeat(depth);
    match &*desc {
        TypeDesc::Tvar(name) => {
            let generic_str = if level == GENERIC_LEVEL { "GENERIC" } else { "NON-GENERIC" };
            debug.push(format!("{}Tvar({:?}) {:?} {} level={}", indent, name, ty, generic_str, level));
        }
        TypeDesc::Tconstr { path, args, .. } => {
            debug.push(format!("{}Tconstr({:?}) {:?} level={} args={}", indent, path, ty, level, args.len()));
            let args = args.clone();
            drop(desc);
            for arg in &args {
                dump_all_tvars(ctx, *arg, debug, seen, depth + 1);
            }
            return;
        }
        TypeDesc::Tarrow { arg, ret, .. } => {
            let (at, r) = (arg.typ, *ret);
            drop(desc);
            dump_all_tvars(ctx, at, debug, seen, depth + 1);
            dump_all_tvars(ctx, r, debug, seen, depth + 1);
            return;
        }
        _ => {}
    }
    drop(desc);
}

fn extract_pat_name(
    pat: &crate::types::typedtree::Pattern,
) -> Option<String> {
    match &pat.pat_desc {
        crate::types::typedtree::PatternDesc::Tpat_var(id, _) => {
            Some(id.name().to_string())
        }
        crate::types::typedtree::PatternDesc::Tpat_alias(_, id, _) => {
            Some(id.name().to_string())
        }
        _ => None,
    }
}

/// Check if two paths are compatible for moregen linking.
/// OCaml's moregen uses path equality because both impl and iface have
/// the same qualified paths (due to Subst.type_declaration). In Rust,
/// impl has local Pident while iface has qualified Pdot, so we compare
/// the leaf name instead.
fn moregen_paths_compatible(p1: &crate::types::Path, p2: &crate::types::Path) -> bool {
    use crate::types::Path;
    if p1.same(p2) {
        return true;
    }
    let leaf1 = match p1 {
        Path::Pident(id) => id.name(),
        Path::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    let leaf2 = match p2 {
        Path::Pident(id) => id.name(),
        Path::Pdot(_, name, _) => name.as_str(),
        _ => return false,
    };
    leaf1 == leaf2
}

/// Walk two types structurally and link non-generic Tvars in the impl
/// to the corresponding interface types. Matches OCaml's moregen.
fn moregen_link(
    ctx: &TypeContext<'_>,
    impl_ty: crate::types::type_expr::TypeExprRef,
    iface_ty: crate::types::type_expr::TypeExprRef,
    visited: &mut std::collections::HashSet<(crate::types::type_expr::TypeExprRef, crate::types::type_expr::TypeExprRef)>,
    debug: &mut Vec<String>,
) {
    use crate::types::type_expr::{TypeDesc, GENERIC_LEVEL};

    let impl_ty = ctx.repr(impl_ty);
    let iface_ty = ctx.repr(iface_ty);
    if impl_ty == iface_ty {
        return;
    }
    if !visited.insert((impl_ty, iface_ty)) {
        return;
    }

    let impl_desc = ctx.get_desc(impl_ty);
    let iface_desc = ctx.get_desc(iface_ty);

    match (&*impl_desc, &*iface_desc) {
        (TypeDesc::Tvar(name), _) if ctx.get_level(impl_ty) != GENERIC_LEVEL => {
            // Non-generic impl Tvar: link to interface type
            let iface_summary = match &*iface_desc {
                TypeDesc::Tvar(n) => format!("Tvar({:?})", n),
                TypeDesc::Tconstr { path, .. } => format!("Tconstr({:?})", path),
                _ => "other".to_string(),
            };
            debug.push(format!("  LINK {:?} Tvar({:?}) level={} -> {}",
                impl_ty, name, ctx.get_level(impl_ty), iface_summary));
            drop(impl_desc);
            drop(iface_desc);
            crate::types::ctype::link_type(ctx, impl_ty, iface_ty);
        }
        (TypeDesc::Tvar(name), _) => {
            debug.push(format!("  SKIP generic {:?} Tvar({:?}) level={}",
                impl_ty, name, ctx.get_level(impl_ty)));
        }
        (TypeDesc::Tconstr { path: p1, args: a1, .. },
         TypeDesc::Tconstr { path: p2, args: a2, .. })
            if moregen_paths_compatible(p1, p2) && a1.len() == a2.len() =>
        {
            debug.push(format!("  Tconstr match: {:?} ~ {:?} args={}", p1, p2, a1.len()));
            let a1 = a1.clone();
            let a2 = a2.clone();
            drop(impl_desc);
            drop(iface_desc);
            for (a, b) in a1.iter().zip(a2.iter()) {
                moregen_link(ctx, *a, *b, visited, debug);
            }
        }
        (TypeDesc::Tarrow { arg: a1, ret: r1, .. },
         TypeDesc::Tarrow { arg: a2, ret: r2, .. }) =>
        {
            debug.push(format!("  Tarrow match"));
            let (a1t, r1) = (a1.typ, *r1);
            let (a2t, r2) = (a2.typ, *r2);
            drop(impl_desc);
            drop(iface_desc);
            moregen_link(ctx, a1t, a2t, visited, debug);
            moregen_link(ctx, r1, r2, visited, debug);
        }
        (TypeDesc::Ttuple(t1), TypeDesc::Ttuple(t2)) if t1.len() == t2.len() => {
            let t1 = t1.clone();
            let t2 = t2.clone();
            drop(impl_desc);
            drop(iface_desc);
            for (a, b) in t1.iter().zip(t2.iter()) {
                moregen_link(ctx, *a, *b, visited, debug);
            }
        }
        (TypeDesc::Tconstr { path: p1, args: a1, .. },
         TypeDesc::Tconstr { path: p2, args: a2, .. }) =>
        {
            debug.push(format!("  Tconstr MISMATCH: impl={:?}({}) iface={:?}({})",
                p1, a1.len(), p2, a2.len()));
        }
        _ => {
            debug.push(format!("  NO match"));
        }
    }
}

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

    let jsx_version = jsx_version_for_structure(&structure, options, &arena);
    let structure = if let Some(jsx_version) = jsx_version {
        if structure_needs_jsx_rewrite(&structure, &arena) {
            jsx_ppx::transform_structure(structure, jsx_version, &mut arena)
        } else {
            structure
        }
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
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
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
    load_pervasives(&mut pers_env, &mut env, &type_ctx, &options.open_modules);
    tctx.set_persistent_env(pers_env);

    let typed_signature = transl_signature(&mut tctx, &env, &arena, &signature)
        .map_err(|e| anyhow!("Type checking failed: {e:?}"))?;

    print_typed_signature_with_locs(&arena, &type_ctx, &typed_signature, writer)
        .map_err(|e| anyhow!("Failed to write sexp: {e}"))?;

    Ok(())
}

/// Normalize types to match OCaml's normalize_signature.
/// OCaml calls normalize_type on each Sig_value's val_type in the top-level
/// inferred signature. normalize_type is recursive (walks all children via
/// iter_type_expr), so all types reachable from a top-level val_type are normalized.
///
/// Key: OCaml's val_type comes from `enter_variable` during pattern typing, which
/// uses `build_as_type(inner)` for alias patterns. For `Tpat_alias(Tpat_any, "v")`,
/// val_type = Tpat_any's pat_type, NOT the outer pattern's pat_type. We look up
/// val_type from the env to match this behavior exactly.
fn normalize_signature_types(
    type_ctx: &TypeContext<'_>,
    typed_structure: &crate::types::typedtree::Structure,
    final_env: &crate::types::env::Env,
) {
    use crate::types::ctype::normalize_type;
    use crate::types::typedtree::{StructureItemDesc, ModuleExprDesc, PatternDesc};

    /// Collect bound variable names from a pattern.
    fn collect_bound_names(pat: &crate::types::typedtree::Pattern, names: &mut Vec<String>) {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) => {
                names.push(id.name().to_string());
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                collect_bound_names(inner, names);
                names.push(id.name().to_string());
            }
            PatternDesc::Tpat_tuple(pats)
            | PatternDesc::Tpat_construct(_, _, pats)
            | PatternDesc::Tpat_array(pats) => {
                for p in pats { collect_bound_names(p, names); }
            }
            PatternDesc::Tpat_record(fields, _) => {
                for (_, _, p, _) in fields { collect_bound_names(p, names); }
            }
            PatternDesc::Tpat_variant(_, Some(inner), _) => collect_bound_names(inner, names),
            PatternDesc::Tpat_or(left, _, _) => collect_bound_names(left, names),
            _ => {}
        }
    }

    fn norm_structure(ctx: &TypeContext<'_>, env: &crate::types::env::Env, s: &crate::types::typedtree::Structure) {
        for item in &s.str_items {
            match &item.str_desc {
                StructureItemDesc::Tstr_value(_, bindings) => {
                    for b in bindings {
                        // Look up val_type from env for each bound variable,
                        // matching OCaml's normalize_signature_item(Sig_value).
                        let mut names = Vec::new();
                        collect_bound_names(&b.vb_pat, &mut names);
                        for name in &names {
                            if let Ok(vd) = env.find_value(name) {
                                normalize_type(ctx, vd.val_type);
                            }
                        }
                        // Fallback: if no bound names found (shouldn't happen),
                        // normalize the pattern type directly.
                        if names.is_empty() {
                            normalize_type(ctx, b.vb_pat.pat_type);
                        }
                    }
                }
                StructureItemDesc::Tstr_primitive(vd) => {
                    // Normalize the primitive's top-level type
                    normalize_type(ctx, vd.val_desc.ctyp_type);
                }
                StructureItemDesc::Tstr_module(mb) => {
                    norm_modexpr(ctx, env, &mb.mb_expr);
                }
                _ => {}
            }
        }
    }

    fn norm_modexpr(ctx: &TypeContext<'_>, env: &crate::types::env::Env, me: &crate::types::typedtree::ModuleExpr) {
        match &me.mod_desc {
            ModuleExprDesc::Tmod_structure(s) => { norm_structure(ctx, env, s); }
            ModuleExprDesc::Tmod_constraint(me, _, _, _) => { norm_modexpr(ctx, env, me); }
            ModuleExprDesc::Tmod_functor(_, _, _, me) => { norm_modexpr(ctx, env, me); }
            ModuleExprDesc::Tmod_apply(me1, me2, _) => { norm_modexpr(ctx, env, me1); norm_modexpr(ctx, env, me2); }
            _ => {}
        }
    }

    norm_structure(type_ctx, final_env, typed_structure);
}
