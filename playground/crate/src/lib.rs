use wasm_bindgen::prelude::*;

use std::cell::RefCell;

use rescript_compiler::cmi::persistent_env::{ModuleRegistry, PersistentEnv};
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::parser::{module, jsx_ppx, Parser};
use rescript_compiler::binary_ast::ppx;
use rescript_compiler::context::IdGenerator;
use rescript_compiler::types::{
    initial_env, type_structure, TypeCheckContext, TypeContext,
    sexp_typedtree,
};
use rescript_compiler::wasm_vfs;

// ── Virtual filesystem ──────────────────────────────────────────────────────

thread_local! {
    static REGISTRY: RefCell<ModuleRegistry> = RefCell::new(ModuleRegistry::new());
}

/// Write a file to the virtual filesystem.
/// Call this with stdlib .res/.resi files at startup, and with user files on edit.
#[wasm_bindgen]
pub fn vfs_write_file(path: &str, content: &str) {
    wasm_vfs::write_file(path, content.to_string());
}

/// Delete a file from the virtual filesystem.
#[wasm_bindgen]
pub fn vfs_delete_file(path: &str) {
    wasm_vfs::delete_file(path);
}

/// Clear all files and reset the module registry.
#[wasm_bindgen]
pub fn vfs_clear() {
    wasm_vfs::clear();
    REGISTRY.with(|r| *r.borrow_mut() = ModuleRegistry::new());
}

/// Register a module's source path for on-demand type checking.
/// module_name: e.g. "Pervasives", "Js", "Belt"
/// source_path: path in the VFS, e.g. "/stdlib/Pervasives.resi"
#[wasm_bindgen]
pub fn register_source_module(module_name: &str, source_path: &str) {
    REGISTRY.with(|r| {
        r.borrow_mut()
            .source_fallback_paths
            .insert(module_name.to_string(), source_path.into());
    });
}

// ── Parse only (fast, no type checking) ─────────────────────────────────────

/// Parse ReScript source and return the parse tree as sexp with locations.
/// Returns JSON: { type: "success", parse_tree: "..." } or { type: "error", ... }
#[wasm_bindgen]
pub fn parse_to_sexp(source: &str, filename: &str) -> String {
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);

    if parser.has_errors() {
        let errors: Vec<String> = parser
            .diagnostics()
            .iter()
            .map(|d| format!("{:?}", d))
            .collect();
        return serde_json::json!({
            "type": "error",
            "stage": "parse",
            "errors": errors,
        })
        .to_string();
    }

    let mut buf = Vec::new();
    rescript_compiler::parser::sexp_locs::print_structure(
        &structure,
        parser.arena(),
        &mut buf,
    );
    let sexp = String::from_utf8_lossy(&buf).into_owned();

    serde_json::json!({
        "type": "success",
        "parse_tree": sexp,
    })
    .to_string()
}

// ── Full compilation pipeline ───────────────────────────────────────────────

/// Compile ReScript source through the full pipeline.
/// Returns JSON with all intermediate representations:
/// { type: "success", parse_tree, typed_tree, raw_lambda, lambda, js }
/// or { type: "error", stage, errors, ...partial results }
#[wasm_bindgen]
pub fn compile_all(source: &str, filename: &str) -> String {
    // 1. Parse
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);

    if parser.has_errors() {
        let errors: Vec<String> = parser
            .diagnostics()
            .iter()
            .map(|d| format!("{:?}", d))
            .collect();
        return serde_json::json!({
            "type": "error",
            "stage": "parse",
            "errors": errors,
        })
        .to_string();
    }

    // Capture parse tree sexp
    let mut parse_buf = Vec::new();
    rescript_compiler::parser::sexp_locs::print_structure(
        &structure,
        parser.arena(),
        &mut parse_buf,
    );
    let parse_tree_sexp = String::from_utf8_lossy(&parse_buf).into_owned();

    // 2. PPX transforms
    let options = CompilerOptions::default();
    let jsx_version = driver::jsx_version_for_structure(&structure, &options, parser.arena());
    let structure = if let Some(jsx_version) = jsx_version {
        jsx_ppx::transform_structure(structure, jsx_version, parser.arena_mut())
    } else {
        structure
    };
    let structure = ppx::expand_extensions(&structure, parser.arena_mut());
    let structure = match ppx::rewrite_structure(&structure, parser.arena_mut()) {
        Ok(s) => s,
        Err(e) => {
            return serde_json::json!({
                "type": "error",
                "stage": "ppx",
                "errors": [format!("{e}")],
                "parse_tree": parse_tree_sexp,
            })
            .to_string();
        }
    };

    // 3. Type check
    rescript_compiler::Ident::set_current_time(999);
    let id_gen = IdGenerator::with_start_stamp(999);
    let _ = id_gen.next_stamp();
    let type_ctx = TypeContext::new(&id_gen);
    let mut tctx = TypeCheckContext::new(&type_ctx, parser.arena());
    let mut env = initial_env(&type_ctx);

    // Set up persistent env from registry (in-process mode)
    let pers_env = REGISTRY.with(|r| PersistentEnv::from_registry(&r.borrow()));
    tctx.set_persistent_env(pers_env);

    // Load pervasives
    if let Some(ref mut pe) = tctx.persistent_env {
        driver::load_pervasives(
            pe,
            &mut env,
            &type_ctx,
            &options.open_modules,
            options.nopervasives,
            options.module_name.as_deref(),
        );
    }

    let (typed_structure, _final_env) =
        match type_structure(&mut tctx, &env, parser.arena(), &structure) {
            Ok(result) => result,
            Err(e) => {
                return serde_json::json!({
                    "type": "error",
                    "stage": "typecheck",
                    "errors": [format!("{e:?}")],
                    "parse_tree": parse_tree_sexp,
                })
                .to_string();
            }
        };

    // Capture typed tree sexp
    let mut typed_buf = Vec::new();
    let _ = sexp_typedtree::print_typed_structure_with_locs(
        parser.arena(),
        &type_ctx,
        &typed_structure,
        &mut typed_buf,
    );
    let typed_tree_sexp = String::from_utf8_lossy(&typed_buf).into_owned();

    // 4. Lambda conversion
    let lambda_start_stamp = type_ctx
        .current_stamp()
        .max(driver::max_lambda_input_stamp(&typed_structure));

    let unit_name = driver::module_name_from_source_filename(filename);
    let implementation_coercion =
        rescript_compiler::types::typedtree::ModuleCoercion::Tcoerce_none;

    let mut raw_converter =
        rescript_compiler::raw_lambda::convert::RawLambdaConverter::with_start_stamp_and_unit_name(
            parser.arena(),
            &type_ctx,
            &env,
            lambda_start_stamp,
            unit_name,
        );
    if let Some(persistent_env) = tctx.persistent_env.clone() {
        raw_converter.set_persistent_env(persistent_env);
    }
    let raw_lambda =
        raw_converter.convert_structure_with_coercion(&typed_structure, &implementation_coercion);
    let raw_lambda_current_stamp = raw_converter.current_stamp();

    // Capture raw lambda
    let mut raw_lambda_buf = Vec::new();
    rescript_compiler::raw_lambda::print::print_raw_lambda(&raw_lambda, &mut raw_lambda_buf);
    let raw_lambda_str = String::from_utf8_lossy(&raw_lambda_buf).into_owned();

    // 5. Lambda lowering
    let lowered_lambda =
        rescript_compiler::raw_lambda::lower::lower_to_lambda_with_start_stamp(
            raw_lambda,
            raw_lambda_current_stamp,
        );

    // Capture lambda sexp
    let mut lambda_buf = Vec::new();
    let _ = rescript_compiler::lambda::sexp_lambda::print_lambda_with_locs(
        &lowered_lambda,
        &mut lambda_buf,
    );
    let lambda_sexp = String::from_utf8_lossy(&lambda_buf).into_owned();

    // 6. JS codegen
    let mut compiler =
        rescript_compiler::lambda::compile::LambdaCompiler::with_module_path_resolver(None);
    let empty_modules = std::collections::HashSet::new();
    let program = compiler
        .compile_deps_program_with_possible_required_modules(&lowered_lambda, &empty_modules);

    let empty_directives: Vec<String> = vec![];
    let js = rescript_compiler::js_ir::printer::print_deps_program_with_directives(
        &program,
        None,
        &empty_directives,
        false,
        false,
    );

    serde_json::json!({
        "type": "success",
        "parse_tree": parse_tree_sexp,
        "typed_tree": typed_tree_sexp,
        "raw_lambda": raw_lambda_str,
        "lambda": lambda_sexp,
        "js": js,
    })
    .to_string()
}
