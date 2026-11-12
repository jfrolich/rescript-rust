//! Browser-only compiler entry points. Build for `wasm32-unknown-unknown`;
//! `npm run test:wasm` runs the web bundle in Node.

use wasm_bindgen::prelude::*;

use std::cell::RefCell;

use rescript_compiler::cmi::persistent_env::{
    CmjPackageInfo, CmjPackageModuleSystem, InMemoryModuleInfo, ModuleRegistry,
};
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::parser::{module, Parser};
use rescript_compiler::wasm_vfs;

#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
}

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
            .insert_source_fallback_path(module_name.to_string(), source_path.into());
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
    // Each editor request is a new build, just as in rewatch's compile pass.
    // Keep portable registry signatures, but discard worker views from the
    // previous request (source-fallback declarations belong to its context).
    rescript_compiler::types::thread_store::begin_build();

    // Capture parse tree for display (separate parser since we don't want to
    // mutate the one compile_source_in_process uses).
    let mut parse_parser = Parser::new(filename, source);
    let parse_structure = module::parse_structure(&mut parse_parser);
    if parse_parser.has_errors() {
        let errors: Vec<String> = parse_parser
            .diagnostics()
            .iter()
            .map(|d| format!("{:?}", d))
            .collect();
        return serde_json::json!({ "type": "error", "stage": "parse", "errors": errors }).to_string();
    }
    let mut parse_buf = Vec::new();
    rescript_compiler::parser::sexp_locs::print_structure(
        &parse_structure,
        parse_parser.arena(),
        &mut parse_buf,
    );
    let parse_tree_sexp = String::from_utf8_lossy(&parse_buf).into_owned();

    // Derive a stable module name from the source filename.
    let module_name = driver::module_name_from_source_filename(filename);

    // Remove any stale copy of this module from the registry before compiling
    // (so a previous compile's signature doesn't shadow the new source).
    REGISTRY.with(|r| {
        let mut reg = r.borrow_mut();
        reg.purge_module(&module_name);
    });

    let options = CompilerOptions {
        source_filename: Some(filename.to_string()),
        module_name: Some(module_name.clone()),
        capture_intermediates: true,
        // User modules form one virtual package; script mode would probe disk
        // for each dependency's generated JavaScript.
        package_name: Some("playground".into()),
        output_module_format: Some(rescript_compiler::js_ir::ModuleFormat::CommonJs),
        ..Default::default()
    };

    let registry_snapshot = REGISTRY.with(|r| r.borrow().clone());
    let result = driver::compile_source_in_process(
        source,
        filename,
        &module_name,
        &options,
        &registry_snapshot,
        false,
        None,
    );

    match result {
        Ok(compiled) => {
            REGISTRY.with(|r| {
                let mut reg = r.borrow_mut();
                if let Some(ps) = compiled.pers_struct {
                    let info = InMemoryModuleInfo::new(
                        filename.into(),
                        compiled.is_pure,
                        compiled.cmj_export_constants,
                        false,
                    )
                    .with_package("playground".into(), "/".into(), Some(".js".into()))
                    .with_package_outputs(vec![CmjPackageInfo {
                        module_system: CmjPackageModuleSystem::CommonJs,
                        path: std::path::Path::new(filename)
                            .parent()
                            .unwrap_or_else(|| std::path::Path::new(""))
                            .to_string_lossy()
                            .into_owned(),
                        suffix: ".js".into(),
                    }])
                    .with_cmj_export_arities(compiled.cmj_export_arities)
                    .with_cmj_export_lambdas(compiled.cmj_export_lambdas);
                    reg.register_module_arc(&module_name, ps, info);
                }
            });
            serde_json::json!({
                "type": "success",
                "parse_tree": parse_tree_sexp,
                "typed_tree": compiled.typed_tree_sexp,
                "raw_lambda": compiled.raw_lambda_sexp,
                "lambda": compiled.lambda_sexp,
                "js": compiled.js_output,
            })
            .to_string()
        }
        Err(e) => serde_json::json!({
            "type": "error",
            "stage": "compile",
            "errors": [format!("{e:?}")],
            "parse_tree": parse_tree_sexp,
        })
        .to_string(),
    }
}
