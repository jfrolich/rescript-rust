use wasm_bindgen::prelude::*;

use std::cell::RefCell;
use std::path::PathBuf;
use std::sync::Arc;

use rescript_compiler::cmi::persistent_env::{InMemoryModuleInfo, ModuleRegistry};
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::js_ir::ModuleFormat;
use rescript_compiler::macros::MacroHost;
use rescript_compiler::parser::{module, Parser};
use rescript_compiler::wasm_vfs;

#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
}

// ── Source text ─────────────────────────────────────────────────────────────

/// The compiler reads a source file as one character per byte (so that every
/// offset is a byte offset) and writes its output the same way.
fn to_compiler_text(text: &str) -> String {
    text.bytes().map(char::from).collect()
}

/// The inverse of [`to_compiler_text`], for text the compiler produced.
fn from_compiler_text(text: &str) -> String {
    let bytes: Option<Vec<u8>> = text.chars().map(|c| u8::try_from(c as u32).ok()).collect();
    match bytes.map(String::from_utf8) {
        Some(Ok(decoded)) => decoded,
        _ => text.to_string(),
    }
}

// ── Virtual filesystem ──────────────────────────────────────────────────────

thread_local! {
    static REGISTRY: RefCell<ModuleRegistry> = RefCell::new(new_registry());
}

fn new_registry() -> ModuleRegistry {
    let mut registry = ModuleRegistry::new();
    // The standard library is here as source only: it is type checked on
    // demand and imported from `@rescript/runtime`.
    registry.set_source_fallback_is_runtime(true);
    registry
}

/// Write a file to the virtual filesystem.
/// Call this with stdlib .res/.resi files at startup, and with user files on edit.
#[wasm_bindgen]
pub fn vfs_write_file(path: &str, content: &str) {
    wasm_vfs::write_file(path, to_compiler_text(content));
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
    REGISTRY.with(|r| *r.borrow_mut() = new_registry());
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

/// Forget a compiled module, so that modules compiled later cannot see it.
#[wasm_bindgen]
pub fn forget_module(module_name: &str) {
    REGISTRY.with(|r| r.borrow_mut().purge_module(module_name));
}

// ── Macros ──────────────────────────────────────────────────────────────────

#[wasm_bindgen]
extern "C" {
    /// `__rescript_macro_call` of `host.js`, which the page evaluates once
    /// (see [`macro_host_js`]).
    #[wasm_bindgen(catch, js_name = __rescript_macro_call)]
    fn macro_call(request: &str) -> Result<String, JsValue>;
}

/// The macro engine of the browser build: the page's own JavaScript engine.
struct PageHost;

impl MacroHost for PageHost {
    fn call(&self, request: &str) -> Result<String, String> {
        macro_call(request).map_err(|error| {
            error
                .as_string()
                .or_else(|| {
                    js_sys_message(&error)
                })
                .unwrap_or_else(|| "the macro engine failed".to_string())
        })
    }
}

fn js_sys_message(error: &JsValue) -> Option<String> {
    let message = js_reflect_get(error, "message").ok()?;
    message.as_string()
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(catch, js_namespace = Reflect, js_name = get)]
    fn js_reflect_get(target: &JsValue, key: &str) -> Result<JsValue, JsValue>;
}

/// The script the page evaluates to get `__rescript_macro_call`. Before it
/// does, it defines `__rescript_macro_source(moduleName)`, which returns the
/// compiled JavaScript of a module.
#[wasm_bindgen]
pub fn macro_host_js() -> String {
    rescript_compiler::macros::HOST_JS.to_string()
}

// ── Parse only (fast, no type checking) ─────────────────────────────────────

/// Parse ReScript source and return the parse tree as sexp with locations.
/// Returns JSON: { type: "success", parse_tree: "..." } or { type: "error", ... }
#[wasm_bindgen]
pub fn parse_to_sexp(source: &str, filename: &str) -> String {
    let source = to_compiler_text(source);
    match parse_tree_sexp(&source, filename) {
        Some(sexp) => serde_json::json!({ "type": "success", "parse_tree": sexp }).to_string(),
        None => serde_json::json!({ "type": "error", "stage": "parse", "errors": [] }).to_string(),
    }
}

fn parse_tree_sexp(source: &str, filename: &str) -> Option<String> {
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return None;
    }
    let mut buf = Vec::new();
    rescript_compiler::parser::sexp_locs::print_structure(&structure, parser.arena(), &mut buf);
    Some(String::from_utf8_lossy(&buf).into_owned())
}

// ── Full compilation pipeline ───────────────────────────────────────────────

/// Compile one file of a project, expanding the macros it uses.
///
/// The files it depends on were compiled before it; `is_runtime` marks a file
/// of `@rescript/runtime` itself. Returns JSON with the JavaScript, the
/// macro-expanded source when the file uses macros, the warnings and the
/// intermediate representations:
/// `{ type: "success", js, expanded, warnings, parse_tree, typed_tree, raw_lambda, lambda }`
/// or `{ type: "error", message, parse_tree }`.
#[wasm_bindgen]
pub fn compile_file(source: &str, filename: &str, is_runtime: bool) -> String {
    let source = to_compiler_text(source);
    // Diagnostics show a frame of the source file.
    wasm_vfs::write_file(filename, source.clone());
    let parse_tree = parse_tree_sexp(&source, filename);
    let module_name = driver::module_name_from_source_filename(filename);

    // A previous compile's signature must not shadow the new source.
    REGISTRY.with(|r| r.borrow_mut().purge_module(&module_name));

    let host: Arc<dyn MacroHost> = Arc::new(PageHost);
    let options = CompilerOptions {
        source_filename: Some(filename.to_string()),
        module_name: Some(module_name.clone()),
        capture_intermediates: true,
        output_module_format: Some(ModuleFormat::EsModule),
        macro_host: Some(host),
        ..Default::default()
    };

    let registry_snapshot = REGISTRY.with(|r| r.borrow().clone());
    let result = driver::compile_source_in_process(
        &source,
        filename,
        &module_name,
        &options,
        &registry_snapshot,
        false,
    );

    match result {
        Ok(compiled) => {
            if let Some(pers_struct) = compiled.pers_struct {
                REGISTRY.with(|r| {
                    r.borrow_mut().register_module(
                        &module_name,
                        pers_struct,
                        InMemoryModuleInfo::new(
                            PathBuf::from(filename),
                            false,
                            Default::default(),
                            is_runtime,
                        ),
                    );
                });
            }
            serde_json::json!({
                "type": "success",
                "js": from_compiler_text(&compiled.js_output),
                "expanded": compiled.expanded_source.as_deref().map(from_compiler_text),
                "warnings": from_compiler_text(&compiled.warnings),
                "parse_tree": parse_tree,
                "typed_tree": compiled.typed_tree_sexp,
                "raw_lambda": compiled.raw_lambda_sexp,
                "lambda": compiled.lambda_sexp,
            })
            .to_string()
        }
        Err(error) => serde_json::json!({
            "type": "error",
            "message": from_compiler_text(&format!("{error:#}")),
            "parse_tree": parse_tree,
        })
        .to_string(),
    }
}
