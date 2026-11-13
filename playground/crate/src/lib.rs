use wasm_bindgen::prelude::*;

use std::cell::RefCell;
use std::collections::HashMap;
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
    /// The modules of the standard library, with the path of their source.
    static RUNTIME_SOURCES: RefCell<HashMap<String, PathBuf>> = RefCell::new(HashMap::new());
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
    RUNTIME_SOURCES.with(|sources| sources.borrow_mut().clear());
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
    RUNTIME_SOURCES.with(|sources| {
        sources
            .borrow_mut()
            .insert(module_name.to_string(), source_path.into());
    });
}

/// Keep the standard library modules a compilation type checked from
/// source, so that the next compilation does not check them again.
fn keep_runtime_modules(loaded: Vec<rescript_compiler::cmi::portable_types::PortablePersStruct>) {
    RUNTIME_SOURCES.with(|sources| {
        let sources = sources.borrow();
        REGISTRY.with(|r| {
            let mut registry = r.borrow_mut();
            for module in loaded {
                let name = module.ps_name.clone();
                let Some(path) = sources.get(&name) else {
                    continue;
                };
                if registry.has_cached_module(&name) {
                    continue;
                }
                registry.register_module(
                    &name,
                    module,
                    InMemoryModuleInfo::new(path.clone(), false, Default::default(), true),
                );
            }
        });
    });
}

// ── Expanded source ─────────────────────────────────────────────────────────

/// The macro-expanded source of a file as a person wants to read it: without
/// the bookkeeping attributes of expansion, and formatted.
fn readable_expansion(expanded: &str, filename: &str) -> String {
    let text = strip_expansion_attributes(expanded);
    let mut parser = Parser::for_expanded_source(filename, &text);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return text;
    }
    let comments = parser.comments().to_vec();
    let printed = rescript_compiler::parser::printer::print_structure_with_comments(
        &structure,
        comments,
        parser.arena_mut(),
    );
    space_instance_groups(&unescape_generated_names(&printed))
}

/// An instance group reads as one block: no blank line between its
/// functions, one after it.
fn space_instance_groups(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let mut out = String::with_capacity(text.len());
    let mut in_group = false;
    for (index, line) in lines.iter().enumerate() {
        let continues = |line: &str| {
            line.starts_with("and ") || line.starts_with([' ', '}', ')', ']', '|'])
        };
        if in_group {
            if line.is_empty() {
                let next = lines[index + 1..].iter().find(|next| !next.is_empty());
                if next.is_some_and(|next| continues(next)) {
                    continue;
                }
                in_group = false;
            } else if !continues(line) {
                in_group = false;
                out.push('\n');
            }
        }
        if let Some(rest) = line.strip_prefix("let rec ")
            && rest.split([' ', ':', '=']).next().is_some_and(|name| name.contains('$'))
        {
            in_group = true;
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// Remove `@res.macroInstances`, the `@warning("-39")` that follows it, and
/// `@expanded.M.f`, the mark of a macro attribute that was expanded.
fn strip_expansion_attributes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    loop {
        let next = ["@res.macroInstances @warning(\"-39\") ", "@expanded."]
            .iter()
            .filter_map(|marker| rest.find(marker).map(|at| (at, *marker)))
            .min();
        let Some((at, marker)) = next else {
            out.push_str(rest);
            return out;
        };
        out.push_str(&rest[..at]);
        rest = &rest[at + marker.len()..];
        if marker == "@expanded." {
            // The macro's name, and the whitespace up to what it was on.
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
                .unwrap_or(rest.len());
            rest = rest[end..].trim_start();
        }
    }
}

/// The printer writes a name with a `$` as an exotic identifier, `\"a$"`.
fn unescape_generated_names(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("\\\"") {
        out.push_str(&rest[..at]);
        let after = &rest[at + 2..];
        match after.find('"') {
            Some(end)
                if after[..end].contains('$')
                    && after[..end]
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '\'') =>
            {
                out.push_str(&after[..end]);
                rest = &after[end + 1..];
            }
            _ => {
                out.push_str("\\\"");
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
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
/// `{ type: "success", js, expanded, expanded_raw, formatted, warnings, signature, parse_tree, typed_tree, raw_lambda, lambda }`
/// or `{ type: "error", message, parse_tree }`.
#[wasm_bindgen]
pub fn compile_file(source: &str, filename: &str, is_runtime: bool) -> String {
    compile(source, filename, is_runtime, Vec::new(), Vec::new())
}

/// Compile one input of a read-eval-print loop: a file of its own, with the
/// modules `open_modules` (the earlier inputs) opened. The result is the one
/// of [`compile_file`]; its `signature` is what the loop prints.
#[wasm_bindgen]
pub fn compile_input(source: &str, filename: &str, open_modules: Vec<String>) -> String {
    // An `open` is for the inputs after it: it is not unused (warning 33)
    // when its own input does not use it.
    compile(source, filename, false, open_modules, vec!["-33".to_string()])
}

/// What a read-eval-print loop compiles for an input. Returns JSON:
/// `{ type: "success", source, result_at, binding, opens }`: `source` has
/// `binding` (`let it = `) before a last expression, at the line and column
/// `result_at` (counted from one, null without such an expression), and
/// `opens` is the text of each top-level `open`. Or `{ type: "error" }` when
/// the input does not parse (compiling it gives the message).
#[wasm_bindgen]
pub fn prepare_input(source: &str, filename: &str) -> String {
    match rescript_compiler::repl::prepare(&to_compiler_text(source), filename) {
        Some(prepared) => serde_json::json!({
            "type": "success",
            "source": from_compiler_text(&prepared.source),
            "result_at": prepared.result_at.map(|(line, column)| [line, column]),
            "binding": rescript_compiler::repl::BINDING,
            "opens": prepared
                .opens
                .iter()
                .map(|open| from_compiler_text(open))
                .collect::<Vec<_>>(),
        })
        .to_string(),
        None => serde_json::json!({ "type": "error" }).to_string(),
    }
}

fn compile(
    source: &str,
    filename: &str,
    is_runtime: bool,
    open_modules: Vec<String>,
    warning_specs: Vec<String>,
) -> String {
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
        capture_loaded_modules: true,
        output_module_format: Some(ModuleFormat::EsModule),
        macro_host: Some(host),
        open_modules,
        warning_specs,
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
        Ok(mut compiled) => {
            keep_runtime_modules(std::mem::take(&mut compiled.loaded_modules));
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
                "expanded": compiled
                    .expanded_source
                    .as_deref()
                    .map(|expanded| from_compiler_text(&readable_expansion(expanded, filename))),
                "expanded_raw": compiled.expanded_source.as_deref().map(from_compiler_text),
                // The file as written, printed the same way: the lines of
                // `expanded` that are not in it were generated.
                "formatted": compiled
                    .expanded_source
                    .is_some()
                    .then(|| from_compiler_text(&readable_expansion(&source, filename))),
                "warnings": from_compiler_text(&compiled.warnings),
                "parse_tree": parse_tree,
                "typed_tree": compiled.typed_tree_sexp,
                "raw_lambda": compiled.raw_lambda_sexp,
                "lambda": compiled.lambda_sexp,
                // What the file defines (`repl::describe_signature`).
                "signature": serde_json::from_str::<serde_json::Value>(
                    &from_compiler_text(&compiled.signature_description),
                )
                .unwrap_or(serde_json::Value::Null),
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
