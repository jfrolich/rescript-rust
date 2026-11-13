//! The ReScript compiler as a WebAssembly module, for the pages of
//! docs/verify.
//!
//! The page talks to it with one call: it writes a JSON request into the
//! input buffer, calls `rv_run`, and reads a JSON reply from the output
//! buffer. Requests are `{"op": "stdlib", ...}` (the runtime sources, once)
//! and `{"op": "build", ...}` (one ReScript file).

use std::cell::RefCell;
use std::collections::BTreeMap;

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::js_ir::ModuleFormat;
use rescript_compiler::parser::code_frame;
use rescript_compiler::source_text::decode_internal_utf8_runs;
use rescript_compiler::wasm_vfs;
use serde::{Deserialize, Serialize};

thread_local! {
    static INPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static OUTPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static REGISTRY: RefCell<ModuleRegistry> = RefCell::new(ModuleRegistry::new());
}

/// Sizes the input buffer and returns where the page writes the request.
#[unsafe(no_mangle)]
pub extern "C" fn rv_input(len: usize) -> *mut u8 {
    INPUT.with(|input| {
        let mut input = input.borrow_mut();
        input.clear();
        input.resize(len, 0);
        input.as_mut_ptr()
    })
}

/// Handles the request in the input buffer; the reply is in the output buffer.
#[unsafe(no_mangle)]
pub extern "C" fn rv_run() {
    let request = INPUT.with(|input| std::mem::take(&mut *input.borrow_mut()));
    let reply = match serde_json::from_slice::<Request>(&request) {
        Ok(request) => handle(request),
        Err(error) => serde_json::json!({ "error": format!("bad request: {error}") }),
    };
    OUTPUT.with(|output| *output.borrow_mut() = reply.to_string().into_bytes());
}

/// Where the reply starts.
#[unsafe(no_mangle)]
pub extern "C" fn rv_output() -> *const u8 {
    OUTPUT.with(|output| output.borrow().as_ptr())
}

/// The length of the reply in bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rv_output_len() -> usize {
    OUTPUT.with(|output| output.borrow().len())
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "lowercase")]
enum Request {
    /// The runtime's `.res` and `.resi` files by path. They are type checked
    /// from source when a program uses them.
    Stdlib { files: BTreeMap<String, String> },
    /// One ReScript file.
    Build { name: String, source: String },
}

#[derive(Serialize, Default)]
struct BuildOut {
    /// `success` or `error`.
    r#type: &'static str,
    js: Option<String>,
    message: Option<String>,
    warnings: Option<String>,
}

/// The compiler reads a source file as one character per byte, so that every
/// offset is a byte offset.
fn to_compiler_text(text: &str) -> String {
    text.bytes().map(char::from).collect()
}

/// `text` without terminal escape sequences: the page shows plain text.
fn plain(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(ch) = chars.next() {
        if ch == '\u{1b}' {
            // `ESC [ ... letter`
            for next in chars.by_ref() {
                if next.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn handle(request: Request) -> serde_json::Value {
    match request {
        Request::Stdlib { files } => {
            REGISTRY.with(|registry| {
                let mut registry = registry.borrow_mut();
                // The page has the runtime as source: generated JavaScript
                // imports it from the package.
                registry.set_source_fallback_is_runtime(true);
                // An interface is the module's type, so it is registered last.
                for extension in [".res", ".resi"] {
                    for (path, content) in &files {
                        let Some(stem) = path.strip_suffix(extension) else { continue };
                        wasm_vfs::write_file(path, to_compiler_text(content));
                        let name = stem.rsplit('/').next().unwrap_or(stem).to_string();
                        registry.insert_source_fallback_path(name, path.into());
                    }
                }
            });
            serde_json::json!({ "ok": true })
        }
        Request::Build { name, source } => serde_json::to_value(build(&name, &source)).unwrap_or_default(),
    }
}

fn build(name: &str, source: &str) -> BuildOut {
    code_frame::set_color_mode(code_frame::ColorMode::Never);
    let filename = format!("/app/src/{name}");
    let source = to_compiler_text(source);
    // The compiler reads the file again for the code frame of a report.
    wasm_vfs::write_file(&filename, source.clone());
    let module_name = driver::module_name_from_source_filename(&filename);
    let options = CompilerOptions {
        source_filename: Some(filename.clone()),
        module_name: Some(module_name.clone()),
        output_module_format: Some(ModuleFormat::EsModule),
        ..Default::default()
    };
    let registry = REGISTRY.with(|registry| registry.borrow().clone());
    let mut out = BuildOut { r#type: "error", ..Default::default() };
    match driver::compile_source_in_process(&source, &filename, &module_name, &options, &registry, false, None) {
        Ok(compiled) => {
            out.r#type = "success";
            out.js = Some(decode_internal_utf8_runs(&compiled.js_output).into_owned());
            if !compiled.warnings.is_empty() {
                out.warnings = Some(plain(&decode_internal_utf8_runs(&compiled.warnings)).trim().to_string());
            }
        }
        Err(error) => {
            out.message = Some(plain(&decode_internal_utf8_runs(&format!("{error}"))).trim().to_string());
        }
    }
    out
}
