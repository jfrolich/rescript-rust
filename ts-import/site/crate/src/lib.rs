//! The ReScript compiler with `%ts` imports, as a WebAssembly module.
//!
//! The page talks to it with one call: it writes a JSON request into the
//! input buffer, calls `tsi_run`, and reads a JSON reply from the output
//! buffer. Requests are `{"op": "stdlib", ...}` (the runtime sources, once)
//! and `{"op": "build", ...}` (TypeScript files and one ReScript file).

use std::cell::RefCell;
use std::collections::BTreeMap;

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::js_ir::ModuleFormat;
use rescript_compiler::parser::code_frame;
use rescript_compiler::source_text::decode_internal_utf8_runs;
use rescript_compiler::{ts_import, wasm_vfs};
use serde::{Deserialize, Serialize};

thread_local! {
    static INPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static OUTPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static REGISTRY: RefCell<ModuleRegistry> = RefCell::new(ModuleRegistry::new());
}

/// Sizes the input buffer and returns where the page writes the request.
#[unsafe(no_mangle)]
pub extern "C" fn tsi_input(len: usize) -> *mut u8 {
    INPUT.with(|input| {
        let mut input = input.borrow_mut();
        input.clear();
        input.resize(len, 0);
        input.as_mut_ptr()
    })
}

/// Handles the request in the input buffer; the reply is in the output buffer.
#[unsafe(no_mangle)]
pub extern "C" fn tsi_run() {
    let request = INPUT.with(|input| std::mem::take(&mut *input.borrow_mut()));
    let reply = match serde_json::from_slice::<Request>(&request) {
        Ok(request) => handle(request),
        Err(error) => serde_json::json!({ "error": format!("bad request: {error}") }),
    };
    OUTPUT.with(|output| *output.borrow_mut() = reply.to_string().into_bytes());
}

#[unsafe(no_mangle)]
pub extern "C" fn tsi_output() -> *const u8 {
    OUTPUT.with(|output| output.borrow().as_ptr())
}

#[unsafe(no_mangle)]
pub extern "C" fn tsi_output_len() -> usize {
    OUTPUT.with(|output| output.borrow().len())
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "lowercase")]
enum Request {
    /// The runtime's `.res` and `.resi` files by path. They are type checked
    /// from source when a program uses them.
    Stdlib { files: BTreeMap<String, String> },
    Build {
        files: Vec<File>,
        /// Also type check the TypeScript files in full, for comparison.
        #[serde(default)]
        full: bool,
    },
}

#[derive(Deserialize)]
struct File {
    name: String,
    source: String,
}

#[derive(Serialize)]
struct NoteOut {
    gap: &'static str,
    subject: String,
    path: String,
    ts: String,
    message: String,
}

#[derive(Serialize)]
struct ImportOut {
    start: usize,
    end: usize,
    code: Option<String>,
    error: Option<String>,
    notes: Vec<NoteOut>,
}

#[derive(Serialize, Default)]
struct StatsOut {
    files: usize,
    lib_files: usize,
    lines: usize,
    types: usize,
    micros: u64,
}

#[derive(Serialize)]
struct FullOut {
    types: usize,
    errors: usize,
    micros: u64,
}

#[derive(Serialize, Default)]
struct BuildOut {
    /// `success` or `error`.
    r#type: &'static str,
    js: Option<String>,
    message: Option<String>,
    warnings: Option<String>,
    /// The ReScript file with its `%ts` items replaced by declarations.
    expanded: Option<String>,
    imports: Vec<ImportOut>,
    stats: StatsOut,
    full: Option<FullOut>,
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
            // Parse TypeScript's own declaration files now, so that the
            // first build costs what every later one costs.
            let warm = vec![("/app/warm.ts".to_string(), "export const warm = 1;".to_string())];
            let _ = ts_import::report("let {warm} = %ts(\"./warm.ts\")", "/app/Warm.res", Some(&warm));
            serde_json::json!({ "ok": true })
        }
        Request::Build { files, full } => serde_json::to_value(build(&files, full)).unwrap_or_default(),
    }
}

fn build(files: &[File], full: bool) -> BuildOut {
    code_frame::set_color_mode(code_frame::ColorMode::Never);
    let Some(entry) = files.iter().rev().find(|file| file.name.ends_with(".res")) else {
        return BuildOut { r#type: "error", message: Some("There is no ReScript file to compile.".into()), ..Default::default() };
    };
    let ts_files: Vec<(String, String)> = files
        .iter()
        .filter(|file| !file.name.ends_with(".res"))
        .map(|file| (format!("/app/{}", file.name), file.source.clone()))
        .collect();
    let filename = format!("/app/{}", entry.name);
    let source = to_compiler_text(&entry.source);
    let mut out = BuildOut { r#type: "error", ..Default::default() };

    match ts_import::report(&source, &filename, Some(&ts_files)) {
        Ok(report) => {
            out.expanded = Some(decode_internal_utf8_runs(&report.expanded_source(&source)).into_owned());
            out.stats = StatsOut {
                files: report.stats.files,
                lib_files: report.stats.lib_files,
                lines: report.stats.lines,
                types: report.stats.types,
                micros: report.stats.micros as u64,
            };
            let mut modules: Vec<String> = Vec::new();
            for import in &report.imports {
                if !modules.contains(&import.request.module) {
                    modules.push(import.request.module.clone());
                }
            }
            out.imports = report
                .imports
                .into_iter()
                .map(|import| ImportOut {
                    start: import.start,
                    end: import.end,
                    code: import.code.as_ref().ok().cloned(),
                    error: import.code.err(),
                    notes: import
                        .notes
                        .into_iter()
                        .map(|note| NoteOut {
                            gap: note.gap.id(),
                            subject: note.subject,
                            path: note.path,
                            ts: note.ts,
                            message: note.message,
                        })
                        .collect(),
                })
                .collect();
            if full && !modules.is_empty() {
                let files = rescript_ts_import::Files::Memory(ts_files.clone());
                if let Ok(check) = rescript_ts_import::full_check(&files, &filename, &modules) {
                    out.full = Some(FullOut { types: check.types, errors: check.errors, micros: check.micros as u64 });
                }
            }
        }
        Err(message) => {
            out.message = Some(message);
            return out;
        }
    }

    let module_name = driver::module_name_from_source_filename(&filename);
    let options = CompilerOptions {
        source_filename: Some(filename.clone()),
        module_name: Some(module_name.clone()),
        output_module_format: Some(ModuleFormat::EsModule),
        ts_files: Some(ts_files),
        ..Default::default()
    };
    let registry = REGISTRY.with(|registry| registry.borrow().clone());
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
