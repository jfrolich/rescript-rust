//! A small in-memory project for the macro tests: the standard library is
//! type checked from source, and macros run in QuickJS.
#![allow(dead_code)]

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::macros::MacroHost;
use rescript_compiler::macros::quickjs::QuickJsHost;

pub fn runtime_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime")
}


pub struct Project {
    registry: ModuleRegistry,
    /// Compiled JavaScript of the project's modules, for the macro engine.
    javascript: Arc<Mutex<HashMap<String, String>>>,
    host: Arc<QuickJsHost>,
    /// The expanded source of the last compiled file, when it uses macros.
    pub expanded: Option<String>,
    /// The warnings of the last compiled file.
    pub warnings: String,
}

impl Project {
    pub fn new() -> Self {
        let mut registry = ModuleRegistry::new();
        let mut modules: ahash::AHashMap<String, PathBuf> = Default::default();
        for entry in std::fs::read_dir(runtime_dir()).unwrap() {
            let path = entry.unwrap().path();
            let Some(ext) = path.extension().and_then(|e| e.to_str()) else {
                continue;
            };
            if ext != "res" && ext != "resi" {
                continue;
            }
            let name = path.file_stem().unwrap().to_str().unwrap().to_string();
            if ext == "resi" || !modules.contains_key(&name) {
                modules.insert(name, path);
            }
        }
        registry.set_source_fallback_paths(modules);
        registry.set_source_fallback_is_runtime(true);
        let javascript: Arc<Mutex<HashMap<String, String>>> = Default::default();
        let sources = javascript.clone();
        let host = Arc::new(QuickJsHost::new(Arc::new(move |name: &str| {
            if let Some(source) = sources.lock().unwrap().get(name) {
                return Some(source.clone());
            }
            std::fs::read_to_string(runtime_dir().join(format!("lib/js/{name}.cjs"))).ok()
        })));
        let mut project = Project {
            registry,
            javascript,
            host,
            expanded: None,
            warnings: String::new(),
        };
        // The macro API, compiled from source like the rest of the project.
        let macro_source = std::fs::read_to_string(runtime_dir().join("Macro.res")).unwrap();
        project.compile("Macro.res", &macro_source).unwrap();
        project
    }

    pub fn compile(&mut self, filename: &str, source: &str) -> Result<String, String> {
        let module_name = driver::module_name_from_source_filename(filename);
        let host: Arc<dyn MacroHost> = self.host.clone();
        let options = CompilerOptions {
            source_filename: Some(filename.to_string()),
            module_name: Some(module_name.clone()),
            macro_host: Some(host),
            ..Default::default()
        };
        // As the compiler reads a file: one `char` per byte.
        let source: String = source.bytes().map(char::from).collect();
        let source = source.as_str();
        match driver::compile_source_in_process(
            source,
            filename,
            &module_name,
            &options,
            &self.registry,
            false,
        ) {
            Ok(compiled) => {
                if let Some(ps) = compiled.pers_struct {
                    self.registry.register_module(
                        &module_name,
                        ps,
                        rescript_compiler::cmi::persistent_env::InMemoryModuleInfo::new(
                            PathBuf::from(filename),
                            false,
                            Default::default(),
                            module_name == "Macro",
                        ),
                    );
                }
                let text = |text: &str| {
                    rescript_compiler::source_text::decode_internal_utf8(text).into_owned()
                };
                let js = text(&compiled.js_output);
                self.javascript.lock().unwrap().insert(module_name, js.clone());
                self.host.invalidate();
                self.expanded = compiled.expanded_source.as_deref().map(text);
                self.warnings = text(&compiled.warnings);
                Ok(js)
            }
            Err(e) => Err(rescript_compiler::source_text::decode_internal_utf8(&format!("{e:#}")).into_owned()),
        }
    }
}
