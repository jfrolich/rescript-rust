//! End-to-end tests of compile-time macros: each test compiles a small
//! project in memory, with the standard library type-checked from source.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::macros::MacroHost;
use rescript_compiler::macros::quickjs::QuickJsHost;

fn runtime_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime")
}


struct Project {
    registry: ModuleRegistry,
    /// Compiled JavaScript of the project's modules, for the macro engine.
    javascript: Arc<Mutex<HashMap<String, String>>>,
    host: Arc<QuickJsHost>,
    /// The expanded source of the last compiled file, when it uses macros.
    expanded: Option<String>,
}

impl Project {
    fn new() -> Self {
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
        };
        // The macro API, compiled from source like the rest of the project.
        let macro_source = std::fs::read_to_string(runtime_dir().join("Macro.res")).unwrap();
        project.compile("Macro.res", &macro_source).unwrap();
        project
    }

    fn compile(&mut self, filename: &str, source: &str) -> Result<String, String> {
        let module_name = driver::module_name_from_source_filename(filename);
        let host: Arc<dyn MacroHost> = self.host.clone();
        let options = CompilerOptions {
            source_filename: Some(filename.to_string()),
            module_name: Some(module_name.clone()),
            macro_host: Some(host),
            ..Default::default()
        };
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
                            false,
                        ),
                    );
                }
                self.javascript
                    .lock()
                    .unwrap()
                    .insert(module_name, compiled.js_output.clone());
                self.host.invalidate();
                self.expanded = compiled.expanded_source;
                Ok(compiled.js_output)
            }
            Err(e) => Err(format!("{e:#}")),
        }
    }
}

#[test]
fn plain_module_compiles() {
    let mut project = Project::new();
    let js = project
        .compile("Plain.res", "let double = x => x * 2\nlet xs = [1, 2]->Array.map(double)\n")
        .unwrap();
    assert!(js.contains("double"));
    assert!(project.expanded.is_none());
}

const DEBUG: &str = r#"
open Macro

@macro
let dbg = (e: code<'a>): code<'a> =>
  %code({
    let v = ${e}
    Console.log2(${Code.string(Code.print(e) ++ " =")}, v)
    v
  })
"#;

#[test]
fn expression_macro() {
    let mut project = Project::new();
    project.compile("Debug.res", DEBUG).unwrap();
    println!("--- Debug.res expanded\n{}", project.expanded.clone().unwrap_or_default());
    let js = project
        .compile("Main.res", "let age = 41\nlet next = %Debug.dbg(age + 1)\n")
        .unwrap();
    println!("--- Main.res expanded\n{}\n--- js\n{js}", project.expanded.clone().unwrap_or_default());
    assert!(js.contains("\"age + 1 =\""), "{js}");
}
