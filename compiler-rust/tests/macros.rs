//! End-to-end tests of compile-time macros: each test compiles a small
//! project in memory, with the standard library type-checked from source.

use std::path::PathBuf;

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};

fn runtime_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime")
}

struct Project {
    registry: ModuleRegistry,
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
        Project { registry }
    }

    fn compile(&mut self, filename: &str, source: &str) -> Result<String, String> {
        let module_name = driver::module_name_from_source_filename(filename);
        let options = CompilerOptions {
            source_filename: Some(filename.to_string()),
            module_name: Some(module_name.clone()),
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
    println!("{js}");
    assert!(js.contains("double"));
}
