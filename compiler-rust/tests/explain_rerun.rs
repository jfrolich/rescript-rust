//! A unit that fails is typed a second time, from the same syntax and in a
//! fresh context, to explain the failure.

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};

/// A registry that type checks the runtime from its sources.
fn registry() -> ModuleRegistry {
    let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime");
    let mut registry = ModuleRegistry::new();
    let mut entries: Vec<PathBuf> = std::fs::read_dir(runtime)
        .expect("runtime sources")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    entries.sort();
    for extension in ["res", "resi"] {
        for path in &entries {
            if path.extension().and_then(|ext| ext.to_str()) == Some(extension) {
                let name = path.file_stem().unwrap().to_string_lossy().to_string();
                registry.insert_source_fallback_path(name, path.clone());
            }
        }
    }
    registry
}

/// The declaration locations of the syntax take a scope of the second
/// context. The scope the first context gave them can be one the second
/// gives an async function's allocation, and the location table then saw
/// two locations with one identity.
#[test]
fn a_failure_next_to_an_async_function_is_explained() {
    let options = CompilerOptions {
        source_filename: Some("/app/src/Explain.res".to_string()),
        module_name: Some("Explain".to_string()),
        check_only: true,
        ..Default::default()
    };
    let error = driver::compile_source_in_process(
        "@foo\nlet f = async x => x + 1\nlet g: string = 1\n",
        "/app/src/Explain.res",
        "Explain",
        &options,
        &registry(),
        false,
        None,
    )
    .map(|compiled| compiled.js_output)
    .expect_err("g is not a string");
    let error = format!("{error:#}");
    assert!(error.contains("But it's expected to have type:"), "{error}");
}
