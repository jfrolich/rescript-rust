//! A unit whose first check fails is checked again in a fresh type context.
//! Modules type checked from their sources during that second check must not
//! reuse the location scope the unit's own syntax received in the first.

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};

/// The runtime and `modules`, all type checked from their sources.
fn registry(directory: &Path, modules: &[(&str, &str)]) -> ModuleRegistry {
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
    std::fs::create_dir_all(directory).unwrap();
    for (name, source) in modules {
        let path = directory.join(format!("{name}.res"));
        std::fs::write(&path, source).unwrap();
        registry.insert_source_fallback_path(name.to_string(), path);
    }
    registry
}

#[test]
fn a_type_error_after_a_module_loaded_from_source_is_reported() {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let directory =
        std::env::temp_dir().join(format!("source-fallback-retry-{}", std::process::id()));
    let registry = registry(
        &directory,
        &[
            ("Aa", "type t\nexternal make: unit => t = \"make\""),
            (
                "Bb",
                "@deprecated(\"y\") type u\n@deprecated(\"z\") type v\nlet take = (_: int) => ()",
            ),
        ],
    );
    // `Bb` is first needed after the parameter `x` gave the unit's syntax a
    // location scope, in both checks.
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        ..CompilerOptions::default()
    };
    let result = driver::compile_source_in_process(
        "let f = (x: Aa.t) => Bb.take(x)",
        "/app/src/Demo.res",
        "Demo",
        &options,
        &registry,
        false,
        None,
    );
    for name in ["Aa", "Bb"] {
        std::fs::remove_file(directory.join(format!("{name}.res"))).unwrap();
    }
    std::fs::remove_dir(&directory).unwrap();
    let error = format!("{:#}", result.err().expect("a type error"));
    // Without the escape sequences that colour a type in a message.
    let error = plain(&error);
    assert!(error.contains("This has type: Aa.t"), "{error}");
}

fn plain(message: &str) -> String {
    let mut plain = String::with_capacity(message.len());
    let mut chars = message.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            for c in chars.by_ref() {
                if c == 'm' {
                    break;
                }
            }
        } else {
            plain.push(c);
        }
    }
    plain
}
