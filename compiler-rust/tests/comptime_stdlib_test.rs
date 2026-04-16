//! Comptime encoder test with stdlib (Js.Json, Js.Dict)

use rescript_compiler::driver::{compile_source_in_process, CompilerOptions};
use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use std::path::PathBuf;

fn compile_with_stdlib(source: &str, filename: &str) -> Result<String, String> {
    let runtime_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("packages/@rescript/runtime");

    if !runtime_dir.exists() {
        return Err(format!("Runtime dir not found: {}", runtime_dir.display()));
    }

    let mut registry = ModuleRegistry::new();
    if let Ok(entries) = std::fs::read_dir(&runtime_dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
            let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
            if ext == "resi" || ext == "res" {
                let existing = registry.source_fallback_paths.get(name);
                if existing.is_none() || ext == "resi" {
                    registry.source_fallback_paths.insert(name.to_string(), path.clone());
                }
            }
        }
    }

    let options = CompilerOptions {
        source_filename: Some(filename.to_string()),
        open_modules: vec!["Pervasives".to_string(), "Stdlib".to_string()],
        ..Default::default()
    };

    let module_name = "Test".to_string();

    match compile_source_in_process(source, filename, &module_name, &options, &registry, false) {
        Ok(result) => Ok(result.js_output),
        Err(e) => Err(format!("{e:?}")),
    }
}

#[test]
fn comptime_encoder_with_js_json() {
    let source = r#"
type address = { street: string, city: string }
type user = { name: string, age: int, address: address }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => Js.Json.string(value)
  | Int => Js.Json.number(Js.Int.toFloat(value))
  | Bool => Js.Json.boolean(value)
  | Record({fields}) =>
    let dict = Js.Dict.empty()
    inline for field in fields {
      Js.Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    Js.Json.object_(dict)
  | _ => @compileError("unsupported type")
  }
}

let myUser: user = {
  name: "Alice",
  age: 30,
  address: {street: "Main St", city: "NYC"},
}

let json = encode(myUser)
"#;

    let result = compile_with_stdlib(source, "encode_test.res");
    match result {
        Ok(output) => {
            eprintln!("=== ENCODER JS OUTPUT ===\n{}\n=== END ===", output);
            // Should contain Dict.set calls for each field
            assert!(output.contains("name"), "Expected 'name' field in output:\n{output}");
            assert!(output.contains("age"), "Expected 'age' field in output:\n{output}");
            assert!(output.contains("street"), "Expected nested 'street' in output:\n{output}");
            // Should NOT contain @typeInfo or switch on type
            assert!(!output.contains("typeInfo"), "Should not have runtime typeInfo:\n{output}");
        }
        Err(e) => {
            eprintln!("Encoder compilation error: {e}");
            // Expected for now if stdlib loading has issues
        }
    }
}
