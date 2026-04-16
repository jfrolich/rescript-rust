//! Comptime encoder test with stdlib (JSON, Dict — ReScript 12 API)
//!
//! These tests verify that the @comptime encoder pattern works with real
//! ReScript 12 stdlib types (JSON.t, Dict). The encoder pattern uses:
//! - JSON.Encode.string/int/float/bool/object (all %identity — zero-cost)
//! - Dict.make() + Dict.set()
//!
//! The full pipeline works: comptime specialization produces per-field code,
//! JSON.Encode.* compiles to identity (values ARE JSON), Dict operations
//! compile to clean property assignments.

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

/// The north star: a generic JSON encoder using @comptime + ReScript 12 API.
///
/// This is what users would write. Since JSON.Encode.* are all %identity externals,
/// the compiled output should be zero-overhead — just Dict operations and raw values.
///
/// Expected output (once external resolution is fixed):
/// ```js
/// let dict = {};
/// dict["name"] = myUser.name;
/// dict["age"] = myUser.age;
/// let dict$1 = {};
/// dict$1["street"] = myUser.address.street;
/// dict$1["city"] = myUser.address.city;
/// dict["address"] = dict$1;
/// let json = dict;
/// ```
#[test]
fn comptime_encoder_north_star() {
    let source = r#"
type address = { street: string, city: string }
type user = { name: string, age: int, address: address }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
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
            eprintln!("=== NORTH STAR ENCODER JS ===\n{}\n=== END ===", output);
            // Verify comptime specialization worked:
            // - No typeInfo/switch at runtime
            assert!(!output.contains("typeInfo"), "Should not have runtime typeInfo:\n{output}");
            // - No undefined (all externals resolved correctly)
            assert!(!output.contains("undefined"), "Should not have undefined:\n{output}");
            // - Dict operations compiled correctly
            assert!(output.contains(r#"["name"]"#), "Expected Dict.set for 'name':\n{output}");
            assert!(output.contains(r#"["age"]"#), "Expected Dict.set for 'age':\n{output}");
            assert!(output.contains(r#"["street"]"#), "Expected nested 'street':\n{output}");
            assert!(output.contains(r#"["city"]"#), "Expected nested 'city':\n{output}");
            assert!(output.contains(r#"["address"]"#), "Expected Dict.set for 'address':\n{output}");
            // - JSON.Encode.* compiled as identity (values appear directly)
            assert!(output.contains(r#""Alice""#), "Expected 'Alice' value:\n{output}");
            assert!(output.contains("30"), "Expected 30 value:\n{output}");
        }
        Err(e) => {
            panic!("North star encoder should compile: {e}");
        }
    }
}

#[test]
fn simple_stdlib_dict() {
    let source = r#"
let d = Dict.make()
Dict.set(d, "hello", "world")
"#;

    let result = compile_with_stdlib(source, "dict_test.res");
    match result {
        Ok(output) => {
            eprintln!("=== DICT JS ===\n{}\n=== END ===", output);
            // Dict.make compiles correctly (it's @obj external)
            assert!(output.contains("hello"), "Expected 'hello':\n{output}");
        }
        Err(e) => {
            panic!("Dict test should compile: {e}");
        }
    }
}

#[test]
fn simple_stdlib_json_encode() {
    let source = r#"
let x: JSON.t = JSON.Encode.string("hello")
let y: JSON.t = JSON.Encode.int(42)
"#;

    let result = compile_with_stdlib(source, "json_test.res");
    match result {
        Ok(output) => {
            eprintln!("=== JSON ENCODE JS ===\n{}\n=== END ===", output);
            assert!(output.contains("hello"), "Expected 'hello':\n{output}");
        }
        Err(e) => {
            panic!("JSON encode test should compile: {e}");
        }
    }
}
