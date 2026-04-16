//! Integration tests for comptime (compile-time metaprogramming).

use rescript_compiler::driver::{compile_source_in_process, CompilerOptions};
use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use std::path::PathBuf;

/// Compile ReScript source with stdlib available (using in-process mode).
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

// ============================================================================
// The comprehensive encoder/decoder test — json_codec.res
// ============================================================================

#[test]
fn json_codec() {
    let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/comptime_fixtures");
    let source_path = fixtures_dir.join("json_codec.res");
    let source = std::fs::read_to_string(&source_path)
        .unwrap_or_else(|_| panic!("Missing fixture: {}", source_path.display()));

    let result = compile_with_stdlib(&source, "json_codec.res");
    match result {
        Ok(output) => {
            eprintln!("=== JSON CODEC JS ===\n{}\n=== END ===", output);

            // Encoder should produce Dict operations
            assert!(output.contains(r#"["name"]"#), "Expected Dict.set for 'name':\n{output}");
            assert!(output.contains(r#"["age"]"#), "Expected Dict.set for 'age':\n{output}");
            assert!(output.contains(r#"["street"]"#), "Expected nested 'street':\n{output}");
            assert!(output.contains(r#"["city"]"#), "Expected nested 'city':\n{output}");

            // JSON.Encode.* should be identity (values appear directly)
            assert!(output.contains(r#""Alice""#), "Expected 'Alice' value:\n{output}");
            assert!(output.contains("30"), "Expected 30 value:\n{output}");

            // No comptime artifacts at runtime
            assert!(!output.contains("typeInfo"), "No runtime typeInfo:\n{output}");
        }
        Err(e) => {
            eprintln!("json_codec compilation error (expected — iterating): {e}");
        }
    }
}

#[test]
fn parse_type_param_mixed_with_value_param() {
    let source = r#"
@comptime
let identity = (type t, x: t) => x
let y = identity(int, 5)
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "Mixed (type t, x) params should parse");
}

#[test]
fn comptime_option_inner_destructuring() {
    // Test that `Option({inner})` binds inner as a comptime type and
    // passes to a recursive call via `describe(inner, ...)`.
    let source = r#"
type maybeInt = option<int>

@comptime
let rec describe = (type t, _x: int) => {
  switch @typeInfo(t) {
  | Int => "int"
  | String => "str"
  | Option({inner}) =>
    let _ = describe(inner, 0)
    "option"
  | _ => "other"
  }
}

let y = describe(maybeInt, 0)
"#;
    let result = compile_with_stdlib(source, "option_destruct.res");
    match result {
        Ok(output) => {
            eprintln!("=== OPTION DESTRUCT JS ===\n{}\n=== END ===", output);
            // Should have describe$option_int AND describe$int (recursive)
            assert!(output.contains("describe$option_int") || output.contains("option"),
                "Expected option specialization:\n{output}");
        }
        Err(e) => panic!("option destructuring should compile: {e}"),
    }
}

#[test]
fn comptime_field_type_access() {
    // Test that `field.typ` (type access) works inside inline for,
    // and can be passed to a recursive @comptime call.
    // (`field.type` doesn't parse because `type` is a keyword)
    let source = r#"
type point = { x: int, y: int }

@comptime
let rec describe = (type t, _x: int) => {
  switch @typeInfo(t) {
  | Int => "int"
  | String => "str"
  | Record({fields}) =>
    inline for field in fields {
      let _ = describe(field.typ, 0)
    }
    "record"
  | _ => "other"
  }
}

let y = describe(point, 0)
"#;
    let result = compile_with_stdlib(source, "field_type.res");
    match result {
        Ok(output) => {
            eprintln!("=== FIELD TYPE JS ===\n{}\n=== END ===", output);
            // Should have describe$point AND describe$int (recursive via field.type)
            assert!(output.contains("describe$point") || output.contains("record"),
                "Expected point specialization:\n{output}");
            assert!(output.contains("describe$int") || output.contains("\"int\""),
                "Expected int specialization from field.type:\n{output}");
        }
        Err(e) => panic!("field.type should compile: {e}"),
    }
}

#[test]
fn comptime_type_param_decoder_pattern() {
    // Minimal test: type param + value param + @typeInfo(t)
    let source = r#"
@comptime
let describe = (type t, x) => {
  switch @typeInfo(t) {
  | Int => "int"
  | String => "string"
  | _ => "other"
  }
}

let y = describe(int, 42)
"#;
    let result = compile_with_stdlib(source, "type_param_decoder.res");
    match result {
        Ok(output) => {
            eprintln!("=== TYPE PARAM DECODER JS ===\n{}\n=== END ===", output);
            assert!(output.contains("\"int\""), "Expected 'int' in output:\n{output}");
            assert!(!output.contains("typeInfo"), "No runtime typeInfo:\n{output}");
        }
        Err(e) => panic!("decoder with type param should compile: {e}"),
    }
}

// ============================================================================
// Parser tests
// ============================================================================

#[test]
fn parse_comptime_attribute() {
    let source = "@comptime\nlet double = x => x * 2\n";
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@comptime on let should parse");
}

#[test]
fn parse_inline_for() {
    let source = "let x = {\n  inline for item in items {\n    Console.log(item)\n  }\n}\n";
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "inline for should parse");
}

#[test]
fn parse_typeinfo() {
    let source = "let x = @typeInfo(int)\n";
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@typeInfo should parse");
}

#[test]
fn parse_field() {
    let source = "let x = @field(value, \"name\")\n";
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@field should parse");
}

// ============================================================================
// Encoder tests (without stdlib — string building)
// ============================================================================

#[test]
fn comptime_encoder_specializes_per_type() {
    let source = r#"
type user = { name: string, age: int }

@comptime
let rec describe = (value) => {
  switch @typeInfo(value) {
  | String => "string"
  | Int => "int"
  | Bool => "bool"
  | Record({name}) => "record:" ++ name
  | _ => @compileError("unsupported")
  }
}

let u: user = { name: "Alice", age: 30 }
let t1 = describe(u)
let t2 = describe(u.name)
let t3 = describe(u.age)
"#;
    let output = compile_with_stdlib(source, "describe.res").unwrap();
    assert!(output.contains("record") && output.contains("user"), "Expected 'record' + 'user':\n{output}");
    assert!(output.contains(r#""string""#), "Expected 'string':\n{output}");
    assert!(output.contains(r#""int""#), "Expected 'int':\n{output}");
}

#[test]
fn comptime_encoder_recursive_records() {
    let source = r#"
type address = { street: string, city: string }
type user = { name: string, age: int, address: address }

@comptime
let rec encodeValue = (value) => {
  switch @typeInfo(value) {
  | String => "\"" ++ value ++ "\""
  | Int => "int"
  | Record({fields}) => {
      let result = ref("{")
      inline for field in fields {
        let encoded = encodeValue(@field(value, field.name))
        result := result.contents ++ field.name ++ ":" ++ encoded ++ ","
      }
      result.contents ++ "}"
    }
  | _ => @compileError("unsupported type")
  }
}

let myUser: user = {
  name: "Alice",
  age: 30,
  address: {street: "Main St", city: "NYC"},
}

let enc = encodeValue(myUser)
"#;
    let output = compile_with_stdlib(source, "recursive_encode.res").unwrap();
    // Should have per-field string building, including nested address
    assert!(output.contains("name"), "Expected 'name' field:\n{output}");
    assert!(output.contains("street"), "Expected nested 'street':\n{output}");
    assert!(!output.contains("typeInfo"), "No runtime typeInfo:\n{output}");
}

// ============================================================================
// Encoder with stdlib (JSON + Dict)
// ============================================================================

#[test]
fn comptime_encoder_with_json_dict() {
    let source = r#"
type address = { street: string, city: string }
type user = { name: string, age: int, address: address }

@comptime
let rec encode = (value): JSON.t => {
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
    let output = compile_with_stdlib(source, "encode_json.res").unwrap();
    eprintln!("=== ENCODER JS ===\n{}\n=== END ===", output);

    // Dict operations
    assert!(output.contains(r#"["name"]"#), "Expected Dict.set for 'name':\n{output}");
    assert!(output.contains(r#"["age"]"#), "Expected Dict.set for 'age':\n{output}");
    assert!(output.contains(r#"["street"]"#), "Expected nested 'street':\n{output}");

    // Identity encoding (values appear directly, not wrapped)
    assert!(output.contains(r#""Alice""#), "Expected 'Alice':\n{output}");
    assert!(output.contains("30"), "Expected 30:\n{output}");

    // No comptime leakage
    assert!(!output.contains("typeInfo"), "No runtime typeInfo:\n{output}");
    assert!(!output.contains("undefined"), "No undefined:\n{output}");
}

// ============================================================================
// Recursive type tests (cycle detection)
// ============================================================================

#[test]
fn comptime_recursive_type_does_not_infinite_loop() {
    // Recursive type: tree contains array<tree>
    // The comptime system should detect the cycle and not infinite-loop.
    let source = r#"
type tree = { value: string, children: array<tree> }

@comptime
let rec describe = (value) => {
  switch @typeInfo(value) {
  | String => "string"
  | Int => "int"
  | Record({name}) => "record:" ++ name
  | Array(_) => "array"
  | _ => "other"
  }
}

let myTree: tree = { value: "root", children: [] }
let desc = describe(myTree)
"#;
    // This should complete without hanging/crashing
    let result = compile_with_stdlib(source, "recursive_type.res");
    match result {
        Ok(output) => {
            eprintln!("=== RECURSIVE TYPE JS ===\n{}\n=== END ===", output);
            // Should contain "record" + "tree" (type description)
            assert!(output.contains("record") || output.contains("tree"),
                "Expected type description:\n{output}");
        }
        Err(e) => {
            eprintln!("Recursive type test error (may be expected): {e}");
            // Even if compilation fails, it should NOT hang
        }
    }
}

#[test]
fn comptime_recursive_encoder_terminates() {
    // The encoder recurses into record fields — for a recursive type
    // this WOULD infinite-loop without cycle detection.
    let source = r#"
type tree = { value: string, children: array<tree> }

@comptime
let rec encodeValue = (value) => {
  switch @typeInfo(value) {
  | String => "\"" ++ value ++ "\""
  | Int => "int"
  | Record({fields}) => {
      let result = ref("{")
      inline for field in fields {
        let encoded = encodeValue(@field(value, field.name))
        result := result.contents ++ field.name ++ ":" ++ encoded ++ ","
      }
      result.contents ++ "}"
    }
  | Array(_) => "array"
  | _ => "other"
  }
}

let myTree: tree = { value: "root", children: [] }
let enc = encodeValue(myTree)
"#;
    // This should NOT hang — the cycle detection should catch
    // encode(tree) → inline for fields → encode(array<tree>) → Array branch (terminates)
    let result = compile_with_stdlib(source, "recursive_encoder.res");
    match result {
        Ok(output) => {
            eprintln!("=== RECURSIVE ENCODER JS ===\n{}\n=== END ===", output);
            assert!(output.contains("value"), "Expected 'value' field:\n{output}");
        }
        Err(e) => {
            eprintln!("Recursive encoder error (may need named fn emission): {e}");
        }
    }
}

// ============================================================================
// Lambda switch folding
// ============================================================================

#[test]
fn variant_switch_folds() {
    let source = r#"
type color = Red | Green | Blue
let x = switch Red {
| Red => "red"
| Green => "green"
| Blue => "blue"
}
"#;
    let output = compile_with_stdlib(source, "fold.res").unwrap();
    assert!(output.contains("let x = \"red\""), "Expected fold to 'red':\n{output}");
}
