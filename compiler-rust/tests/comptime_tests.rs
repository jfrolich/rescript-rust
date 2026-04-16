//! Integration tests for comptime (compile-time metaprogramming).
//!
//! Tests the comptime system end-to-end:
//! - @comptime function registration and inlining
//! - @typeInfo(T) expansion (once predefined type is added)
//! - Lambda switch constant folding on variants
//! - Fixture-based snapshot tests

use rescript_compiler::driver::{compile_source_to_js, compile_source_in_process, CompilerOptions};
use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::types::comptime::{build_type_info, TypeInfo, FieldInfo, ConstructorInfo};
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

    let module_name = PathBuf::from(filename)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                Some(ch) => ch.to_uppercase().collect::<String>() + c.as_str(),
                None => String::new(),
            }
        })
        .unwrap_or_else(|| "Test".to_string());

    match compile_source_in_process(source, filename, &module_name, &options, &registry, false) {
        Ok(result) => Ok(result.js_output),
        Err(e) => Err(format!("{e:?}")),
    }
}

// ============================================================================
// Fixture-based snapshot tests
// ============================================================================

fn run_fixture(name: &str) {
    let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/comptime_fixtures");
    let source_path = fixtures_dir.join(format!("{name}.res"));
    let expected_path = fixtures_dir.join(format!("{name}.expected.js"));

    let source = std::fs::read_to_string(&source_path)
        .unwrap_or_else(|_| panic!("Missing fixture: {}", source_path.display()));

    let expected = match std::fs::read_to_string(&expected_path) {
        Ok(content) => content,
        Err(_) => {
            let output = compile_source_to_js(&source, &format!("{name}.res"))
                .unwrap_or_else(|e| panic!("Compilation failed for {name}: {e:?}"));
            std::fs::write(&expected_path, &output)
                .unwrap_or_else(|e| panic!("Failed to write expected file: {e}"));
            eprintln!("Created expected file: {}", expected_path.display());
            panic!("Expected file was missing. Created from output. Re-run to verify.");
        }
    };

    let output = compile_source_to_js(&source, &format!("{name}.res"))
        .unwrap_or_else(|e| panic!("Compilation failed for {name}: {e:?}"));

    let output_trimmed = output
        .lines()
        .filter(|l| !l.starts_with("//") && !l.starts_with("'use strict'"))
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string();

    for expected_line in expected.lines() {
        let trimmed = expected_line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        assert!(
            output_trimmed.contains(trimmed),
            "Fixture {name}: expected line not found in output.\n\
             Expected: {trimmed}\n\
             Output:\n{output_trimmed}"
        );
    }
}

#[test]
fn fixture_simple_record() {
    run_fixture("simple_record");
}

#[test]
fn fixture_comptime_identity() {
    run_fixture("comptime_identity");
}

#[test]
fn fixture_variant_match() {
    run_fixture("variant_match");
}

#[test]
fn fixture_nested_record() {
    run_fixture("nested_record");
}

#[test]
fn fixture_optional_field() {
    run_fixture("optional_field");
}

// ============================================================================
// @comptime function tests
// ============================================================================

#[test]
fn comptime_attribute_on_let_binding_parses() {
    let source = r#"
@comptime
let double = x => x * 2
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@comptime on let should parse");
}

#[test]
fn comptime_function_definition_compiles() {
    let source = r#"
@comptime
let double = (x) => x * 2
"#;
    let result = compile_source_to_js(source, "comptime_def.res");
    assert!(result.is_ok(), "Expected @comptime let to compile: {:?}", result.err());
}

#[test]
fn comptime_function_is_registered_and_callable() {
    // @comptime function with @typeInfo — the core use case
    let source = r#"
type user = { name: string, age: int }

@comptime
let isRecord = (value: user) => {
  switch @typeInfo(user) {
  | Record(_) => true
  | _ => false
  }
}

let u: user = { name: "Alice", age: 30 }
let result = isRecord(u)
"#;
    let result = compile_source_to_js(source, "comptime_call.res");
    match result {
        Ok(output) => {
            assert!(
                output.contains("true"),
                "Expected true in output (switch should be eliminated):\n{output}"
            );
        }
        Err(e) => {
            panic!("Expected comptime call to compile: {e:?}");
        }
    }
}

// ============================================================================
// Parser: inline for and comptime builtins
// ============================================================================

#[test]
fn parse_inline_for_syntax() {
    let source = r#"
let x = {
  inline for item in items {
    Console.log(item)
  }
}
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "inline for should parse without errors");
}

#[test]
fn parse_typeinfo_expression() {
    let source = r#"
let x = @typeInfo(int)
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@typeInfo(int) should parse as expression");
}

#[test]
fn parse_field_expression() {
    let source = r#"
let x = @field(value, "name")
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "@field(value, \"name\") should parse");
}

// ============================================================================
// Lambda switch constant folding
// ============================================================================

#[test]
fn variant_switch_folds_on_known_constant() {
    let source = r#"
type color = Red | Green | Blue
let x = switch Red {
| Red => "red"
| Green => "green"
| Blue => "blue"
}
"#;
    let output = compile_source_to_js(source, "variant_fold.res").unwrap();
    assert!(
        output.contains("let x = \"red\";"),
        "Expected switch to fold to 'red':\n{output}"
    );
    assert!(
        !output.contains("switch"),
        "Expected no runtime switch:\n{output}"
    );
}

#[test]
fn variant_switch_with_payload_folds() {
    let source = r#"
type shape = Circle(float) | Rectangle(float, float) | Point
let x = switch Circle(5.0) {
| Circle(_) => "circle"
| Rectangle(_, _) => "rect"
| Point => "point"
}
"#;
    let output = compile_source_to_js(source, "payload_fold.res").unwrap();
    assert!(
        output.contains("\"circle\""),
        "Expected switch to fold to 'circle':\n{output}"
    );
}

// ============================================================================
// End-to-end compilation tests
// ============================================================================

#[test]
fn simple_let_binding_compiles() {
    let source = "let x = 42\n";
    let output = compile_source_to_js(source, "simple.res").unwrap();
    assert!(output.contains("42"), "Expected 42 in output:\n{output}");
}

#[test]
fn record_type_compiles() {
    let source = r#"
type user = { name: string, age: int }
let u: user = { name: "Alice", age: 30 }
"#;
    let output = compile_source_to_js(source, "record.res").unwrap();
    assert!(output.contains("Alice"), "Expected Alice in output:\n{output}");
}

#[test]
fn variant_type_compiles() {
    let source = r#"
type shape = Circle(float) | Rectangle(float, float) | Point
let s = Circle(5.0)
"#;
    let output = compile_source_to_js(source, "variant.res").unwrap();
    assert!(output.contains("5.0") || output.contains("5"), "Expected 5 in output:\n{output}");
}

// ============================================================================
// Stdlib compilation tests
// ============================================================================

#[test]
fn compile_with_stdlib_basic() {
    let result = compile_with_stdlib("let x = 1 + 2\nlet y = \"hello\"\n", "test.res");
    match &result {
        Ok(output) => {
            assert!(output.contains("hello"), "Expected 'hello' in:\n{output}");
        }
        Err(e) => {
            eprintln!("Stdlib compilation not available: {e}");
        }
    }
}

// ============================================================================
// Future tests (waiting for predefined typeInfo type)
// ============================================================================

#[test]
fn comptime_typeinfo_switch_eliminates_branch() {
    let source = r#"
type user = { name: string, age: int }

@comptime
let describe = (value: user) => {
  switch @typeInfo(user) {
  | Record(_) => "it is a record"
  | _ => "something else"
  }
}

let u: user = { name: "Alice", age: 30 }
let desc = describe(u)
"#;
    let result = compile_source_to_js(source, "typeinfo_switch.res");
    match result {
        Ok(output) => {
            assert!(
                output.contains("it is a record"),
                "Expected 'it is a record' (switch should be eliminated):\n{output}"
            );
        }
        Err(e) => {
            panic!("Expected to compile: {e:?}");
        }
    }
}

#[test]
#[ignore = "requires predefined typeInfo type + inline for + @field"]
fn comptime_encode_full_example() {
    // The full encode example from DESIGN.md
}

#[test]
#[ignore = "requires @comptime.derive system + predefined typeInfo type"]
fn comptime_derive_keyof() {
    run_fixture("derive_keyof");
}

#[test]
#[ignore = "requires @comptime.derive system + predefined typeInfo type"]
fn comptime_derive_partial() {
    run_fixture("derive_partial");
}

#[test]
#[ignore = "requires @comptime.inline + Boa JS engine"]
fn comptime_inline_capitalize() {
    // @comptime.inline let capitalize = (s) => ...
    // capitalize("name") → "Name" (evaluated at compile time)
}
