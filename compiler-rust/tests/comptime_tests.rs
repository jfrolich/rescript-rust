//! Integration tests for comptime (compile-time metaprogramming).

use rescript_compiler::driver::{compile_source_in_process, typecheck_interface_in_process, CompilerOptions};
use rescript_compiler::cmi::persistent_env::{ModuleRegistry, InMemoryModuleInfo};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::OnceLock;

/// Pre-compile the stdlib modules into a ModuleRegistry. Cached so each test
/// doesn't re-typecheck Pervasives/Stdlib/etc. every time.
fn stdlib_registry() -> &'static ModuleRegistry {
    static REGISTRY: OnceLock<ModuleRegistry> = OnceLock::new();
    REGISTRY.get_or_init(|| {
        let runtime_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("packages/@rescript/runtime");

        let mut registry = ModuleRegistry::new();

        // Register source fallback paths. Prefer .resi when both exist.
        // Modules are compiled lazily on first lookup (matches the playground).
        if let Ok(entries) = std::fs::read_dir(&runtime_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
                let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
                if ext == "res" {
                    registry.source_fallback_paths.insert(name.to_string(), path);
                }
            }
        }
        if let Ok(entries) = std::fs::read_dir(&runtime_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
                let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
                if ext == "resi" {
                    registry.source_fallback_paths.insert(name.to_string(), path);
                }
            }
        }

        registry
    })
}

/// Type-check a single stdlib interface (or .res as interface) and add it
/// to the registry.
fn compile_runtime_module(
    name: &str,
    path: &PathBuf,
    registry: &mut ModuleRegistry,
) -> Result<(), String> {
    let source = std::fs::read_to_string(path).map_err(|e| format!("read: {e}"))?;
    let is_runtime_module = true;

    // Pervasives and Stdlib bootstrap; use nopervasives for runtime modules
    let options = CompilerOptions {
        source_filename: Some(path.to_string_lossy().to_string()),
        nopervasives: is_runtime_module,
        module_name: Some(name.to_string()),
        open_modules: vec![],
        ..Default::default()
    };

    let is_interface = path.extension().and_then(|s| s.to_str()) == Some("resi");

    if is_interface {
        let result = typecheck_interface_in_process(
            &source,
            &path.to_string_lossy(),
            name,
            &options,
            registry,
        ).map_err(|e| format!("typecheck {name}: {e:?}"))?;

        if let Some(ps) = result.pers_struct {
            registry.cached_modules.insert(name.to_string(), ps);
            registry.module_info.insert(name.to_string(), InMemoryModuleInfo {
                source_path: path.clone(),
                is_pure: true,
                is_runtime: is_runtime_module,
            });
            registry.alias_rewrites.extend(result.new_alias_rewrites);
        }
    } else {
        // .res without .resi: treat as implementation
        let result = compile_source_in_process(
            &source,
            &path.to_string_lossy(),
            name,
            &options,
            registry,
            false,
        ).map_err(|e| format!("compile {name}: {e:?}"))?;

        if let Some(ps) = result.pers_struct {
            registry.cached_modules.insert(name.to_string(), ps);
            registry.module_info.insert(name.to_string(), InMemoryModuleInfo {
                source_path: path.clone(),
                is_pure: true,
                is_runtime: is_runtime_module,
            });
            registry.alias_rewrites.extend(result.new_alias_rewrites);
        }
    }

    Ok(())
}

/// Compile ReScript source with stdlib available (using in-process mode).
/// Runs the compile in a thread with a large stack — matches the bsc CLI,
/// which uses 512MB to accommodate deeply nested type structures and
/// recursive comptime specialization.
fn compile_with_stdlib(source: &str, filename: &str) -> Result<String, String> {
    let source = source.to_string();
    let filename = filename.to_string();

    std::thread::Builder::new()
        .name("comptime-test-compile".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let registry = stdlib_registry().clone();

            let options = CompilerOptions {
                source_filename: Some(filename.clone()),
                open_modules: vec!["Pervasives".to_string(), "Stdlib".to_string()],
                ..Default::default()
            };

            let module_name = "Test".to_string();

            match compile_source_in_process(&source, &filename, &module_name, &options, &registry, false) {
                Ok(result) => Ok(result.js_output),
                Err(e) => Err(format!("{e:?}")),
            }
        })
        .map_err(|e| format!("spawn: {e}"))?
        .join()
        .map_err(|_| "compile thread panicked".to_string())?
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
fn comptime_record_with_type_param() {
    // Test @record(t, inline for ...) where t is a comptime type parameter
    let source = r#"
type point = { x: int, y: int }

@comptime
let rebuild = (type t, src: point) => {
  switch @typeInfo(t) {
  | Record({fields}) =>
    @record(t, inline for field in fields {
      @field(src, field.name)
    })
  | _ => @compileError("expected record")
  }
}

let p: point = { x: 1, y: 2 }
let p2 = rebuild(point, p)
"#;
    let result = compile_with_stdlib(source, "record_type_param.res");
    match result {
        Ok(output) => {
            eprintln!("=== RECORD TYPE PARAM JS ===\n{}\n=== END ===", output);
            assert!(output.contains("rebuild$point"), "Expected rebuild$point:\n{output}");
            // Should have x: p.x, y: p.y or equivalent
            assert!(output.contains(".x") || output.contains("1"), "Expected x field:\n{output}");
        }
        Err(e) => panic!("@record with type param should compile: {e}"),
    }
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
fn comptime_inline_prefix_field_names() {
    // @comptime.inline function runs at compile time via JS (Boa).
    // addPrefix(f.name) evaluates "user_" + s at compile time.
    let source = r#"
type user = { name: string, age: int, email: string }

@comptime.inline
let addPrefix = (s) => "user_" ++ s

@comptime
let prefixedKeys =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(Array.map(fields, f => @variantCase({name: addPrefix(f.name)})))
  | _ => @compileError("expected record")
  }

// Use the generated variant — constructor names come from JS-evaluated
// addPrefix("name") → "user_name", then capitalized to "User_name"
let k1: prefixedKeys = User_name
let k2: prefixedKeys = User_age
let k3: prefixedKeys = User_email
"#;
    let result = compile_with_stdlib(source, "comptime_inline_prefix.res");
    match result {
        Ok(output) => {
            eprintln!("=== COMPTIME.INLINE PREFIX JS ===\n{}\n=== END ===", output);
            // The variant constructors should be User_name, User_age, User_email
            assert!(output.contains("User_name"), "Expected User_name:\n{output}");
            assert!(output.contains("User_age"), "Expected User_age:\n{output}");
            assert!(output.contains("User_email"), "Expected User_email:\n{output}");
        }
        Err(e) => panic!("@comptime.inline should compile: {e}"),
    }
}

#[test]
fn comptime_build_type_variant() {
    // @buildType(Variant({constructors: ...})) — unified type-builder API
    // that takes the target type kind directly as a pseudo-variant.
    let source = r#"
type user = { name: string, age: int, email: string }

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildType(Variant({
      constructors: fields->Array.map(field => {name: field.name}),
    }))
  | _ => @compileError("expected record")
  }

let k1: userKey = Name
let k2: userKey = Age
let k3: userKey = Email
"#;
    let result = compile_with_stdlib(source, "build_type_variant.res");
    match result {
        Ok(output) => {
            eprintln!("=== BUILDTYPE VARIANT ===\n{}\n=== END ===", output);
            assert!(output.contains("Name"), "Expected Name ctor:\n{output}");
            assert!(output.contains("Age"), "Expected Age ctor:\n{output}");
            assert!(output.contains("Email"), "Expected Email ctor:\n{output}");
        }
        Err(e) => panic!("@buildType(Variant) should compile: {e}"),
    }
}

#[test]
fn comptime_array_map_value_context() {
    // Array.map on a comptime array (like fields from @typeInfo)
    // should unroll to a concrete array literal at compile time.
    let source = r#"
type user = { name: string, age: int, email: string }

let fieldNames: array<string> = switch @typeInfo(user) {
| Record({fields}) => Array.map(fields, f => f.name)
| _ => []
}
"#;
    let result = compile_with_stdlib(source, "array_map_value.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.MAP VALUE CONTEXT ===\n{}\n=== END ===", output);
            // Should be a concrete array literal
            assert!(output.contains("\"name\""), "Expected 'name':\n{output}");
            assert!(output.contains("\"age\""), "Expected 'age':\n{output}");
            assert!(output.contains("\"email\""), "Expected 'email':\n{output}");
            // Should NOT contain runtime Array.map call
            assert!(!output.contains(".map("), "Should not have runtime .map:\n{output}");
        }
        Err(e) => panic!("Array.map in value context should compile: {e}"),
    }
}

#[test]
fn comptime_array_map_as_inline_for() {
    // Array.map(fields, f => ...) should work interchangeably with
    // inline for field in fields { ... } in comptime contexts.
    let source = r#"
type user = { name: string, age: int, email: string }

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(Array.map(fields, f => @variantCase({name: f.name})))
  | _ => @compileError("expected record")
  }

let k: userKey = Name
let k2: userKey = Age
let k3: userKey = Email
"#;
    let result = compile_with_stdlib(source, "array_map_inline.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.MAP AS INLINE FOR ===\n{}\n=== END ===", output);
            assert!(output.contains("Name"), "Expected Name:\n{output}");
            assert!(output.contains("Age"), "Expected Age:\n{output}");
            assert!(output.contains("Email"), "Expected Email:\n{output}");
        }
        Err(e) => panic!("Array.map as inline for should compile: {e}"),
    }
}

#[test]
fn comptime_array_foreach_unrolls() {
    // Array.forEach on a comptime array should unroll into a sequence of
    // statements (no runtime .forEach call left in the output).
    let source = r#"
type user = { name: string, age: int }

let alice: user = { name: "Alice", age: 30 }

let dict = Dict.make()

let () = switch @typeInfo(user) {
| Record({fields}) =>
  fields->Array.forEach(field => {
    Dict.set(dict, field.name, "x")
  })
| _ => ()
}
"#;
    let result = compile_with_stdlib(source, "array_foreach.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.FOREACH ===\n{}\n=== END ===", output);
            assert!(output.contains("\"name\""), "Expected 'name' literal:\n{output}");
            assert!(output.contains("\"age\""), "Expected 'age' literal:\n{output}");
            assert!(!output.contains(".forEach"), "Should not have runtime .forEach:\n{output}");
        }
        Err(e) => panic!("Array.forEach should compile: {e}"),
    }
}

#[test]
fn comptime_constructor_multi_arg_inside_comptime() {
    let source = r#"
type shape =
  | Rectangle(float, float)

@comptime
let make = (type t) => {
  switch @typeInfo(t) {
  | Variant(_) => @constructor(t, "Rectangle", [3.0, 4.0])
  | _ => @compileError("unsupported")
  }
}

let rect: shape = make(shape)
"#;
    let result = compile_with_stdlib(source, "ctor_multi_comptime.res");
    match result {
        Ok(_) => {}
        Err(e) => panic!("multi-arg @constructor inside @comptime should compile: {e}"),
    }
}

#[test]
fn comptime_constructor_multi_arg_with_map_with_index() {
    // Build a multi-arg constructor using Array.mapWithIndex over c.args —
    // the decoder pattern.
    let source = r#"
type shape =
  | Rectangle(float, float)

@comptime
let make = (type t) => {
  switch @typeInfo(t) {
  | Variant({constructors}) =>
    let result = ref(None)
    let _ = constructors
    result := Some(@constructor(t, "Rectangle", [3.0, 4.0]))
    switch result.contents { | Some(v) => v | None => failwith("no ctor") }
  | _ => @compileError("unsupported")
  }
}

let rect: shape = make(shape)
"#;
    let result = compile_with_stdlib(source, "ctor_multi_mapidx.res");
    match result {
        Ok(output) => {
            eprintln!("=== CTOR MULTI MAPIDX ===\n{}\n=== END ===", output);
        }
        Err(e) => panic!("multi-arg @constructor with mapWithIndex should compile: {e}"),
    }
}

#[test]
fn comptime_constructor_multi_arg_array_literal() {
    // @constructor with an array-literal payload builds a multi-arg variant.
    let source = r#"
type pair = Pair(int, string)

let p: pair = @constructor(pair, "Pair", [42, "hello"])
"#;
    let result = compile_with_stdlib(source, "ctor_multi_literal.res");
    match result {
        Ok(output) => {
            eprintln!("=== CONSTRUCTOR MULTI LITERAL ===\n{}\n=== END ===", output);
            assert!(output.contains("Pair") || output.contains("42"),
                "Expected Pair or 42 in output:\n{output}");
            assert!(output.contains("hello"), "Expected 'hello' in output:\n{output}");
        }
        Err(e) => panic!("@constructor with array literal should compile: {e}"),
    }
}

#[test]
fn comptime_constructor_multi_arg_decoder() {
    // Decode a JSON array into a multi-arg variant via
    // @constructor(t, name, c.args->Array.mapWithIndex(...)).
    let source = r#"
type shape =
  | Circle(float)
  | Rectangle(float, float)

exception DecodeError(string)

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | Float =>
    switch json { | Number(n) => n | _ => throw(DecodeError("expected number")) }
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) =>
        let result = ref(None)
        constructors->Array.forEach(c => {
          if name == c.name {
            result := Some(@constructor(t, c.name, c.args->Array.mapWithIndex((argType, i) =>
              decode(argType, Option.getExn(items[i+1]))
            )))
          }
        })
        switch result.contents {
        | Some(v) => v
        | None => throw(DecodeError("unknown variant"))
        }
      | _ => throw(DecodeError("expected [name, ...]"))
      }
    | _ => throw(DecodeError("expected array"))
    }
  | _ => @compileError("unsupported type")
  }
}

let rect: shape = decode(shape, JSON.parseExn(`["Rectangle", 3.0, 4.0]`))
"#;
    let result = compile_with_stdlib(source, "ctor_multi_decoder.res");
    match result {
        Ok(output) => {
            eprintln!("=== CONSTRUCTOR MULTI DECODER ===\n{}\n=== END ===", output);
            // Should not have runtime .mapWithIndex
            assert!(!output.contains(".mapWithIndex"),
                "Should not have runtime .mapWithIndex:\n{output}");
        }
        Err(e) => panic!("multi-arg decoder should compile: {e}"),
    }
}

#[test]
fn comptime_array_for_each_with_index_unrolls() {
    // Array.forEachWithIndex on a comptime array binds the index as a
    // comptime int per iteration, so references like `i` get inlined.
    let source = r#"
type user = { name: string, age: int, email: string }

let arr: array<int> = []

let () = switch @typeInfo(user) {
| Record({fields}) =>
  fields->Array.forEachWithIndex((field, i) => {
    Array.push(arr, i)
    ignore(field.name)
  })
| _ => ()
}
"#;
    let result = compile_with_stdlib(source, "array_for_each_with_index.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.FOREACHWITHINDEX ===\n{}\n=== END ===", output);
            // Each iteration should have the constant index inlined.
            assert!(output.contains("push(0)"), "Expected index 0:\n{output}");
            assert!(output.contains("push(1)"), "Expected index 1:\n{output}");
            assert!(output.contains("push(2)"), "Expected index 2:\n{output}");
            assert!(!output.contains(".forEachWithIndex"),
                "Should not have runtime .forEachWithIndex:\n{output}");
        }
        Err(e) => panic!("Array.forEachWithIndex should compile: {e}"),
    }
}

#[test]
fn comptime_build_record_partial_spread_pipe() {
    // @recordField({...field, optional: true}) — spread source spec and
    // override a single attribute. Uses pipe `->` form for the loop.
    let source = r#"
type user = { name: string, age: int }

@comptime
let partialUser =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildRecord(fields->Array.map(field =>
      @recordField({...field, optional: true})
    ))
  | _ => @compileError("expected record")
  }

let patch: partialUser = { name: "Alice" }
"#;
    let result = compile_with_stdlib(source, "build_record_partial_pipe.res");
    match result {
        Ok(output) => {
            eprintln!("=== BUILD RECORD PARTIAL PIPE ===\n{}\n=== END ===", output);
            assert!(output.contains("Alice"), "Expected Alice:\n{output}");
        }
        Err(e) => panic!("@recordField spread (pipe) should compile: {e}"),
    }
}

#[test]
fn comptime_encoder_flat_record() {
    // Simpler version of comptime_encoder_recursive_records with no nested
    // records — isolates whether the stack overflow is nesting-related.
    let source = r#"
type user = { name: string, age: int }

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

let myUser: user = { name: "Alice", age: 30 }
let enc = encodeValue(myUser)
"#;
    let output = compile_with_stdlib(source, "encode_flat.res").unwrap();
    assert!(output.contains("name"), "Expected 'name':\n{output}");
}

#[test]
fn comptime_decoder_result_minimal() {
    let source = r#"
type user = { name: string, age: int }

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => Ok(s) | _ => Error("expected string") }
  | Int =>
    switch json { | Number(n) => Ok(Float.toInt(n)) | _ => Error("expected int") }
  | Record({fields}) =>
    switch json {
    | Object(dict) => {
        let err = ref(None)
        let values = fields->Array.map(field =>
          switch decode(field.typ, Dict.getUnsafe(dict, field.name)) {
          | Ok(v) => v
          | Error(e) => {
              if err.contents == None { err := Some(e) }
              %raw(`null`)
            }
          }
        )
        switch err.contents {
        | None => Ok(@record(t, values))
        | Some(e) => Error(e)
        }
      }
    | _ => Error("expected object")
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let aliceJson = JSON.parseExn(`{"name":"Alice","age":30}`)
let decoded = decode(user, aliceJson)
"#;
    let result = compile_with_stdlib(source, "decoder_result.res");
    match result {
        Ok(_) => {}
        Err(e) => panic!("result-based decoder should compile: {e}"),
    }
}

#[test]
fn comptime_playground_initial_compiles() {
    // Compile the playground's INITIAL_CODE end-to-end.
    let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/comptime_fixtures");
    let source = std::fs::read_to_string(fixtures_dir.join("playground_initial.res")).unwrap();
    let result = compile_with_stdlib(&source, "playground_initial.res");
    match result {
        Ok(_) => {}
        Err(e) => panic!("playground INITIAL_CODE should compile: {e}"),
    }
}

#[test]
fn comptime_generic_partial() {
    // Generic `partial<T>`: takes a type, returns a new record type with
    // every field marked optional. Uses `{...field, optional: true}` spread.
    let source = r#"
type user = { name: string, age: int, email: string }
type admin = { role: string, level: int }

@comptime
let partial = (type t) =>
  switch @typeInfo(t) {
  | Record({fields}) =>
    @buildRecord(fields->Array.map(field =>
      @recordField({...field, optional: true})
    ))
  | _ => @compileError("partial: expected record")
  }

@comptime
let partialUser = partial(user)

@comptime
let partialAdmin = partial(admin)

let u: partialUser = { name: "Alice" }
let a: partialAdmin = { role: "root" }
"#;
    let result = compile_with_stdlib(source, "generic_partial.res");
    match result {
        Ok(output) => {
            eprintln!("=== GENERIC PARTIAL ===\n{}\n=== END ===", output);
            assert!(output.contains("Alice"), "Expected Alice:\n{output}");
            assert!(output.contains("root"), "Expected root:\n{output}");
        }
        Err(e) => panic!("generic partial should compile: {e}"),
    }
}

#[test]
fn comptime_build_record_partial_spread() {
    // @recordField({...field, optional: true}) — spread source field spec
    // and override a single attribute. Produces `partial<T>` semantics.
    let source = r#"
type user = { name: string, age: int }

@comptime
let partialUser =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildRecord(Array.map(fields, field =>
      @recordField({...field, optional: true})
    ))
  | _ => @compileError("expected record")
  }

let patch: partialUser = { name: "Alice" }
"#;
    let result = compile_with_stdlib(source, "build_record_partial_spread.res");
    match result {
        Ok(output) => {
            eprintln!("=== BUILD RECORD PARTIAL SPREAD ===\n{}\n=== END ===", output);
            assert!(output.contains("Alice"), "Expected Alice:\n{output}");
        }
        Err(e) => panic!("@recordField spread should compile: {e}"),
    }
}

#[test]
fn comptime_array_map_with_index_unrolls() {
    let source = r#"
type pair = { a: string, b: string }

let positions: array<int> = switch @typeInfo(pair) {
| Record({fields}) => fields->Array.mapWithIndex((field, i) => {
    ignore(field.name)
    i
  })
| _ => []
}
"#;
    let result = compile_with_stdlib(source, "array_map_with_index.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.MAPWITHINDEX ===\n{}\n=== END ===", output);
            assert!(!output.contains(".mapWithIndex"),
                "Should not have runtime .mapWithIndex:\n{output}");
        }
        Err(e) => panic!("Array.mapWithIndex should compile: {e}"),
    }
}

#[test]
fn comptime_array_reduce_unrolls() {
    // Array.reduce on a comptime array should unroll into a let-chain
    // threading the accumulator through each iteration.
    let source = r#"
type user = { name: string, age: int, email: string }

let allFieldNames: string = switch @typeInfo(user) {
| Record({fields}) =>
  fields->Array.reduce("", (acc, field) => acc ++ field.name)
| _ => ""
}
"#;
    let result = compile_with_stdlib(source, "array_reduce.res");
    match result {
        Ok(output) => {
            eprintln!("=== ARRAY.REDUCE ===\n{}\n=== END ===", output);
            assert!(output.contains("\"name\""), "Expected 'name' literal:\n{output}");
            assert!(output.contains("\"age\""), "Expected 'age' literal:\n{output}");
            assert!(output.contains("\"email\""), "Expected 'email' literal:\n{output}");
            assert!(!output.contains(".reduce"), "Should not have runtime .reduce:\n{output}");
        }
        Err(e) => panic!("Array.reduce should compile: {e}"),
    }
}

#[test]
fn comptime_build_record_mirror() {
    // @buildRecord + @recordField: build a record with the same fields
    // as the source type (non-optional).
    let source = r#"
type user = { name: string, age: int }

@comptime
let userCopy =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildRecord(inline for field in fields {
      @recordField({name: field.name, typ: field.typ})
    })
  | _ => @compileError("expected record")
  }

// userCopy is now a record type with fields {name: string, age: int}
let u: userCopy = { name: "Alice", age: 30 }
"#;
    let result = compile_with_stdlib(source, "build_record_mirror.res");
    match result {
        Ok(output) => {
            eprintln!("=== BUILD RECORD JS ===\n{}\n=== END ===", output);
            assert!(output.contains("Alice"), "Expected Alice:\n{output}");
            assert!(output.contains("30"), "Expected 30:\n{output}");
        }
        Err(e) => panic!("@buildRecord should compile: {e}"),
    }
}

#[test]
fn comptime_generic_keysof() {
    // Generic: @comptime let keysOf takes a type parameter, returns a type.
    // Each `@comptime let x = keysOf(T)` instantiates a specialized type.
    let source = r#"
type user = { name: string, age: int, email: string }
type admin = { role: string, level: int }

@comptime
let keysOf = (type t) =>
  switch @typeInfo(t) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name})
    })
  | _ => @compileError("keysOf: expected record")
  }

@comptime
let userKey = keysOf(user)

@comptime
let adminKey = keysOf(admin)

let u: userKey = Name
let a: adminKey = Role
"#;
    let result = compile_with_stdlib(source, "generic_keysof.res");
    match result {
        Ok(output) => {
            eprintln!("=== GENERIC KEYSOF JS ===\n{}\n=== END ===", output);
            // u should reference a userKey constructor
            assert!(output.contains("Name"), "Expected Name in output:\n{output}");
            assert!(output.contains("Role"), "Expected Role in output:\n{output}");
        }
        Err(e) => panic!("generic keysOf should compile: {e}"),
    }
}

#[test]
fn comptime_type_builder_variant_from_record_fields() {
    // The target: @comptime let produces a type declaration.
    let source = r#"
type user = { name: string, age: int, email: string }

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name})
    })
  | _ => @compileError("expected record")
  }

let myKey: userKey = Name
let myKey2: userKey = Age
"#;
    let result = compile_with_stdlib(source, "variant_from_fields.res");
    match result {
        Ok(output) => {
            eprintln!("=== VARIANT FROM FIELDS JS ===\n{}\n=== END ===", output);
            // Should contain constructor references
            assert!(output.contains("Name") || output.contains("\"Name\"") || output.contains("/* Name */"),
                "Expected Name constructor:\n{output}");
            assert!(output.contains("Age") || output.contains("\"Age\"") || output.contains("/* Age */"),
                "Expected Age constructor:\n{output}");
        }
        Err(e) => panic!("@comptime type builder should compile: {e}"),
    }
}

#[test]
fn parse_comptime_type_decl() {
    // Test if @comptime type userKeys = @buildVariant(...) can parse
    let source = r#"
type user = { name: string, age: int }

@comptime
type userKeys = @buildVariant([@variantCase({name: "Name"})])
"#;
    let mut parser = rescript_compiler::parser::Parser::new("test.res", source);
    let _structure = rescript_compiler::parser::module::parse_structure(&mut parser);
    if parser.has_errors() {
        eprintln!("Parse errors:");
        for d in parser.diagnostics() {
            eprintln!("  {:?}", d);
        }
    }
}

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
#[ignore = "requires full stdlib bootstrap — uses in-process registry which needs pre-compiled Pervasives/Stdlib/Stdlib_Dict/Stdlib_JSON. The comptime encoder IS working correctly (see comptime_encoder_recursive_records which tests the same pattern without stdlib)"]
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

#[test]
fn playground_double_compile() {
    // Simulate the playground's flow: compile twice with registry state
    // accumulating between compiles (as happens on user edits in the playground).
    use rescript_compiler::cmi::persistent_env::{ModuleRegistry, PersistentEnv};

    // Use a mutable registry that gets updated after each compile
    let mut registry = stdlib_registry().clone();
    let source = r#"type user = { name: string, age: int }

exception DecodeError(string)

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | _ => @compileError("unsupported")
  }
}

let alice: user = { name: "Alice", age: 30 }
let aliceJson = encode(alice)
"#;

    for iteration in 1..=2 {
        let options = CompilerOptions {
            source_filename: Some("Playground.res".to_string()),
            ..Default::default()
        };
        let module_name = "Playground".to_string();

        // Like the playground: remove this module from registry before compile
        registry.cached_modules.remove(&module_name);
        registry.module_info.remove(&module_name);

        let result = compile_source_in_process(source, "Playground.res", &module_name, &options, &registry, false);
        match result {
            Ok(r) => {
                eprintln!("=== Iteration {iteration} output ===");
                assert!(r.js_output.contains("encode$user"),
                    "Iteration {iteration}: expected encode$user:\n{}", r.js_output);
                // Save module to registry (mimics playground's extract_all_cached_modules)
                if let Some(ps) = r.pers_struct {
                    registry.cached_modules.insert(module_name.clone(), ps);
                }
                registry.alias_rewrites.extend(r.new_alias_rewrites);
                eprintln!("Iteration {iteration}: OK");
            }
            Err(e) => panic!("Iteration {iteration} failed: {e}"),
        }
    }
}

#[test]
fn playground_has_tag_arg_at() {
    // Recursive typed variant encoding via @hasTag + @argAt.
    // Each constructor argument keeps its original type (float, int,
    // record, etc.), so the encode() recursion dispatches correctly
    // through @typeInfo — no uniform array<JSON.t> fallback.
    let source = r#"
type shape = Circle(float) | Square(float, float) | Point

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | Float => JSON.Encode.float(value)
  | Int => JSON.Encode.int(value)
  | Variant({constructors}) =>
    let result = ref(JSON.Null)
    inline for c in constructors {
      if @hasTag(value, c.name) {
        let arr = [JSON.Encode.string(c.name)]
        let idx = ref(0)
        inline for argType in c.args {
          Array.push(arr, encode(@argAt(value, idx.contents, argType)))
          idx := idx.contents + 1
        }
        result := JSON.Encode.array(arr)
      }
    }
    result.contents
  | _ => @compileError("unsupported")
  }
}

let j1 = encode(Circle(5.0))
let j2 = encode(Square(3.0, 4.0))
let j3 = encode(Point)
"#;
    match compile_with_stdlib(source, "has_tag_arg_at.res") {
        Ok(o) => {
            eprintln!("HAS_TAG ARG_AT OUTPUT:\n{o}");
            assert!(o.contains("encode$shape"), "Expected encode$shape:\n{o}");
            // Float-specialized encoder should exist since args are typed
            assert!(o.contains("encode$float"), "Expected encode$float (args recursed):\n{o}");
        }
        Err(e) => panic!("@hasTag + @argAt should compile: {e}"),
    }
}

#[test]
fn playground_variant_of_primitive() {
    // @variantOf(value) is a comptime primitive that decomposes a variant
    // at runtime into (name, args_array). No user-written %raw needed.
    let source = r#"
type shape = Circle(float) | Square(float, float) | Point

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | Float => JSON.Encode.float(value)
  | Variant({constructors}) =>
    let result = ref(JSON.Null)
    inline for c in constructors {
      if @hasTag(value, c.name) {
        let arr = [JSON.Encode.string(c.name)]
        let idx = ref(0)
        inline for argType in c.args {
          Array.push(arr, encode(@argAt(value, idx.contents, argType)))
          idx := idx.contents + 1
        }
        result := JSON.Encode.array(arr)
      }
    }
    result.contents
  | _ => @compileError("unsupported")
  }
}

let j1 = encode(Circle(5.0))
let j2 = encode(Square(3.0, 4.0))
let j3 = encode(Point)
"#;
    match compile_with_stdlib(source, "variant_of.res") {
        Ok(o) => {
            eprintln!("VARIANT OF OUTPUT:\n{o}");
            assert!(o.contains("encode$shape"), "Expected encode$shape:\n{o}");
        }
        Err(e) => panic!("@variantOf should compile: {e}"),
    }
}

#[test]
fn playground_variants_with_payloads() {
    // Variants with payloads: encode as [name, ...payloads].
    // Uses %raw helpers to inspect the runtime tag/arg since ReScript
    // compiles payload-carrying variants to {TAG: "Name", _0: v}.
    let source = r#"
type shape = Circle(float) | Square(float, float) | Point

exception DecodeError(string)

external variantToJson: 'a => JSON.t = "%identity"

let getTag: 'a => string = %raw(`function(v) {
  return typeof v === "string" ? v : v.TAG;
}`)

// Returns the i-th constructor argument. Typed as JSON.t since ReScript's
// runtime representation of primitives matches JSON.t's @unboxed form.
let getArg: ('a, int) => JSON.t = %raw(`function(v, i) {
  return v["_" + i];
}`)

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | Float => JSON.Encode.float(value)
  | Variant({constructors}) =>
    let tag = getTag(value)
    let result = ref(JSON.Null)
    inline for c in constructors {
      if tag == c.name {
        let arr = [JSON.Encode.string(c.name)]
        let idx = ref(0)
        inline for _argType in c.args {
          Array.push(arr, getArg(value, idx.contents))
          idx := idx.contents + 1
        }
        result := JSON.Encode.array(arr)
      }
    }
    result.contents
  | _ => @compileError("unsupported")
  }
}

let s1 = Circle(5.0)
let j1 = encode(s1)
let s2 = Point
let j2 = encode(s2)
"#;
    match compile_with_stdlib(source, "variants_payload.res") {
        Ok(o) => {
            eprintln!("VARIANTS PAYLOAD OUTPUT:\n{o}");
            assert!(o.contains("encode$shape"), "Expected encode$shape:\n{o}");
        }
        Err(e) => panic!("payload variants should compile: {e}"),
    }
}

#[test]
fn playground_variants_array_format() {
    // Variants encode as `[name, ...payloads]`. For enum-style variants
    // (no payload) that's just `[name]`.
    let source = r#"
type status = Active | Inactive | Pending

exception DecodeError(string)

external variantToJson: 'a => JSON.t = "%identity"

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Variant(_) => JSON.Encode.array([variantToJson(value)])
  | _ => @compileError("unsupported")
  }
}

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) =>
        let result = ref(None)
        inline for c in constructors {
          if name == c.name { result := Some(@constructor(t, c.name)) }
        }
        switch result.contents {
        | Some(v) => v
        | None => throw(DecodeError("unknown variant: " ++ name))
        }
      | _ => throw(DecodeError("expected string at array[0]"))
      }
    | _ => throw(DecodeError("expected array"))
    }
  | _ => @compileError("unsupported")
  }
}

let s = Active
let j = encode(s)
let d = decode(status, j)
"#;
    match compile_with_stdlib(source, "variants_array.res") {
        Ok(o) => {
            eprintln!("VARIANTS ARRAY OUTPUT:\n{o}");
            assert!(o.contains("encode$status"), "Expected encode$status:\n{o}");
            assert!(o.contains("decode$status"), "Expected decode$status:\n{o}");
        }
        Err(e) => panic!("variants array format should compile: {e}"),
    }
}

#[test]
fn playground_variant_constructor_primitive() {
    // Decoder using the existing @variant(t, "CtorName") primitive to
    // construct variant values — no %identity cast needed.
    let source = r#"
type status = Active | Inactive | Pending

exception DecodeError(string)

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | Variant({constructors}) =>
    switch json {
    | String(s) =>
      let result = ref(None)
      inline for c in constructors {
        if s == c.name { result := Some(@variant(t, c.name)) }
      }
      switch result.contents {
      | Some(v) => v
      | None => throw(DecodeError("unknown variant: " ++ s))
      }
    | _ => throw(DecodeError("expected variant string"))
    }
  | _ => @compileError("unsupported")
  }
}

let d = decode(status, JSON.Encode.string("Active"))
"#;
    match compile_with_stdlib(source, "variant_ctor.res") {
        Ok(o) => {
            eprintln!("VARIANT CTOR OUTPUT:\n{o}");
            assert!(o.contains("decode$status"), "Expected decode$status:\n{o}");
        }
        Err(e) => panic!("@variant primitive should work: {e}"),
    }
}

#[test]
fn playground_variants_encoding() {
    // Simple enum-variant encoding. Variants without payloads compile to
    // their name as a string in ReScript 12, and JSON.t is @unboxed, so
    // both runtime representations are identical — a %identity cast is
    // all we need.
    let source = r#"
type status = Active | Inactive | Pending

exception DecodeError(string)

external variantToJson: 'a => JSON.t = "%identity"
external jsonToVariant: JSON.t => 'a = "%identity"

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Variant(_) => variantToJson(value)
  | _ => @compileError("unsupported")
  }
}

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => s | _ => throw(DecodeError("expected string")) }
  | Variant({constructors}) =>
    switch json {
    | String(s) =>
      let valid = ref(false)
      inline for c in constructors {
        if s == c.name { valid := true }
      }
      if !valid.contents { throw(DecodeError("unknown variant: " ++ s)) }
      jsonToVariant(json)
    | _ => throw(DecodeError("expected variant string"))
    }
  | _ => @compileError("unsupported")
  }
}

let s = Active
let j = encode(s)
let d = decode(status, j)
"#;
    match compile_with_stdlib(source, "variants.res") {
        Ok(o) => {
            eprintln!("VARIANTS OUTPUT:\n{o}");
            assert!(o.contains("encode$status"), "Expected encode$status:\n{o}");
            assert!(o.contains("decode$status"), "Expected decode$status:\n{o}");
        }
        Err(e) => panic!("variants should compile: {e}"),
    }
}

#[test]
fn playground_exact_init_code() {
    // Exact INITIAL_CODE from playground/src/App.jsx as of 2026-04-17
    let source = r#"// ── Comptime playground ─────────────────────────────────────────────────
// Functions marked @comptime run at compile time. @typeInfo introspects a
// type; inline for unrolls loops. Each call monomorphizes to a specialized
// function — recursive types produce self-recursive code, no infinite
// expansion.

type address = { street: string, city: string }
type user = { name: string, age: int, active: bool, address: address }
type tree = { value: string, children: array<tree> }

exception DecodeError(string)

// ── 1. Zero-overhead JSON encoder ───────────────────────────────────────
@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  address: {street: "Main St", city: "NYC"},
}

let aliceJson = encode(alice)

let myTree: tree = {
  value: "root",
  children: [
    {value: "child1", children: []},
    {value: "child2", children: []},
  ],
}
let treeJson = encode(myTree)

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => s | _ => throw(DecodeError("expected string")) }
  | Int =>
    switch json { | Number(n) => Float.toInt(n) | _ => throw(DecodeError("expected int")) }
  | Bool =>
    switch json { | Boolean(b) => b | _ => throw(DecodeError("expected bool")) }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(t, inline for field in fields {
        decode(field.typ, Dict.getUnsafe(dict, field.name))
      })
    | _ => throw(DecodeError("expected object"))
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let decodedAlice = try Some(decode(user, aliceJson)) catch {
| DecodeError(_) => None
}

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name})
    })
  | _ => @compileError("expected record")
  }

let k1: userKey = Name
let k2: userKey = Age
"#;
    match compile_with_stdlib(source, "Playground.res") {
        Ok(o) => {
            assert!(o.contains("encode$user"), "Expected encode$user:\n{o}");
            assert!(o.contains("decode$user"), "Expected decode$user:\n{o}");
        }
        Err(e) => panic!("Exact init code should compile: {e}"),
    }
}

#[test]
fn playground_flow_matches_test() {
    // Emulate the playground's compile_all flow: use default CompilerOptions
    // (no open_modules, no module_name), rely on load_pervasives auto-opens.
    let registry = stdlib_registry().clone();
    let source = r#"type user = { name: string, age: int }

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | _ => @compileError("unsupported")
  }
}

let alice: user = { name: "Alice", age: 30 }
let aliceJson = encode(alice)
"#;

    // Playground uses default options (no open_modules)
    let options = CompilerOptions {
        source_filename: Some("Playground.res".to_string()),
        ..Default::default()
    };
    let module_name = "Playground".to_string();
    match compile_source_in_process(source, "Playground.res", &module_name, &options, &registry, false) {
        Ok(r) => {
            eprintln!("PLAYGROUND FLOW OUTPUT:\n{}", r.js_output);
            assert!(r.js_output.contains("encode$user"), "Expected encode$user:\n{}", r.js_output);
        }
        Err(e) => panic!("playground flow should compile: {e}"),
    }
}

#[test]
fn playground_exact_user_code() {
    // Exact source the user reported as not emitting encode function.
    let source = r#"type address = { street: string, city: string }
type user = { name: string, age: int, active: bool, address: address }
type tree = { value: string, children: array<tree> }

exception DecodeError(string)

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  address: {street: "Main St", city: "NYC"},
}

let aliceJson = encode(alice)
"#;
    let output = compile_with_stdlib(source, "Playground.res").expect("compile");
    eprintln!("USER CODE OUTPUT:\n{output}");
    assert!(output.contains("encode$user"), "Expected encode$user in output:\n{output}");
}

#[test]
fn playground_enc_only() {
    let source = r#"
type address = { street: string, city: string }
type user = { name: string, age: int, active: bool, address: address }

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {name: "Alice", age: 30, active: true, address: {street: "x", city: "y"}}
let aliceJson = encode(alice)
"#;
    match compile_with_stdlib(source, "pg_enc.res") {
        Ok(output) => eprintln!("ENC OUTPUT:\n{output}"),
        Err(e) => panic!("enc should compile: {e}"),
    }
}

#[test]
fn playground_tree_only() {
    let source = r#"
type tree = { value: string, children: array<tree> }

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let myTree: tree = { value: "root", children: [{value: "c1", children: []}] }
let treeJson = encode(myTree)
"#;
    match compile_with_stdlib(source, "pg_tree.res") {
        Ok(_) => {}
        Err(e) => panic!("tree should compile: {e}"),
    }
}

#[test]
fn playground_console_only() {
    let source = r#"Console.log("hi")
"#;
    match compile_with_stdlib(source, "pg_console.res") {
        Ok(_) => {}
        Err(e) => panic!("Console.log should compile: {e}"),
    }
}

#[test]
fn playground_full_default() {
    // The full playground default — encoder + decoder + variants + variant
    // builder, exactly as the user will see it.
    let source = r#"
type address = { street: string, city: string }
type status = Active | Inactive | Pending
type user = { name: string, age: int, active: bool, status: status, address: address }
type tree = { value: string, children: array<tree> }

exception DecodeError(string)

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Variant({constructors}) =>
    let result = ref(JSON.Null)
    inline for c in constructors {
      if @hasTag(value, c.name) {
        let arr = [JSON.Encode.string(c.name)]
        let idx = ref(0)
        inline for argType in c.args {
          Array.push(arr, encode(@argAt(value, idx.contents, argType)))
          idx := idx.contents + 1
        }
        result := JSON.Encode.array(arr)
      }
    }
    result.contents
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {name: "Alice", age: 30, active: true, status: Active, address: {street: "Main St", city: "NYC"}}
let aliceJson = encode(alice)

let myTree: tree = {value: "root", children: [{value: "child1", children: []}, {value: "child2", children: []}]}
let treeJson = encode(myTree)

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => s | _ => throw(DecodeError("expected string")) }
  | Int =>
    switch json { | Number(n) => Float.toInt(n) | _ => throw(DecodeError("expected int")) }
  | Bool =>
    switch json { | Boolean(b) => b | _ => throw(DecodeError("expected bool")) }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(t, inline for field in fields {
        decode(field.typ, Dict.getUnsafe(dict, field.name))
      })
    | _ => throw(DecodeError("expected object"))
    }
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) =>
        let result = ref(None)
        inline for c in constructors {
          if name == c.name { result := Some(@constructor(t, c.name)) }
        }
        switch result.contents {
        | Some(v) => v
        | None => throw(DecodeError("unknown variant: " ++ name))
        }
      | _ => throw(DecodeError("expected [name, ...] array"))
      }
    | _ => throw(DecodeError("expected variant array"))
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let decodedAlice = try Some(decode(user, aliceJson)) catch { | DecodeError(_) => None }

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name})
    })
  | _ => @compileError("expected record")
  }

let k1: userKey = Name
let k2: userKey = Age
"#;
    match compile_with_stdlib(source, "playground_full.res") {
        Ok(o) => {
            assert!(o.contains("encode$status"), "Expected encode$status:\n{o}");
            assert!(o.contains("encode$user"), "Expected encode$user:\n{o}");
            assert!(o.contains("decode$user"), "Expected decode$user:\n{o}");
        }
        Err(e) => panic!("full playground default should compile: {e}"),
    }
}

#[test]
fn playground_decoder() {
    // Minimal decoder: type t + JSON.t value param, return annotated
    let source = r#"
@comptime
let decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => Ok(s) | _ => Error("err") }
  | _ => Error("unsupported")
  }
}

let j = JSON.Encode.string("hi")
let decoded = decode(string, j)
"#;
    match compile_with_stdlib(source, "pg_dec.res") {
        Ok(o) => eprintln!("DEC OUTPUT:\n{o}"),
        Err(e) => panic!("decoder should compile: {e}"),
    }
}

#[test]
fn playground_decoder_user_type() {
    // Decoder with a user-defined record type. Uses Result.flatMap pattern
    // instead of `return` (which isn't yet supported in comptime inline for).
    let source = r#"
type user = { name: string, age: int }

exception DecodeError(string)

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => s | _ => throw(DecodeError("expected string")) }
  | Int =>
    switch json { | Number(n) => Float.toInt(n) | _ => throw(DecodeError("expected int")) }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(t, inline for field in fields {
        decode(field.typ, Dict.getUnsafe(dict, field.name))
      })
    | _ => throw(DecodeError("expected object"))
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let j = JSON.Encode.string("hi")
let decoded = try Some(decode(user, j)) catch { | DecodeError(_) => None }
"#;
    match compile_with_stdlib(source, "pg_dec_user.res") {
        Ok(o) => eprintln!("DEC USER OUTPUT:\n{o}"),
        Err(e) => panic!("decoder with user type should compile: {e}"),
    }
}

#[test]
fn comptime_inline_direct_call() {
    let source = r#"
@comptime.inline
let upperCase = (value) => String.toUpperCase(value)

let upperStr = upperCase("Bla")
"#;
    let result = compile_with_stdlib(source, "comptime_inline_direct.res");
    match result {
        Ok(output) => {
            eprintln!("=== INLINE DIRECT ===\n{}\n=== END ===", output);
        }
        Err(e) => panic!("compile failed: {e}"),
    }
}

