//! Classes declared on private records (`@instanceOf` with `@extends`) and
//! classes imported from modules (`@module` beside `@instanceOf`).

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::bir::shadow::BackendMode;
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

fn compile(source: &str) -> Result<String, String> {
    // `RESCRIPT_BACKEND=check` runs every test with the comparison.
    compile_in(source, BackendMode::from_env())
}

/// With `BackendMode::Check`, the shadow backend compares its own lowering
/// with the one that is printed. The comparison fails the compilation when
/// the two differ; a form the shadow backend does not lower yet is declined.
fn compile_in(source: &str, backend: BackendMode) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        backend,
        ..Default::default()
    };
    driver::compile_source_in_process(source, "/app/src/Demo.res", "Demo", &options, &registry(), false, None)
        .map(|compiled| compiled.js_output)
        .map_err(|error| format!("{error:#}"))
}

fn error(source: &str) -> String {
    compile(source).expect_err("the program is rejected")
}

const BLOB_AND_FILE: &str = r#"
@instanceOf("Blob")
type blob = private {
  size: float,
  @as("type") type_: string,
}

@instanceOf("File") @extends(: blob)
type file = private {
  ...blob,
  name: string,
  lastModified: float,
}
"#;

#[test]
fn a_record_class_is_a_case_and_keeps_its_fields() {
    let js = compile(&format!(
        r#"{BLOB_AND_FILE}
let describe = (f: file) => `${{f.name}}: ${{Float.toString(f.size)}} bytes`

@unboxed
type blobPart =
  | Text(string)
  | Blob(blob)
  | File(file)
  | Buffer(ArrayBuffer.t)

let kind = part =>
  switch part {{
  | Text(_) => "text"
  | Blob(b) => "blob " ++ b.type_
  | File(f) => "file " ++ f.name
  | Buffer(_) => "buffer"
  }}
"#
    ))
    .unwrap();
    assert!(js.contains("f.size.toString()"), "{js}");
    // The subclass is tested before its superclass.
    let file = js.find("part instanceof File").expect(&js);
    let blob = js.find("part instanceof Blob").expect(&js);
    assert!(file < blob, "{js}");
    assert!(js.contains("typeof part === \"string\""), "{js}");
}

#[test]
fn a_subclass_record_upcasts_to_its_superclass() {
    let js = compile(&format!("{BLOB_AND_FILE}\nlet asBlob = (f: file) => (f :> blob)\n")).unwrap();
    assert!(js.contains("function asBlob(f) {\n  return f;\n}"), "{js}");
}

#[test]
fn a_recursive_group_of_classes() {
    let js = compile(
        r#"
type nodeFields<'node, 'element> = {parentNode: null<'node>, parentElement: null<'element>}

@instanceOf("Node")
type rec baseNode = private {...nodeFields<node, element>}
@instanceOf("Element") @extends(: baseNode)
and element = private {...nodeFields<node, element>, tagName: string}
@unboxed
and node = Element(element) | Other(baseNode)

let tag = (n: node) =>
  switch n {
  | Element(e) => e.tagName
  | Other(_) => "?"
  }
let up = (e: element) => (e :> baseNode)
"#,
    )
    .unwrap();
    assert!(js.contains("n instanceof Element"), "{js}");
    assert!(!js.contains("instanceof Node"), "{js}");
}

#[test]
fn a_class_is_imported_from_its_module() {
    let js = compile(
        r#"
@module("three") @instanceOf("Object3D")
type object3D = private {id: float}

@module("three") @instanceOf("Mesh") @extends(: object3D)
type mesh = private {id: float, geometry: string}

@module("node:stream") @instanceOf("Readable") type readable
@module("node:stream") @instanceOf("Writable") type writable

@unboxed type shape = Mesh(mesh) | Other(object3D)
@unboxed type stream = Readable(readable) | Writable(writable) | Path(string)

let isMesh = (s: shape) =>
  switch s {
  | Mesh(_) => true
  | Other(_) => false
  }
let what = (s: stream) =>
  switch s {
  | Readable(_) => "r"
  | Writable(_) => "w"
  | Path(p) => p
  }
"#,
    )
    .unwrap();
    assert!(js.contains("require(\"three\")"), "{js}");
    assert!(js.contains("s instanceof Three.Mesh"), "{js}");
    assert!(js.contains("require(\"node:stream\")"), "{js}");
    assert!(js.contains("s instanceof Nodestream.Readable"), "{js}");
}

#[test]
fn classes_named_alike_in_two_modules_are_two_classes() {
    let js = compile(
        r#"
@module("a") @instanceOf("Client") type a
@module("b") @instanceOf("Client") type b
@unboxed type client = A(a) | B(b)
let which = (c: client) =>
  switch c {
  | A(_) => "a"
  | B(_) => "b"
  }
"#,
    )
    .unwrap();
    assert!(js.contains("instanceof A.Client"), "{js}");
}

#[test]
fn a_record_class_must_be_private() {
    let message = error(r#"@instanceOf("Blob") type blob = {size: float}"#);
    assert!(message.contains("@instanceOf can only be used on abstract types and type abbreviations"), "{message}");
    let message = error(
        r#"@instanceOf("Blob") type blob = private {size: float}
let b: blob = {size: 1.}"#,
    );
    assert!(message.contains("Cannot create values of the private type blob"), "{message}");
}

#[test]
fn extends_needs_a_class_on_both_sides() {
    let message = error(
        r#"@instanceOf("Blob") type blob = private {size: float}
@extends(: blob) type file = private {size: float, name: string}"#,
    );
    assert!(message.contains("only be used on a private record with @instanceOf"), "{message}");
    let message = error(
        r#"type plain = {size: float}
@instanceOf("File") @extends(: plain) type file = private {size: float, name: string}"#,
    );
    assert!(message.contains("expects a type declared as a class"), "{message}");
    let message = error(
        r#"@instanceOf("Blob") type blob
@instanceOf("File") @extends(: blob) type file"#,
    );
    assert!(message.contains("only be used on a private record with @instanceOf"), "{message}");
}

#[test]
fn a_subclass_record_has_its_superclass_fields() {
    for file in ["{size: float, name: string}", "{size: string, kind: string}"] {
        let message = error(&format!(
            r#"@instanceOf("Blob") type blob = private {{size: float, kind: string}}
@instanceOf("File") @extends(: blob) type file = private {file}"#
        ));
        assert!(message.contains("it must have every field of that record"), "{message}");
    }
}

#[test]
fn only_a_declared_subclass_coerces_to_a_class_record() {
    for (other, reason) in [
        ("type other = {size: float}", "another type cannot be coerced to it"),
        (
            "@instanceOf(\"Other\") type other = private {size: float}",
            "is the class Other and declares no superclass",
        ),
    ] {
        let message = error(&format!(
            r#"@instanceOf("Blob") type blob = private {{size: float}}
{other}
let fake = (p: other) => (p :> blob)"#
        ));
        assert!(message.contains(reason), "{message}");
    }
}

#[test]
fn a_method_returning_its_own_class_is_inherited() {
    // `rename(): this` in TypeScript: the subclass's method returns the
    // subclass, which is a subtype because the declaration says so.
    let js = compile(
        r#"
@instanceOf("Animal")
type rec animal = private {name: string, rename: string => animal}

@instanceOf("Dog") @extends(: animal)
type rec dog = private {name: string, rename: string => dog, fetch: unit => unit}

let asAnimal = (d: dog) => (d :> animal)
@unboxed type pet = Dog(dog) | Animal(animal)
let name = (p: pet) =>
  switch p {
  | Dog(d) => "dog " ++ d.name
  | Animal(a) => a.name
  }
"#,
    )
    .unwrap();
    assert!(js.contains("p instanceof Dog"), "{js}");
}

#[test]
fn the_shadow_backend_declines_a_class_imported_from_a_module() {
    let source = r#"
@module("node:stream") @instanceOf("Readable") type readable
@module("node:stream") @instanceOf("Writable") type writable
@unboxed type stream = Readable(readable) | Writable(writable) | Path(string)
let what = (s: stream) =>
  switch s {
  | Readable(_) => "r"
  | Writable(_) => "w"
  | Path(p) => p
  }
"#;
    let compared = compile_in(source, BackendMode::Check).unwrap();
    assert!(compared.contains("s instanceof Nodestream.Readable"), "{compared}");
    assert_eq!(compared, compile(source).unwrap());
}
