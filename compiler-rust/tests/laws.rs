//! `@law` (docs/verify/law.md): what a build and `rescript verify` compile a
//! law to, the shapes its parameters get, and the reports for laws that
//! cannot be run.

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::verify::Checks;
use rescript_compiler::verify::laws::Item;

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

/// Removes the colour codes of a report: the colour mode is one setting
/// for the process, and tests run in parallel.
fn plain(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            for c in chars.by_ref() {
                if c == 'm' {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// The JavaScript of a program and, when its checks are kept, their
/// descriptions.
fn compile(source: &str, checks: Checks, check_only: bool) -> Result<(String, Vec<Item>), String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        check_only,
        checks: checks.clone(),
        ..Default::default()
    };
    let compiled = driver::compile_source_in_process(
        source,
        "/app/src/Demo.res",
        "Demo",
        &options,
        &registry(),
        false,
        None,
    )
    .map_err(|error| plain(&format!("{error:#}")))?;
    let items = match checks {
        Checks::Kept(items) => items.lock().unwrap().clone(),
        Checks::LeftOut => Vec::new(),
    };
    Ok((compiled.js_output, items))
}

/// The descriptions of a program's checks.
#[track_caller]
fn items(source: &str) -> Vec<Item> {
    match compile(source, Checks::kept(), true) {
        Ok((_, items)) => items,
        Err(report) => panic!("expected the program to compile:\n{source}\n{report}"),
    }
}

#[track_caller]
fn rejected(source: &str, fragments: &[&str]) {
    match compile(source, Checks::LeftOut, true) {
        Ok(_) => panic!("expected the program to be rejected:\n{source}"),
        Err(report) => {
            for fragment in fragments {
                assert!(
                    report.contains(fragment),
                    "the report lacks {fragment:?}:\n{source}\n{report}"
                );
            }
        }
    }
}

const PROGRAM: &str = r#"
let double = x => x * 2

@law
let doubleIsEven = (n: int) => mod(double(n), 2) == 0

module Inner = {
  @law
  let nested = (a: bool, b: bool) => (a && b) == (b && a)
}
"#;

#[test]
fn a_build_leaves_laws_out() {
    let (js, items) = compile(PROGRAM, Checks::LeftOut, false).unwrap();
    assert!(js.contains("function double(x)"), "{js}");
    assert!(!js.contains("doubleIsEven"), "{js}");
    assert!(!js.contains("nested"), "{js}");
    assert!(js.contains("let Inner = {};"), "{js}");
    assert!(items.is_empty());
}

#[test]
fn verify_exports_laws() {
    let (js, items) = compile(PROGRAM, Checks::kept(), false).unwrap();
    assert!(js.contains("function doubleIsEven(n)"), "{js}");
    assert!(js.contains("exports.doubleIsEven = doubleIsEven;"), "{js}");
    assert!(js.contains("nested: nested"), "{js}");
    let paths: Vec<String> = items.iter().map(|item| item.path.join(".")).collect();
    assert_eq!(paths, ["doubleIsEven", "Inner.nested"]);
    assert_eq!(items[0].kind, "law");
    assert_eq!(items[0].line, 4);
    assert_eq!(items[0].detail["defs"], serde_json::json!({}));
    assert_eq!(
        items[0].detail["params"],
        serde_json::json!([{ "name": "n", "shape": { "k": "int" } }])
    );
}

/// The shape of the first parameter of a program's only law, and the
/// definitions it names.
#[track_caller]
fn shape(types: &str, parameter: &str) -> (serde_json::Value, serde_json::Value) {
    let source = format!("{types}\n@law\nlet law = (x: {parameter}) => x == x\n");
    let items = items(&source);
    assert_eq!(items.len(), 1);
    let detail = &items[0].detail;
    (detail["params"][0]["shape"].clone(), detail["defs"].clone())
}

#[test]
fn shapes_of_built_in_types() {
    use serde_json::json;
    for (ty, kind) in [
        ("int", "int"),
        ("float", "float"),
        ("string", "string"),
        ("bool", "bool"),
        ("unit", "unit"),
        ("bigint", "bigint"),
    ] {
        assert_eq!(shape("", ty).0, json!({ "k": kind }), "{ty}");
    }
    assert_eq!(
        shape("", "option<array<int>>").0,
        json!({ "k": "option", "of": { "k": "array", "of": { "k": "int" } } })
    );
    assert_eq!(
        shape("", "list<(bool, string)>").0,
        json!({ "k": "list", "of": { "k": "tuple", "of": [{ "k": "bool" }, { "k": "string" }] } })
    );
    assert_eq!(
        shape("", "dict<float>").0,
        json!({ "k": "dict", "of": { "k": "float" } })
    );
    assert_eq!(
        shape("", "[#a | #b(int)]").0,
        json!({ "k": "poly", "cases": [{ "n": "a" }, { "n": "b", "arg": { "k": "int" } }] })
    );
    // A law about every type is tested at `int`.
    assert_eq!(
        shape("", "array<'a>").0,
        json!({ "k": "array", "of": { "k": "int" } })
    );
}

#[test]
fn a_record_keeps_its_runtime_names() {
    use serde_json::json;
    let (shape, defs) = shape(
        r#"type point = {x: int, @as("why") y: float, label?: string}"#,
        "point",
    );
    assert_eq!(shape, json!({ "k": "named", "id": "point" }));
    assert_eq!(
        defs["point"],
        json!({
            "k": "record",
            "name": "point",
            "repr": "object",
            "fields": [
                { "n": "x", "js": "x", "opt": false, "s": { "k": "int" } },
                { "n": "y", "js": "why", "opt": false, "s": { "k": "float" } },
                { "n": "label", "js": "label", "opt": true, "s": { "k": "option", "of": { "k": "string" } } },
            ],
        })
    );
    let (_, defs) = self::shape("@unboxed type wrapped = {value: int}", "wrapped");
    assert_eq!(defs["wrapped"]["repr"], json!("unboxed"));
}

#[test]
fn a_variant_has_the_layout_the_backend_compiles() {
    use serde_json::json;
    let (_, defs) = shape(
        r#"type shape = Circle(float) | Rect({w: float, h: float}) | @as("dot") Point"#,
        "shape",
    );
    assert_eq!(
        defs["shape"]["cases"],
        json!([
            { "n": "Circle", "lit": "Circle", "tagName": "TAG", "args": [{ "k": "float" }] },
            {
                "n": "Rect",
                "lit": "Rect",
                "tagName": "TAG",
                "fields": [
                    { "n": "w", "js": "w", "opt": false, "s": { "k": "float" } },
                    { "n": "h", "js": "h", "opt": false, "s": { "k": "float" } },
                ],
            },
            { "n": "Point", "lit": "dot" },
        ])
    );
    let (_, defs) = self::shape(
        r#"@tag("kind") type event = Key(string) | @as(1) Idle"#,
        "event",
    );
    assert_eq!(
        defs["event"]["cases"],
        json!([
            { "n": "Key", "lit": "Key", "tagName": "kind", "args": [{ "k": "string" }] },
            { "n": "Idle", "lit": 1 },
        ])
    );
    let (_, defs) = self::shape(
        "@unboxed type id = Num(float) | Str(string) | @as(null) Missing | @as(undefined) Absent",
        "id",
    );
    assert_eq!(
        defs["id"]["cases"],
        json!([
            { "n": "Num", "untagged": true, "args": [{ "k": "float" }] },
            { "n": "Str", "untagged": true, "args": [{ "k": "string" }] },
            { "n": "Missing", "lit": null },
            { "n": "Absent", "lit": { "undefined": true } },
        ])
    );
}

#[test]
fn a_type_with_arguments_is_defined_once_per_use() {
    use serde_json::json;
    let (shape, defs) = shape(
        "type rec tree<'a> = Leaf | Node(tree<'a>, 'a, tree<'a>)\ntype pair<'a> = ('a, 'a)",
        "pair<tree<bool>>",
    );
    let tree = json!({ "k": "named", "id": "tree<bool>" });
    assert_eq!(shape, json!({ "k": "tuple", "of": [tree, tree] }));
    assert_eq!(
        defs["tree<bool>"]["cases"][1]["args"],
        json!([tree, { "k": "bool" }, tree])
    );
}

#[test]
fn a_law_returns_bool() {
    rejected(
        "@law\nlet sum = (a: int, b: int) => a + b\n",
        &["A law returns `bool`", "`sum` returns something else"],
    );
    rejected(
        "@law\nlet answer = 42\n",
        &["A law is a function that returns `bool`"],
    );
    rejected(
        "@law\nlet curried = (a: int) => (b: int) => a + b == b + a\n",
        &["A law returns `bool`"],
    );
}

#[test]
fn a_parameter_needs_a_type_with_known_values() {
    rejected(
        "module Id: {\n  type t\n  let make: int => t\n} = {\n  type t = int\n  let make = n => n\n}\n@law\nlet same = (id: Id.t) => id == id\n",
        &[
            "No value can be made for `id`: `Id.t` is an abstract type: only its module can make its values.",
            "Take what this value is built from as the parameter",
        ],
    );
    rejected(
        "@law\nlet apply = (f: int => int, x: int) => f(x) == f(x)\n",
        &["No value can be made for `f`: it has a function in it"],
    );
    rejected(
        "type t = private {n: int}\n@law\nlet same = (t: t) => t == t\n",
        &["`t` is a private type"],
    );
    rejected(
        "@law\nlet same = (p: promise<int>) => p == p\n",
        &["it has a promise in it"],
    );
}

#[test]
fn a_law_is_pure() {
    rejected(
        "@law\nlet logs = (n: int) => {\n  Console.log(n)\n  n == n\n}\n",
        &["The external `Console.log` is not marked @pure, and `logs` is @pure."],
    );
    rejected(
        "@law\nlet now = (n: float) => Date.now() >= n\n",
        &["The external `Date.now` is not marked @pure"],
    );
}

#[test]
fn nothing_refers_to_a_law() {
    rejected(
        "@law\nlet holds = (n: int) => n == n\nlet use = holds(1)\n",
        &["The value holds can't be found"],
    );
}

#[test]
fn a_law_is_at_the_top_level() {
    rejected(
        "let f = () => {\n  @law\n  let inner = (n: int) => n == n\n  inner\n}\n",
        &["A law or spec must be a `let` at the top level of a file"],
    );
    rejected(
        "module M: {\n  let x: int\n} = {\n  let x = 1\n  @law\n  let hidden = (n: int) => n + x == x + n\n}\n",
        &["A law or spec must be a `let` at the top level of a file"],
    );
    rejected(
        "@law\nlet a = (n: int) => n == n\nand b = (n: int) => n == n\n",
        &["it cannot be one of several bindings joined by `and`"],
    );
}
