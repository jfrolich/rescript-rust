//! Tagged variants whose cases share a tag, told apart inside its arm by
//! their other fields (`docs/ts-import/README.md`, "Shared tags on tagged
//! variants").

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

fn compile_with(source: &str, registry: &ModuleRegistry) -> Result<String, String> {
    // `RESCRIPT_BACKEND=check` runs every test with the comparison.
    compile_in(source, registry, BackendMode::from_env())
}

fn compile_in(source: &str, registry: &ModuleRegistry, backend: BackendMode) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        backend,
        ..Default::default()
    };
    driver::compile_source_in_process(source, "/app/src/Demo.res", "Demo", &options, registry, false, None)
        .map(|compiled| compiled.js_output)
        .map_err(|error| format!("{error:#}"))
}

fn compile(source: &str) -> Result<String, String> {
    compile_with(source, &registry())
}

fn js(source: &str) -> String {
    compile(source).unwrap_or_else(|error| panic!("the program compiles:\n{error}"))
}

/// `source` compiled while the shadow backend compares its own lowering with
/// the one that is printed. The comparison fails the compilation when the
/// two differ; a form the shadow backend does not lower yet is declined.
fn js_compared(source: &str) -> String {
    compile_in(source, &registry(), BackendMode::Check)
        .unwrap_or_else(|error| panic!("the program compiles:\n{error}"))
}

fn error(source: &str) -> String {
    compile(source).expect_err("the program is rejected")
}

/// The body of function `name` in the generated JavaScript, with its lines
/// joined and their indentation removed.
fn function(js: &str, name: &str) -> String {
    let start = js
        .find(&format!("function {name}("))
        .unwrap_or_else(|| panic!("function {name} in\n{js}"));
    let end = js[start..].find("\n}\n").expect("end of function") + start;
    js[start..end]
        .lines()
        .skip(1)
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Runs `js` and then `check` under Node and returns what it prints; `None`
/// without Node.
fn run_node(js: &str, check: &str) -> Option<String> {
    let dir = std::env::temp_dir().join(format!("shared-tags-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let file = dir.join(format!("run-{}-{}.js", js.len(), check.len()));
    std::fs::write(&file, format!("{js}\n{check}\n")).ok()?;
    let output = std::process::Command::new("node").arg(&file).output().ok()?;
    let _ = std::fs::remove_file(&file);
    assert!(output.status.success(), "{}\n{js}", String::from_utf8_lossy(&output.stderr));
    Some(String::from_utf8_lossy(&output.stdout).into_owned())
}

const NODE: &str = r#"
@tag("type")
type node =
  | @as("Literal") StringLiteral({value: string})
  | @as("Literal") NumericLiteral({value: float})
  | @as("ThisExpression") This({start: int})
  | @as("Super") Super({start: int})
"#;

const SAMPLES: &str = r#"
const samples = [
  {type: "Literal", value: "s"},
  {type: "Literal", value: 1},
  {type: "ThisExpression", start: 0},
  {type: "Super", start: 3},
];
"#;

#[test]
fn the_cases_of_a_shared_tag_are_told_apart_in_its_arm() {
    let js = js(&format!(
        r#"{NODE}
let name = node =>
  switch node {{
  | StringLiteral({{value}}) => value
  | NumericLiteral({{value}}) => Float.toString(value)
  | This(_) => "this"
  | Super(_) => "super"
  }}

let made = Super({{start: 3}})
"#
    ));
    assert_eq!(
        function(&js, "name"),
        concat!(
            r#"switch (node.type) { case "Literal" : if (typeof node.value === "string") { return node.value; } "#,
            r#"else { return node.value.toString(); } case "ThisExpression" : return "this"; case "Super" : return "super"; }"#
        )
    );
    let check = format!("{SAMPLES}console.log(samples.map(exports.name).join(' '), JSON.stringify(exports.made));");
    if let Some(output) = run_node(&js, &check) {
        assert_eq!(output, "s 1 this super {\"type\":\"Super\",\"start\":3}\n");
    }
}

#[test]
fn a_switch_naming_some_cases_of_a_tag_tests_those() {
    let js = js(&format!(
        r#"{NODE}
let isNumber = node => switch node {{ | NumericLiteral(_) => true | _ => false }}
let isString = node => switch node {{ | StringLiteral(_) => true | _ => false }}
let literal = node => switch node {{ | StringLiteral(_) | NumericLiteral(_) => true | _ => false }}
let start = node => switch node {{ | This({{start}}) | Super({{start}}) => start | _ => 0 }}
"#
    ));
    // Both cases of one tag with one body need no test on their fields.
    assert!(!function(&js, "literal").contains("typeof"), "{js}");
    assert!(!function(&js, "start").contains("typeof"), "{js}");
    let check = format!(
        "{SAMPLES}for (const f of ['isNumber', 'isString', 'literal', 'start']) console.log(samples.map(exports[f]).join(' '));"
    );
    if let Some(output) = run_node(&js, &check) {
        assert_eq!(
            output,
            "false true false false\ntrue false false false\ntrue true false false\n0 0 0 3\n"
        );
    }
}

#[test]
fn nested_and_optional_values_and_constants() {
    let js = js(&format!(
        r#"{NODE}
let first = (node: option<node>) =>
  switch node {{
  | Some(StringLiteral({{value: "a"}})) => "the string a"
  | Some(StringLiteral(_)) => "a string"
  | Some(NumericLiteral({{value}})) if value > 1. => "a big number"
  | Some(NumericLiteral(_)) => "a number"
  | Some(This(_) | Super(_)) => "other"
  | None => "nothing"
  }}
// A constant is folded to the arm of its own case.
let folded = switch NumericLiteral({{value: 2.}}) {{
  | StringLiteral(_) => "string"
  | NumericLiteral(_) => "number"
  | _ => "other"
  }}
"#
    ));
    let check = r#"
const values = [{type: "Literal", value: "a"}, {type: "Literal", value: "b"}, {type: "Literal", value: 2},
  {type: "Literal", value: 1}, {type: "Super", start: 0}, undefined];
console.log(values.map(exports.first).join(', '), '|', exports.folded);
"#;
    if let Some(output) = run_node(&js, check) {
        assert_eq!(
            output,
            "the string a, a string, a big number, a number, other, nothing | number\n"
        );
    }
}

#[test]
fn literal_cases_beside_shared_tags() {
    let js = js(r#"
@tag("kind")
type shape =
  | @as("round") Circle({radius: float})
  | @as("round") Ellipse({rx: float, ry: float})
  | Square({side: float})
  | @as(null) Nothing
  | Unknown
let area = shape =>
  switch shape {
  | Circle({radius}) => radius *. radius *. 3.
  | Ellipse({rx, ry}) => rx *. ry *. 3.
  | Square({side}) => side *. side
  | Nothing => 0.
  | Unknown => -1.
  }
"#);
    let check = r#"
const shapes = [{kind: "round", radius: 1}, {kind: "round", rx: 1, ry: 2}, {kind: "Square", side: 2}, null, "Unknown"];
console.log(shapes.map(exports.area).join(' '));
"#;
    if let Some(output) = run_node(&js, check) {
        assert_eq!(output, "3 6 4 0 -1\n", "{js}");
    }
}

#[test]
fn cases_that_cannot_share_a_tag_are_duplicates() {
    let duplicate = "Duplicate literal Literal.";
    for declaration in [
        // The same fields at the same kinds: no test tells them apart.
        r#"| @as("Literal") A({value: string}) | @as("Literal") B({value: string})"#,
        // A tuple payload keeps its values under `_0`.
        r#"| @as("Literal") A(string) | @as("Literal") B({value: string})"#,
        r#"| @as("Literal") A({value: string}) | @as("Literal") B(float)"#,
    ] {
        let message = error(&format!("@tag(\"type\")\ntype t =\n  {declaration}\n"));
        assert!(message.contains(duplicate), "{declaration}\n{message}");
    }
}

#[test]
fn exhaustiveness_and_redundancy_are_unchanged() {
    let missing = error(&format!(
        "@@warning(\"@8\")\n{NODE}\nlet f = node => switch node {{ | StringLiteral(_) => 1 | This(_) | Super(_) => 2 }}\n"
    ));
    assert!(missing.contains("NumericLiteral"), "{missing}");
    let redundant = error(&format!(
        "@@warning(\"@11\")\n{NODE}\nlet f = node => switch node {{ | StringLiteral(_) => 1 | StringLiteral(_) => 2 | _ => 3 }}\n"
    ));
    assert!(redundant.contains("unused"), "{redundant}");
}

#[test]
fn through_an_interface_a_functor_and_an_include() {
    let js = js(&format!(
        r#"
module type S = {{
  {NODE}
}}
module Impl: S = {{
  {NODE}
}}
module Make = (M: S) => {{
  let kind = (node: M.node) =>
    switch node {{
    | M.StringLiteral(_) => "string"
    | M.NumericLiteral(_) => "number"
    | M.This(_) | M.Super(_) => "other"
    }}
}}
module Applied = Make(Impl)
module Included = {{
  include Impl
  let kind = node =>
    switch node {{
    | StringLiteral(_) => "string"
    | NumericLiteral(_) => "number"
    | This(_) | Super(_) => "other"
    }}
}}
let viaFunctor = Applied.kind
let viaInclude = Included.kind
"#
    ));
    let check = format!(
        "{SAMPLES}console.log(samples.map(exports.viaFunctor).join(' '), '|', samples.map(exports.viaInclude).join(' '));"
    );
    if let Some(output) = run_node(&js, &check) {
        assert_eq!(output, "string number other other | string number other other\n", "{js}");
    }
}

#[test]
fn the_shadow_backend_declines_shared_tags() {
    let source = format!(
        r#"{NODE}
let name = node =>
  switch node {{
  | StringLiteral({{value}}) => value
  | NumericLiteral({{value}}) => Float.toString(value)
  | This(_) => "this"
  | Super(_) => "super"
  }}
let isLiteral = node =>
  switch node {{
  | StringLiteral(_) | NumericLiteral(_) => true
  | This(_) | Super(_) => false
  }}
"#
    );
    assert_eq!(js_compared(&source), js(&source));
}
