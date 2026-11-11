//! Untagged variants with several object cases, told apart by their fields
//! (`docs/ts-import/README.md`, "Object cases told apart by their fields").

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

fn compile_with(source: &str, registry: &ModuleRegistry) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
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

/// The tests of a complete match on `type t`, one arm per case, in the
/// order the generated code runs them.
fn tests_of(declaration: &str, cases: &[&str]) -> Vec<String> {
    let arms: String = cases
        .iter()
        .enumerate()
        .map(|(index, case)| format!("| {case}(_) => {index}\n"))
        .collect();
    let js = js(&format!("@unboxed\ntype t = {declaration}\nlet f = x => switch x {{\n{arms}}}\n"));
    let body = function(&js, "f");
    body.split("if (")
        .skip(1)
        .map(|part| part[..part.find(") {").expect("an if")].to_string())
        .collect()
}

const SAME_MESSAGE: &str = "This untagged variant definition is invalid: At most one case can be an object type.";

#[test]
fn the_first_example_tests_one_field() {
    let js = js(r#"
@unboxed
type outcome = Ok({result: string}) | Failed({error: string, code?: int})
let message = outcome =>
  switch outcome {
  | Ok({result}) => result
  | Failed({error}) => error
  }
"#);
    assert_eq!(
        function(&js, "message"),
        r#"if ("result" in outcome) { return outcome.result; } else { return outcome.error; }"#
    );
}

#[test]
fn the_rows_of_the_table() {
    assert_eq!(
        tests_of("Ok({result: string}) | Failed({error: string})", &["Ok", "Failed"]),
        [r#""result" in x"#]
    );
    assert_eq!(
        tests_of("Text({value: string}) | Number({value: float})", &["Text", "Number"]),
        [r#"typeof x.value === "string""#]
    );
    assert_eq!(
        tests_of("Named({name: string}) | Person({name: string, age: float})", &["Named", "Person"]),
        [r#""age" in x"#]
    );
    let js = js(r#"
type element = {props: dict<string>, key: string}
type portal = {props: dict<string>, key: string, children: array<element>}
@unboxed type node = Element(element) | Portal(portal) | Other(dict<unknown>)
let f = x => switch x { | Element(_) => 1 | Portal(_) => 2 | Other(_) => 3 }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if ("children" in x) { return 2; } else if ("props" in x) { return 1; } else { return 3; }"#
    );
    assert_eq!(
        tests_of("A({kind: [#a], x: int}) | B({kind: [#b], x: int})", &["A", "B"]),
        [r#"x.kind === "a""#]
    );
}

#[test]
fn a_literal_check_tests_every_literal_of_the_field() {
    assert_eq!(
        tests_of("A({kind: [#a | #b], v: int}) | C({kind: [#c], v: int})", &["A", "C"]),
        [r#"x.kind === "a" || x.kind === "b""#]
    );
    assert_eq!(
        tests_of("A({flag: bool, x: int}) | B({flag: [#yes], x: int})", &["A", "B"]),
        ["x.flag === true || x.flag === false"]
    );
    let js = js(r#"
type shape = | @as("circle") Circle | @as("square") Square
@unboxed type t = Round({kind: shape, r: float}) | Other({kind: [#other], r: float})
let f = x => switch x { | Round(_) => 1 | Other(_) => 2 }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if (x.kind === "circle" || x.kind === "square") { return 1; } else { return 2; }"#
    );
}

#[test]
fn a_numeric_polymorphic_variant_tag_is_a_number() {
    assert_eq!(
        tests_of("A({k: [#1], v: int}) | B({k: [#2], v: int})", &["A", "B"]),
        ["x.k === 1"]
    );
}

#[test]
fn checks_are_joined_when_no_single_one_is_enough() {
    assert_eq!(
        tests_of("Both({x: int, y: int}) | X({x: int}) | Y({y: int})", &["Both", "X", "Y"]),
        [r#""x" in x && "y" in x"#, r#""x" in x"#]
    );
}

#[test]
fn an_optional_field_passes_no_presence_check_but_blocks_one() {
    // `B` has no required field `A` lacks but `z`; `A` cannot be told by `y`,
    // which `B` may have.
    assert_eq!(
        tests_of("A({y: int}) | B({y?: int, z: int})", &["A", "B"]),
        [r#""z" in x"#]
    );
    // Only an optional field tells them apart: no order.
    assert!(error("@unboxed type t = A({x: int}) | B({x: int, y?: int})").contains(SAME_MESSAGE));
}

#[test]
fn fields_are_named_by_their_javascript_name() {
    assert_eq!(
        tests_of(
            r#"R({@as("type") type_: [#r]}) | Q({@as("type") type_: [#q], @as("my-field") f: int})"#,
            &["R", "Q"]
        ),
        [r#"x.type === "r""#]
    );
    assert_eq!(
        tests_of(r#"A({@as("my-field") f: int}) | B({g: int})"#, &["A", "B"]),
        [r#""my-field" in x"#]
    );
}

#[test]
fn named_generic_and_inline_records() {
    let js = js(r#"
type ok = {result: string}
type gen<'a> = {value: 'a}
@unboxed type t = Ok(ok) | Failed({error: string})
@unboxed type g = G(gen<string>) | H({value: float})
let f = x => switch x { | Ok(o) => o.result | Failed({error}) => error }
let k = v => switch v { | G(_) => 1 | H(_) => 2 }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if ("result" in x) { return x.result; } else { return x.error; }"#
    );
    assert_eq!(
        function(&js, "k"),
        r#"if (typeof v.value === "string") { return 1; } else { return 2; }"#
    );
}

#[test]
fn the_open_case_is_last() {
    let js = js(r#"
@typeOf("object") type opaque
@unboxed type t = O(opaque) | A({x: int}) | B({y: string})
let f = v => switch v { | O(_) => 3 | A(_) => 1 | B(_) => 2 }
@unboxed type d = D(dict<int>) | A({x: int})
let g = v => switch v { | D(_) => 2 | A(_) => 1 }
@unboxed type o = A({x: int}) | B({"y": string})
let h = v => switch v { | A(_) => 1 | B(_) => 2 }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if ("x" in v) { return 1; } else if ("y" in v) { return 2; } else { return 3; }"#
    );
    assert_eq!(function(&js, "g"), r#"if ("x" in v) { return 1; } else { return 2; }"#);
    assert_eq!(function(&js, "h"), r#"if ("x" in v) { return 1; } else { return 2; }"#);
    // Two open cases cannot be told apart.
    assert!(error(r#"
@typeOf("object") type opaque
@unboxed type t = O(opaque) | D(dict<int>) | A({x: int})
"#)
    .contains(SAME_MESSAGE));
}

#[test]
fn object_cases_come_after_literals_primitives_arrays_and_classes() {
    let js = js(r#"
@unboxed
type t =
  | S(string)
  | N(float)
  | Arr(array<int>)
  | D(Date.t)
  | O1({p: int})
  | O2({q: int})
  | @as(null) Nil
let f = v =>
  switch v {
  | S(_) => 1
  | N(_) => 2
  | Arr(_) => 3
  | D(_) => 4
  | O1(_) => 5
  | O2(_) => 6
  | Nil => 7
  }
let g = v => switch v { | O2({q}) => q | _ => 0 }
"#);
    let f = function(&js, "f");
    assert!(f.starts_with("if (v === null) { return 7; }"), "{f}");
    assert!(
        f.contains(r#"if (Array.isArray(v)) { return 3; } else if (v instanceof Date) { return 4; } else if ("p" in v) { return 5; } else { return 6; }"#),
        "{f}"
    );
    assert_eq!(
        function(&js, "g"),
        r#"if (typeof v === "object" && v !== null && !(v instanceof Date) && !Array.isArray(v) && !("p" in v)) { return v.q; } else { return 0; }"#
    );
}

#[test]
fn a_switch_naming_some_cases_tests_only_those() {
    let js = js(r#"
@unboxed type t = A({a: int}) | B({b: int}) | C({c: int})
let first = v => switch v { | A({a}) => a | _ => 0 }
let last = v => switch v { | C({c}) => c | _ => 0 }
"#);
    assert_eq!(function(&js, "first"), r#"if ("a" in v) { return v.a; } else { return 0; }"#);
    assert_eq!(
        function(&js, "last"),
        r#"if ("a" in v || "b" in v) { return 0; } else { return v.c; }"#
    );
}

#[test]
fn an_option_of_the_variant() {
    let js = js(r#"
@unboxed type t = A({a: int}) | B({b: int})
let f = o => switch o { | Some(A({a})) => a | Some(B({b})) => b | None => 0 }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if (o !== undefined) { if ("a" in o) { return o.a; } else { return o.b; } } else { return 0; }"#
    );
}

#[test]
fn values_are_plain_objects() {
    let js = js(r#"
@unboxed type outcome = Ok({result: string}) | Failed({error: string})
let ok = Ok({result: "x"})
let failed = Failed({error: "e"})
"#);
    assert!(js.contains("let ok = {\n  result: \"x\"\n};"), "{js}");
    assert!(js.contains("let failed = {\n  error: \"e\"\n};"), "{js}");
}

#[test]
fn cases_that_cannot_be_told_apart_are_rejected_as_before() {
    let message = error("@unboxed type t = A({x: int}) | B({x: int})");
    assert!(message.contains(SAME_MESSAGE), "{message}");
    assert!(message.contains("Demo.res:1:31-43"), "{message}");
    // The same fields at the same kinds.
    assert!(error("@unboxed type t = A({x: int}) | B({x: float})").contains(SAME_MESSAGE));
}

#[test]
fn one_object_case_is_unchanged() {
    let js = js(r#"
@unboxed type t = S(string) | O({x: int}) | @as(null) Nil
let f = v => switch v { | S(s) => s | O(_) => "o" | Nil => "nil" }
"#);
    assert_eq!(
        function(&js, "f"),
        r#"if (v === null) { return "nil"; } else if (typeof v === "string") { return v; } else { return "o"; }"#
    );
}

#[test]
fn an_interface_with_the_same_cases_is_accepted() {
    let js = js(r#"
module M: {
  @unboxed type t = A({a: int}) | B({b: string})
  let make: int => t
} = {
  @unboxed type t = A({a: int}) | B({b: string})
  let make = a => A({a: a})
}
let f = (v: M.t) => switch v { | A({a}) => a | B(_) => 0 }
"#);
    assert_eq!(function(&js, "f"), r#"if ("a" in v) { return v.a; } else { return 0; }"#);
}

/// A variant declared in another module, whose interface is all the
/// compiler sees of it.
#[test]
fn a_variant_of_another_module() {
    let dir = std::env::temp_dir().join(format!("object_cases_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let declaration = "@unboxed type t = Ok({result: string}) | Failed({error: string, code?: int})\n";
    std::fs::write(dir.join("Shapes.res"), declaration).unwrap();
    std::fs::write(dir.join("Shapes.resi"), declaration).unwrap();
    let mut registry = registry();
    registry.insert_source_fallback_path("Shapes".to_string(), dir.join("Shapes.resi"));
    let js = compile_with(
        "let f = (v: Shapes.t) => switch v { | Ok({result}) => result | Failed({error}) => error }\n",
        &registry,
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(
        function(&js, "f"),
        r#"if ("result" in v) { return v.result; } else { return v.error; }"#
    );
}



#[test]
fn a_field_that_may_be_null_or_missing_has_no_kind() {
    // `typeof x.v === "string"` fails for `None`, `null` and `undefined`, so
    // none of these types gives `A` a kind test: `B` is told apart by `w`.
    for field in ["option<string>", "Null.t<string>", "Nullable.t<string>"] {
        assert_eq!(
            tests_of(&format!("A({{v: {field}}}) | B({{v: float, w: int}})"), &["A", "B"]),
            [r#""w" in x"#],
            "{field}"
        );
    }
}

#[test]
fn a_variant_through_a_functor_argument_and_an_include() {
    let js = js(r#"
module type S = {
  @unboxed type t = Ok({result: string}) | Failed({error: string})
}
module Make = (M: S) => {
  let message = (v: M.t) => switch v { | M.Ok({result}) => result | M.Failed({error}) => error }
}
module Impl = {
  @unboxed type t = Ok({result: string}) | Failed({error: string})
}
module Applied = Make(Impl)
module Included = {
  include Impl
  let message = v => switch v { | Ok({result}) => result | Failed({error}) => error }
}
let viaFunctor = Applied.message
let viaInclude = Included.message
"#);
    assert!(
        js.matches(r#"if ("result" in v) {"#).count() >= 2,
        "{js}"
    );
}

#[test]
fn a_joined_test_keeps_only_the_checks_it_needs() {
    let js = js(r#"
type regex = {pattern: string, flags: string}
@unboxed type node =
  | StringLiteral({@as("type") type_: [#Literal], value: string, raw: Null.t<string>})
  | NumericLiteral({@as("type") type_: [#Literal], value: float, raw: Null.t<string>})
  | RegExpLiteral({@as("type") type_: [#Literal], value: Null.t<RegExp.t>, regex: regex})
  | IdentifierName({@as("type") type_: [#Identifier], name: string})
let f = node =>
  switch node {
  | StringLiteral(_) => 1
  | NumericLiteral(_) => 2
  | RegExpLiteral(_) => 3
  | IdentifierName(_) => 4
  }
"#);
    let f = function(&js, "f");
    assert!(
        f.starts_with(r#"if ("raw" in node && typeof node.value === "string") { return 1; }"#),
        "{f}"
    );
}


const SYNTAX_NODE: &str = r#"
type regex = {pattern: string, flags: string}
@unboxed type node =
  | StringLiteral({@as("type") type_: [#Literal], value: string, raw: Null.t<string>})
  | NumericLiteral({@as("type") type_: [#Literal], value: float, raw: Null.t<string>})
  | RegExpLiteral({@as("type") type_: [#Literal], value: Null.t<RegExp.t>, regex: regex})
  | Identifier({@as("type") type_: [#Identifier | #IdentifierName], name: string})
  | Block({@as("type") type_: [#BlockStatement], body: array<int>})
  | Empty({@as("type") type_: [#EmptyStatement], start: float})
  | Custom({kind: string, data: dict<string>})
"#;

#[test]
fn many_cases_are_a_switch_on_their_literal_field() {
    let js = js(&format!(
        r#"{SYNTAX_NODE}
let describe = node =>
  switch node {{
  | StringLiteral(_) => 1
  | NumericLiteral(_) => 2
  | RegExpLiteral(_) => 3
  | Identifier(_) => 4
  | Block(_) => 5
  | Empty(_) => 6
  | Custom(_) => 7
  }}
"#
    ));
    // The cases that share `"Literal"` are told apart inside its arm, a case
    // with two literals has two labels, and the case without a `type`
    // literal is the default.
    assert_eq!(
        function(&js, "describe"),
        concat!(
            r#"switch (node.type) { case "Literal" : if ("raw" in node && typeof node.value === "string") { return 1; } "#,
            r#"else if ("raw" in node) { return 2; } else { return 3; } "#,
            r#"case "IdentifierName" : case "Identifier" : return 4; "#,
            r#"case "BlockStatement" : return 5; case "EmptyStatement" : return 6; default: return 7; }"#
        )
    );
}

#[test]
fn a_switch_with_a_default_tests_the_named_cases() {
    let js = js(&format!(
        r#"{SYNTAX_NODE}
let isBlock = node => switch node {{ | Block(_) => true | _ => false }}
let literal = node => switch node {{ | NumericLiteral({{value}}) => value | _ => 0. }}
"#
    ));
    assert_eq!(
        function(&js, "isBlock"),
        r#"if (typeof node !== "object") { return false; } switch (node.type) { case "BlockStatement" : return true; default: return false; }"#
    );
    assert!(function(&js, "literal").contains(r#"switch (node.type) { case "Literal" :"#), "{js}");
}

#[test]
fn three_literals_keep_the_if_chain() {
    assert_eq!(
        tests_of(
            "A({kind: [#a], x: int}) | B({kind: [#b], x: int}) | C({kind: [#c], x: int})",
            &["A", "B", "C"]
        ),
        [r#"x.kind === "a""#, r#"x.kind === "b""#]
    );
}

