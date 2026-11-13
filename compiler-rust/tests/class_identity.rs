//! A class type (`@instanceOf`) is compatible with every declaration of the
//! same class, and coerces to every declaration of an ancestor
//! (docs/class-identity).

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

fn compile(source: &str) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        ..Default::default()
    };
    driver::compile_source_in_process(source, "/app/src/Demo.res", "Demo", &options, &registry(), false, None)
        .map(|compiled| compiled.js_output)
        .map_err(|error| format!("{error:#}"))
}

fn error(source: &str) -> String {
    compile(source).expect_err("the program is rejected")
}

/// Three packages. React declares the classes it names, as abstract types.
/// WebAPI describes them as records. Forms has its own slice.
const PACKAGES: &str = r#"
module ReactDOM = {
  @instanceOf("EventTarget") type eventTarget
  @instanceOf("Node") type node = private eventTarget
  @instanceOf("Element") type element = private node
  type root
  external createRoot: element => root = "createRoot"
  external contains: (node, node) => bool = "contains"
}

module WebAPI = {
  @instanceOf("EventTarget")
  type eventTarget = private {mutable onerror: string}
  @instanceOf("Node") @extends(: eventTarget)
  type node = private {mutable onerror: string, nodeName: string}
  @instanceOf("Element") @extends(: node)
  type element = private {mutable onerror: string, nodeName: string, tagName: string, mutable id: string}
  @instanceOf("HTMLInputElement") @extends(: element)
  type input = private {
    mutable onerror: string,
    nodeName: string,
    tagName: string,
    mutable id: string,
    mutable value: string,
  }
  @send external focus: element => unit = "focus"
}

module Forms = {
  @instanceOf("HTMLInputElement") type input
}
"#;

fn with_packages(program: &str) -> Result<String, String> {
    compile(&format!("{PACKAGES}\n{program}"))
}

#[test]
fn two_declarations_of_a_class_coerce_both_ways() {
    let js = with_packages(
        r#"
let toRecord = (el: ReactDOM.element) => (el :> WebAPI.element)
let toAbstract = (el: WebAPI.element) => (el :> ReactDOM.element)
let tag = (el: ReactDOM.element) => (el :> WebAPI.element).tagName
"#,
    )
    .unwrap();
    assert!(js.contains("function toRecord(el) {\n  return el;\n}"), "{js}");
    assert!(js.contains("function toAbstract(el) {\n  return el;\n}"), "{js}");
    assert!(js.contains("return el.tagName;"), "{js}");
}

#[test]
fn a_subclass_coerces_to_another_declaration_of_an_ancestor() {
    let js = with_packages(
        r#"
let one = (input: WebAPI.input) => (input :> ReactDOM.element)
let two = (input: WebAPI.input) => (input :> ReactDOM.node)
let three = (input: WebAPI.input) => (input :> ReactDOM.eventTarget)
let fromAbstract = (el: ReactDOM.element) => (el :> WebAPI.node)
"#,
    )
    .unwrap();
    assert!(js.contains("function three(input) {\n  return input;\n}"), "{js}");
}

#[test]
fn a_class_does_not_coerce_down_or_sideways() {
    for (from, to) in [
        ("ReactDOM.element", "WebAPI.input"),
        ("WebAPI.element", "WebAPI.input"),
        ("ReactDOM.node", "ReactDOM.element"),
        ("ReactDOM.node", "WebAPI.element"),
        ("ReactDOM.root", "WebAPI.element"),
    ] {
        let message = with_packages(&format!("let f = (x: {from}) => (x :> {to})")).unwrap_err();
        assert!(message.contains("is not a subtype of"), "{from} :> {to}: {message}");
    }
}

#[test]
fn a_slice_without_its_chain_does_not_coerce_up() {
    // `Forms.input` declares no parent, so nothing says it is an Element.
    let message = with_packages("let f = (x: Forms.input) => (x :> ReactDOM.element)").unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    // It is still the class HTMLInputElement.
    with_packages("let f = (x: Forms.input) => (x :> WebAPI.input)").unwrap();
    with_packages("let f = (x: WebAPI.input) => (x :> Forms.input)").unwrap();
}

#[test]
fn nothing_but_the_class_coerces_into_a_class_record() {
    let message = with_packages(
        r#"
type plain = {mutable onerror: string, nodeName: string, tagName: string, mutable id: string}
let fake = (p: plain) => (p :> WebAPI.element)
"#,
    )
    .unwrap_err();
    assert!(message.contains("another type cannot be coerced to it"), "{message}");
}

#[test]
fn a_refinement_of_a_class_is_not_the_class() {
    // `mine` abbreviates a class type without `@instanceOf`: its values are
    // elements, but not every element is one of its values.
    let program = |body: &str| {
        format!(
            r#"
module Owner = {{
  type mine = private ReactDOM.element
}}
{body}"#
        )
    };
    with_packages(&program("let up = (x: Owner.mine) => (x :> WebAPI.element)")).unwrap();
    let message = with_packages(&program("let down = (x: WebAPI.element) => (x :> Owner.mine)")).unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message =
        with_packages(&program("let down = (x: ReactDOM.element) => (x :> Owner.mine)")).unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
}

#[test]
fn coercion_follows_variance() {
    with_packages(
        r#"
let optional = (input: option<WebAPI.input>) => (input :> option<ReactDOM.element>)
let promised = (input: promise<WebAPI.input>) => (input :> promise<ReactDOM.node>)
let listener = (f: ReactDOM.node => unit) => (f :> WebAPI.input => unit)
let nullable = (el: Null.t<ReactDOM.element>) => (el :> Null.t<WebAPI.element>)
// An array is written to, so its elements must be equal: the same class is.
let elements = (elements: array<ReactDOM.element>) => (elements :> array<WebAPI.element>)
"#,
    )
    .unwrap();
    let message =
        with_packages("let f = (inputs: array<WebAPI.input>) => (inputs :> array<ReactDOM.element>)").unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message =
        with_packages("let listener = (f: WebAPI.input => unit) => (f :> ReactDOM.node => unit)").unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
}

#[test]
fn the_same_class_is_equal_where_types_must_be_equal() {
    with_packages(
        r#"
type ref<'a> = {mutable current: 'a}
let same = (ref: ref<Null.t<ReactDOM.element>>) => (ref :> ref<Null.t<WebAPI.element>>)

type mine = {mutable target: ReactDOM.element}
type theirs = {mutable target: WebAPI.element}
let field = (x: mine) => (x :> theirs)
"#,
    )
    .unwrap();
    // A subclass is not equal to its superclass.
    let message = with_packages(
        r#"
type ref<'a> = {mutable current: 'a}
let up = (ref: ref<WebAPI.input>) => (ref :> ref<ReactDOM.element>)
"#,
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message = with_packages(
        r#"
type mine = {mutable target: WebAPI.input}
type theirs = {mutable target: ReactDOM.element}
let field = (x: mine) => (x :> theirs)
"#,
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
}

#[test]
fn classes_of_two_modules_are_two_classes() {
    let message = compile(
        r#"
module A = { @module("a") @instanceOf("Client") type client }
module B = { @module("b") @instanceOf("Client") type client }
module C = { @instanceOf("Client") type client }
let f = (x: A.client) => (x :> B.client)
"#,
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message = compile(
        r#"
module A = { @module("a") @instanceOf("Client") type client }
module C = { @instanceOf("Client") type client }
let f = (x: A.client) => (x :> C.client)
"#,
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    compile(
        r#"
module A = { @module("a") @instanceOf("Client") type client }
module B = { @module("a") @instanceOf("Client") type client = private {id: string} }
let f = (x: A.client) => (x :> B.client).id
"#,
    )
    .unwrap();
}

#[test]
fn a_class_with_type_parameters_keeps_its_rules() {
    let message = compile(
        r#"
module A = { @instanceOf("Box") type box<'a> }
module B = { @instanceOf("Box") type box<'a> }
let f = (x: A.box<int>) => (x :> B.box<int>)
"#,
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
}

#[test]
fn extends_still_compares_the_fields() {
    let message = error(
        r#"@instanceOf("Blob") type blob = private {size: float, kind: string}
@instanceOf("File") @extends(: blob) type file = private {size: float, name: string}"#,
    );
    assert!(message.contains("it must have every field of that record"), "{message}");
}
