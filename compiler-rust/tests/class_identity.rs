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
    compile_with(source, CompilerOptions::default())
}

fn compile_with(source: &str, options: CompilerOptions) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        ..options
    };
    driver::compile_source_in_process(
        source,
        "/app/src/Demo.res",
        "Demo",
        &options,
        &registry(),
        false,
        None,
    )
    .map(|compiled| compiled.js_output)
    .map_err(|error| plain(&format!("{error:#}")))
}

/// Without the escape sequences that colour a type in a message.
fn plain(message: &str) -> String {
    let mut out = String::new();
    let mut rest = message;
    while let Some(start) = rest.find("\u{1b}[") {
        out.push_str(&rest[..start]);
        rest = rest[start..].split_once('m').map_or("", |(_, after)| after);
    }
    out + rest
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
    assert!(
        js.contains("function toRecord(el) {\n  return el;\n}"),
        "{js}"
    );
    assert!(
        js.contains("function toAbstract(el) {\n  return el;\n}"),
        "{js}"
    );
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
    assert!(
        js.contains("function three(input) {\n  return input;\n}"),
        "{js}"
    );
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
        assert!(
            message.contains("is not a subtype of"),
            "{from} :> {to}: {message}"
        );
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
    assert!(
        message.contains("another type cannot be coerced to it"),
        "{message}"
    );
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
    with_packages(&program(
        "let up = (x: Owner.mine) => (x :> WebAPI.element)",
    ))
    .unwrap();
    let message = with_packages(&program(
        "let down = (x: WebAPI.element) => (x :> Owner.mine)",
    ))
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message = with_packages(&program(
        "let down = (x: ReactDOM.element) => (x :> Owner.mine)",
    ))
    .unwrap_err();
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
    let message = with_packages(
        "let f = (inputs: array<WebAPI.input>) => (inputs :> array<ReactDOM.element>)",
    )
    .unwrap_err();
    assert!(message.contains("is not a subtype of"), "{message}");
    let message =
        with_packages("let listener = (f: WebAPI.input => unit) => (f :> ReactDOM.node => unit)")
            .unwrap_err();
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
    assert!(
        message.contains("it must have every field of that record"),
        "{message}"
    );
}

// Rule 3: at an argument, a record field and a constructor payload, the
// coercion does not have to be written.

#[test]
fn an_argument_of_the_same_class_is_accepted() {
    let js = with_packages(
        r#"
let mount = (container: WebAPI.element) => ReactDOM.createRoot(container)
let focus = (el: ReactDOM.element) => WebAPI.focus(el)
let piped = (el: ReactDOM.element) => el->WebAPI.focus
let twice = (a: WebAPI.node, b: WebAPI.element) => ReactDOM.contains(a, b)
"#,
    )
    .unwrap();
    assert!(
        js.contains("function mount(container) {\n  return createRoot(container);\n}"),
        "{js}"
    );
    assert!(
        js.contains("function focus(el) {\n  el.focus();\n}"),
        "{js}"
    );
    assert!(
        js.contains("function piped(el) {\n  el.focus();\n}"),
        "{js}"
    );
}

#[test]
fn an_argument_of_a_subclass_is_accepted() {
    with_packages(
        r#"
let mount = (input: WebAPI.input) => ReactDOM.createRoot(input)
let own = (input: WebAPI.input) => WebAPI.focus(input)
let abstract_ = (el: ReactDOM.element, node: ReactDOM.node) => ReactDOM.contains(node, el)
"#,
    )
    .unwrap();
}

#[test]
fn labelled_and_optional_arguments_are_arguments() {
    with_packages(
        r#"
let attach = (~container: ReactDOM.element, ~before: option<ReactDOM.node>=?) => (container, before)
let a = (input: WebAPI.input) => attach(~container=input)
let b = (el: WebAPI.element, input: WebAPI.input) => attach(~container=el, ~before=input)
let c = (el: WebAPI.element, node: option<WebAPI.node>) => attach(~container=el, ~before=?node)
"#,
    )
    .unwrap();
}

#[test]
fn an_argument_of_a_superclass_is_refused() {
    let message = with_packages("let f = (node: ReactDOM.node) => WebAPI.focus(node)").unwrap_err();
    assert!(
        message.contains("This has type: ReactDOM.node"),
        "{message}"
    );
    assert!(
        message.contains("But this function argument is expecting: WebAPI.element"),
        "{message}"
    );
    let message = with_packages("let f = (x: Forms.input) => ReactDOM.createRoot(x)").unwrap_err();
    assert!(message.contains("This has type: Forms.input"), "{message}");
}

#[test]
fn the_same_class_is_accepted_inside_the_type_of_an_argument() {
    with_packages(
        r#"
type ref<'a> = {mutable current: 'a}
external useRef: unit => ref<Null.t<ReactDOM.element>> = "useRef"
external observe: ref<Null.t<WebAPI.element>> => unit = "observe"
external listen: (ReactDOM.element => unit) => unit = "listen"
external all: array<ReactDOM.element> => unit = "all"
external both: ((ReactDOM.element, int)) => unit = "both"

let a = () => observe(useRef())
let b = (handler: WebAPI.element => unit) => listen(handler)
let c = (elements: array<WebAPI.element>) => all(elements)
let d = (pair: (WebAPI.element, int)) => both(pair)
"#,
    )
    .unwrap();
}

#[test]
fn a_subclass_inside_the_type_of_an_argument_is_written() {
    let program = |call: &str| {
        format!(
            r#"
external maybe: option<ReactDOM.element> => unit = "maybe"
let f = (input: option<WebAPI.input>) => {call}
"#
        )
    };
    let message = with_packages(&program("maybe(input)")).unwrap_err();
    assert!(
        message.contains("This has type: option<WebAPI.input>"),
        "{message}"
    );
    with_packages(&program("maybe((input :> option<ReactDOM.element>))")).unwrap();
}

#[test]
fn a_record_field_and_a_constructor_payload_are_accepted() {
    let js = with_packages(
        r#"
type props = {container: ReactDOM.element, title: string}
type target = Element(ReactDOM.element) | Window
type pair = Pair(ReactDOM.node, ReactDOM.node)

let props = (input: WebAPI.input) => {container: input, title: "x"}
let update = (props: props, el: WebAPI.element) => {...props, container: el}
let target = (el: WebAPI.element) => Element(el)
let pair = (el: WebAPI.element, input: WebAPI.input) => Pair(el, input)
let some = (el: WebAPI.element): option<ReactDOM.element> => Some(el)
"#,
    )
    .unwrap();
    assert!(js.contains("container: input"), "{js}");
}

#[test]
fn the_result_of_a_call_and_a_field_are_arguments() {
    with_packages(
        r#"
external find: string => WebAPI.input = "find"
external later: unit => promise<WebAPI.element> = "later"
type holder = {el: WebAPI.element}
let a = () => ReactDOM.createRoot(find("x"))
let b = (holder: holder) => ReactDOM.createRoot(holder.el)
let c = async () => ReactDOM.createRoot(await later())
"#,
    )
    .unwrap();
}

#[test]
fn outside_those_sites_the_coercion_is_written() {
    for program in [
        // The branches of an `if`: neither is the expected type of the other.
        "let f = (c, a: ReactDOM.element, b: WebAPI.element) => c ? a : b",
        "let f = (c, a: ReactDOM.element, b: WebAPI.element) => if c { a } else { b }",
        // The elements of an array.
        "let f = (a: ReactDOM.element, b: WebAPI.element) => [a, b]",
        // The cases of a switch.
        "let f = (c, a: ReactDOM.element, b: WebAPI.element) => switch c { | true => a | false => b }",
        // The last expression of a block that is an argument.
        "let f = (a: WebAPI.element) => ReactDOM.createRoot({ let b = a; b })",
        // An annotation.
        "let f = (a: ReactDOM.element) => { let b: WebAPI.element = a; b }",
        "let f = (a: ReactDOM.element): WebAPI.element => a",
    ] {
        let message = with_packages(program).unwrap_err();
        assert!(
            message.contains("ReactDOM.element") && message.contains("WebAPI.element"),
            "{program}: {message}"
        );
    }
    with_packages(
        "let f = (c, a: ReactDOM.element, b: WebAPI.element) => c ? a : (b :> ReactDOM.element)",
    )
    .unwrap();
}

#[test]
fn an_accepted_argument_keeps_its_own_fields() {
    // The argument is coerced where it is passed. The variable keeps its
    // type, so its fields are those of its own declaration.
    let js = with_packages(
        r#"
let f = (el: WebAPI.element) => {
  let root = ReactDOM.createRoot(el)
  (root, el.tagName)
}
"#,
    )
    .unwrap();
    assert!(js.contains("el.tagName"), "{js}");
    let message = with_packages(
        r#"
let f = (el: ReactDOM.element) => {
  WebAPI.focus(el)
  el.tagName
}
"#,
    )
    .unwrap_err();
    assert!(message.contains("tagName"), "{message}");
}

#[test]
fn other_clashes_at_an_argument_are_reported_as_before() {
    let message = with_packages("let f = () => ReactDOM.createRoot(1)").unwrap_err();
    assert!(message.contains("This has type: int"), "{message}");
    assert!(
        message.contains("But this function argument is expecting: ReactDOM.element"),
        "{message}"
    );
    // The class fits and the rest does not: the error is the clash, with
    // the types as they were.
    let message = with_packages(
        r#"
external both: ((ReactDOM.element, int, array<string>)) => unit = "both"
let f = (triple: (WebAPI.element, int, array<'a>), first: 'a) => {
  both(triple)
  first
}
let g = (triple: (WebAPI.element, string, array<'a>)) => both(triple)
"#,
    )
    .unwrap_err();
    assert!(
        message.contains("This has type: (WebAPI.element, string, array<'a>)"),
        "{message}"
    );
    assert!(
        message.contains("(ReactDOM.element, int, array<string>)"),
        "{message}"
    );
    let message = with_packages(
        r#"
type plain = {mutable onerror: string, nodeName: string, tagName: string, mutable id: string}
let f = (p: plain) => WebAPI.focus(p)
"#,
    )
    .unwrap_err();
    assert!(message.contains("This has type: plain"), "{message}");
}

#[test]
fn a_jsx_prop_is_a_record_field() {
    let source = format!(
        r#"{PACKAGES}
module React = {{
  type element
  type component<'props> = 'props => element
  external jsx: (component<'props>, 'props) => element = "jsx"
}}
module Portal = {{
  type props = {{container: ReactDOM.element, before?: ReactDOM.node}}
  external make: props => React.element = "Portal"
}}
let a = (input: WebAPI.input) => <Portal container=input />
let b = (el: WebAPI.element, node: WebAPI.node) => <Portal container={{el}} before=node />
"#
    );
    let options = CompilerOptions {
        jsx_version: Some(4),
        ..Default::default()
    };
    let js = compile_with(&source, options).unwrap();
    assert!(js.contains("container: input"), "{js}");
}
