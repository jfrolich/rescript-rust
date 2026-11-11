//! End-to-end tests of compile-time macros: each test compiles a small
//! project in memory, with the standard library type-checked from source.

mod macros_support;

use std::path::PathBuf;

use macros_support::Project;

#[test]
fn plain_module_compiles() {
    let mut project = Project::new();
    let js = project
        .compile("Plain.res", "let double = x => x * 2\nlet xs = [1, 2]->Array.map(double)\n")
        .unwrap();
    assert!(js.contains("double"));
    assert!(project.expanded.is_none());
}

const DEBUG: &str = r#"
open Macro

@macro
let dbg = (e: code<'a>): code<'a> =>
  %code({
    let v = ${e}
    Console.log2(${Code.string(Code.print(e) ++ " =")}, v)
    v
  })
"#;

#[test]
fn expression_macro() {
    let mut project = Project::new();
    project.compile("Debug.res", DEBUG).unwrap();
    println!("--- Debug.res expanded\n{}", project.expanded.clone().unwrap_or_default());
    let js = project
        .compile("Main.res", "let age = 41\nlet next = %Debug.dbg(age + 1)\n")
        .unwrap();
    println!("--- Main.res expanded\n{}\n--- js\n{js}", project.expanded.clone().unwrap_or_default());
    assert!(js.contains("\"age + 1 =\""), "{js}");
}

const JSON: &str = r#"
open Macro

@generic
let encode = (value: code<'a>): code<JSON.t> =>
  switch Type.info(typeOf(value)) {
  | String => %code(JSON.Encode.string(${value}))
  | Int => %code(JSON.Encode.int(${value}))
  | Float => %code(JSON.Encode.float(${value}))
  | Bool => %code(JSON.Encode.bool(${value}))
  | Option(_) =>
    %code(
      switch ${value} {
      | Some(v) => encode(v)
      | None => JSON.Encode.null
      }
    )
  | Array(_) => %code(JSON.Encode.array(${value}->Array.map(v => encode(v))))
  | Record({fields}) =>
    let entries = fields->Array.map(f => {
      let key = f.attrs->Attr.string("Json.key")->Option.getOr(f.jsName)
      %code((${Code.string(key)}, encode(${value->Code.field(f.name)})))
    })
    %code(JSON.Encode.object(Dict.fromArray(${Code.array(entries)})))
  | Variant({constructors}) =>
    Code.switch_(
      value,
      constructors->Array.map(c => {
        let (pattern, args) = Pat.constructor(c)
        let encoded = args->Array.map(arg => %code(encode(${arg})))
        (
          pattern,
          %code(
            JSON.Encode.object(
              Dict.fromArray([
                ("tag", JSON.Encode.string(${Code.string(c.name)})),
                ("args", JSON.Encode.array(${Code.array(encoded)})),
              ]),
            )
          ),
        )
      }),
    )
  | Abstract({name}) =>
    switch Type.companion(typeOf(value), "toJson") {
    | Some(toJson) => %code(${toJson}(${value}))
    | None => error(`${name} is abstract and its module has no toJson`)
    }
  | _ => error(`unsupported type ${Type.name(typeOf(value))}`)
  }

@macro
let codec = (t: Type.decl): decls =>
  %code(
    let ${Pat.var(t.name ++ "_encode")} = (value: ${t.typ}) => encode(value)
  )
"#;

const USER: &str = r#"
type address = {street: string, city: string}

type user = {
  name: string,
  @Json.key("user_age") age: int,
  email: option<string>,
  address: address,
  tags: array<string>,
}

let alice = {name: "Alice", age: 30, email: None, address: {street: "Main St", city: "Utrecht"}, tags: ["admin"]}
let json = Json.encode(alice)
"#;

#[test]
fn generic_macro_makes_one_function_per_type() {
    let mut project = Project::new();
    project.compile("Json.res", JSON).unwrap();
    let js = project.compile("User.res", USER).unwrap();
    println!("--- User.res expanded\n{}\n--- js\n{js}", project.expanded.clone().unwrap_or_default());
    assert!(js.contains("\"user_age\""), "{js}");
    assert!(js.contains("value.address") || js.contains("address"), "{js}");
}

fn compile_ok(project: &mut Project, filename: &str, source: &str) -> String {
    match project.compile(filename, source) {
        Ok(js) => {
            println!(
                "--- {filename} expanded\n{}\n--- {filename} js\n{js}",
                project.expanded.clone().unwrap_or_default()
            );
            js
        }
        Err(error) => panic!("{filename} failed:\n{error}"),
    }
}

#[test]
fn derive_on_a_type_adds_declarations() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let js = compile_ok(
        &mut project,
        "Account.res",
        r#"
@Json.codec
type account = {id: string, balance: float}

let json = account_encode({id: "a1", balance: 12.5})
"#,
    );
    assert!(js.contains("account_encode"), "{js}");
    assert!(js.contains("exports.account_encode"), "{js}");
    assert!(!js.contains("exports.encode$"), "{js}");
}

#[test]
fn recursive_types_and_variants() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let js = compile_ok(
        &mut project,
        "Tree.res",
        r#"
type rec tree = {value: int, children: array<tree>}
type shape = Circle(float) | Rect({width: float, height: float}) | Point

let encodeTree = (t: tree) => Json.encode(t)
let encodeShape = (s: shape) => Json.encode(s)
"#,
    );
    assert!(js.contains("encode$tree"), "{js}");
    assert!(js.contains("\"Circle\""), "{js}");
}

#[test]
fn generic_waits_for_inference() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let js = compile_ok(
        &mut project,
        "Save.res",
        r#"
type user = {name: string}
let store = (_user: user, _body: JSON.t) => ()
let save = user => {
  let body = Json.encode(user)
  store(user, body)
}
"#,
    );
    assert!(js.contains("encode$user"), "{js}");
}

#[test]
fn generic_with_compile_time_argument() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Power.res",
        r#"
open Macro

@generic
let rec pow = (base: code<float>, n: int): code<float> =>
  n == 0 ? %code(1.0) : %code(${base} *. ${pow(base, n - 1)})
"#,
    );
    let js = compile_ok(&mut project, "Cube.res", "let cube = x => Power.pow(x, 3)\n");
    assert!(js.contains("* 1.0"), "{js}");
}

#[test]
fn type_macro() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Partial.res",
        r#"
open Macro

@macro
let t = (source: typ): typ =>
  switch Type.info(source) {
  | Record({fields}) => Type.record(fields->Array.map(f => {...f, optional: true}))
  | _ => error("Partial.t needs a record type")
  }
"#,
    );
    let js = compile_ok(
        &mut project,
        "Patch.res",
        r#"
type user = {name: string, age: int}
type userPatch = %Partial.t(user)
let patch: userPatch = {age: 3}
"#,
    );
    assert!(js.contains("age: 3"), "{js}");
}

#[test]
fn module_and_item_macros() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Gen.res",
        r#"
open Macro

@macro
let constants = (prefix: string, count: int): decls =>
  Code.decls(
    Array.fromInitializer(~length=count, i =>
      %code(let ${Pat.var(prefix ++ Int.toString(i))} = ${Code.int(i * 10)})
    ),
  )

@macro
let span = (b: Decl.value): decls =>
  %code(let ${b.pat} = Gen.wrap(${Code.string(b.name)}, ${b.expr}))

let wrap = (name: string, f: 'a => 'b): ('a => 'b) => x => {
  Console.log(name)
  f(x)
}
"#,
    );
    let js = compile_ok(
        &mut project,
        "UseGen.res",
        r#"
module K = %Gen.constants("k", 3)
%%Gen.constants("top", 2)
let sum = K.k1 + K.k2 + top1

@Gen.span
let double = x => x * 2
"#,
    );
    assert!(js.contains("\"double\""), "{js}");
    assert!(js.contains("30") || js.contains("k2"), "{js}");
}

#[test]
fn comptime_evaluates_now() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Table.res",
        "let squares = n => Array.fromInitializer(~length=n, i => i * i)\nlet config = () => {\"name\": \"x\"}\n",
    );
    let js = compile_ok(
        &mut project,
        "UseTable.res",
        "let table = %comptime(Table.squares(5))\nlet label = %comptime(String.toUpperCase(\"abc\") ++ \"!\")\n",
    );
    assert!(js.contains("16"), "{js}");
    assert!(js.contains("\"ABC!\""), "{js}");
    assert!(!js.contains("Table"), "{js}");
}

#[test]
fn macro_errors_point_at_the_use() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let error = project
        .compile("Bad.res", "let f = (g: int => int) => Json.encode(g)\n")
        .unwrap_err();
    println!("{error}");
    assert!(error.contains("Bad.res:1:"), "{error}");
    assert!(error.contains("unsupported type"), "{error}");

    let error = project
        .compile("Unknown.res", "let f = x => Json.encode(x)\n")
        .unwrap_err();
    println!("{error}");
    assert!(error.contains("generated per type"), "{error}");
}

#[test]
fn text_outside_ascii() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Shout.res",
        r#"
open Macro

@macro
let label = (text: string): code<string> => Code.string("« " ++ String.toUpperCase(text) ++ " » ✓")
"#,
    );
    let js = compile_ok(
        &mut project,
        "Menu.res",
        "let cafe = \"crème brûlée\"\nlet title = %Shout.label(\"déjà vu\")\nlet both = cafe ++ title\n",
    );
    assert!(js.contains("\"« DÉJÀ VU » ✓\""), "{js}");
    assert!(js.contains("crème brûlée"), "{js}");

    // A macro error after non-ASCII text is reported at the right column.
    compile_ok(
        &mut project,
        "Fail.res",
        "open Macro\n@macro\nlet now = (text: string): code<string> => error(\"no \" ++ text)\n",
    );
    let error = project
        .compile("Late.res", "let s = \"déjà\"; let t = %Fail.now(\"été\")\n")
        .unwrap_err();
    println!("{error}");
    assert!(error.contains("no été"), "{error}");
    assert!(error.contains("Late.res:1:"), "{error}");
}

#[test]
fn array_spread_needs_a_runtime_module_first() {
    // `Primitive_array` is type checked from source here, before anything
    // else needed it.
    let mut project = Project::new();
    let js = compile_ok(&mut project, "Spread.res", "let f = (a, rest) => [a, ...rest]\n");
    assert!(js.contains("Primitive_array"), "{js}");
}

#[test]
fn compile_time_arguments_can_be_structured() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Sum.res",
        r#"
open Macro

type options = {scale: int, label: string}

@macro
let total = (items: array<(string, int)>, options: options): code<string> => {
  let sum = items->Array.reduce(0, (sum, (_, n)) => sum + n) * options.scale
  Code.string(options.label ++ Int.toString(sum))
}
"#,
    );
    let js = compile_ok(
        &mut project,
        "UseSum.res",
        "let total = %Sum.total([(\"a\", 1), (\"b\", 2)], {scale: 10, label: \"sum=\"})\n",
    );
    assert!(js.contains("\"sum=30\""), "{js}");
}

#[test]
fn opening_macro_does_not_warn() {
    let mut project = Project::new();
    project
        .compile(
            "Quiet.res",
            "open Macro\n@macro\nlet name = (t: typ): code<string> => Code.string(Type.name(t))\nlet kind = Type.typeof(1)\n",
        )
        .unwrap();
    assert_eq!(project.warnings, "");
}

/// The examples of the playground compile. `playground/scripts/smoke.mjs`
/// also runs them, with the compiler built to WebAssembly.
#[test]
fn playground_examples_compile() {
    // A debug build of the type checker needs more stack than a test thread
    // has; the compiler's own threads have it.
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(compile_playground_examples)
        .unwrap()
        .join()
        .unwrap();
}

fn compile_playground_examples() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../playground/examples");
    let index: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(dir.join("index.json")).unwrap()).unwrap();
    for example in index.as_array().unwrap() {
        let id = example["id"].as_str().unwrap();
        let mut project = Project::new();
        for file in example["files"].as_array().unwrap() {
            let name = file.as_str().unwrap();
            if !name.ends_with(".res") {
                continue;
            }
            let path = dir.join(id).join(name);
            let source = std::fs::read_to_string(&path).unwrap();
            if let Err(error) = project.compile(path.to_str().unwrap(), &source) {
                panic!("example {id}, {name}:\n{error}");
            }
            assert_eq!(project.warnings, "", "example {id}, {name}");
        }
    }
}

#[test]
fn an_instance_is_generated_once() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let js = compile_ok(
        &mut project,
        "Twice.res",
        r#"
type point = {x: float, y: float}
type line = {from: point, to: point}

let a = (l: line) => Json.encode(l)
let b = (p: point) => Json.encode(p)
let c = (xs: array<float>) => Json.encode(xs)
let d = (p: point, n: float) => (Json.encode(p), Json.encode(n))
"#,
    );
    let expanded = project.expanded.clone().unwrap();
    for name in ["encode$point", "encode$float", "encode$line", "encode$array_float"] {
        assert_eq!(expanded.matches(&format!("{name} = (")).count(), 1, "{name}\n{expanded}");
    }
    assert!(!expanded.contains("$2"), "{expanded}");
    assert_eq!(js.matches("function encode$point(").count(), 1, "{js}");
}

#[test]
fn an_instance_moves_to_the_first_item_that_needs_it() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    // `tree` is needed by the first item only through `forest`, which is
    // found a pass after the second item made `encode$tree`.
    let js = compile_ok(
        &mut project,
        "Forest.res",
        r#"
type rec tree = {value: int, children: array<tree>}
type forest = {trees: array<tree>, name: option<string>}

let a = (f: forest) => Json.encode(f)
let b = (t: tree) => Json.encode(t)
"#,
    );
    let expanded = project.expanded.clone().unwrap();
    for name in ["encode$tree", "encode$forest", "encode$int", "encode$array_tree"] {
        assert_eq!(expanded.matches(&format!("{name} = (")).count(), 1, "{name}\n{expanded}");
    }
    assert_eq!(js.matches("function encode$tree(").count(), 1, "{js}");
    // One group, before the first item.
    assert_eq!(expanded.matches("@res.macroInstances").count(), 1, "{expanded}");
}

fn compile_err(project: &mut Project, filename: &str, source: &str) -> String {
    match project.compile(filename, source) {
        Ok(js) => panic!("{filename} compiled:\n{js}"),
        Err(error) => {
            println!("--- {filename}\n{error}");
            error
        }
    }
}

#[test]
fn misuse_is_explained() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    compile_ok(&mut project, "Debug.res", DEBUG);

    let error = compile_err(
        &mut project,
        "Same.res",
        "open Macro\n@macro\nlet one = (): code<int> => %code(1)\nlet x = %Same.one()\n",
    );
    assert!(error.contains("cannot be used in the file that defines it"), "{error}");
    assert!(error.contains("Same.res:4:9"), "{error}");

    let error = compile_err(&mut project, "Unknown.res", "let x = %Nope.f(1)\n");
    assert!(error.contains("The macro `Nope.f` cannot be found."), "{error}");

    let error = compile_err(&mut project, "Plain.res", "let x = %Stdlib.Int.toString(1)\n");
    assert!(error.contains("is not a macro"), "{error}");

    let error = compile_err(&mut project, "Arity.res", "let x = %Debug.dbg\n");
    assert!(error.contains("takes 1 argument, and 0 are given"), "{error}");

    let error = compile_err(&mut project, "Hole.res", "let x = ${1}\n");
    assert!(error.contains("can only be used inside a quote"), "{error}");
    assert!(error.contains("Hole.res:1:9"), "{error}");

    let error = compile_err(&mut project, "Kind.res", "type t = %Debug.dbg(int)\n");
    assert!(error.contains("does not return a type"), "{error}");

    // The generated code is type checked like written code.
    let error = compile_err(&mut project, "TypeErr.res", "let x: string = %Debug.dbg(1 + 1)\n");
    assert!(error.contains("This has type: int"), "{error}");
}

#[test]
fn macro_code_has_no_clock_and_no_random_numbers() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Rand.res",
        "open Macro\n@macro\nlet r = (): code<float> => Code.float(Math.random())\n@macro\nlet now = (): code<float> => Code.float(Date.now())\n",
    );
    let error = compile_err(&mut project, "UseRand.res", "let x = %Rand.r()\n");
    assert!(error.contains("Math.random is not available at compile time"), "{error}");
    let error = compile_err(&mut project, "UseNow.res", "let x = %Rand.now()\n");
    assert!(error.contains("Date.now is not available at compile time"), "{error}");
}

#[test]
fn generated_syntax_errors_show_the_generated_code() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Bad.res",
        "open Macro\n@macro\nlet bad = (): code<int> => Code.raw(\"1 +\")\n",
    );
    let error = compile_err(&mut project, "UseBad.res", "let x = %Bad.bad()\n");
    assert!(error.contains("A macro generated code with a syntax error"), "{error}");
    assert!(error.contains("let x = (1 +)"), "{error}");
}

#[test]
fn pattern_macro() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Http.res",
        r#"
open Macro

@macro
let status = (name: string): pat =>
  switch name {
  | "ok" => %pat(200 | 201 | 204)
  | "missing" => Pat.int(404)
  | _ => error(`Http.status: unknown status "${name}"`)
  }
"#,
    );
    let js = compile_ok(
        &mut project,
        "Handle.res",
        r#"
let describe = code =>
  switch code {
  | %Http.status("ok") => "fine"
  | %Http.status("missing") => "not found"
  | _ => "other"
  }
"#,
    );
    assert!(js.contains("404"), "{js}");
    assert!(js.contains("204"), "{js}");
}

#[test]
fn macro_in_a_submodule() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Lib.res",
        "open Macro\nmodule Numbers = {\n  @macro\n  let answer = (): code<int> => %code(42)\n}\n",
    );
    let js = compile_ok(&mut project, "UseLib.res", "let x = %Lib.Numbers.answer()\n");
    assert!(js.contains("42"), "{js}");
}

#[test]
fn generic_as_a_value_and_in_a_pipe() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    let js = compile_ok(
        &mut project,
        "Values.res",
        "type p = {x: int}\nlet all = (ps: array<p>) => ps->Array.map(Json.encode)\nlet one = (p: p) => p->Json.encode\n",
    );
    assert!(js.contains("ps.map(encode$p)"), "{js}");
}

#[test]
fn companion_of_an_abstract_type() {
    let mut project = Project::new();
    compile_ok(&mut project, "Json.res", JSON);
    compile_ok(
        &mut project,
        "Money.res",
        "type t\n@new external make: int => t = \"Money\"\nlet toJson = (_: t): JSON.t => JSON.Encode.string(\"money\")\n",
    );
    let js = compile_ok(
        &mut project,
        "Invoice.res",
        "type invoice = {id: string, total: Money.t}\nlet encode = (i: invoice) => Json.encode(i)\n",
    );
    assert!(js.contains("Money.toJson(i.total)"), "{js}");
    assert!(project.expanded.as_deref().unwrap().contains("encode$Money_t"));

    compile_ok(&mut project, "Opaque.res", "type t\n");
    let error = compile_err(
        &mut project,
        "NoCompanion.res",
        "let encode = (o: Opaque.t) => Json.encode(o)\n",
    );
    assert!(error.contains("is abstract and its module has no toJson"), "{error}");
}

#[test]
fn generic_by_the_expected_type() {
    let mut project = Project::new();
    compile_ok(
        &mut project,
        "Default.res",
        r#"
open Macro

@generic
let rec value = (_: code<unit>): code<'a> =>
  switch Type.info(expected()) {
  | Int => %code(0)
  | String => %code("")
  | Bool => %code(false)
  | Array(_) => %code([])
  | Option(_) => %code(None)
  | Record({fields}) => Code.record(fields->Array.map(f => (f.name, %code(value()))))
  | _ => error(`Default.value: no default for ${Type.name(expected())}`)
  }
"#,
    );
    let js = compile_ok(
        &mut project,
        "Settings.res",
        "type settings = {name: string, retries: int, verbose: bool, tags: array<string>}\nlet initial: settings = Default.value()\n",
    );
    let expanded = project.expanded.clone().unwrap();
    assert!(expanded.contains("value$settings = "), "{expanded}");
    assert!(expanded.contains("value$array_string = "), "{expanded}");
    assert!(js.contains("retries: 0"), "{js}");
    assert!(js.contains("verbose: false"), "{js}");
}
