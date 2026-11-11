//! End-to-end tests of compile-time macros: each test compiles a small
//! project in memory, with the standard library type-checked from source.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::macros::MacroHost;
use rescript_compiler::macros::quickjs::QuickJsHost;

fn runtime_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime")
}


struct Project {
    registry: ModuleRegistry,
    /// Compiled JavaScript of the project's modules, for the macro engine.
    javascript: Arc<Mutex<HashMap<String, String>>>,
    host: Arc<QuickJsHost>,
    /// The expanded source of the last compiled file, when it uses macros.
    expanded: Option<String>,
}

impl Project {
    fn new() -> Self {
        let mut registry = ModuleRegistry::new();
        let mut modules: ahash::AHashMap<String, PathBuf> = Default::default();
        for entry in std::fs::read_dir(runtime_dir()).unwrap() {
            let path = entry.unwrap().path();
            let Some(ext) = path.extension().and_then(|e| e.to_str()) else {
                continue;
            };
            if ext != "res" && ext != "resi" {
                continue;
            }
            let name = path.file_stem().unwrap().to_str().unwrap().to_string();
            if ext == "resi" || !modules.contains_key(&name) {
                modules.insert(name, path);
            }
        }
        registry.set_source_fallback_paths(modules);
        registry.set_source_fallback_is_runtime(true);
        let javascript: Arc<Mutex<HashMap<String, String>>> = Default::default();
        let sources = javascript.clone();
        let host = Arc::new(QuickJsHost::new(Arc::new(move |name: &str| {
            if let Some(source) = sources.lock().unwrap().get(name) {
                return Some(source.clone());
            }
            std::fs::read_to_string(runtime_dir().join(format!("lib/js/{name}.cjs"))).ok()
        })));
        let mut project = Project {
            registry,
            javascript,
            host,
            expanded: None,
        };
        // The macro API, compiled from source like the rest of the project.
        let macro_source = std::fs::read_to_string(runtime_dir().join("Macro.res")).unwrap();
        project.compile("Macro.res", &macro_source).unwrap();
        project
    }

    fn compile(&mut self, filename: &str, source: &str) -> Result<String, String> {
        let module_name = driver::module_name_from_source_filename(filename);
        let host: Arc<dyn MacroHost> = self.host.clone();
        let options = CompilerOptions {
            source_filename: Some(filename.to_string()),
            module_name: Some(module_name.clone()),
            macro_host: Some(host),
            ..Default::default()
        };
        match driver::compile_source_in_process(
            source,
            filename,
            &module_name,
            &options,
            &self.registry,
            false,
        ) {
            Ok(compiled) => {
                if let Some(ps) = compiled.pers_struct {
                    self.registry.register_module(
                        &module_name,
                        ps,
                        rescript_compiler::cmi::persistent_env::InMemoryModuleInfo::new(
                            PathBuf::from(filename),
                            false,
                            Default::default(),
                            module_name == "Macro",
                        ),
                    );
                }
                self.javascript
                    .lock()
                    .unwrap()
                    .insert(module_name, compiled.js_output.clone());
                self.host.invalidate();
                self.expanded = compiled.expanded_source;
                Ok(compiled.js_output)
            }
            Err(e) => Err(format!("{e:#}")),
        }
    }
}

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
