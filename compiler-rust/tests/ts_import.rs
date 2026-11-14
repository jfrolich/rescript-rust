//! `%ts` imports end to end: ReScript source with TypeScript files in memory
//! in, JavaScript (or a diagnostic) out.

#![cfg(feature = "ts-import")]

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};

fn runtime_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime")
}

/// A registry that type checks the runtime from its sources, so the test
/// needs no built `lib/rescript`.
fn registry() -> ModuleRegistry {
    let mut registry = ModuleRegistry::new();
    let mut entries: Vec<PathBuf> = std::fs::read_dir(runtime_dir())
        .expect("runtime sources")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    entries.sort();
    // An interface wins over its implementation.
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

fn compile(source: &str, ts: &[(&str, &str)]) -> Result<String, String> {
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        // `RESCRIPT_BACKEND=check` also compares the shadow backend's lowering.
        backend: rescript_compiler::bir::shadow::BackendMode::from_env(),
        ts_files: Some(ts.iter().map(|(path, text)| (path.to_string(), text.to_string())).collect()),
        ..Default::default()
    };
    driver::compile_source_in_process(source, "/app/src/Demo.res", "Demo", &options, &registry(), false, None)
        .map(|compiled| compiled.js_output)
        .map_err(|error| format!("{error:#}"))
}

const API: &str = r#"
export interface User { id: string; name: string; age?: number }
export type Shape = { kind: "circle"; radius: number } | { kind: "rect"; width: number; height: number };
export function getUser(id: string): Promise<User | undefined> { return null as any; }
export const add = (a: number, b: number) => a + b;
export function area(shape: Shape): number { return 0; }
export function greet(user: User, greeting?: string): string { return ""; }
export function sum(...values: number[]): number { return 0; }
export class Counter { constructor(public count: number) {} increment(): Counter { return this; } static zero(): Counter { return new Counter(0); } }
"#;

#[test]
fn values_are_typed_by_typescript() {
    let js = compile(
        r#"
let {add, greet, area, sum} = %ts("./api.ts")
let three = add(1., 2.)
let hello = greet({id: "1", name: "Ada"})
let hey = greet({id: "1", name: "Ada", age: 36.}, ~greeting="Hey")
let circle = area(Circle({radius: 2.}))
let total = sum([1., 2., 3.])
"#,
        &[("/app/src/api.ts", API)],
    )
    .unwrap();
    println!("{js}");
    assert!(js.contains("require(\"./api.ts\")"), "{js}");
    assert!(js.contains("ApiTs.add(1, 2)"), "{js}");
    assert!(js.contains("kind: \"circle\""), "{js}");
    assert!(js.contains("sum(1, 2, 3)"), "{js}");
}

#[test]
fn a_wrong_argument_is_a_type_error_at_the_call() {
    let error = compile(
        r#"
let {add} = %ts("./api.ts")
let three = add("1", 2.)
"#,
        &[("/app/src/api.ts", API)],
    )
    .unwrap_err();
    println!("{error}");
    assert!(error.contains("string") && error.contains("float"), "{error}");
}

#[test]
fn types_modules_and_classes() {
    let js = compile(
        r#"
type user = %ts("./api.ts#User")
module Api = %ts("./api.ts")
module Counter = %ts("./api.ts#Counter")
let ada: user = {id: "1", name: "Ada"}
let name = ada.name
let fetched = Api.getUser("1")
let counter = Counter.make(1.)
let next = counter.increment()
let zero = Counter.zero()
"#,
        &[("/app/src/api.ts", API)],
    )
    .unwrap();
    println!("{js}");
    assert!(js.contains("new ApiTs.Counter(1)"), "{js}");
    assert!(js.contains("counter.increment()"), "{js}");
}

#[test]
fn a_missing_export_is_reported_at_the_import() {
    let error = compile(
        "let {nope} = %ts(\"./api.ts\")\n",
        &[("/app/src/api.ts", API)],
    )
    .unwrap_err();
    println!("{error}");
    assert!(error.contains("has no export named `nope`"), "{error}");
    assert!(error.contains("Demo.res"), "{error}");
}

/// Everything the converter generates for `ts-import/tests/fixtures/features.ts`
/// (one export per TypeScript feature) is ReScript the type checker accepts.
#[test]
fn every_catalog_declaration_type_checks() {
    let features = Path::new(env!("CARGO_MANIFEST_DIR")).join("../ts-import/tests/fixtures/features.ts");
    let features = std::fs::read_to_string(features).unwrap();
    let js = compile(
        r#"
module Features = %ts("./features.ts")
let point: Features.point = {x: 1., y: 2.}
let direction: Features.direction = #up
let shape = Features.Circle({radius: 1.})
let json = Features.Array([Features.String("a"), Features.Null])
let dog = Features.Dog.make("Rex")
let fetched = dog.fetch("ball")
"#,
        &[("/app/src/features.ts", &features)],
    );
    match js {
        Ok(js) => assert!(js.contains("new FeaturesTs.Dog(\"Rex\")"), "{js}"),
        Err(error) => panic!("{error}"),
    }
}

/// The examples of the documentation page (`ts-import/site/examples`) compile,
/// except the ones that show an error.
#[test]
fn site_examples_compile() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../ts-import/site/examples");
    let index = std::fs::read_to_string(root.join("index.json")).unwrap();
    let index: serde_json::Value = serde_json::from_str(&index).unwrap();
    for example in index.as_array().unwrap() {
        let id = example["id"].as_str().unwrap();
        let mut ts: Vec<(String, String)> = Vec::new();
        let mut source = String::new();
        for name in example["files"].as_array().unwrap() {
            let name = name.as_str().unwrap();
            let text = std::fs::read_to_string(root.join(id).join(name)).unwrap();
            if name.ends_with(".res") {
                source = text;
            } else {
                ts.push((format!("/app/src/{name}"), text));
            }
        }
        let ts: Vec<(&str, &str)> = ts.iter().map(|(path, text)| (path.as_str(), text.as_str())).collect();
        let result = compile(&source, &ts);
        let fails = example["fails"].as_bool().unwrap_or(false);
        match result {
            Ok(_) if fails => panic!("{id} compiles, but is marked as failing"),
            Err(error) if !fails => panic!("{id} does not compile:\n{error}"),
            _ => {}
        }
    }
}

/// Two compilations on one thread that both type check the runtime from
/// source: the second must not see declarations of the first.
#[test]
fn classes_and_symbols_are_cases_of_a_union() {
    let ts = r#"
export class Vehicle { constructor(public wheels: number) {} }
export class Car extends Vehicle { honk(): string { return "beep"; } }
export function park(what: Car | Vehicle | string): void {}
export function on(name: string | symbol, target: URL | Date): void {}
"#;
    let js = compile(
        r#"
module Garage = %ts("./garage.ts")

let describe = (what: Garage.parkWhat) =>
  switch what {
  | String(plate) => plate
  | Car(car) => car.honk()
  | Vehicle(vehicle) => Float.toString(vehicle.wheels)
  }
let isSymbol = (name: Garage.onName) =>
  switch name {
  | Symbol(_) => true
  | String(_) => false
  }
let isUrl = (target: Garage.onTarget) =>
  switch target {
  | Url(_) => true
  | Date(_) => false
  }
let car = Garage.Car.make(4.)
Garage.park(Car(car))
Garage.park(Vehicle((car :> Garage.vehicle)))
"#,
        &[("/app/src/garage.ts", ts)],
    )
    .unwrap();
    // The class is the module's export, and the subclass is tested first.
    assert!(js.contains("require(\"./garage.ts\")"), "{js}");
    // so the superclass is what is left and needs no test.
    assert!(js.contains("what instanceof GarageTs.Car"), "{js}");
    assert!(!js.contains("instanceof GarageTs.Vehicle"), "{js}");
    assert!(js.contains("typeof name !== \"string\""), "{js}");
    assert!(js.contains("!(target instanceof Date)"), "{js}");
}

/// Whole modules of real packages compile. The packages are those the
/// repository installs for its own tooling; without `node_modules` (or
/// `TS_IMPORT_PACKAGES`, a directory that has one) there is nothing to
/// check.
#[test]
fn installed_packages_compile() {
    // Declaration files of large packages nest deeply; builds compile on
    // threads with a stack this size too.
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(compile_installed_packages)
        .expect("thread")
        .join()
        .expect("installed packages compile");
}

fn compile_installed_packages() {
    let root = match std::env::var("TS_IMPORT_PACKAGES") {
        Ok(dir) => PathBuf::from(dir),
        Err(_) => Path::new(env!("CARGO_MANIFEST_DIR")).join(".."),
    };
    let Ok(root) = root.canonicalize() else { return };
    let installed = |package: &str| root.join("node_modules").join(package).is_dir();
    let mut modules: Vec<&str> = Vec::new();
    if installed("@types/node") {
        modules.extend([
            "node:events",
            "node:url",
            "node:path",
            "node:os",
            "node:child_process",
            "node:fs",
            "node:http",
        ]);
    }
    for (package, types) in [
        ("semver", "@types/semver"),
        ("chalk", "chalk"),
        ("react", "@types/react"),
        ("react-dom", "@types/react-dom"),
        ("vite", "vite"),
    ] {
        if installed(package) && installed(types) {
            modules.push(package);
        }
    }
    let file = root.join("Importer.res").to_string_lossy().to_string();
    let mut failures = Vec::new();
    for module in modules {
        let source = format!("module M = %ts(\"{module}\")\n");
        let options = CompilerOptions {
            source_filename: Some(file.clone()),
            module_name: Some("Importer".to_string()),
            ..Default::default()
        };
        if let Err(error) =
            driver::compile_source_in_process(&source, &file, "Importer", &options, &registry(), false, None)
        {
            let text = format!("{error:#}");
            let kept: Vec<&str> = text.split("\n\n\n").filter(|part| !part.contains("Warning number")).collect();
            failures.push(format!("{module}:\n{}", kept.join("\n").chars().take(1500).collect::<String>()));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn compilations_on_one_thread_are_independent() {
    compile("let x = Array.length([1])", &[]).unwrap();
    compile("let y = Array.length([1])", &[]).unwrap();
}

/// Runs `js` (CommonJS, with no imports left) and `check` under Node, and
/// returns what it prints; `None` without Node.
fn run_node(js: &str, check: &str) -> Option<String> {
    let dir = std::env::temp_dir().join(format!("ts-import-node-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let file = dir.join(format!("run-{}.js", js.len()));
    std::fs::write(&file, format!("{js}\n{check}\n")).ok()?;
    let output = std::process::Command::new("node").arg(&file).output().ok()?;
    let _ = std::fs::remove_file(&file);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    Some(String::from_utf8_lossy(&output.stdout).into_owned())
}

#[test]
fn a_member_with_only_the_tag_is_an_object() {
    let ts = r#"
export type Shape = { kind: "circle"; radius: number } | { kind: "point" };
"#;
    let js = compile(
        r#"
module Shapes = %ts("./shapes.ts")

let describe = (shape: Shapes.shape) =>
  switch shape {
  | Circle({radius}) => `circle ${Float.toString(radius)}`
  | Point(_) => "point"
  }
let point: Shapes.shape = Point({})
"#,
        &[("/app/src/shapes.ts", ts)],
    )
    .unwrap();
    // `{kind: "point"}`, not the string "point".
    assert!(js.contains(r#"kind: "point""#), "{js}");
    let check = r#"
console.log(JSON.stringify(exports.point));
console.log(exports.describe({kind: "point"}), exports.describe({kind: "circle", radius: 2}));
"#;
    if let Some(output) = run_node(&js, check) {
        assert_eq!(output, "{\"kind\":\"point\"}\npoint circle 2\n", "{js}");
    }
}
