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
/// needs no built `lib/ocaml`.
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
