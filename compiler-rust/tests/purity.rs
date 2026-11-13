//! `@pure` and `@mutates` (docs/verify/pure.md): programs the check accepts
//! and the reports for the ones it rejects.

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

fn compile(source: &str) -> Result<String, String> {
    compile_with(source, false)
}

/// Type checks only: the JavaScript of a program that calls the runtime
/// needs the runtime's compiled modules.
fn check(source: &str) -> Result<String, String> {
    compile_with(source, true)
}

fn compile_with(source: &str, check_only: bool) -> Result<String, String> {
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Never,
    );
    let options = CompilerOptions {
        source_filename: Some("/app/src/Demo.res".to_string()),
        module_name: Some("Demo".to_string()),
        check_only,
        ..Default::default()
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

#[track_caller]
fn accepted(source: &str) -> String {
    match check(source) {
        Ok(js) => js,
        Err(report) => panic!("expected the program to compile:\n{source}\n{report}"),
    }
}

/// The program is rejected, and its report has every fragment.
#[track_caller]
fn rejected(source: &str, fragments: &[&str]) {
    match check(source) {
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

#[test]
fn a_pure_function_compiles_to_the_same_javascript() {
    let with = compile("@pure\nlet add = (a, b) => a + b\n").unwrap();
    let without = compile("let add = (a, b) => a + b\n").unwrap();
    assert!(with.contains("function add(a, b)"), "{with}");
    assert_eq!(with, without);
}

#[test]
fn standard_library_calls_and_data() {
    accepted(
        r#"
type point = {x: int, y: int}
type shape = Circle(float) | Rect(point, point)

@pure
let total = xs => xs->Array.map(x => x * 2)->Array.reduce(0, (a, b) => a + b)

@pure
let area = shape =>
  switch shape {
  | Circle(r) => Math.Constants.pi *. r *. r
  | Rect(a, b) => Int.toFloat(Math.Int.abs(b.x - a.x) * Math.Int.abs(b.y - a.y))
  }

@pure
let move = (p, dx) => {...p, x: p.x + dx}

@pure
let label = (name, n) => `${name}: ${Int.toString(n)}`

@pure
let first = xs =>
  switch xs->List.fromArray {
  | list{x, ..._} => Some(x)
  | list{} => None
  }
"#,
    );
}

#[test]
fn a_function_may_change_what_it_creates() {
    accepted(
        r#"
@pure
let sum = xs => {
  let total = ref(0)
  for i in 0 to Array.length(xs) - 1 {
    total := total.contents + xs->Array.getUnsafe(i)
  }
  total.contents
}

@pure
let evens = xs => {
  let out = []
  xs->Array.forEach(x =>
    if mod(x, 2) == 0 {
      out->Array.push(x)
    }
  )
  out
}

@pure
let index = xs => {
  let seen = Dict.make()
  xs->Array.forEachWithIndex((x, i) => seen->Dict.set(x, i))
  seen
}

type counter = {mutable count: int}

@pure
let count = xs => {
  let c = {count: 0}
  xs->Array.forEach(_ => c.count = c.count + 1)
  c.count
}

@pure
let sorted = xs => {
  let copy = xs->Array.copy
  copy->Array.sort((a, b) => Float.fromInt(a - b))
  copy
}
"#,
    );
}

#[test]
fn a_local_function_that_changes_a_local_can_be_called() {
    accepted(
        r#"
@pure
let collect = n => {
  let out = []
  let add = x => out->Array.push(x)
  for i in 1 to n {
    add(i)
  }
  out
}
"#,
    );
}

#[test]
fn functions_of_the_file_are_looked_into() {
    accepted(
        r#"
let double = x => x * 2
let rec fact = n => n <= 1 ? 1 : n * fact(n - 1)
let limit = 10

module Helpers = {
  let clamp = x => x > limit ? limit : x
}

@pure
let f = x => Helpers.clamp(fact(double(x)))
"#,
    );
}

#[test]
fn a_function_argument_is_called_as_given() {
    accepted(
        r#"
@pure
let twice = (f, x) => f(f(x))

@pure
let apply = (xs, f) => xs->Array.map(f)
"#,
    );
}

#[test]
fn raising_and_catching_is_pure() {
    accepted(
        r#"
exception Negative(int)

@pure
let check = n => n < 0 ? throw(Negative(n)) : n

@pure
let safe = n =>
  try check(n) catch {
  | Negative(_) => 0
  }
"#,
    );
}

#[test]
fn mutates_changes_its_first_argument() {
    accepted(
        r#"
type buffer = {mutable items: array<string>, mutable size: int}

@mutates
let add = (buffer, item) => {
  buffer.items = buffer.items->Array.concat([item])
  buffer.size = buffer.size + 1
}

@pure
let fromArray = items => {
  let buffer = {items: [], size: 0}
  items->Array.forEach(item => buffer->add(item))
  buffer
}
"#,
    );
}

#[test]
fn an_external_is_taken_on_trust() {
    accepted(
        r#"
@pure @val external parseFloat: string => float = "parseFloat"
@pure @send external padStart: (string, int, string) => string = "padStart"
@pure(unchecked)
let hash: string => int = %raw(`s => s.length`)

@pure
let f = s => parseFloat(s->padStart(4, "0")) +. Int.toFloat(hash(s))
"#,
    );
}

#[test]
fn unchecked_skips_the_check() {
    accepted(
        r#"
@pure(unchecked)
let now = () => Date.now()

@pure
let f = () => now()
"#,
    );
}

#[test]
fn an_effect_is_rejected() {
    rejected(
        "@pure\nlet now = () => Date.now()\n",
        &["`Date.now` is not marked @pure", "`now` is @pure"],
    );
    rejected(
        "@pure\nlet roll = () => Math.random()\n",
        &["`Math.random` is not marked @pure"],
    );
    rejected(
        "@pure\nlet log = x => {\n  Console.log(x)\n  x\n}\n",
        &[
            "`Console.log` is not marked @pure",
            "/app/src/Demo.res:3:3-13",
        ],
    );
}

#[test]
fn changing_an_argument_is_rejected() {
    rejected(
        "@pure\nlet add = (xs, x) => {\n  xs->Array.push(x)\n  xs\n}\n",
        &["This changes `xs`, and `add` did not create it"],
    );
    rejected(
        "type t = {mutable n: int}\n@pure\nlet bump = t => {\n  t.n = t.n + 1\n  t\n}\n",
        &["This changes `t`, and `bump` did not create it"],
    );
    rejected("@pure\nlet reset = r => r := 0\n", &["This changes `r`"]);
    // An alias is not a new value.
    rejected(
        "@pure\nlet add = (xs, x) => {\n  let ys = xs\n  ys->Array.push(x)\n  ys\n}\n",
        &["This changes `ys`, and `add` did not create it"],
    );
    // A part of a value the function created may be shared.
    rejected(
        "type t = {items: array<int>}\n@pure\nlet add = (items, x) => {\n  let t = {items: items}\n  t.items->Array.push(x)\n  t\n}\n",
        &["This changes a value that `add` did not create itself"],
    );
}

#[test]
fn state_outside_the_function_is_rejected() {
    rejected(
        "let counter = ref(0)\n@pure\nlet next = () => counter.contents + 1\n",
        &["`counter` is defined outside `next` and its type lets it change"],
    );
    rejected(
        "let counter = ref(0)\n@pure\nlet bump = () => counter := counter.contents + 1\n",
        &["This changes `counter`, and it is defined outside this function"],
    );
    rejected(
        "let cache: dict<int> = Dict.make()\n@pure\nlet lookup = key => cache->Dict.get(key)\n",
        &["`cache` is defined outside `lookup`"],
    );
}

#[test]
fn an_unmarked_external_is_rejected() {
    rejected(
        "@val external now: unit => float = \"performance.now\"\n@pure\nlet f = () => now()\n",
        &["The external `now` is not marked @pure"],
    );
}

#[test]
fn an_impure_function_of_the_file_is_rejected() {
    rejected(
        "let stamp = x => {\n  Console.log(x)\n  x\n}\n@pure\nlet f = x => stamp(x)\n",
        &[
            "`stamp` is not pure, and `f` is @pure",
            "Line 2: The external `Console.log` is not marked @pure.",
        ],
    );
}

#[test]
fn a_function_that_keeps_state_cannot_leave() {
    rejected(
        "@pure\nlet counter = () => {\n  let n = ref(0)\n  () => {\n    n := n.contents + 1\n    n.contents\n  }\n}\n",
        &["This function changes `n`, which was created outside it"],
    );
    rejected(
        "@pure\nlet counter = () => {\n  let n = ref(0)\n  let next = () => {\n    n := n.contents + 1\n    n.contents\n  }\n  next\n}\n",
        &["`next` changes a value created outside it"],
    );
}

#[test]
fn async_and_raw_are_rejected() {
    rejected(
        "@pure\nlet f = async x => x + 1\n",
        &["An async function is not pure"],
    );
    rejected(
        "@pure\nlet f = x => x + %raw(`Date.now()`)\n",
        &["%raw is JavaScript, which the compiler cannot check"],
    );
}

#[test]
fn a_mutating_function_is_only_called() {
    rejected(
        "@pure\nlet f = xs => {\n  let push = Array.push\n  push(xs, 1)\n}\n",
        &["`Array.push` changes its first argument"],
    );
}

#[test]
fn the_argument_of_the_attribute_is_checked() {
    rejected(
        "@pure(trusted)\nlet f = x => x\n",
        &["@pure takes no argument, or `unchecked`"],
    );
}

#[test]
fn a_signature_requires_the_effect_it_declares() {
    accepted(
        r#"
module type Ord = {
  type t
  @pure
  let compare: (t, t) => Ordering.t
}

module Reversed = {
  type t = int
  let compare = (a, b) => Int.compare(b, a)
}

module Max = (O: Ord) => {
  @pure
  let max = (a, b) => Ordering.isGreater(O.compare(a, b)) ? a : b
}

module ReversedMax = Max(Reversed)
module StringMax = Max(String)
"#,
    );
    rejected(
        r#"
module type Ord = {
  type t
  @pure
  let compare: (t, t) => int
}

module Logged = {
  type t = int
  let compare = (a, b) => {
    Console.log2(a, b)
    a - b
  }
}

module Max = (O: Ord) => {
  @pure
  let max = (a, b) => O.compare(a, b) >= 0 ? a : b
}

module LoggedMax = Max(Logged)
"#,
        &["`Console.log2` is not marked @pure, and `compare` is @pure"],
    );
    rejected(
        r#"
module Counter: {
  @pure
  let next: int => int
} = {
  let calls = ref(0)
  let next = n => {
    calls := calls.contents + 1
    n + 1
  }
}
"#,
        &["This changes `calls`"],
    );
}
