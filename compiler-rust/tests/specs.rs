//! `@spec` (docs/verify/spec.md): what a build and `rescript verify` compile
//! a spec to, what the runner is told about its states and actions, and the
//! reports for specs that cannot be checked.

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::verify::Checks;
use rescript_compiler::verify::laws::Item;
use serde_json::json;

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
type state = {count: int, on: bool}
type action = Increment | Toggle

let reduce = (state, action) =>
  switch action {
  | Increment => {...state, count: mod(state.count + 1, 3)}
  | Toggle => {...state, on: !state.on}
  }

@spec
let counter: Spec.t<state, action> = {
  init: {count: 0, on: false},
  step: reduce,
  always: state => state.count < 3,
}
"#;

#[test]
fn a_build_leaves_specs_out() {
    let (js, items) = compile(PROGRAM, Checks::LeftOut, false).unwrap();
    assert!(js.contains("function reduce(state, action)"), "{js}");
    assert!(!js.contains("counter"), "{js}");
    assert!(items.is_empty());
}

#[test]
fn verify_exports_specs() {
    let (js, items) = compile(PROGRAM, Checks::kept(), false).unwrap();
    assert!(js.contains("exports.counter = counter;"), "{js}");
    assert_eq!(items.len(), 1);
    assert_eq!(items[0].kind, "spec");
    assert_eq!(items[0].path, ["counter"]);
    assert_eq!(items[0].line, 11);
    let detail = &items[0].detail;
    assert_eq!(detail["actions"], "all");
    assert_eq!(detail["state"], json!({ "k": "named", "id": "state" }));
    assert_eq!(detail["action"], json!({ "k": "named", "id": "action" }));
    assert_eq!(detail["defs"]["state"]["fields"][0]["n"], "count");
    assert_eq!(detail["defs"]["action"]["cases"][1]["n"], "Toggle");
}

/// The description of a program's only spec.
#[track_caller]
fn detail(source: &str) -> serde_json::Value {
    let items = items(source);
    assert_eq!(items.len(), 1, "{source}");
    items[0].detail.clone()
}

#[test]
fn a_spec_with_actions_can_have_any_action_type() {
    let detail = detail(
        r#"
type action = Add(int) | Clear
@spec
let sum: Spec.t<int, action> = {
  init: 0,
  step: (total, action) =>
    switch action {
    | Add(n) => total + n
    | Clear => 0
    },
  actions: total => total < 3 ? [Add(1), Clear] : [Clear],
  always: total => total <= 3,
}
"#,
    );
    assert_eq!(detail["actions"], "given");
    assert_eq!(detail["state"], json!({ "k": "int" }));
}

#[test]
fn a_spec_without_actions_needs_few_of_them() {
    rejected(
        r#"
type action = Add(int) | Clear
@spec
let sum: Spec.t<int, action> = {
  init: 0,
  step: (total, action) =>
    switch action {
    | Add(n) => total + n
    | Clear => 0
    },
  always: total => total >= 0,
}
"#,
        &[
            "The actions of the spec `sum` cannot be listed: the type has too many values",
            "Give this one `actions: state => [...]`",
        ],
    );
    rejected(
        r#"
@spec
let callbacks: Spec.t<int, int => int> = {
  init: 0,
  step: (total, f) => f(total),
  always: total => total >= 0,
}
"#,
        &["cannot be listed: it has a function in it"],
    );
}

#[test]
fn a_state_is_printed_as_far_as_its_type_is_known() {
    let detail = detail(
        r#"
module Id: {
  type t
  @pure
  let first: t
} = {
  type t = int
  let first = 1
}
type state = {id: Id.t, open_: bool}
@spec
let door: Spec.t<state, bool> = {
  init: {id: Id.first, open_: false},
  step: (state, open_) => {...state, open_},
  sometimes: state => state.open_,
}
"#,
    );
    assert_eq!(
        detail["defs"]["state"]["fields"][0]["s"],
        json!({ "k": "opaque" })
    );
    assert_eq!(
        detail["defs"]["state"]["fields"][1]["s"],
        json!({ "k": "bool" })
    );
    assert_eq!(detail["action"], json!({ "k": "bool" }));
}

#[test]
fn a_spec_built_from_another_value_is_looked_at_when_run() {
    let detail = detail(
        r#"
@pure
let machine: Spec.t<bool, unit> = {init: false, step: (on, ()) => !on}
@spec
let flips: Spec.t<bool, unit> = {...machine, sometimes: on => on}
"#,
    );
    assert_eq!(detail["actions"], "unknown");
}

#[test]
fn a_spec_is_a_spec() {
    rejected(
        "@spec\nlet notOne = (state: int) => state > 0\n",
        &[
            "A spec is a `Spec.t<state, action>`",
            "let notOne: Spec.t<state, action> = {init: ..., step: ..., always: state => ...}",
        ],
    );
}

#[test]
fn a_spec_checks_something() {
    rejected(
        "@spec\nlet idle: Spec.t<int, bool> = {init: 0, step: (n, _) => n}\n",
        &[
            "The spec `idle` checks nothing.",
            "`always`, `sometimes`, `reachable` or `eventually`",
        ],
    );
}

#[test]
fn a_spec_is_pure() {
    rejected(
        r#"
@spec
let noisy: Spec.t<int, bool> = {
  init: 0,
  step: (n, _) => {
    Console.log(n)
    n
  },
  always: n => n == 0,
}
"#,
        &["The external `Console.log` is not marked @pure"],
    );
}

#[test]
fn nothing_refers_to_a_spec() {
    rejected(
        r#"
@spec
let flips: Spec.t<bool, unit> = {init: false, step: (on, ()) => !on, sometimes: on => on}
let start = flips.init
"#,
        &["flips"],
    );
}
