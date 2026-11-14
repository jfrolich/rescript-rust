//! Proofs of laws (docs/verify/proof.md): what the prover shows for every
//! value, what it leaves to a run, and that it does not prove what is false.

use std::path::{Path, PathBuf};

use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use rescript_compiler::driver::{self, CompilerOptions};
use rescript_compiler::verify::Checks;
use rescript_compiler::verify::laws::Item;
use serde_json::{Value, json};

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

/// What the prover says about each law of a program, by name.
#[track_caller]
fn proofs(source: &str) -> Vec<(String, Value)> {
    items(source)
        .into_iter()
        .map(|item| (item.path.join("."), item.detail["proof"].clone()))
        .collect()
}

#[track_caller]
fn proved(source: &str) -> Vec<(String, Value)> {
    let proofs = proofs(source);
    for (name, proof) in &proofs {
        assert_eq!(proof["status"], "proved", "{name}: {proof}");
    }
    proofs
}

/// The reason the only law of a program is not proved.
#[track_caller]
fn unproved(source: &str) -> String {
    let proofs = proofs(source);
    let (name, proof) = proofs.last().expect("a law");
    assert_eq!(proof["status"], "unproved", "{name}: {proof}");
    proof["reason"].as_str().unwrap().to_string()
}

const LISTS: &str = r#"
let rec append = (xs, ys) =>
  switch xs {
  | list{} => ys
  | list{x, ...rest} => list{x, ...append(rest, ys)}
  }

let rec length = xs =>
  switch xs {
  | list{} => 0
  | list{_, ...rest} => 1 + length(rest)
  }

let rec reverse = xs =>
  switch xs {
  | list{} => list{}
  | list{x, ...rest} => append(reverse(rest), list{x})
  }
"#;

#[test]
fn induction_on_a_list() {
    let proofs = proved(&format!(
        "{LISTS}
@law
let appendNil = (xs: list<int>) => append(xs, list{{}}) == xs

@law
let lengthAppend = (xs: list<int>, ys: list<int>) =>
  length(append(xs, ys)) == length(xs) + length(ys)
"
    ));
    assert_eq!(proofs[0].1["induction"], json!(["xs"]));
    assert_eq!(proofs[1].1["induction"], json!(["xs"]));
    assert_eq!(proofs[1].1["lemmas"], json!([]));
}

#[test]
fn earlier_laws_are_lemmas() {
    let laws = "
@law
let appendNil = (xs: list<int>) => append(xs, list{}) == xs

@law
let appendAssoc = (xs: list<int>, ys: list<int>, zs: list<int>) =>
  append(append(xs, ys), zs) == append(xs, append(ys, zs))

@law
let reverseAppend = (xs: list<int>, ys: list<int>) =>
  reverse(append(xs, ys)) == append(reverse(ys), reverse(xs))

@law
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs
";
    let proofs = proved(&format!("{LISTS}{laws}"));
    assert_eq!(proofs[2].1["lemmas"], json!(["appendNil", "appendAssoc"]));
    assert_eq!(proofs[3].1["lemmas"], json!(["reverseAppend"]));

    // Without the lemma the last law is not proved.
    let alone = "
@law
let reverseTwice = (xs: list<int>) => reverse(reverse(xs)) == xs
";
    unproved(&format!("{LISTS}{alone}"));
}

#[test]
fn induction_on_a_tree() {
    proved(
        r#"
type rec tree = Leaf | Node(tree, int, tree)

let rec size = tree =>
  switch tree {
  | Leaf => 0
  | Node(left, _, right) => size(left) + 1 + size(right)
  }

let rec mirror = tree =>
  switch tree {
  | Leaf => Leaf
  | Node(left, value, right) => Node(mirror(right), value, mirror(left))
  }

@law
let mirrorTwice = (t: tree) => mirror(mirror(t)) == t

@law
let mirrorKeepsSize = (t: tree) => size(mirror(t)) == size(t)
"#,
    );
}

#[test]
fn two_inductions() {
    let proofs = proved(
        r#"
type rec nat = Zero | Succ(nat)

let rec add = (a, b) =>
  switch a {
  | Zero => b
  | Succ(rest) => Succ(add(rest, b))
  }

@law
let addCommutes = (a: nat, b: nat) => add(a, b) == add(b, a)
"#,
    );
    assert_eq!(proofs[0].1["induction"], json!(["a", "b"]));
}

#[test]
fn cases_and_integers() {
    proved(
        r#"
type coupon = Percent(int) | Fixed(int) | FreeShipping
type order = {amount: int, coupon: coupon}

let discount = order =>
  switch order.coupon {
  | Fixed(n) => n
  | Percent(_) | FreeShipping => 0
  }

let clamp = (x, low, high) => x < low ? low : x > high ? high : x

@law
let discountIsWhatWasTakenOff = (order: order) =>
  order.amount - discount(order) + discount(order) == order.amount

@law
let clampStaysInRange = (x: int, low: int, high: int) =>
  low > high || {
      let clamped = clamp(x, low, high)
      low <= clamped && clamped <= high
    }

@law
let squareOfSum = (a: int, b: int) => (a + b) * (a + b) == a * a + 2 * a * b + b * b

@law
let orderIsTransitive = (a: int, b: int, c: int) => !(a <= b && b < c) || a < c
"#,
    );
}

#[test]
fn what_is_false_is_not_proved() {
    // False at the largest int: `+` wraps around.
    unproved("@law\nlet successorIsLarger = (a: int) => a + 1 > a\n");
    // False for the empty list.
    let reason = unproved(&format!(
        "{LISTS}
@law
let neverEmpty = (xs: list<int>) => length(xs) > 0
"
    ));
    assert_eq!(reason, "it could not show a case to be true");
    // Not true of NaN.
    let reason = unproved("@law\nlet itself = (x: float) => x == x\n");
    assert!(reason.contains("floats"), "{reason}");
}

#[test]
fn only_total_functions_of_the_file_are_read() {
    let reason = unproved(
        "@law\nlet reverseTwice = (xs: list<int>) => List.reverse(List.reverse(xs)) == xs\n",
    );
    assert_eq!(
        reason,
        "it uses `List.reverse`, which is defined in another file"
    );

    // `loop` never returns, so a law about it never returns `true`.
    let reason = unproved(
        r#"
let rec loop = (xs: list<int>) => loop(list{1, ...xs})

@law
let loops = (xs: list<int>) => loop(xs) == loop(xs)
"#,
    );
    assert_eq!(
        reason,
        "`loop` is recursive, and not on a part of one of its arguments"
    );

    let reason = unproved("@law\nlet halves = (a: int, b: int) => a / b * b <= a || b == 0\n");
    assert_eq!(reason, "it divides by a number that could be zero");
}

#[test]
fn a_law_can_ask_for_a_proof() {
    let items = items("@law(proved)\nlet same = (a: int) => a + 0 == a\n");
    assert_eq!(items[0].detail["must"], true);
    assert_eq!(items[0].detail["proof"]["status"], "proved");
    let items = super_plain("@law\nlet same = (a: int) => a + 0 == a\n");
    assert!(items[0].detail.get("must").is_none());
}

fn super_plain(source: &str) -> Vec<Item> {
    items(source)
}

#[test]
fn a_build_does_not_prove() {
    let (_, items) = compile(
        "@law\nlet same = (a: int) => a + 0 == a\n",
        Checks::LeftOut,
        true,
    )
    .unwrap();
    assert!(items.is_empty());
}
