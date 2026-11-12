//! What the compiler says when a file that uses macros has a problem.
//!
//! Each case compiles a file and compares the diagnostics with
//! `tests/macro_errors/<case>.txt`. Run with `UPDATE_EXPECTED=1` to write
//! those files, then read the difference.

mod macros_support;
use macros_support::Project;

const JSON: &str = include_str!("../../playground/examples/json/Json.res");
const DEBUG: &str = include_str!("../../playground/examples/debug/Debug.res");

const USER: &str = "type user = {name: string, age: int}\nlet alice = {name: \"Alice\", age: 30}\n";

const QUOTED: &str = r#"open Macro

@macro
let twice = (e: code<int>): code<int> =>
  %code({
    let v = ${e}
    v + "two"
  })

@macro
let unbound = (e: code<'a>): code<'a> => %code(notDefinedAnywhere(${e}))

@macro
let shadow = (e: code<int>): code<int> => %code({
  let unused = 1
  ${e}
})

@generic
let show = (value: code<'a>): code<string> =>
  switch Type.info(typeOf(value)) {
  | Int => %code(Int.toString(${value}) + 1)
  | _ => error("only int")
  }

@macro
let decl = (): decls => %code(let made: int = "x")

// Code that is not written in a quote.
@macro
let built = (e: code<int>): code<int> => Code.call(Code.raw("notDefinedAnywhere"), [e])
"#;

const THROWS: &str = r#"open Macro

exception Boom(string)

@macro
let exn = (): code<int> => throw(Boom("bang"))

@macro
let js = (): code<int> => {
  let xs: array<int> = []
  Code.int(xs->Array.getUnsafe(3)->Int.toString->String.length)
}

@macro
let syntax = (): code<int> => Code.raw("let = 1 +")

@macro
let rec loop = (): code<int> => %code(%Throws.loop())
"#;

/// The diagnostics of a file that does not compile, or the warnings of one
/// that does.
fn diagnostics(project: &mut Project, filename: &str, source: &str) -> String {
    match project.compile(filename, source) {
        Ok(_) => format!("(compiles)\n{}", project.warnings),
        Err(error) => error,
    }
}

fn check(project: &mut Project, case: &str, source: &str) {
    let filename = format!("{}.res", case[..1].to_uppercase() + &case[1..]);
    let actual = format!("{source}----\n{}", diagnostics(project, &filename, source));
    // Lines without trailing spaces: the compiler prints some.
    let actual: String = actual
        .lines()
        .map(|line| format!("{}\n", line.trim_end()))
        .collect();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/macro_errors")
        .join(format!("{case}.txt"));
    if std::env::var_os("UPDATE_EXPECTED").is_some() {
        std::fs::write(&path, &actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        actual == expected,
        "{case}: the diagnostics differ from {}.\n---- expected\n{expected}\n---- actual\n{actual}",
        path.display()
    );
}

fn on_a_big_stack(test: fn()) {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn an_error_in_an_argument_points_at_the_argument() {
    on_a_big_stack(|| {
        let mut project = Project::new();
        project.compile("Json.res", JSON).unwrap();
        project.compile("Debug.res", DEBUG).unwrap();
        check(
            &mut project,
            "argumentType",
            "let x = %Debug.log(1 + \"a\")\n",
        );
        check(
            &mut project,
            "argumentUnbound",
            "let x = %Debug.log(nope)\n",
        );
        check(
            &mut project,
            "genericArgumentUnbound",
            &format!("{USER}let j = Json.encode(alicia)\n"),
        );
        // An error elsewhere in the item of a use is the error reported.
        check(
            &mut project,
            "errorBesideAUse",
            &format!("{USER}Console.log(JSON.stringify(Json.encode(alice), ~space=\"x\"))\n"),
        );
    });
}

#[test]
fn an_error_in_generated_code_shows_where_it_was_written() {
    on_a_big_stack(|| {
        let mut project = Project::new();
        project.compile("Quoted.res", QUOTED).unwrap();
        check(
            &mut project,
            "quotedType",
            "let a = 1\nlet x = %Quoted.twice(a + 1)\n",
        );
        check(
            &mut project,
            "quotedUnbound",
            "let x = %Quoted.unbound(1)\n",
        );
        check(&mut project, "quotedWarning", "let x = %Quoted.shadow(1)\n");
        check(&mut project, "quotedInGeneric", "let s = Quoted.show(1)\n");
        check(&mut project, "quotedDeclarations", "%%Quoted.decl()\n");
        check(&mut project, "builtCode", "let x = %Quoted.built(1)\n");
    });
}

#[test]
fn an_error_of_a_macro_is_reported_at_its_use() {
    on_a_big_stack(|| {
        let mut project = Project::new();
        project.compile("Json.res", JSON).unwrap();
        project.compile("Quoted.res", QUOTED).unwrap();
        project.compile("Throws.res", THROWS).unwrap();
        check(&mut project, "macroReports", "let s = Quoted.show(\"a\")\n");
        check(&mut project, "macroThrows", "let x = %Throws.exn()\n");
        check(&mut project, "macroThrowsJs", "let x = %Throws.js()\n");
        // A use in generated code: the error says what generated that code.
        check(
            &mut project,
            "macroReportsInAnInstance",
            "type t = {name: string, f: int => int}\nlet enc = (t: t) => Json.encode(t)\n",
        );
        check(
            &mut project,
            "generatedSyntax",
            "let a = 1\nlet x = %Throws.syntax()\nlet b = 2\n",
        );
        check(
            &mut project,
            "expansionWithoutEnd",
            "let x = %Throws.loop()\n",
        );
        check(&mut project, "unknownMacro", "let x = %Throws.exm()\n");
    });
}

#[test]
fn eval_errors() {
    on_a_big_stack(|| {
        let mut project = Project::new();
        check(
            &mut project,
            "evalLocal",
            "let n = 3\nlet x = %Macro.eval(n + 1)\n",
        );
        check(
            &mut project,
            "evalThrows",
            "let x = %Macro.eval(Option.getOrThrow((None: option<int>)))\n",
        );
        check(
            &mut project,
            "evalType",
            "let x = %Macro.eval(1 + \"a\")\n",
        );
        check(
            &mut project,
            "evalFunction",
            "let x = %Macro.eval((a: int) => a)\n",
        );
        // It is an expression, with one argument.
        check(&mut project, "evalWithoutExpression", "let x = %Macro.eval()\n");
        check(
            &mut project,
            "evalAsAPattern",
            "let f = x =>\n  switch x {\n  | %Macro.eval(1) => true\n  | _ => false\n  }\n",
        );
    });
}

const SPLICED: &str = r#"open Macro

// Entries of a record, one of them a quote with the wrong type.
@macro
let point = (x: code<int>): code<'r> => {
  let entries = [Code.entry("x", x), Code.entry("y", %code("two"))]
  %code({${...entries}})
}

@macro
let flagged = (source: typ): typ =>
  switch Type.info(source) {
  | Record({fields}) => Type.record(fields->Array.map(f => {...f, optional: true}))
  | _ => error("flagged needs a record")
  }
"#;

#[test]
fn splice_holes_and_optional_fields() {
    on_a_big_stack(|| {
        let mut project = Project::new();
        project.compile("Spliced.res", SPLICED).unwrap();
        // A splice hole stands in a list of a quote, and nowhere else.
        check(
            &mut project,
            "spliceOutOfPlace",
            "open Macro\n@macro\nlet sum = (a: code<int>): code<int> => %code(1 + ${...[a]})\n",
        );
        check(
            &mut project,
            "spliceOutsideAQuote",
            "let xs = [1]\nlet ys = [0, ${...xs}]\n",
        );
        // Spliced code keeps the place it was written at.
        check(
            &mut project,
            "splicedEntryType",
            "type point = {x: int, y: int}\nlet p: point = %Spliced.point(1)\n",
        );
        check(
            &mut project,
            "optionalFieldByHand",
            "type user = {name: string}\ntype t = %Spliced.flagged(user)\n",
        );
    });
}
