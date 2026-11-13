//! What a read-eval-print loop asks of the compiler: an input is a file of
//! its own with the earlier inputs opened, and the compiler says what it
//! defined and what its values look like at run time.

mod macros_support;

use macros_support::Project;
use rescript_compiler::repl;
use serde_json::json;

/// Compile `input` as the next file of a session.
fn eval(project: &mut Project, input: &str) -> Result<serde_json::Value, String> {
    let name = format!("Repl{}", project.open_modules.len() + 1);
    let filename = format!("{name}.res");
    let source = match repl::prepare(input, &filename) {
        Some(prepared) => prepared.source,
        None => input.to_string(),
    };
    project.compile(&filename, &source)?;
    project.open_modules.push(name);
    Ok(project.signature.clone())
}

fn texts(signature: &serde_json::Value) -> Vec<String> {
    signature["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|item| item["text"].as_str().unwrap().to_string())
        .collect()
}

fn session(run: impl FnOnce(&mut Project) + Send + 'static) {
    // A debug build of the type checker needs more stack than a test thread
    // has.
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(&mut Project::new()))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn an_input_sees_the_inputs_before_it() {
    session(|project| {
        let first = eval(project, "let x = 20").unwrap();
        assert_eq!(texts(&first), ["let x: int"]);
        let second = eval(project, "x + 1").unwrap();
        assert_eq!(texts(&second), ["let it: int"]);
        assert_eq!(second["items"][0]["shape"], json!({ "k": "int" }));
        let third = eval(project, "it * 2").unwrap();
        assert_eq!(texts(&third), ["let it: int"]);
        // A later binding of a name is the one that is seen.
        eval(project, "let x = \"now a string\"").unwrap();
        let fifth = eval(project, "x").unwrap();
        assert_eq!(texts(&fifth), ["let it: string"]);
        // An input that does not compile leaves the session as it was.
        assert!(eval(project, "x + 1").is_err());
    });
}

#[test]
fn a_value_is_described_by_its_type() {
    session(|project| {
        let signature = eval(
            project,
            "type shape = Circle(float) | Square({side: float}) | @as(\"dot\") Point\n\
             type rec user = {name: string, age?: int, @as(\"best_friend\") friend: option<user>, shape: shape}\n\
             let ada = {name: \"Ada\", friend: None, shape: Point}\n\
             let all = (Some([1]), list{Ok(1.5)}, #a(\"b\"), x => x + 1)\n",
        )
        .unwrap();
        assert_eq!(
            texts(&signature),
            [
                "type shape = Circle(float) | Square({side: float}) | @as(\"dot\") Point",
                "type rec user = {name: string, age?: int, friend: option<user>, shape: shape}",
                "let ada: user",
                "let all: (\n  option<array<int>>,\n  list<result<float, 'a>>,\n  [> #a(string)],\n  int => int,\n)",
            ]
        );
        let items = signature["items"].as_array().unwrap();
        let defs = signature["defs"].as_array().unwrap();
        // The record refers to itself and to the variant by index.
        let user = &defs[items[2]["shape"]["id"].as_u64().unwrap() as usize];
        assert_eq!(user["k"], "record");
        let fields = user["fields"].as_array().unwrap();
        assert_eq!(
            fields[1],
            json!({ "name": "age", "js": "age", "optional": true, "of": { "k": "int" } })
        );
        assert_eq!(fields[2]["js"], "best_friend");
        assert_eq!(
            fields[2]["of"],
            json!({ "k": "option", "of": items[2]["shape"] })
        );
        let shape = &defs[fields[3]["of"]["id"].as_u64().unwrap() as usize];
        let cases = shape["cases"].as_array().unwrap();
        assert_eq!(cases[0]["args"], json!([{ "k": "float" }]));
        assert_eq!(cases[0]["tag"], json!({ "t": "string", "v": "Circle" }));
        assert_eq!(cases[1]["fields"][0]["name"], "side");
        assert_eq!(cases[2]["constant"], true);
        assert_eq!(cases[2]["tag"], json!({ "t": "string", "v": "dot" }));
        assert_eq!(
            items[3]["shape"],
            json!({ "k": "tuple", "of": [
                { "k": "option", "of": { "k": "array", "of": { "k": "int" } } },
                { "k": "list", "of": { "k": "result", "ok": { "k": "float" }, "error": { "k": "other", "name": "'a" } } },
                { "k": "poly", "cases": [{ "name": "a", "of": { "k": "string" } }] },
                { "k": "fn" },
            ] })
        );
    });
}

#[test]
fn a_macro_of_one_input_is_used_in_the_next() {
    session(|project| {
        eval(
            project,
            "module Twice = {\n  open Macro\n  @macro\n  let f = (e: code<int>): code<int> => %code(${e} + ${e})\n}",
        )
        .unwrap();
        let signature = eval(project, "%Twice.f(21)").unwrap();
        assert_eq!(texts(&signature), ["let it: int"]);
        let expanded = project.expanded.clone().unwrap();
        assert_eq!(expanded.matches("21").count(), 2, "{expanded}");
    });
}
