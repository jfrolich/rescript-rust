//! Programs that derive codecs, for the tests of the checker and the
//! backend, which compile them with plans and without and compare the two.

use crate::parser::ast::StructureItem;
use crate::parser::{Parser, module};

/// A library of codecs over a local JSON type, so the tests need no
/// standard library, and declarations that derive from it.
pub(crate) const LIBRARY: &str = r#"
type rec json = Str(string) | Num(float) | Arr(array<json>) | Null
type decoded<'a> = result<'a, string>
module Spice = {
  let stringToJson = (s: string) => Str(s)
  let stringFromJson = (j: json): decoded<string> =>
    switch j {
    | Str(s) => Ok(s)
    | Num(_) | Arr(_) | Null => Error("string")
    }
  let intToJson = (_: int) => Num(0.)
  let intFromJson = (_: json): decoded<int> => Ok(0)
  let arrayToJson = (_: 'a => json, _: array<'a>) => Arr([])
  let arrayFromJson = (_: json => decoded<'a>, _: json): decoded<array<'a>> => Ok([])
  let optionToJson = (_: 'a => json, _: option<'a>): option<json> => None
  let optionToNullableJson = (_: 'a => json, _: option<'a>) => Null
  let optionFromJson = (_: json => decoded<'a>, _: json): decoded<option<'a>> => Ok(None)
  let resultToJson = (_: 'a => json, _: 'b => json, _: result<'a, 'b>) => Null
  let resultFromJson = (
    _: json => decoded<'a>,
    _: json => decoded<'b>,
    _: json,
  ): decoded<result<'a, 'b>> => Error("result")
  let dictToJson = (_: 'a => json, _: dict<'a>) => Null
  let dictFromJson = (_: json => decoded<'a>, _: json): decoded<dict<'a>> => Error("dict")
  let dictOptionalToJson = (_: 'a => option<json>, _: dict<option<'a>>) => Null
}
module A = {
  type t = int
  let t_encode = Spice.intToJson
  let t_encodeJson = Spice.intToJson
  let t_decode = Spice.intFromJson
}
"#;

/// Ten declarations whose manifest is a constructor application.
pub(crate) const DECLARATIONS: [&str; 10] = [
    "@spice type id = string",
    "@spice type ids = array<string>",
    "@spice type id = string\n@spice type ids = array<id>",
    "@spice type m = option<A.t>",
    "@spice type r = result<int, array<string>>",
    "@spice type d = dict<int>",
    "@spice type d = dict<option<array<int>>>",
    "@spice type n = array<option<array<option<A.t>>>>",
    "@spice.decode type only = array<int>\n@spice.encode type other = option<int>",
    "@spice type a = string\n@spice and b = array<int>\n@spice type c = result<a, b>",
];

/// Declarations inside a module expression: a submodule, a submodule of a
/// submodule, a functor body, a first-class module and a module bound in an
/// expression. Each is followed by values that use its codecs, so the types
/// the codecs get are visible at the top level. The second number is how
/// many items take a plan.
pub(crate) const NESTED: [(&str, usize); 5] = [
    (
        "module M = {\n  @spice type id = string\n  @spice type ids = array<id>\n}\nlet e = M.ids_encode\nlet d = M.ids_decode",
        2,
    ),
    (
        "module M = {\n  @spice type id = string\n  module N = {\n    @spice type ids = array<option<id>>\n  }\n}\nlet e = M.N.ids_encode\nlet d = M.N.ids_decode",
        2,
    ),
    (
        "module F = (X: {\n  type t\n  let t_encode: t => json\n  let t_encodeJson: t => json\n  let t_decode: json => decoded<t>\n}) => {\n  @spice type ids = array<X.t>\n}\nmodule I = F(A)\nlet e = I.ids_encode\nlet d = I.ids_decode",
        1,
    ),
    (
        "module type S = {\n  type id\n  let id_encode: id => json\n  let id_decode: json => decoded<id>\n}\nlet m: module(S) = module({\n  @spice type id = string\n})",
        1,
    ),
    (
        "let e = {\n  module L = {\n    @spice type ids = array<int>\n  }\n  L.ids_encode\n}",
        1,
    ),
];

/// Parse `source` after the library and run the derive over its items,
/// with plans (`true`) or with every item as syntax.
pub(crate) fn derive_source(
    source: &str,
    plans: bool,
) -> (Parser<'static>, Vec<StructureItem>) {
    let source: &'static str = Box::leak(format!("{LIBRARY}{source}").into_boxed_str());
    let mut parser = Parser::new("Test.res", source);
    let items = module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "{source}");
    parser
        .arena_mut()
        .set_derived_plans((!plans).then_some(super::GeneralReason::Switch));
    let expanded: Vec<StructureItem> = items
        .iter()
        .flat_map(|item| {
            super::expand_structure_item_with_mapper(item, parser.arena_mut(), true)
                .unwrap()
        })
        .collect();
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    (parser, expanded)
}


/// Programs whose plan has an obligation that fails: no codec in scope, and
/// a codec that is no function.
pub(crate) const FAILING: [&str; 2] = [
    "type plain = {a: int}\n@spice type t = array<plain>",
    "let wrong_encodeJson = 1\nlet wrong_decode = Spice.intFromJson\ntype wrong = int\n@spice type t = array<wrong>",
];

/// A program whose library has another shape than plans assume (a curried
/// codec): the obligation fails and the general form types.
pub(crate) const CURRIED_LIBRARY: &str = "module Curried = {\n  module Spice = {\n    let arrayToJson = (e: 'a => json) => (_: array<'a>) => { let _ = e; Null }\n  }\n}\nopen Curried\n@spice.encode type t = array<A.t>";

/// The library the bodies of record codecs call, with the shapes the real
/// one has (`tests/ppx_spice/src/Spice.res` and the standard library's
/// `JSON`, `Dict` and `Option`): an untagged `JSON.t`, `Dict` as externals,
/// `Spice.error` with an optional `~path`. Self-contained, so the tests need
/// no compiled standard library.
pub(crate) const RECORD_LIBRARY: &str = r#"
external \"++": (string, string) => string = "%string_concat"
module JSON = {
  @unboxed
  type rec t =
    | Boolean(bool)
    | @as(null) Null
    | String(string)
    | Number(float)
    | Object(dict<t>)
    | Array(array<t>)
}
module Dict = {
  @val external fromArray: array<(string, 'a)> => dict<'a> = "Object.fromEntries"
  @get_index external get: (dict<'a>, string) => option<'a> = ""
}
module Option = {
  let map = (opt, f) =>
    switch opt {
    | Some(x) => Some(f(x))
    | None => None
    }
  let getOr = (opt, default) =>
    switch opt {
    | Some(x) => x
    | None => default
    }
}
module Null = {
  @unboxed type t<'a> = Value('a) | @as(null) Null
}
module Spice = {
  type decodeError = {
    path: string,
    message: string,
    value: JSON.t,
  }
  type result<'a> = result<'a, decodeError>
  let error = (~path=?, message, value) => {
    let path = switch path {
    | None => ""
    | Some(s) => s
    }
    Error({path, message, value})
  }
  let stringToJson = (s): JSON.t => JSON.String(s)
  let stringFromJson = j =>
    switch (j: JSON.t) {
    | JSON.String(s) => Ok(s)
    | _ => Error({path: "", message: "Not a string", value: j})
    }
  let intToJson = (_: int): JSON.t => JSON.Number(0.)
  let intFromJson = (j: JSON.t): result<int> => Error({path: "", message: "Not a number", value: j})
  let floatToJson = (f): JSON.t => JSON.Number(f)
  let floatFromJson = (j: JSON.t): result<float> =>
    Error({path: "", message: "Not a number", value: j})
  let boolToJson = (b): JSON.t => JSON.Boolean(b)
  let boolFromJson = (j: JSON.t): result<bool> =>
    Error({path: "", message: "Not a boolean", value: j})
  let bigintToJson = (_: bigint): JSON.t => JSON.Number(0.)
  let bigintFromJson = (j: JSON.t): result<bigint> =>
    Error({path: "", message: "Not a number", value: j})
  let arrayToJson = (_: 'a => JSON.t, _: array<'a>): JSON.t => JSON.Array([])
  let arrayFromJson = (_: JSON.t => result<'a>, j: JSON.t): result<array<'a>> =>
    Error({path: "", message: "Not an array", value: j})
  let filterOptional = (arr: array<(string, option<JSON.t>)>): array<(string, JSON.t)> => {
    let _ = arr
    []
  }
  let optionToJson = (encoder, opt): option<JSON.t> =>
    switch opt {
    | Some(x) => Some(encoder(x))
    | None => None
    }
  let optionToNullableJson = (encoder, opt): JSON.t =>
    switch opt {
    | Some(x) => encoder(x)
    | None => JSON.Null
    }
  let optionFromJson = (decoder, json) =>
    switch (json: JSON.t) {
    | JSON.Null => Ok(None)
    | _ =>
      switch decoder(json) {
      | Ok(v) => Ok(Some(v))
      | Error(e) => Error(e)
      }
    }
  let optionalFieldFromJson = (decoder, json) =>
    switch (json: JSON.t) {
    | JSON.Null =>
      switch decoder(json) {
      | Ok(v) => Ok(Some(v))
      | Error(_) => Ok(None)
      }
    | _ =>
      switch decoder(json) {
      | Ok(v) => Ok(Some(v))
      | Error(e) => Error(e)
      }
    }
  let nullToJson = (encoder, opt): JSON.t =>
    switch opt {
    | Null.Value(x) => encoder(x)
    | Null.Null => JSON.Null
    }
  let nullFromJson = (decoder, json) =>
    switch (json: JSON.t) {
    | JSON.Null => Ok(Null.Null)
    | _ =>
      switch decoder(json) {
      | Ok(v) => Ok(Null.Value(v))
      | Error(e) => Error(e)
      }
    }
}
"#;

/// Parse `source` after [`RECORD_LIBRARY`] and run the whole front end over
/// it (the built-in rewrites give the library's externals their meaning),
/// with plans (`true`) or with every derived item as syntax.
pub(crate) fn frontend_source(source: &str, plans: bool) -> (Parser<'static>, Vec<StructureItem>) {
    let source: &'static str = Box::leak(format!("{RECORD_LIBRARY}{source}").into_boxed_str());
    let mut parser = Parser::new("Test.res", source);
    let structure = module::parse_structure(&mut parser);
    assert!(!parser.has_errors(), "{source}");
    let options = crate::driver::CompilerOptions {
        spice_ppx: true,
        derived_path: if plans {
            crate::driver::DerivedPath::Plans
        } else {
            crate::driver::DerivedPath::General
        },
        derived_census: None,
        ..Default::default()
    };
    let mut out = String::new();
    crate::binary_ast::spice_ppx::plan::PLAN_RECORDS.set(plans);
    let frontend = crate::driver::run_implementation_frontend(
        &mut parser,
        structure,
        source,
        "Test.res",
        &options,
        &mut out,
    )
    .unwrap_or_else(|error| panic!("{error}\n{source}"));
    crate::binary_ast::spice_ppx::plan::PLAN_RECORDS.set(false);
    assert!(out.is_empty(), "{out}");
    crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
    (parser, frontend.structure)
}
