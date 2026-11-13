//! Programs that derive codecs, for the tests of the checker and the
//! backend, which compile them with plans and without and compare the two.

use super::Scope;
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
    let scope = Scope::TopLevel;
    let expanded: Vec<StructureItem> = items
        .iter()
        .flat_map(|item| {
            super::expand_structure_item_with_mapper(item, parser.arena_mut(), true, scope)
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
