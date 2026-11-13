//! The exceptions library functions throw
//! (analysis/reanalyze/src/exn_lib.ml).

use super::log::Exceptions;
use std::collections::HashMap;
use std::sync::OnceLock;

const ASSERT_FAILURE: &str = "Assert_failure";
const DECODE_ERROR: &str = "DecodeError";
const DIVISION_BY_ZERO: &str = "Division_by_zero";
const INVALID_ARGUMENT: &str = "Invalid_argument";
const JS_EXN: &str = "JsExn";
const NOT_FOUND: &str = "Not_found";
const YOJSON_JSON_ERROR: &str = "Yojson.Json_error";
const YOJSON_TYPE_ERROR: &str = "Yojson.Basic.Util.Type_error";

/// The functions of a module and the exceptions each throws.
type Group = &'static [(&'static str, &'static [&'static str])];

const BELT_ARRAY: Group = &[
    ("getExn", &[ASSERT_FAILURE]),
    ("getOrThrow", &[ASSERT_FAILURE]),
    ("setExn", &[ASSERT_FAILURE]),
    ("setOrThrow", &[ASSERT_FAILURE]),
];
const BELT_LIST: Group = &[
    ("getExn", &[NOT_FOUND]),
    ("getOrThrow", &[NOT_FOUND]),
    ("headExn", &[NOT_FOUND]),
    ("headOrThrow", &[NOT_FOUND]),
    ("tailExn", &[NOT_FOUND]),
    ("tailOrThrow", &[NOT_FOUND]),
];
const BELT_MAP: Group = &[("getExn", &[NOT_FOUND]), ("getOrThrow", &[NOT_FOUND])];
const BELT_MUTABLE_MAP: Group = BELT_MAP;
const BELT_MUTABLE_QUEUE: Group = &[
    ("peekExn", &[NOT_FOUND]),
    ("peekOrThrow", &[NOT_FOUND]),
    ("popExn", &[NOT_FOUND]),
    ("popOrThrow", &[NOT_FOUND]),
];
const BELT_SET: Group = &[("getExn", &[NOT_FOUND]), ("getOrThrow", &[NOT_FOUND])];
const BELT_MUTABLE_SET: Group = BELT_SET;
const BELT_OPTION: Group = &[("getExn", &[NOT_FOUND]), ("getOrThrow", &[NOT_FOUND])];
const BELT_RESULT: Group = &[("getExn", &[NOT_FOUND]), ("getOrThrow", &[NOT_FOUND])];
const BS_JSON: Group = &[
    ("bool", &[DECODE_ERROR]),
    ("float", &[DECODE_ERROR]),
    ("int", &[DECODE_ERROR]),
    ("string", &[DECODE_ERROR]),
    ("char", &[DECODE_ERROR]),
    ("date", &[DECODE_ERROR]),
    ("nullable", &[DECODE_ERROR]),
    ("nullAs", &[DECODE_ERROR]),
    ("array", &[DECODE_ERROR]),
    ("list", &[DECODE_ERROR]),
    ("pair", &[DECODE_ERROR]),
    ("tuple2", &[DECODE_ERROR]),
    ("tuple3", &[DECODE_ERROR]),
    ("tuple4", &[DECODE_ERROR]),
    ("dict", &[DECODE_ERROR]),
    ("field", &[DECODE_ERROR]),
    ("at", &[DECODE_ERROR, INVALID_ARGUMENT]),
    ("oneOf", &[DECODE_ERROR]),
    ("either", &[DECODE_ERROR]),
];
const STDLIB: Group = &[
    ("panic", &[JS_EXN]),
    ("assertEqual", &[JS_EXN]),
    ("/", &[DIVISION_BY_ZERO]),
    ("mod", &[DIVISION_BY_ZERO]),
];
const STDLIB_BIG_INT: Group = &[
    ("fromStringOrThrow", &[JS_EXN]),
    ("fromFloatOrThrow", &[JS_EXN]),
];
const STDLIB_BOOL: Group = &[("fromStringOrThrow", &[INVALID_ARGUMENT])];
const STDLIB_JS_ERROR: Group = &[
    ("EvalError.throwWithMessage", &[JS_EXN]),
    ("RangeError.throwWithMessage", &[JS_EXN]),
    ("ReferenceError.throwWithMessage", &[JS_EXN]),
    ("SyntaxError.throwWithMessage", &[JS_EXN]),
    ("TypeError.throwWithMessage", &[JS_EXN]),
    ("URIError.throwWithMessage", &[JS_EXN]),
    ("panic", &[JS_EXN]),
    ("throw", &[JS_EXN]),
    ("throwWithMessage", &[JS_EXN]),
];
const STDLIB_JSON: Group = &[("parseOrThrow", &[JS_EXN]), ("stringifyAny", &[JS_EXN])];
const STDLIB_LIST: Group = &[
    ("headOrThrow", &[NOT_FOUND]),
    ("tailOrThrow", &[NOT_FOUND]),
    ("getOrThrow", &[NOT_FOUND]),
];
const STDLIB_NULL: Group = &[("getOrThrow", &[INVALID_ARGUMENT])];
const STDLIB_NULLABLE: Group = &[("getOrThrow", &[INVALID_ARGUMENT])];
const STDLIB_OPTION: Group = &[("getOrThrow", &[JS_EXN])];
const STDLIB_RESULT: Group = &[("getOrThrow", &[JS_EXN])];
const YOJSON_BASIC: Group = &[("from_string", &[YOJSON_JSON_ERROR])];
const YOJSON_BASIC_UTIL: Group = &[
    ("member", &[YOJSON_TYPE_ERROR]),
    ("to_assoc", &[YOJSON_TYPE_ERROR]),
    ("to_bool", &[YOJSON_TYPE_ERROR]),
    ("to_bool_option", &[YOJSON_TYPE_ERROR]),
    ("to_float", &[YOJSON_TYPE_ERROR]),
    ("to_float_option", &[YOJSON_TYPE_ERROR]),
    ("to_int", &[YOJSON_TYPE_ERROR]),
    ("to_list", &[YOJSON_TYPE_ERROR]),
    ("to_number", &[YOJSON_TYPE_ERROR]),
    ("to_number_option", &[YOJSON_TYPE_ERROR]),
    ("to_string", &[YOJSON_TYPE_ERROR]),
    ("to_string_option", &[YOJSON_TYPE_ERROR]),
];

/// The modules whose functions throw, under each name they are reached by.
const MODULES: &[(&str, Group)] = &[
    ("Belt.Array", BELT_ARRAY),
    ("Belt_Array", BELT_ARRAY),
    ("Belt.List", BELT_LIST),
    ("Belt_List", BELT_LIST),
    ("Belt.Map", BELT_MAP),
    ("Belt.Map.Int", BELT_MAP),
    ("Belt.Map.String", BELT_MAP),
    ("Belt_Map", BELT_MAP),
    ("Belt_Map.Int", BELT_MAP),
    ("Belt_Map.String", BELT_MAP),
    ("Belt_MapInt", BELT_MAP),
    ("Belt_MapString", BELT_MAP),
    ("Belt.MutableMap", BELT_MUTABLE_MAP),
    ("Belt.MutableMap.Int", BELT_MUTABLE_MAP),
    ("Belt.MutableMap.String", BELT_MUTABLE_MAP),
    ("Belt_MutableMap", BELT_MUTABLE_MAP),
    ("Belt_MutableMap.Int", BELT_MUTABLE_MAP),
    ("Belt_MutableMap.String", BELT_MUTABLE_MAP),
    ("Belt_MutableMapInt", BELT_MUTABLE_MAP),
    ("Belt_MutableMapString", BELT_MUTABLE_MAP),
    ("Belt.MutableQueue", BELT_MUTABLE_QUEUE),
    ("Belt_MutableQueue", BELT_MUTABLE_QUEUE),
    ("Belt_MutableSetInt", BELT_MUTABLE_SET),
    ("Belt_MutableSetString", BELT_MUTABLE_SET),
    ("Belt.MutableSet", BELT_MUTABLE_SET),
    ("Belt.MutableSet.Int", BELT_MUTABLE_SET),
    ("Belt.MutableSet.String", BELT_MUTABLE_SET),
    ("Belt.Option", BELT_OPTION),
    ("Belt_Option", BELT_OPTION),
    ("Belt.Result", BELT_RESULT),
    ("Belt_Result", BELT_RESULT),
    ("Belt.Set", BELT_SET),
    ("Belt.Set.Int", BELT_SET),
    ("Belt.Set.String", BELT_SET),
    ("Belt_Set", BELT_SET),
    ("Belt_Set.Int", BELT_SET),
    ("Belt_Set.String", BELT_SET),
    ("Belt_SetInt", BELT_SET),
    ("Belt_SetString", BELT_SET),
    ("BigInt", STDLIB_BIG_INT),
    ("Bool", STDLIB_BOOL),
    ("JsError", STDLIB_JS_ERROR),
    ("JSON", STDLIB_JSON),
    ("Json_decode", BS_JSON),
    ("Json.Decode", BS_JSON),
    ("List", STDLIB_LIST),
    ("MutableSet", BELT_MUTABLE_SET),
    ("MutableSet.Int", BELT_MUTABLE_SET),
    ("MutableSet.String", BELT_MUTABLE_SET),
    ("Null", STDLIB_NULL),
    ("Nullable", STDLIB_NULLABLE),
    ("Option", STDLIB_OPTION),
    ("Pervasives", STDLIB),
    ("Result", STDLIB_RESULT),
    ("Stdlib", STDLIB),
    ("Stdlib_BigInt", STDLIB_BIG_INT),
    ("Stdlib.BigInt", STDLIB_BIG_INT),
    ("Stdlib_Bool", STDLIB_BOOL),
    ("Stdlib.Bool", STDLIB_BOOL),
    ("Stdlib_JsError", STDLIB_JS_ERROR),
    ("Stdlib.JsError", STDLIB_JS_ERROR),
    ("Stdlib_JSON", STDLIB_JSON),
    ("Stdlib.JSON", STDLIB_JSON),
    ("Stdlib_List", STDLIB_LIST),
    ("Stdlib.List", STDLIB_LIST),
    ("Stdlib_Null", STDLIB_NULL),
    ("Stdlib.Null", STDLIB_NULL),
    ("Stdlib_Nullable", STDLIB_NULLABLE),
    ("Stdlib.Nullable", STDLIB_NULLABLE),
    ("Stdlib_Option", STDLIB_OPTION),
    ("Stdlib.Option", STDLIB_OPTION),
    ("Stdlib_Result", STDLIB_RESULT),
    ("Stdlib.Result", STDLIB_RESULT),
    ("Yojson.Basic", YOJSON_BASIC),
    ("Yojson.Basic.Util", YOJSON_BASIC_UTIL),
];

fn table() -> &'static HashMap<String, &'static [&'static str]> {
    static TABLE: OnceLock<HashMap<String, &'static [&'static str]>> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut table = HashMap::new();
        for (module, group) in MODULES {
            for (function, exceptions) in group.iter() {
                table.insert(format!("{module}.{function}"), *exceptions);
            }
        }
        table
    })
}

/// `Exn_lib.find`: the exceptions the library function at the dotted `path`
/// throws.
pub fn find(path: &str) -> Option<Exceptions> {
    table()
        .get(path)
        .map(|exceptions| exceptions.iter().map(|exn| exn.to_string()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn library_functions_are_found_by_dotted_path() {
        assert_eq!(
            find("Belt.List.headExn"),
            Some(Exceptions::from([NOT_FOUND.to_string()]))
        );
        assert_eq!(
            find("Json.Decode.at"),
            Some(Exceptions::from([
                DECODE_ERROR.to_string(),
                INVALID_ARGUMENT.to_string()
            ]))
        );
        assert_eq!(
            find("Stdlib.JsError.TypeError.throwWithMessage"),
            Some(Exceptions::from([JS_EXN.to_string()]))
        );
        assert_eq!(find("Belt.List.head"), None);
    }
}
