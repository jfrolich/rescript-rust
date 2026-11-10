//! Predefined type constructors with special typing rules.
//!
//! Matches OCaml's `Predef` module: each predef type gets a unique stamp
//! allocated sequentially starting from 1. After all predefs are created,
//! the stamp counter is set to 999 so user identifiers start at 1000.

use crate::ident::{Ident, IdentFlags};
use crate::types::path::Path;
use crate::types::path::PathView;

// ============================================================================
// Predef type ident stamps (matching OCaml's allocation order in predef.ml)
// ============================================================================

// Types (Ident.create)
const STAMP_INT: i32 = 1;
const STAMP_CHAR: i32 = 2;
const STAMP_FLOAT: i32 = 3;
const STAMP_BOOL: i32 = 4;
const STAMP_UNIT: i32 = 5;
const STAMP_EXN: i32 = 6;
const STAMP_ARRAY: i32 = 7;
const STAMP_ITERABLE: i32 = 8;
const STAMP_ASYNC_ITERABLE: i32 = 9;
const STAMP_LIST: i32 = 10;
const STAMP_OPTION: i32 = 11;
const STAMP_RESULT: i32 = 12;
const STAMP_DICT: i32 = 13;
const STAMP_BIGINT: i32 = 14;
const STAMP_STRING: i32 = 15;
const STAMP_UNKNOWN: i32 = 16;
const STAMP_PROMISE: i32 = 17;
// Upstream compiler/ml/predef.ml:68 allocates taggedTemplate immediately after promise.
const STAMP_TAGGED_TEMPLATE: i32 = 18;

// Predef exceptions (Ident.create_predef_exn) — same counter, with PREDEF_EXN flag
const STAMP_MATCH_FAILURE: i32 = 19;
const STAMP_INVALID_ARGUMENT: i32 = 20;
const STAMP_FAILURE: i32 = 21;
const STAMP_OK: i32 = 22;
const STAMP_ERROR: i32 = 23;
const STAMP_JS_EXN: i32 = 24;
const STAMP_NOT_FOUND: i32 = 25;
const STAMP_END_OF_FILE: i32 = 26;
const STAMP_DIVISION_BY_ZERO: i32 = 27;
const STAMP_ASSERT_FAILURE: i32 = 28;
const STAMP_UNDEFINED_RECURSIVE_MODULE: i32 = 29;

// Constructor idents (regular Ident.create, in common_initial_env)
const STAMP_FALSE: i32 = 30;
const STAMP_TRUE: i32 = 31;
const STAMP_VOID: i32 = 32; // "()"
const STAMP_NIL: i32 = 33; // "[]"
const STAMP_CONS: i32 = 34; // "::"
const STAMP_NONE: i32 = 35;
const STAMP_SOME: i32 = 36;
const STAMP_CTOR_UNKNOWN: i32 = 37;

/// The stamp counter value after all predefs are allocated.
/// OCaml sets `Ident.set_current_time 999` at the end of predef.ml.
pub const PREDEF_STAMP_BARRIER: i32 = 999;

// ============================================================================
// Type idents
// ============================================================================

/// Whether `id` is exactly one of the predefined type identifiers installed
/// by `env::initial_env` (OCaml `Predef.build_initial_env`,
/// compiler/ml/predef.ml:239-424). None of them has a manifest.
#[inline]
pub fn is_predef_type_ident(id: &Ident) -> bool {
    let expected = match id.stamp() {
        STAMP_INT => "int",
        STAMP_CHAR => "char",
        STAMP_FLOAT => "float",
        STAMP_BOOL => "bool",
        STAMP_UNIT => "unit",
        STAMP_EXN => "exn",
        STAMP_ARRAY => "array",
        STAMP_ITERABLE => "iterable",
        STAMP_ASYNC_ITERABLE => "asyncIterable",
        STAMP_LIST => "list",
        STAMP_OPTION => "option",
        STAMP_RESULT => "result",
        STAMP_DICT => "dict",
        STAMP_BIGINT => "bigint",
        STAMP_STRING => "string",
        STAMP_UNKNOWN => "unknown",
        STAMP_PROMISE => "promise",
        STAMP_TAGGED_TEMPLATE => "taggedTemplate",
        _ => return false,
    };
    !id.is_persistent() && id.name() == expected
}

fn make_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::NONE)
}

fn make_predef_exn_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::PREDEF_EXN.with_global())
}

pub fn ident_int() -> Ident {
    make_ident("int", STAMP_INT)
}
pub fn ident_char() -> Ident {
    make_ident("char", STAMP_CHAR)
}
pub fn ident_float() -> Ident {
    make_ident("float", STAMP_FLOAT)
}
pub fn ident_bool() -> Ident {
    make_ident("bool", STAMP_BOOL)
}
pub fn ident_unit() -> Ident {
    make_ident("unit", STAMP_UNIT)
}
pub fn ident_exn() -> Ident {
    make_ident("exn", STAMP_EXN)
}
pub fn ident_array() -> Ident {
    make_ident("array", STAMP_ARRAY)
}
pub fn ident_iterable() -> Ident {
    make_ident("iterable", STAMP_ITERABLE)
}
pub fn ident_async_iterable() -> Ident {
    make_ident("asyncIterable", STAMP_ASYNC_ITERABLE)
}
pub fn ident_list() -> Ident {
    make_ident("list", STAMP_LIST)
}
pub fn ident_option() -> Ident {
    make_ident("option", STAMP_OPTION)
}
pub fn ident_result() -> Ident {
    make_ident("result", STAMP_RESULT)
}
pub fn ident_dict() -> Ident {
    make_ident("dict", STAMP_DICT)
}
pub fn ident_bigint() -> Ident {
    make_ident("bigint", STAMP_BIGINT)
}
pub fn ident_string() -> Ident {
    make_ident("string", STAMP_STRING)
}
pub fn ident_unknown() -> Ident {
    make_ident("unknown", STAMP_UNKNOWN)
}
pub fn ident_promise() -> Ident {
    make_ident("promise", STAMP_PROMISE)
}
pub fn ident_tagged_template() -> Ident {
    make_ident("taggedTemplate", STAMP_TAGGED_TEMPLATE)
}

// ============================================================================
// Predef exception idents
// ============================================================================

pub fn ident_match_failure() -> Ident {
    make_predef_exn_ident("Match_failure", STAMP_MATCH_FAILURE)
}
pub fn ident_invalid_argument() -> Ident {
    make_predef_exn_ident("Invalid_argument", STAMP_INVALID_ARGUMENT)
}
pub fn ident_failure() -> Ident {
    make_predef_exn_ident("Failure", STAMP_FAILURE)
}
pub fn ident_ok() -> Ident {
    make_predef_exn_ident("Ok", STAMP_OK)
}
pub fn ident_error() -> Ident {
    make_predef_exn_ident("Error", STAMP_ERROR)
}
pub fn ident_js_exn() -> Ident {
    make_predef_exn_ident("JsExn", STAMP_JS_EXN)
}
pub fn ident_not_found() -> Ident {
    make_predef_exn_ident("Not_found", STAMP_NOT_FOUND)
}
pub fn ident_end_of_file() -> Ident {
    make_predef_exn_ident("End_of_file", STAMP_END_OF_FILE)
}
pub fn ident_division_by_zero() -> Ident {
    make_predef_exn_ident("Division_by_zero", STAMP_DIVISION_BY_ZERO)
}
pub fn ident_assert_failure() -> Ident {
    make_predef_exn_ident("Assert_failure", STAMP_ASSERT_FAILURE)
}
pub fn ident_undefined_recursive_module() -> Ident {
    make_predef_exn_ident(
        "Undefined_recursive_module",
        STAMP_UNDEFINED_RECURSIVE_MODULE,
    )
}

// ============================================================================
// Constructor idents
// ============================================================================

pub fn ident_false() -> Ident {
    make_ident("false", STAMP_FALSE)
}
pub fn ident_true() -> Ident {
    make_ident("true", STAMP_TRUE)
}
pub fn ident_void() -> Ident {
    make_ident("()", STAMP_VOID)
}
pub fn ident_nil() -> Ident {
    make_ident("[]", STAMP_NIL)
}
pub fn ident_cons() -> Ident {
    make_ident("::", STAMP_CONS)
}
pub fn ident_none() -> Ident {
    make_ident("None", STAMP_NONE)
}
pub fn ident_some() -> Ident {
    make_ident("Some", STAMP_SOME)
}
pub fn ident_ctor_unknown() -> Ident {
    make_ident("Unknown", STAMP_CTOR_UNKNOWN)
}

// ============================================================================
// Paths (Pident wrappers)
// ============================================================================

pub fn path_int() -> Path {
    Path::pident(ident_int())
}
pub fn path_char() -> Path {
    Path::pident(ident_char())
}
pub fn path_float() -> Path {
    Path::pident(ident_float())
}
pub fn path_bool() -> Path {
    Path::pident(ident_bool())
}
pub fn path_unit() -> Path {
    Path::pident(ident_unit())
}
pub fn path_exn() -> Path {
    Path::pident(ident_exn())
}
pub fn path_array() -> Path {
    Path::pident(ident_array())
}
pub fn path_iterable() -> Path {
    Path::pident(ident_iterable())
}
pub fn path_async_iterable() -> Path {
    Path::pident(ident_async_iterable())
}
pub fn path_list() -> Path {
    Path::pident(ident_list())
}
pub fn path_option() -> Path {
    Path::pident(ident_option())
}
pub fn path_result() -> Path {
    Path::pident(ident_result())
}
pub fn path_dict() -> Path {
    Path::pident(ident_dict())
}
pub fn path_bigint() -> Path {
    Path::pident(ident_bigint())
}
pub fn path_string() -> Path {
    Path::pident(ident_string())
}
pub fn path_unknown() -> Path {
    Path::pident(ident_unknown())
}
pub fn path_promise() -> Path {
    Path::pident(ident_promise())
}
pub fn path_tagged_template() -> Path {
    Path::pident(ident_tagged_template())
}
pub fn path_match_failure() -> Path {
    Path::pident(ident_match_failure())
}
pub fn path_assert_failure() -> Path {
    Path::pident(ident_assert_failure())
}
pub fn path_undefined_recursive_module() -> Path {
    Path::pident(ident_undefined_recursive_module())
}

// ============================================================================
// Stamp-based predef detection (matches OCaml's type_is_builtin_path_but_option)
// ============================================================================

/// Check if a path refers to a builtin type (excluding option).
pub fn type_is_builtin_path_but_option(p: &Path) -> Option<bool> {
    match p.view() {
        PathView::Pident(id) if id.stamp() == STAMP_OPTION => Some(false),
        PathView::Pident(id) if id.stamp() == STAMP_UNIT => Some(false),
        PathView::Pident(id) if id.stamp() >= STAMP_INT && id.stamp() <= STAMP_TAGGED_TEMPLATE => {
            Some(true)
        }
        _ => None,
    }
}

/// Look up the predef ident for a given type name.
/// Returns None for non-predef names.
pub fn find_predef_ident(name: &str) -> Option<Ident> {
    match name {
        "int" => Some(ident_int()),
        "char" => Some(ident_char()),
        "float" => Some(ident_float()),
        "bool" => Some(ident_bool()),
        "unit" => Some(ident_unit()),
        "exn" => Some(ident_exn()),
        "array" => Some(ident_array()),
        "iterable" => Some(ident_iterable()),
        "asyncIterable" => Some(ident_async_iterable()),
        "list" => Some(ident_list()),
        "option" => Some(ident_option()),
        "result" => Some(ident_result()),
        "dict" => Some(ident_dict()),
        "bigint" => Some(ident_bigint()),
        "string" => Some(ident_string()),
        "unknown" => Some(ident_unknown()),
        "promise" => Some(ident_promise()),
        "taggedTemplate" => Some(ident_tagged_template()),
        _ => None,
    }
}

/// Look up the predef path for a given type name.
/// Returns None for non-predef names.
pub fn find_predef_path(name: &str) -> Option<Path> {
    find_predef_ident(name).map(Path::pident)
}
