use super::*;

#[test]
fn gpr_1760_test_keeps_checked_division_and_mod_effects_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_1760_test");
    assert!(
        output.contains("Primitive_int.div(0, 0);"),
        "expected the checked fixture to keep Primitive_int.div(0, 0), got:\n{output}"
    );
    assert!(
        output.contains("Primitive_int.mod_(0, 0);"),
        "expected the checked fixture to keep Primitive_int.mod_(0, 0), got:\n{output}"
    );
}

#[test]
fn div_by_zero_test_keeps_checked_throw_helpers_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("div_by_zero_test");
    assert!(
        output.contains("Primitive_int.div(3, 0);"),
        "expected the checked fixture to call Primitive_int.div(3, 0), got:\n{output}"
    );
    assert!(
        output.contains("Primitive_int.mod_(3, 0);"),
        "expected the checked fixture to call Primitive_int.mod_(3, 0), got:\n{output}"
    );
}

#[test]
fn array_subtle_tail_guard_keeps_positive_if_shape() {
    let output = compile_checked_in_test_file_to_js("array_subtle_test");
    assert!(
        output.contains("if (x.length >= 10) {"),
        "expected the checked-in fixture to keep the positive array-length guard, got:\n{output}"
    );
    assert!(
        output.contains("console.log(\"hi\");"),
        "expected the guarded effect to stay inside the positive branch, got:\n{output}"
    );
    assert!(
        output.contains("return;"),
        "expected the positive tail branch to keep its explicit return, got:\n{output}"
    );
    assert!(
        !output.contains("if (x.length < 10) {"),
        "unexpected negative early-return guard in checked-in fixture output:\n{output}"
    );
}

#[test]
fn test_primitive_keeps_positive_effectful_if_else_return_shape() {
    let output = compile_checked_in_test_file_to_js("test_primitive");
    assert!(
        output.contains("function u(b) {\n  if (b) {"),
        "expected test_primitive.u to keep OCaml's positive if/else guard, got:\n{output}"
    );
    assert!(
        output.contains("console.log(1);"),
        "expected the effectful success branch to stay inside the positive guard, got:\n{output}"
    );
    assert!(
        output.contains("} else {\n    return 7;\n  }"),
        "expected the fallback return to stay in an explicit else branch, got:\n{output}"
    );
    assert!(
        !output.contains("function u(b) {\n  if (!b) {"),
        "unexpected negative early-return guard for test_primitive.u:\n{output}"
    );
}

#[test]
fn pr6726_inlines_local_module_wrapper_call_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("pr6726");
    assert!(
        output.contains("let v = 33;"),
        "expected pr6726 to match the OCaml snapshot by fully inlining the wrapper call, got:\n{output}"
    );
    assert!(
        output.contains("v: v"),
        "expected the local module block to reference the call-result binding, got:\n{output}"
    );
    assert!(
        output.contains("/* No side effect */"),
        "expected pr6726 to match OCaml's pure-module classification after inlining, got:\n{output}"
    );
    assert!(
        !output.contains("v: 33"),
        "unexpected inlined local-module wrapper call result in pr6726:\n{output}"
    );
}

#[test]
fn variant_drops_pure_local_module_wrapper_call_outside_materialized_block_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("variant");
    assert!(
        !output.contains("find(p);"),
        "unexpected retained pure local-module wrapper call in variant:\n{output}"
    );
    assert!(
        output.contains("function rollback_path(subst, p) {\n  try {"),
        "expected variant.rollback_path to start directly with the try block, got:\n{output}"
    );
}

#[test]
fn a_drops_dead_functor_argument_wrapper_call_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("a");
    assert!(
        !output.contains("function add(x, y) {") && !output.contains("add(1, 2);"),
        "unexpected retained dead functor-argument wrapper or call in a:\n{output}"
    );
    assert!(
        output.contains("/* No side effect */"),
        "expected a to recover OCaml's pure-module comment after dropping the dead call, got:\n{output}"
    );
}

#[test]
fn test_match_exception_keeps_direct_try_return_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("test_match_exception");
    assert!(
        output.contains("function f(g, x) {\n  try {\n    return g(x);"),
        "expected test_match_exception to keep the try body in direct return position, got:\n{output}"
    );
    assert!(
        output.contains("if (exn.RE_EXN_ID === \"Not_found\") {\n      return 3;\n    }"),
        "expected test_match_exception to keep the catch return shape, got:\n{output}"
    );
    assert!(
        !output.contains("let y;")
            && !output.contains("y = g(x);")
            && !output.contains("return y;"),
        "unexpected staticcatch temp assignment shape remained in test_match_exception:\n{output}"
    );
}

#[test]
fn uncurried_always_keeps_non_module_field_partial_calls_inlineable() {
    let output = compile_checked_in_test_file_to_js("UncurriedAlways");
    assert!(
        output.contains("let a1 = [\n  \"x\",\n  \"y\",\n  \"z\"\n];"),
        "expected UncurriedAlways.AllLabels.a1 to stay inlined to the tuple literal, got:\n{output}"
    );
    assert!(
        !output.contains("let a1 = ptl$1(\"x\", \"z\");"),
        "unexpected preserved partial-wrapper call in UncurriedAlways:\n{output}"
    );
}

#[test]
fn gpr_1728_unit_if_tail_stays_as_condition_effect() {
    let output = compile_checked_in_test_file_to_js("gpr_1728_test");
    assert!(
        output.contains("Number.parseInt(x) !== 3;"),
        "expected the checked-in fixture to keep the condition as an effect statement, got:\n{output}"
    );
    assert!(
        !output.contains("if (Number.parseInt(x) !== 3) {"),
        "unexpected unit-return guard for the checked-in fixture:\n{output}"
    );
}

#[test]
fn gpr_1891_keeps_unit_polyvariant_guard_flattened_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_1891_test");
    assert!(
        output.contains("if (typeof x === \"object\" && x.NAME === \"Foo\" && x.VAL === 3) {"),
        "expected gpr_1891_test.foo4 to keep the flattened payload guard, got:\n{output}"
    );
    assert!(
        output.contains("return h();"),
        "expected gpr_1891_test.foo4 to keep the guarded call in the body, got:\n{output}"
    );
    assert!(
        !output.contains(
            "if (typeof x === \"object\" && x.NAME === \"Foo\") {\n    if (x.VAL !== 3) {"
        ),
        "unexpected nested negative payload guard in gpr_1891_test.foo4:\n{output}"
    );
}

#[test]
fn gpr_3154_keeps_none_guard_chain_conjoined_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3154_test");
    assert!(
        output.contains(
            "if (match !== undefined && Primitive_option.valFromOption(match) === undefined) {"
        ),
        "expected gpr_3154_test to keep the shared fallback guard chain collapsed into one positive conjunction, got:\n{output}"
    );
    assert!(
        !output.contains("if (match === undefined) {\n      return Test_utils.ok("),
        "unexpected standalone negative guard on the option match in gpr_3154_test:\n{output}"
    );
    assert!(
        !output.contains("if (Primitive_option.valFromOption(match) !== undefined) {"),
        "unexpected nested negative payload guard in gpr_3154_test:\n{output}"
    );
}

#[test]
fn gpr_3609_keeps_explicit_else_tail_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3609_test");
    assert!(
        output.contains("if (typeof state !== \"object\") {"),
        "expected gpr_3609_test.func to keep the outer object guard, got:\n{output}"
    );
    assert!(
        output.contains("  } else {\n    return 0 + state._0 | 0;\n  }"),
        "expected gpr_3609_test.func to keep the explicit else tail, got:\n{output}"
    );
    assert!(
        !output.contains(
            "if (typeof state !== \"object\") {\n    return 0;\n  }\n  return 0 + state._0 | 0;"
        ),
        "unexpected fallthrough tail in gpr_3609_test.func:\n{output}"
    );
}

#[test]
fn gpr_3770_keeps_all_zero_guard_conjoined_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3770_test");
    assert!(
        output.contains("if (a === 0 && x._1 === 0 && x._2 === 0) {"),
        "expected gpr_3770_test.show to keep the all-zero guard collapsed into one positive conjunction, got:\n{output}"
    );
    assert!(
        output.contains("return \"zeroes\";"),
        "expected gpr_3770_test.show to keep the zero case in the guarded branch, got:\n{output}"
    );
    assert!(
        output.contains("return a.toString() + x._1.toString();"),
        "expected gpr_3770_test.show to keep the non-zero fallback return after the guard, got:\n{output}"
    );
    assert!(
        !output.contains("if (a !== 0) {"),
        "unexpected leading negative guard in gpr_3770_test.show:\n{output}"
    );
    assert!(
        !output.contains("else if (x._1 !== 0) {") && !output.contains("else if (x._2 !== 0) {"),
        "unexpected nested negative guard chain in gpr_3770_test.show:\n{output}"
    );
    assert!(
        !output.contains("  } else {\n    return a.toString() + x._1.toString();\n  }"),
        "unexpected explicit else tail in gpr_3770_test.show:\n{output}"
    );
}

#[test]
fn bal_set_mini_unwraps_terminal_return_blocks_before_if_fallthrough_flattening() {
    let output = compile_checked_in_test_file_to_js("bal_set_mini");
    assert!(
        output.contains("  }\n  if (hr <= (hl + 2 | 0)) {"),
        "expected the checked-in fixture to keep the right-balance guard as fallthrough after the left branch, got:\n{output}"
    );
    assert!(
        !output.contains("    } else {\n    if (hr <= (hl + 2 | 0)) {")
            && !output.contains("    } else {\n      if (hr <= (hl + 2 | 0)) {"),
        "unexpected nested else-wrapper around the right-balance guard in the checked-in fixture:\n{output}"
    );
}

#[test]
fn bal_set_mini_binds_named_variant_switch_scrutinee_once_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("bal_set_mini");
    assert!(
        output.contains("let match = v;\n\nif (typeof match === \"object\") {"),
        "expected bal_set_mini to bind the shared named-variant scrutinee before the final switch dispatch, got:\n{output}"
    );
    assert!(
        !output.contains("if (typeof v === \"object\") {"),
        "unexpected direct final dispatch on v in bal_set_mini; OCaml binds the shared scrutinee first:\n{output}"
    );
}

#[test]
fn let_unwrap_keeps_declared_switch_binding_shape_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("LetUnwrap");
    assert!(
        output.contains("let someResult;\n\nsomeResult = x.TAG === \"Ok\" ? x._0 : ("),
        "expected LetUnwrap to keep the declared result binding before the switch assignment, got:\n{output}"
    );
    assert!(
        !output.contains("let someResult = x.TAG === \"Ok\" ? x._0 : ("),
        "unexpected initialized declaration for LetUnwrap's switch-bound result:\n{output}"
    );
}

#[test]
fn gpr_2608_test_keeps_declared_short_circuit_binding_shape_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_2608_test");
    assert!(
        output.contains("let huntGrootCondition = false;")
            && output.contains("let huntGrootCondition2 = true;"),
        "expected gpr_2608_test to keep the declared short-circuit bindings, got:\n{output}"
    );
    assert!(
        !output.contains("let tmp = false;")
            && !output.contains("let tmp$1 = true;")
            && !output.contains("let huntGrootCondition = tmp;")
            && !output.contains("let huntGrootCondition2 = tmp$1;"),
        "unexpected temporary alias binding remained in gpr_2608_test:\n{output}"
    );
}

#[test]
fn variant_pattern_matching_spreads_keeps_positive_unit_fallthrough_guards_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("VariantPatternMatchingSpreads");
    assert!(
        output.contains(
            "function doWithB(b) {\n  if (b === \"One\") {\n    console.log(\"aaa\");\n    return;\n  }\n  console.log(\"twwwoooo\");"
        ),
        "expected doWithB to keep the positive-guard fallthrough shape, got:\n{output}"
    );
    assert!(
        output.contains("function lookupOpt(b) {\n  if (b !== undefined) {"),
        "expected lookupOpt to keep the positive option guard, got:\n{output}"
    );
    assert!(
        output.contains(
            "function doWithZ(z) {\n  if (z === \"First\") {\n    console.log(\"First\");\n    return;\n  }\n  console.log(\"Second\");"
        ),
        "expected doWithZ to keep the positive-guard fallthrough shape, got:\n{output}"
    );
}

#[test]
fn variant_pattern_matching_spreads_with_payloads_keeps_nested_handlers_inline_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("VariantPatternMatchingSpreadsWithPayloads");
    assert!(
        output.contains(
            "function lookup2(d) {\n  if (typeof d !== \"object\") {\n    switch (d) {\n      case \"Four\" :\n      case \"Five\" :\n        return doWithB(d);\n      case \"Six\" :\n        console.log(\"Got rest of d\");\n        return;\n      default:\n        return doWithA(d);\n    }\n  } else {"
        ),
        "expected lookup2 to keep the shared const-side handler inline inside the switch, got:\n{output}"
    );
    assert!(
        output.contains(
            "  } else {\n    if (d.TAG !== \"Seven\") {\n      return doWithA(d);\n    }\n    console.log(\"Got rest of d\");\n    return;\n  }\n}"
        ),
        "expected lookup2 to keep the payload-side handler inline inside the outer else branch, got:\n{output}"
    );
    assert!(
        !output.contains("  doWithB(d);\n}"),
        "unexpected nested fallthrough handler escaped after lookup2's switch:\n{output}"
    );
}

#[test]
fn inline_record_test_keeps_positive_exception_fallthrough_guard_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("inline_record_test");
    assert!(
        output.contains(
            "function ff0(x) {\n  if (x.RE_EXN_ID === A4) {\n    x.x = x.x + 1 | 0;\n    x.z = x.z + 1 | 0;\n    return;\n  }\n}"
        ),
        "expected inline_record_test.ff0 to keep the positive exception guard with guarded fallthrough, got:\n{output}"
    );
    assert!(
        !output.contains("if (x.RE_EXN_ID !== A4) {"),
        "unexpected negative early-return guard in inline_record_test.ff0:\n{output}"
    );
}

#[test]
fn json_decorders_keeps_needvalue_if_temp_declared_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("json_decorders");
    assert!(
        output.contains("let tmp;\n  tmp = typeof email === \"string\" ? email : undefined;"),
        "expected json_decorders to keep the declared conditional temp before assignment, got:\n{output}"
    );
    assert!(
        !output.contains("let tmp = typeof email === \"string\" ? email : undefined;"),
        "unexpected initialized conditional temp in json_decorders:\n{output}"
    );
}

#[test]
fn res_debug_materializes_two_field_record_payload_bindings_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("res_debug");
    assert!(
        output.contains("let ok_name = optionMap(undefined, x => x);")
            && output.contains("let bad_name = optionMap(undefined, x => x);"),
        "expected res_debug to materialize the optional record payload temps, got:\n{output}"
    );
    assert!(
        output.contains("let ok = {\n  name: ok_name\n};")
            && output.contains("let bad = {\n  name: bad_name\n};"),
        "expected res_debug to reuse the materialized record payload temps, got:\n{output}"
    );
}

#[test]
fn record_coercion_materializes_nested_two_field_record_blocks_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("RecordCoercion");
    assert!(
        output.contains("let TestInlining_a = {\n  number: 42,\n  name: \"a\"\n};"),
        "expected RecordCoercion to keep the nested record payload materialized, got:\n{output}"
    );
    assert!(
        output.contains("let TestInlining = {\n  a: TestInlining_a,\n  name: \"a\"\n};"),
        "expected RecordCoercion to reuse the nested record temp in the module block, got:\n{output}"
    );
}

#[test]
fn record_debug_test_keeps_record_update_projection_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("record_debug_test");
    assert!(
        output.contains("let u_a = 2;")
            && output.contains("let u_b = v.b;")
            && output.contains("let u = {\n  a: u_a,\n  b: u_b\n};"),
        "expected record_debug_test to keep the record-update projection materialized, got:\n{output}"
    );
    assert!(
        !output.contains("let v_b = {\n  xx: 2,\n  yy: 3\n};")
            && !output.contains("let u_b = {\n  xx: 2,\n  yy: 3\n};"),
        "did not expect record_debug_test to inline the nested allocating record field, got:\n{output}"
    );
}

#[test]
fn gpr_2503_test_keeps_obj_external_accumulator_before_optional_value_temp_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_2503_test");
    assert!(
        output.contains(
            "function makeWrapper4(foo, param) {\n  console.log(2);\n  let tmp = {};\n  let tmp$1 = foo > 100 ? undefined : ("
        ),
        "expected gpr_2503_test to materialize the object accumulator before the complex optional value temp, got:\n{output}"
    );
    assert!(
        output.contains(
            "function makeWrapper3(foo, param) {\n  console.log(2);\n  let tmp = {};\n  if (foo !== undefined) {"
        ),
        "expected gpr_2503_test to keep the simple optional wrapper on the same tmp accumulator naming path, got:\n{output}"
    );
    assert!(
        !output.contains("let obj = foo > 100 ? undefined") && !output.contains("let obj$1 = {};"),
        "unexpected Rust-only object-temp ordering remained in gpr_2503_test:\n{output}"
    );
}

#[test]
fn derive_projector_test_collapses_pure_record_projection_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("derive_projector_test");
    assert!(
        output.contains("let v = {\n  TAG: \"D_int\",\n  _0: 3\n};"),
        "expected the checked-in fixture to collapse the pure record projection to the payload value, got:\n{output}"
    );
    assert!(
        !output.contains("let v = ({") && !output.contains("}).d;"),
        "unexpected materialized fresh-record projection remained in checked-in fixture output:\n{output}"
    );
}

#[test]
fn deriving_accessors_curried_rewrites_alias_initializers_through_exported_bindings_like_snapshot()
{
    let output = compile_checked_in_test_file_to_js("DerivingAccessorsCurried");
    assert!(
        output.contains("let _myFieldAlias = myField;")
            && output.contains("let _noParamAlias = \"NoParam\";")
            && output.contains("let _numAlias = num;")
            && output.contains("let _doubleNumAlias = doubleNum;"),
        "expected DerivingAccessorsCurried to reuse the underlying exported bindings in later alias initializers, got:\n{output}"
    );
    assert!(
        !output.contains("let myField$1 = myField;")
            && !output.contains("let num$1 = num;")
            && !output.contains("let doubleNum$1 = doubleNum;")
            && !output.contains("let _noParamAlias = noParam;"),
        "unexpected redundant same-name export aliases remained in DerivingAccessorsCurried:\n{output}"
    );
    let compose_idx = output.find("function compose").unwrap();
    let no_param_idx = output.find("let noParam = \"NoParam\";").unwrap();
    assert!(
        no_param_idx < compose_idx,
        "expected the rebound literal export to retain source order before compose in DerivingAccessorsCurried, got:\n{output}"
    );
}

#[test]
fn deriving_accessors_uncurried_rewrites_alias_initializers_through_exported_bindings_like_snapshot()
 {
    let output = compile_checked_in_test_file_to_js("DerivingAccessorsUncurried");
    assert!(
        output.contains("let _myFieldAlias = myField;")
            && output.contains("let _noParamAlias = \"NoParam\";")
            && output.contains("let _numAlias = num;")
            && output.contains("let _doubleNumAlias = doubleNum;"),
        "expected DerivingAccessorsUncurried to reuse the underlying exported bindings in later alias initializers, got:\n{output}"
    );
    assert!(
        !output.contains("let myField$1 = myField;")
            && !output.contains("let num$1 = num;")
            && !output.contains("let doubleNum$1 = doubleNum;")
            && !output.contains("let _noParamAlias = noParam;"),
        "unexpected redundant same-name export aliases remained in DerivingAccessorsUncurried:\n{output}"
    );
    let compose_idx = output.find("function compose").unwrap();
    let no_param_idx = output.find("let noParam = \"NoParam\";").unwrap();
    assert!(
        no_param_idx < compose_idx,
        "expected the rebound literal export to retain source order before compose in DerivingAccessorsUncurried, got:\n{output}"
    );
}

#[test]
fn coercion_rebinds_same_name_literal_exports_after_surviving_function_binding_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("Coercion");
    let foo_idx = output.find("function foo").unwrap();
    let x_idx = output.find("let x = 1;").unwrap();
    let xx_idx = output.find("let xx = 1;").unwrap();
    assert!(
        foo_idx < x_idx && x_idx < xx_idx,
        "expected Coercion to keep the surviving function binding before the rebound literal exports, got:\n{output}"
    );
}

#[test]
fn block_alias_test_keeps_exported_alias_before_mocha_effects_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("block_alias_test");
    let alias_idx = output.find("let f = Primitive_object.equal;").unwrap();
    let describe_idx = output.find("Mocha.describe(").unwrap();
    assert!(
        alias_idx < describe_idx,
        "expected block_alias_test to keep the exported alias before Mocha.describe, got:\n{output}"
    );
}

#[test]
fn ffi_arity_test_keeps_exported_alias_before_later_effects_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ffi_arity_test");
    let alias_idx = output.find("let abc_u = abc;").unwrap();
    let call_idx = output
        .rfind("((function(){console.log(\"forgiving arity\")})());")
        .unwrap();
    assert!(
        alias_idx < call_idx,
        "expected ffi_arity_test to keep abc_u before the later top-level effects, got:\n{output}"
    );
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn module_parameter_test_keeps_local_module_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("module_parameter_test");
    assert!(
        output.contains("let s = Stdlib_String;\n\nlet N = {\n  s: s\n};"),
        "expected module_parameter_test to keep the local module alias binding materialized, got:\n{output}"
    );
    assert!(
        output.contains("3, \"abc\".length"),
        "expected module_parameter_test to match current OCaml by reducing the exported wrapper call at the checked site, got:\n{output}"
    );
    assert!(
        !output.contains("s: Stdlib_String") && !output.contains("3, v(\"abc\")"),
        "unexpected inlined local-module field or stale snapshot-era wrapper call remained in module_parameter_test:\n{output}"
    );
}

#[test]
fn import_keeps_nested_module_field_alias_binding_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("Import");
    assert!(
        output.contains("let N1_each = O.forEach;\n\nlet N1 = {\n  O: O,\n  each: N1_each\n};"),
        "expected Import to keep the nested module-field alias binding materialized, got:\n{output}"
    );
    assert!(
        output.contains("let N_each = N2.forEach;\n\nlet N = {\n  N0: N0,\n  N1: N1,\n  N2: N2,\n  each: N_each\n};"),
        "expected Import to keep the outer module-field alias binding materialized with the module-prefixed name, got:\n{output}"
    );
    assert!(
        !output.contains("each: O.forEach") && !output.contains("each: each$1"),
        "unexpected inlined nested module-field alias remained in Import:\n{output}"
    );
}

#[test]
fn relative_path_keeps_exported_import_alias_chain_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("relative_path");
    assert!(
        output.contains("let foo = FileJs.foo;\n") && output.contains("let bar = foo;\n"),
        "expected relative_path to keep the exported import alias chain materialized, got:\n{output}"
    );
    assert!(
        !output.contains("let bar = FileJs.foo;"),
        "unexpected direct qualified import rebound remained in relative_path:\n{output}"
    );
}

#[test]
fn import_attributes_keeps_exported_alias_bindings_before_log_calls_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ImportAttributes");
    assert!(
        output.contains("let myJson = MyJsonJson;\n\nconsole.log(myJson);"),
        "expected ImportAttributes to keep the exported JSON alias binding ahead of the log call, got:\n{output}"
    );
    assert!(
        output.contains("let buttonCss = MyCssCss.button;\n\nconsole.log(buttonCss);"),
        "expected ImportAttributes to keep the exported CSS alias binding ahead of the log call, got:\n{output}"
    );
    assert!(
        !output.contains("console.log(MyJsonJson);")
            && !output.contains("console.log(MyCssCss.button);"),
        "unexpected direct imported-value logging remained in ImportAttributes:\n{output}"
    );
}

#[test]
#[test]
#[test]
fn inline_string_test_keeps_alias_materialized_named_matcher_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("inline_string_test");
    assert!(
        output.contains("function f(x) {\n  if (x !== undefined) {\n    return \"Some\";\n  } else {\n    return \"None\";\n  }\n}"),
        "expected inline_string_test to keep the named matcher function materialized, got:\n{output}"
    );
    assert!(
        output.contains("console.log([\n  f(3),\n  \"None\",\n  \"Some\"\n]);"),
        "expected inline_string_test to keep the alias-substituted `f(3)` call while inlining only the direct constant cases, got:\n{output}"
    );
    assert!(
        !output.contains("console.log([\n  \"Some\",\n  \"None\",\n  \"Some\"\n]);"),
        "unexpected full constant inlining remained in inline_string_test:\n{output}"
    );
}

#[test]
fn gpr_3142_test_reuses_same_name_export_alias_bindings_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_3142_test");
    assert!(
        output.contains("Test_utils.eq(\"File \\\"gpr_3142_test.res\\\", line 18, characters 7-14\", tToJs(\"a\"), \"x\")")
            && output.contains("Test_utils.eq(\"File \\\"gpr_3142_test.res\\\", line 23, characters 7-14\", tFromJs(\"x\"), \"a\")"),
        "expected gpr_3142_test to inline the exported aliases back to direct converter calls at the checked internal sites, got:\n{output}"
    );
    assert!(
        output.contains("let v = tToJs;\n\nlet u = tFromJs;"),
        "expected gpr_3142_test to keep the exported alias bindings materialized for the final export payload, got:\n{output}"
    );
    assert!(
        output.contains("export {\n  tToJs,\n  tFromJs,\n  v,\n  u,\n}")
            && output.find("Mocha.describe(\"Gpr_3142_test\"").is_some()
            && output.find("let v = tToJs;").is_some()
            && output.find("Mocha.describe(\"Gpr_3142_test\"").unwrap()
                < output.find("let v = tToJs;").unwrap()
            && !output.contains("v$1 as v")
            && !output.contains("u$1 as u"),
        "expected gpr_3142_test to keep the aliases only as late export bindings with no rebound export aliases, got:\n{output}"
    );
}

#[test]
fn string_set_reuses_same_name_export_aliases_for_module_fields_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("string_set");
    assert!(
        output.contains("return Set_gen.empty;")
            && output.contains("return Set_gen.singleton(x0);")
            && output.contains("return Set_gen.of_sorted_list(Stdlib_List.sort(l, (a, b) => Primitive_string.compare(a, b) | 0));"),
        "expected string_set to inline exported module-field aliases at ordinary internal call sites like OCaml, got:\n{output}"
    );
    assert!(
        output.contains("let empty = Set_gen.empty;")
            && output.contains("let singleton = Set_gen.singleton;")
            && output.contains("let of_sorted_list = Set_gen.of_sorted_list;")
            && output.find("function invariant(t)").is_some()
            && output.find("let empty = Set_gen.empty;").is_some()
            && output.find("function invariant(t)").unwrap()
                < output.find("let empty = Set_gen.empty;").unwrap(),
        "expected string_set to keep those alias bindings only in the later export section, got:\n{output}"
    );
    assert!(
        output.contains("export {\n  compare_elt,\n  empty,")
            && output.contains("  singleton,")
            && output.contains("  of_sorted_list,")
            && !output.contains("empty$1 as empty")
            && !output.contains("singleton$1 as singleton")
            && !output.contains("of_sorted_list$1 as of_sorted_list"),
        "unexpected rebound export aliases remained in string_set:\n{output}"
    );
}

#[test]
fn string_bound_get_test_keeps_direct_literal_export_binding_before_internal_uses_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("string_bound_get_test");
    assert!(
        output.contains("let v = \"ghos\";\n\nlet u_a = v[0];")
            && output.contains("function u_b() {\n  return v[-1];\n}")
            && output.find("let v = \"ghos\";").is_some()
            && output.find("let u_a = v[0];").is_some()
            && output.find("let v = \"ghos\";").unwrap() < output.find("let u_a = v[0];").unwrap(),
        "expected string_bound_get_test to keep the direct literal export binding ahead of later internal uses like OCaml, got:\n{output}"
    );
    assert!(
        !output.contains("function u_b() {\n  return \"ghos\"[-1];\n}"),
        "unexpected literal inlining of the exported binding into string_bound_get_test.u_b:\n{output}"
    );
}

#[test]
fn external_shadow_keeps_new_wrapper_after_new_module_binding_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ExternalShadow");
    assert!(
        output.contains(
            "let New = {};\n\nfunction url(prim) {\n  return new URL(prim);\n}\n\nlet Global = {};"
        ),
        "expected ExternalShadow to keep the @new wrapper after the New module binding and before Global, got:\n{output}"
    );
    assert!(
        output.find("let X = {};").is_some()
            && output.find("function url(prim) {").is_some()
            && output.find("let X = {};").unwrap() < output.find("function url(prim) {").unwrap(),
        "expected ExternalShadow to keep earlier module/value bindings ahead of the @new wrapper, got:\n{output}"
    );
}

#[test]
fn forward_ref_regress_keeps_props_ref_wrapper_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("forwardRef_regress");
    assert!(
        output.contains("let make = React.forwardRef((props, ref) => props.children);"),
        "expected forwardRef_regress to keep the OCaml-style props/ref wrapper materialized, got:\n{output}"
    );
    assert!(
        !output.contains("function make(")
            && !output.contains("React.forwardRef(make)")
            && !output.contains("make$1 as make"),
        "unexpected helper hoist or rebound export alias remained in forwardRef_regress:\n{output}"
    );
}

#[test]
#[test]
fn offset_keeps_exported_module_alias_placeholder_before_local_module_block_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("offset");
    assert!(
        output.contains("let $$Set;\n\nlet M = {\n  x: 1,\n  $$Set: $$Set\n};"),
        "expected offset to keep the exported module alias placeholder before M, got:\n{output}"
    );
    assert!(
        !output.contains("$$Set: undefined")
            && !output.contains("let $$Set$1 = $$Set;")
            && !output.contains("$$Set$1 as $$Set"),
        "unexpected placeholder-field inlining or rebound export alias remained in offset:\n{output}"
    );
}

#[test]
fn gpr_977_keeps_exported_constant_name_while_inlining_non_export_uses_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_977_test");
    assert!(
        output.contains("let u = f(-2147483648);"),
        "expected gpr_977_test to inline the non-export call argument to the literal, got:\n{output}"
    );
    assert!(
        output.contains("Test_utils.eq(\"File \\\"gpr_977_test.res\\\", line 15, characters 39-46\", -2147483648, u)")
            && output.contains("let min_32_int = -2147483648;"),
        "expected gpr_977_test to keep the exported constant name only at the export binding site, got:\n{output}"
    );
    assert!(
        !output.contains("let min_32_int$1 = -2147483648;")
            && !output.contains("f(min_32_int)")
            && !output.contains("Test_utils.eq(\"File \\\"gpr_977_test.res\\\", line 15, characters 39-46\", min_32_int, u)"),
        "unexpected retained internal exported-constant alias uses remained in gpr_977_test:\n{output}"
    );
}

#[test]
fn async_await_inlines_exported_wrapped_named_helper_calls_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("async_await");
    assert!(
        output.contains("function next(n) {\n  return n + 1 | 0;\n}\n\nasync function useNext() {\n  return 4;\n}"),
        "expected async_await to inline the exported wrapped helper call to the constant result, got:\n{output}"
    );
    assert!(
        !output.contains("async function useNext() {\n  return next(3);\n}"),
        "unexpected retained wrapped helper call remained in async_await:\n{output}"
    );
}

#[test]
fn async_inline_keeps_same_name_export_alias_for_eta_reduced_async_wrapper_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("async_inline");
    assert!(
        output.contains("let broken$2 = broken$1;"),
        "expected async_inline to keep the eta-reduced async wrapper export alias binding, got:\n{output}"
    );
    assert!(
        output.contains("broken$2 as broken,"),
        "expected async_inline to export the preserved alias binding, got:\n{output}"
    );
    assert!(
        !output.contains("broken$1 as broken,"),
        "unexpected direct export of the underlying async helper in async_inline:\n{output}"
    );
}

#[test]
fn gpr_4900_inlines_local_matcher_calls_to_constants_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_4900_test");
    assert!(
        output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 14, characters 7-14\", true, true);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 15, characters 7-14\", false, false);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 16, characters 7-14\", true, true);"
        ),
        "expected gpr_4900_test to inline the local matcher calls to constants, got:\n{output}"
    );
    assert!(
        !output.contains("let showToJs = x =>"),
        "unexpected retained local matcher helper in gpr_4900_test:\n{output}"
    );
}

#[test]
fn gpr_4924_inlines_local_variant_matcher_calls_to_constants_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_4924_test");
    assert!(
        output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 29, characters 7-14\", false, false);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 30, characters 7-14\", true, true);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 31, characters 7-14\", true, true);"
        ),
        "expected gpr_4924_test to inline the local matcher calls to constants, got:\n{output}"
    );
    assert!(
        !output.contains("let u2 = b =>"),
        "unexpected retained local matcher helper in gpr_4924_test:\n{output}"
    );
}

#[test]
fn uncurried_cast_keeps_local_module_field_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("uncurried_cast");
    assert!(
        output.contains("let map = Stdlib_List.map;\n\nlet List = {\n  map: map\n};"),
        "expected uncurried_cast to keep the eta-reduced module field alias materialized in List, got:\n{output}"
    );
    assert!(
        output.contains("let l = Stdlib_List.map({")
            && output.contains("function partial(x) {\n  return Stdlib_List.map({")
            && output.contains("let l$1 = Stdlib_List.map({")
            && output.contains("function partial$1(extra) {\n  return Stdlib_List.map({"),
        "expected uncurried_cast to rewrite map call sites back to Stdlib_List.map like OCaml, got:\n{output}"
    );
    assert!(
        !output.contains("let List = {\n  map: Belt_List.map\n};"),
        "unexpected inlined Belt_List.map inside the local module block for uncurried_cast:\n{output}"
    );
    assert!(
        !output.contains("let l = map({")
            && !output.contains("function partial(x) {\n  return map({")
            && !output.contains("let l$1 = map({")
            && !output.contains("function partial$1(extra) {\n  return map({"),
        "unexpected residual local alias calls remained in uncurried_cast:\n{output}"
    );
}

#[test]
fn recursive_module_test_keeps_include_field_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("recursive_module_test");
    assert!(
        output.contains("let fact$1 = M.fact;\n\nlet Fact = {\n  M: M,\n  fact: fact$1\n};"),
        "expected recursive_module_test to keep the included module field alias materialized, got:\n{output}"
    );
    assert!(
        output.contains("120, fact$1(5)"),
        "expected recursive_module_test to keep the fact$1 call shape, got:\n{output}"
    );
    assert!(
        !output.contains("let Fact_fact = M.fact;") && !output.contains("120, M.fact(5)"),
        "unexpected renamed or inlined recursive module field alias in recursive_module_test:\n{output}"
    );
}

#[test]
fn complex_while_loop_keeps_effectful_condition_blocks_inside_iifes() {
    let output = compile_checked_in_test_file_to_js("complex_while_loop");
    assert!(
        output.contains("while ((() => {")
            && output.contains("let fib = x => {")
            && output.contains("return fib(n) > 10;"),
        "expected complex_while_loop to keep the recursive condition binding scoped inside the while predicate IIFE, got:\n{output}"
    );
    assert!(
        output.contains("let b = 9;") && output.contains("return (3 + b | 0) > 10;"),
        "expected complex_while_loop's second predicate to stay as an IIFE-wrapped block, got:\n{output}"
    );
    assert!(
        !output.contains("while (fib(n) > 10)") && !output.contains("while ((3 + b | 0) > 10)"),
        "unexpected dropped predicate-prelude scope in complex_while_loop:\n{output}"
    );
}

#[test]
fn test_while_side_effect_keeps_local_condition_bindings_in_iifes() {
    let output = compile_checked_in_test_file_to_js("test_while_side_effect");
    assert!(
        output.contains("while ((() => {")
            && output.contains("let y = 3;")
            && output.contains("console.log(x.contents.toString());")
            && output.contains("y = y + 1 | 0;")
            && output.contains("x.contents = x.contents + 1 | 0;")
            && output.contains("return (fib(x.contents) + fib(x.contents) | 0) < 20;"),
        "expected test_while_side_effect to keep the local binding and side effects inside the predicate IIFE, got:\n{output}"
    );
    assert!(
        !output.contains(
            "while (x.contents = x.contents + 1 | 0, (fib(x.contents) + fib(x.contents) | 0) < 20)"
        ),
        "unexpected flattened predicate sequence lost the local binding scope in test_while_side_effect:\n{output}"
    );
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn internal_unused_test_omits_dead_private_relative_external_import_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("internal_unused_test");

    assert!(
        !output.contains("import * as X from \"./x\";"),
        "expected dead private relative external import to be omitted, got:\n{output}"
    );
    assert!(
        output.contains(
            "import * as Primitive_exceptions from \"@rescript/runtime/lib/es6/Primitive_exceptions.js\";"
        ),
        "expected checked-in runtime import to remain, got:\n{output}"
    );
}
