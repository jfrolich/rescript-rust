use super::*;
use crate::expect_dump;
use crate::js_ir::arena::{JsDepsProgram as DepsProgram, JsProgram as Program};
use crate::js_ir::dump;
use crate::js_ir::printer::{print_expr, print_stmts};
use crate::js_ir::test_util::test_props;
use crate::lambda::LamLoc;
use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass;
use crate::lambda::js_pass_flatten_and_mark_dead::{
    apply_js_flatten_and_mark_dead_pass, apply_js_flatten_pass,
};
use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass;
use crate::lambda::js_shake::apply_js_shake_pass;

#[test]
fn lowers_js_var_without_args_to_a_value() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "process".to_string(),
            arg_types: vec![],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "process".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            },
        })),
        vec![],
        LamLoc::NONE,
    );

    let compiled = compiler.compile_expr_lam(&lam);
    assert!(compiled.prelude.is_empty());
    expect_dump!(dump::expr(&compiler.j, compiled.expr), "process");
}

#[test]
fn lowers_js_var_calls_with_runtime_args_even_without_external_arg_metadata() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "foo1".to_string(),
            arg_types: vec![],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "foo1".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            },
        })),
        vec![Lambda::Lconst(Constant::Int {
            i: 10,
            comment: None,
        })],
        LamLoc::NONE,
    );

    let program = compiler.compile_program(&lam);
    expect_dump!(
        dump::block(&program.arena, &program.block),
        "Exp(Call[Na](foo1; 10))"
    );
}

#[test]
fn lowers_module_external_calls_to_namespace_imports() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "describe".to_string(),
            arg_types: vec![],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "describe".to_string(),
                },
                module_: Some(ModuleSource::ModuleNamed(external_module("mocha"))),
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![],
        LamLoc::NONE,
    );

    let deps = compiler.compile_deps_program(&lam);
    assert!(matches!(
        deps.modules.as_slice(),
        [ModuleId {
            kind: Kind::External { name, default, .. },
            ..
        }] if name == "mocha" && !default
    ));

    expect_dump!(
        dump::block(&deps.program.arena, &deps.program.block),
        "Exp(Call[Na](Mocha.describe<External { name: \"mocha\", default: false, import_attributes: None }>; ))"
    );
}

#[test]
fn translates_external_module_values_to_qualified_members_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let expr = compiler.translate_scoped_module_value(
        Some(&external_module("react/jsx-runtime")),
        "jsx",
        &[],
    );

    expect_dump!(
        dump::expr(&compiler.j, expr),
        "JsxRuntime.jsx<External { name: \"react/jsx-runtime\", default: false, import_attributes: None }>"
    );
    assert_eq!(print_expr(&compiler.j, expr), "JsxRuntime.jsx");
}

#[test]
fn lowers_pjs_object_get_to_method_calls() {
    let mut compiler = LambdaCompiler::new();
    let john = Ident::create_persistent("john");
    let lam = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::prim(
            Primitive::PjsObjectGet("say".to_string()),
            vec![Lambda::var(john)],
            LamLoc::NONE,
        )),
        ap_args: vec![
            Lambda::const_(Constant::String("hey".to_string())),
            Lambda::const_(Constant::String("jude".to_string())),
        ],
        ap_info: ApInfo {
            loc: LamLoc::NONE,

            status: ApplyStatus::Uncurry,
        },
    }));

    let program = compiler.compile_program(&lam);
    let rendered = print_stmts(&program.arena, &program.block);
    assert_eq!(rendered, "john.say(\"hey\", \"jude\");");
}

#[test]
fn lowers_pjs_object_set_to_property_assignments() {
    let mut compiler = LambdaCompiler::new();
    let student = Ident::create_persistent("student1");
    let lam = Lambda::prim(
        Primitive::PjsObjectSet("name".to_string()),
        vec![
            Lambda::var(student),
            Lambda::const_(Constant::String("Mary".to_string())),
        ],
        LamLoc::NONE,
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_stmts(&program.arena, &program.block);
    assert_eq!(rendered, "student1.name = \"Mary\";");
}

#[test]
fn lowers_spliced_js_calls_by_flattening_literal_variadic_arrays() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "join".to_string(),
            arg_types: vec![Param::dummy()],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "join".to_string(),
                },
                module_: Some(ModuleSource::ModuleNamed(external_module("path"))),
                scopes: vec![],
                variadic: true,
                effective_arity: 1,
            },
        })),
        vec![Lambda::prim(
            Primitive::Pmakearray,
            vec![
                Lambda::const_(Constant::String(".".to_string())),
                Lambda::const_(Constant::String("Node_path_test".to_string())),
            ],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_stmts(&program.arena, &program.block);
    assert_eq!(rendered, "Path.join(\".\", \"Node_path_test\");");
}

#[test]
fn lowers_default_module_values_in_dynamic_imports() {
    let mut compiler = LambdaCompiler::new();
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pimport(Box::new(ImportSource::ImportExternal {
            module_: external_module("a"),
            path: vec!["default".to_string()],
        })),
        vec![],
        LamLoc::NONE,
    ));
    let rendered = print_stmts(&program.arena, &program.block);
    assert_eq!(rendered, "import(\"a\").then(m => m.default);");
}

#[test]
fn lowers_js_send_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "toString".to_string(),
            arg_types: vec![
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgEmpty,
                },
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgOptional,
                },
            ],
            ffi: ExternalDecl {
                kind: DeclKind::DeclSend {
                    name: "toString".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 2,
            },
        })),
        vec![
            Lambda::const_(Constant::Float("42.".to_string())),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        LamLoc::NONE,
    );

    let rendered = {
        let p = compiler.compile_program(&lam);
        print_stmts(&p.arena, &p.block)
    };
    assert_eq!(rendered, "(42).toString();");
}

#[test]
fn lowers_js_new_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "RegExp".to_string(),
            arg_types: vec![
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgEmpty,
                },
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgOptional,
                },
            ],
            ffi: ExternalDecl {
                kind: DeclKind::DeclNew {
                    name: "RegExp".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![
            Lambda::const_(Constant::String("ab+c".to_string())),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        LamLoc::NONE,
    );

    let rendered = {
        let p = compiler.compile_program(&lam);
        print_stmts(&p.arena, &p.block)
    };
    assert_eq!(rendered, "new RegExp(\"ab+c\");");
}

#[test]
fn lowers_external_polyvar_string_and_int_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "consume".to_string(),
            arg_types: vec![
                Param {
                    arg_type: Attr::PolyVarString {
                        descr: vec![
                            ("on_closed".to_string(), "on_closed".to_string()),
                            ("on_open".to_string(), "on_open".to_string()),
                            ("in_".to_string(), "in".to_string()),
                        ],
                    },
                    arg_label: LabelNoname::ArgEmpty,
                },
                Param {
                    arg_type: Attr::Int(vec![
                        ("on_closed".to_string(), 0),
                        ("on_open".to_string(), 3),
                        ("in_".to_string(), 4),
                    ]),
                    arg_label: LabelNoname::ArgEmpty,
                },
            ],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "consume".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![
            Lambda::const_(Constant::Pointer("in_".to_string())),
            Lambda::const_(Constant::Pointer("on_open".to_string())),
        ],
        LamLoc::NONE,
    );

    let rendered = {
        let p = compiler.compile_program(&lam);
        print_stmts(&p.arena, &p.block)
    };
    assert_eq!(rendered, "consume(\"in\", 3);");
}

#[test]
fn lowers_external_polyvar_payload_args_to_two_js_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "handle".to_string(),
            arg_types: vec![Param {
                arg_type: Attr::PolyVar {
                    descr: Some(vec![("b".to_string(), "renamed".to_string())]),
                },
                arg_label: LabelNoname::ArgEmpty,
            }],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "handle".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![Lambda::const_(Constant::Block {
            tag_info: Box::new(TagInfo::PolyVar("b".to_string())),
            elements: vec![Constant::Pointer("b".to_string()), Constant::int(2)],
        })],
        LamLoc::NONE,
    );

    let rendered = {
        let p = compiler.compile_program(&lam);
        print_stmts(&p.arena, &p.block)
    };
    assert_eq!(rendered, "handle(\"renamed\", 2);");
}

#[test]
fn bs_unwrap_keeps_exported_polyvar_wrappers_materialized_like_snapshot() {
    let source = r#"
@val
external log1: @unwrap
[
  | #Pair(string, int)
  | #Int(int)
  | #String(string)
] => unit = "console.log"

let arg_string = #String("hi runtime")
let _ = log1(arg_string)

let arg_pair = #Pair("hi", 1)
let _ = log1(arg_pair)
"#;

    let output = compile_test_source_to_js(source, "bs_unwrap_exported_polyvars.res").unwrap();

    assert!(
        output.contains("console.log(arg_string.VAL);"),
        "expected the exported string polyvar wrapper to stay materialized, got:\n{output}"
    );
    assert!(
        output.contains("console.log(arg_pair.VAL);"),
        "expected the exported pair polyvar wrapper to stay materialized, got:\n{output}"
    );
    assert!(
        !output.contains("console.log(\"hi runtime\");"),
        "did not expect the exported string polyvar wrapper to unwrap to a raw payload:\n{output}"
    );
    assert!(
        !output.contains("let arg_pair_1 = ["),
        "did not expect the exported pair payload to be split into a separate temp:\n{output}"
    );
}

#[test]
fn lowers_marshaled_constant_args_in_js_call() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "somefn".to_string(),
            arg_types: vec![Param {
                arg_type: Attr::ArgCst(Cst::ArgJsonLit("{foo:true}".to_string())),
                arg_label: LabelNoname::ArgEmpty,
            }],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "somefn".to_string(),
                },
                module_: None,
                scopes: vec!["somescope".to_string()],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![],
        LamLoc::NONE,
    );

    let program = compiler.compile_program(&lam);
    expect_dump!(
        dump::block(&program.arena, &program.block),
        "Exp(Call[Na](somescope.somefn; Json(\"{foo:true}\")))"
    );
}

#[test]
fn lowers_js_object_create_with_marshaled_fields() {
    let mut compiler = LambdaCompiler::new();
    let name_ident = Ident::create_local("name");
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![
            ObjParam {
                obj_arg_type: Attr::ArgCst(Cst::ArgJsonLit("false".to_string())),
                obj_arg_label: Label::ObjLabel {
                    name: "objectMode".to_string(),
                },
            },
            ObjParam {
                obj_arg_type: Attr::Nothing,
                obj_arg_label: Label::ObjLabel {
                    name: "name".to_string(),
                },
            },
            ObjParam {
                obj_arg_type: Attr::ArgCst(Cst::ArgJsonLit("true".to_string())),
                obj_arg_label: Label::ObjLabel {
                    name: "someOther".to_string(),
                },
            },
            ObjParam {
                obj_arg_type: Attr::ExternUnit,
                obj_arg_label: Label::ObjEmpty,
            },
        ]),
        vec![
            Lambda::var(name_ident),
            Lambda::const_(Constant::JsUndefined { is_unit: true }),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    expect_dump!(
        dump::expr(&compiler.j, compiled.expr),
        "{\"objectMode\": Json(\"false\"), \"name\": name, \"someOther\": Json(\"true\")}"
    );
}

#[test]
fn lowers_js_object_create_with_polyvar_string_field_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::PolyVarString {
                descr: vec![
                    ("lookup".to_string(), "lookup".to_string()),
                    ("best_fit".to_string(), "best fit".to_string()),
                ],
            },
            obj_arg_label: Label::ObjLabel {
                name: "localeMatcher".to_string(),
            },
        }]),
        vec![Lambda::const_(Constant::Pointer("best_fit".to_string()))],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    expect_dump!(
        dump::expr(&compiler.j, compiled.expr),
        "{\"localeMatcher\": \"best fit\"}"
    );
}

#[test]
fn lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::PolyVarString {
                descr: vec![
                    ("numeric".to_string(), "numeric".to_string()),
                    ("two_digit".to_string(), "2-digit".to_string()),
                ],
            },
            obj_arg_label: Label::ObjOptional {
                name: "day".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::Pointer("two_digit".to_string()))],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    expect_dump!(
        dump::expr(&compiler.j, compiled.expr),
        "{\"day\": \"2-digit\"}"
    );
}

#[test]
fn bind_switch_scrutinee_once_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let (prelude, expr) = {
        let a0 = vec![];
        let a1 = JE::call(
            JE::var(Ident::create_local("compute"), &mut compiler.j),
            &[JE::number(Number::int(1), &mut compiler.j)],
            CallInfo::default(),
            &mut compiler.j,
        );
        compiler.bind_switch_scrutinee_once(a0, a1)
    };

    expect_dump!(dump::expr(&compiler.j, expr), "tmp");

    expect_dump!(
        dump::block(&compiler.j, &prelude),
        "let[Strict] tmp = Call[Na](compute; 1)"
    );
}

#[test]
fn lowers_js_object_create_with_statically_present_optional_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::Nothing,
            obj_arg_label: Label::ObjOptional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::string("pic"))],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    expect_dump!(dump::expr(&compiler.j, compiled.expr), "{\"alt\": \"pic\"}");
}

#[test]
fn lowers_js_object_create_with_unknown_optional_field_to_conditional_assignment_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let opt = Ident::create_local("opt");
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::Nothing,
            obj_arg_label: Label::ObjOptional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::var(opt)],
        LamLoc::NONE,
    ));

    expect_dump!(dump::expr(&compiler.j, compiled.expr), "tmp");

    expect_dump!(
        dump::block(&compiler.j, &compiled.prelude),
        "let[Variable] tmp = {}; If(NotEqEq(opt, undefined)) {Exp(Eq(tmp.alt, Call[BuiltinRuntime,full](Primitive_option.valFromOption<Runtime>; opt)))} else {}"
    );
}

#[test]
fn lowers_js_object_create_with_nonduplicable_optional_field_after_object_temp_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::Nothing,
            obj_arg_label: Label::ObjOptional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::PrawJsCode(JsRawInfo {
                code: "computeOption()".to_string(),
                is_stmt: false,
            }),
            vec![],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
    ));

    expect_dump!(dump::expr(&compiler.j, compiled.expr), "tmp");

    expect_dump!(
        dump::block(&compiler.j, &compiled.prelude),
        "let[Variable] tmp = {}; let[Strict] tmp#1 = Raw(\"computeOption()\"); If(NotEqEq(tmp#1, undefined)) {Exp(Eq(tmp.alt, Call[BuiltinRuntime,full](Primitive_option.valFromOption<Runtime>; tmp#1)))} else {}"
    );
}

#[test]
fn lowers_ignored_js_call_args_to_ocaml_sequence_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "somefn".to_string(),
            arg_types: vec![
                Param {
                    arg_type: Attr::Ignore,
                    arg_label: LabelNoname::ArgEmpty,
                },
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgEmpty,
                },
            ],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "somefn".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        vec![
            Lambda::Lsequence(
                Box::new(Lambda::prim(
                    Primitive::PrawJsCode(JsRawInfo {
                        code: "sideEffect()".to_string(),
                        is_stmt: false,
                    }),
                    vec![],
                    LamLoc::NONE,
                )),
                Box::new(Lambda::const_(Constant::string("Float"))),
            ),
            Lambda::const_(Constant::int(3)),
        ],
        LamLoc::NONE,
    );

    let compiled = compiler.compile_expr_lam(&lam);
    assert!(
        compiled.prelude.is_empty(),
        "expected ignored-call effects to stay in the expression, got {:?}",
        compiled.prelude
    );
    expect_dump!(
        dump::expr(&compiler.j, compiled.expr),
        "Seq(Seq(Raw(\"sideEffect()\"), \"Float\"), Call[Na](somefn; 3))"
    );
}

#[test]
fn compile_deps_program_keeps_exported_dict_initializer_object_literals() {
    let mut compiler = LambdaCompiler::new();
    let dict_ident = Ident::create_local("stringDict");
    let dict_value = Lambda::prim(
        Primitive::Pmakedict,
        vec![Lambda::prim(
            Primitive::Pmakearray,
            vec![Lambda::prim(
                Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                vec![
                    Lambda::const_(Constant::string("first")),
                    Lambda::const_(Constant::string("hello")),
                ],
                LamLoc::NONE,
            )],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        dict_ident,
        dict_value,
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![dict_ident]), Mutable::Immutable),
            vec![Lambda::var(dict_ident)],
            LamLoc::NONE,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    expect_dump!(
        dump::block(&deps.program.arena, &deps.program.block),
        "let[StrictOpt,Exported] stringDict = {\"first\": \"hello\"}"
    );
}

#[test]
fn compile_dict_has_primitive_emits_in_operator_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let dict = Ident::create_local("dict");
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PdictHas,
        vec![Lambda::var(dict), Lambda::const_(Constant::string("key1"))],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expr(&compiler.j, compiled.expr), "\"key1\" in dict");
}

#[test]
fn js_pass_pipeline_preserves_dict_has_in_operator_through_typeof() {
    let mut j = JsArena::new();
    let dict = Ident::create_local("dict");
    let result = Ident::create_local("result");
    let deps = apply_js_shake_pass(apply_js_flatten_and_mark_dead_pass(
        apply_js_tailcall_inline_pass(apply_external_shadow_pass(apply_js_flatten_pass(
            DepsProgram {
                program: Program::new_in(
                    vec![
                        JS::variable(
                            VarDecl {
                                ident: dict,
                                value: Some(JE::new(
                                    ExprKind::Object(test_props(vec![], &mut j)),
                                    &mut j,
                                )),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            },
                            &mut j,
                        ),
                        JS::variable(
                            VarDecl {
                                ident: result,
                                value: Some(JE::new(
                                    ExprKind::Typeof(JE::new(
                                        ExprKind::In(
                                            JE::string("key1", &mut j),
                                            JE::var(dict, &mut j),
                                        ),
                                        &mut j,
                                    )),
                                    &mut j,
                                )),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            },
                            &mut j,
                        ),
                    ],
                    vec![result],
                    std::mem::take(&mut j),
                ),
                modules: vec![],
                side_effect: None,
            },
        ))),
        false,
    ));
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("typeof (\"key1\" in dict)"),
        "expected the JS pass pipeline to preserve the Dict.has `in` operator, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("typeof undefined"),
        "unexpected dropped Dict.has `in` operator after the JS passes:\n{rendered}"
    );
}

#[test]
fn collects_static_module_dependencies() {
    let mut compiler = LambdaCompiler::new();
    let deps = compiler.compile_deps_program(&Lambda::global_module(Ident::create_persistent(
        "Belt_List",
    )));

    assert_eq!(deps.modules.len(), 1);
    assert_eq!(deps.modules[0].id.name(), "Belt_List");
    assert!(!deps.modules[0].dynamic_import);
}

#[test]
fn external_module_import_attributes_preserve_all_fields() {
    let module = ExternalModuleName {
        bundle: "./myJson.json".to_string(),
        module_bind_name: ModuleBindName::PhintNothing,
        import_attributes: Some(vec![
            ("type".to_string(), "json".to_string()),
            ("some-identifier".to_string(), "yep".to_string()),
        ]),
    };

    let attrs = external_module_import_attributes(&module).expect("expected import attributes");

    assert_eq!(
        attrs.entries,
        vec![
            ("type".to_string(), "json".to_string()),
            ("some-identifier".to_string(), "yep".to_string()),
        ]
    );
}

#[test]
fn dynamic_import_only_possible_required_modules_still_mark_effects_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let extras = ahash::AHashSet::from([ModuleId {
        id: Ident::create_persistent("Side_effect"),
        kind: Kind::Ml,
        dynamic_import: true,
    }]);
    let deps =
        compiler.compile_deps_program_with_possible_required_modules(&Lambda::unit(), &extras);

    assert_eq!(deps.modules.len(), 1);
    assert!(deps.modules[0].dynamic_import);
    assert_eq!(deps.side_effect.as_deref(), Some("Side_effect"));
}

#[test]
fn required_modules_skip_dead_pure_external_bindings_like_printer() {
    let mut compiler = LambdaCompiler::new();
    let dead_info = IdentInfo {
        used_stats: UsedStats::DeadPure,
    };
    let block = vec![JS::variable(
        VarDecl {
            ident: Ident::create_local("dead_external"),
            value: Some(JE::qualified(
                ModuleId {
                    id: Ident::create_local("X"),
                    kind: Kind::External {
                        name: "./x".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                Some("x".to_string()),
                &mut compiler.j,
            )),
            property: LetKind::StrictOpt,
            ident_info: dead_info,
        },
        &mut compiler.j,
    )];

    let modules = compiler.collect_required_modules(&block);

    assert!(
        modules.is_empty(),
        "dead pure bindings are omitted by the printer, so they must not keep module deps"
    );
}

#[test]
fn sorts_external_module_dependencies_by_module_name() {
    let mut compiler = LambdaCompiler::new();
    let block = vec![
        JS::exp(
            JE::qualified(
                ModuleId {
                    id: Ident::create_persistent("JsxRuntime"),
                    kind: Kind::External {
                        name: "react/jsx-runtime".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(
                ModuleId {
                    id: Ident::create_persistent("ReactIntl"),
                    kind: Kind::External {
                        name: "react-intl".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "react-intl");
    assert_eq!(module_sort_name(&modules[1]), "react/jsx-runtime");
}

#[test]
fn sorts_required_modules_by_length_before_bytes() {
    let mut compiler = LambdaCompiler::new();
    let block = vec![
        JS::exp(
            JE::qualified(
                ModuleId {
                    id: Ident::create_persistent("Test_utils"),
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                None,
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(
                ModuleId {
                    id: Ident::create_persistent("Mocha"),
                    kind: Kind::External {
                        name: "mocha".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "mocha");
    assert_eq!(module_sort_name(&modules[1]), "Test_utils");
}

#[test]
fn required_modules_match_ocaml_sort_across_same_name_import_pairs() {
    let mut compiler = LambdaCompiler::new();
    let some_default = ModuleId {
        id: Ident::create_local("SomeEs6Module"),
        kind: Kind::External {
            name: "some-es6-module".to_string(),
            default: true,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let some_namespace = ModuleId {
        id: Ident::create_local("SomeEs6Module"),
        kind: Kind::External {
            name: "some-es6-module".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let ome_default = ModuleId {
        id: Ident::create_local("OmeEs6Module"),
        kind: Kind::External {
            name: "./ome-es6-module".to_string(),
            default: true,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let ome_namespace = ModuleId {
        id: Ident::create_local("OmeEs6Module"),
        kind: Kind::External {
            name: "./ome-es6-module".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let vscode = ModuleId {
        id: Ident::create_local("Vscode"),
        kind: Kind::External {
            name: "vscode".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let block = vec![
        JS::exp(
            JE::qualified(some_default.clone(), None, &mut compiler.j),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(
                some_namespace.clone(),
                Some("default2".to_string()),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(ome_default.clone(), None, &mut compiler.j),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(
                ome_namespace.clone(),
                Some("default2".to_string()),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
        JS::exp(
            JE::qualified(vscode.clone(), Some("window".to_string()), &mut compiler.j),
            &mut compiler.j,
        ),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(
        modules,
        vec![
            vscode,
            some_namespace,
            some_default,
            ome_namespace,
            ome_default,
        ]
    );
}

#[test]
fn required_module_effect_reason_uses_external_module_name() {
    let reason = required_module_side_effect_reason(
        None,
        &[ModuleId {
            id: Ident::create_persistent("GentTypeReTestGen"),
            kind: Kind::External {
                name: "./gentTypeReTest.gen".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        }],
    );

    assert_eq!(reason.as_deref(), Some("./gentTypeReTest.gen"));
}

#[test]
fn pure_ml_dependencies_do_not_mark_module_impure() {
    let resolver = resolver_with_checked_in_cmj();
    let reason = required_module_side_effect_reason(
        Some(&resolver),
        &[ModuleId {
            id: Ident::create_persistent("Side_effect_free"),
            kind: Kind::Ml,
            dynamic_import: false,
        }],
    );

    assert_eq!(reason, None);
}

#[test]
fn preserves_impure_side_effect_only_ml_dependencies_from_lambda() {
    let resolver = resolver_with_checked_in_cmj();
    let side_effect = Ident::create_persistent("Side_effect");
    let include_binding = Ident::create_local("include");
    let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
    let deps = compiler.compile_deps_program(&Lambda::let_(
        LetKind::Alias,
        include_binding,
        Lambda::global_module(side_effect),
        Lambda::unit(),
    ));

    assert!(deps.program.block.is_empty());
    assert!(deps.program.exports.is_empty());
    assert_eq!(deps.modules.len(), 1);
    assert_eq!(deps.modules[0].id.name(), side_effect.name());
    assert_eq!(deps.modules[0].kind, Kind::Ml);
    assert_eq!(deps.side_effect.as_deref(), Some("Side_effect"));
}

#[test]
fn impure_ml_dependencies_use_module_name_as_effect_reason() {
    let resolver = resolver_with_checked_in_cmj();
    let reason = required_module_side_effect_reason(
        Some(&resolver),
        &[ModuleId {
            id: Ident::create_persistent("Test_utils"),
            kind: Kind::Ml,
            dynamic_import: false,
        }],
    );

    assert_eq!(reason.as_deref(), Some("Test_utils"));
}

#[test]
fn module_side_effect_reason_uses_first_impure_group_in_final_order_like_ocaml() {
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let lam = Lambda::let_(
        LetKind::Strict,
        first,
        Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
        Lambda::let_(
            LetKind::Strict,
            second,
            Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
            Lambda::unit(),
        ),
    );

    assert_eq!(
        module_side_effect_reason_tree(&lam).as_deref(),
        Some("first")
    );
}

#[test]
fn module_side_effect_reason_uses_binding_name_for_impure_group_bodies() {
    let match_id = Ident::create_local("match");
    let lam = Lambda::seq(
        Lambda::let_(
            LetKind::Strict,
            match_id,
            Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
            Lambda::unit(),
        ),
        Lambda::unit(),
    );

    assert_eq!(
        module_side_effect_reason_tree(&lam).as_deref(),
        Some("match")
    );
}

#[test]
fn module_side_effect_reason_keeps_empty_reason_for_impure_nops() {
    let lam = Lambda::seq(
        Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
        Lambda::unit(),
    );

    assert_eq!(module_side_effect_reason_tree(&lam).as_deref(), Some(""));
}

#[test]
fn resolves_local_module_paths_from_ast_metadata() {
    let project = tempdir().expect("failed to create project tempdir");
    let source_dir = project.path().join("src");
    let build_dir = project.path().join("lib").join("rescript");
    fs::create_dir_all(&source_dir).expect("failed to create source dir");
    fs::create_dir_all(&build_dir).expect("failed to create build dir");

    let current_source = source_dir.join("Current.res");
    let target_source = source_dir.join("ModuleWithAlias.res");
    fs::write(&current_source, "").expect("failed to stub current source");
    fs::write(&target_source, "").expect("failed to stub target source");
    write_ast_source_stub(&build_dir.join("ModuleWithAlias.ast"), &target_source);

    let mut pers = PersistentEnv::new();
    pers.set_load_path(vec![build_dir]);

    let resolver = ModulePathResolver::from_compile_options(
        Some(current_source.to_str().expect("utf8 current source path")),
        Some(source_dir.join("Current.mjs").as_path()),
        None,
        None,
        None,
        Some(pers),
        false,
    );
    let module = ModuleId {
        id: Ident::create_persistent("ModuleWithAlias"),
        kind: Kind::Ml,
        dynamic_import: true,
    };

    assert_eq!(
        resolver.resolve_module_path(&module).as_deref(),
        Some("./ModuleWithAlias.mjs")
    );
}

#[test]
fn external_module_ids_reuse_first_binding_for_same_bundle_and_default() {
    let mut compiler = LambdaCompiler::new();
    let plain = ExternalModuleName {
        bundle: "x".to_string(),
        module_bind_name: ModuleBindName::PhintNothing,
        import_attributes: None,
    };
    let hinted = ExternalModuleName {
        bundle: "x".to_string(),
        module_bind_name: ModuleBindName::PhintName("U".to_string()),
        import_attributes: None,
    };

    let plain_module = compiler.external_module_id(&plain, false, false);
    let hinted_module = compiler.external_module_id(&hinted, false, false);
    let default_module = compiler.external_module_id(&plain, true, false);
    let dynamic_plain_module = compiler.external_module_id(&plain, false, true);

    assert_eq!(plain_module, hinted_module);
    assert_eq!(plain_module.id.name(), "X");
    assert!(!plain_module.id.same(&default_module.id));
    assert!(plain_module.id.same(&dynamic_plain_module.id));
    assert!(!plain_module.dynamic_import);
    assert!(dynamic_plain_module.dynamic_import);
}

#[test]
fn lowers_nullable_predicates_to_js_null_checks() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");

    let null_compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PisNull,
        vec![Lambda::var(value)],
        LamLoc::NONE,
    ));
    let undefined_compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PisUndefined,
        vec![Lambda::var(value)],
        LamLoc::NONE,
    ));
    let nullable_compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PisNullUndefined,
        vec![Lambda::var(value)],
        LamLoc::NONE,
    ));

    assert!(null_compiled.prelude.is_empty());
    expect_dump!(
        dump::expr(&compiler.j, null_compiled.expr),
        "EqEqEq(value, null)"
    );
    expect_dump!(
        dump::expr(&compiler.j, undefined_compiled.expr),
        "EqEqEq(value, undefined)"
    );
    expect_dump!(
        dump::expr(&compiler.j, nullable_compiled.expr),
        "IsNullOrUndefined(value)"
    );
    assert!(nullable_compiled.prelude.is_empty());
    assert!(undefined_compiled.prelude.is_empty());
}

fn js_val_call(name: &str, arg_types: Vec<Param>, args: Vec<Lambda>) -> Lambda {
    Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: name.to_string(),
            arg_types,
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: name.to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            },
        })),
        args,
        LamLoc::NONE,
    )
}

fn polyvar_param(arg_type: Attr) -> Param {
    Param {
        arg_type,
        arg_label: LabelNoname::ArgEmpty,
    }
}

// lam_compile_external_call.ml `hold_arg` (#9217): an event-style argument
// is read twice, so a call is bound to a temporary and runs once.
#[test]
fn event_style_polyvar_call_argument_runs_once() {
    let mut compiler = LambdaCompiler::new();
    let next = js_val_call(
        "next",
        vec![polyvar_param(Attr::Nothing)],
        vec![Lambda::const_(Constant::int(0))],
    );
    let lam = js_val_call(
        "on",
        vec![polyvar_param(Attr::PolyVar { descr: None })],
        vec![next],
    );
    let p = compiler.compile_program(&lam);
    assert_eq!(
        print_stmts(&p.arena, &p.block),
        "let tmp = next(0);\n\non(tmp.NAME, tmp.VAL);"
    );
}

// The literal `#click(wrap(h))` passes its tag and payload in place, even
// with an effectful payload.
#[test]
fn event_style_polyvar_literal_with_effectful_payload_passes_in_place() {
    let mut compiler = LambdaCompiler::new();
    let wrap = js_val_call(
        "wrap",
        vec![polyvar_param(Attr::Nothing)],
        vec![Lambda::const_(Constant::int(1))],
    );
    let literal = Lambda::prim(
        Primitive::Pmakeblock(TagInfo::PolyVar("click".to_string()), Mutable::Immutable),
        vec![Lambda::const_(Constant::Pointer("click".to_string())), wrap],
        LamLoc::NONE,
    );
    let lam = js_val_call(
        "on",
        vec![polyvar_param(Attr::PolyVar { descr: None })],
        vec![literal],
    );
    let p = compiler.compile_program(&lam);
    assert_eq!(print_stmts(&p.arena, &p.block), "on(\"click\", wrap(1));");
}

// An `@int` dispatch switches on its argument in a function; an `await`
// there would be a syntax error, so it is bound before the call.
#[test]
fn int_polyvar_await_argument_is_bound_outside_the_dispatch() {
    let mut compiler = LambdaCompiler::new();
    let p_ident = Ident::create_local("p");
    let awaited = Lambda::prim(Primitive::Pawait, vec![Lambda::var(p_ident)], LamLoc::NONE);
    let lam = js_val_call(
        "setLevel",
        vec![polyvar_param(Attr::Int(vec![
            ("low".to_string(), 0),
            ("high".to_string(), 10),
        ]))],
        vec![awaited],
    );
    let p = compiler.compile_program(&lam);
    let printed = print_stmts(&p.arena, &p.block);
    assert!(
        printed.starts_with("let tmp = await p;"),
        "await is bound first: {printed}"
    );
    assert!(printed.contains("switch (tmp)"), "{printed}");
}

// A variable is read in place, as is any argument an `@string` dispatch
// reads once without effects.
#[test]
fn polyvar_variable_argument_needs_no_temporary() {
    let mut compiler = LambdaCompiler::new();
    let x = Ident::create_local("x");
    let lam = js_val_call(
        "on",
        vec![polyvar_param(Attr::PolyVar { descr: None })],
        vec![Lambda::var(x)],
    );
    let p = compiler.compile_program(&lam);
    assert_eq!(print_stmts(&p.arena, &p.block), "on(x.NAME, x.VAL);");
}

// lam_compile_external_obj.ml `hold_obj_args`: an `@obj` field with an `@int`
// dispatch binds an effectful argument too.
#[test]
fn obj_polyvar_int_field_call_argument_is_bound() {
    let mut compiler = LambdaCompiler::new();
    let next = js_val_call(
        "next",
        vec![polyvar_param(Attr::Nothing)],
        vec![Lambda::const_(Constant::int(0))],
    );
    let compiled = compiler.compile_expr_lam(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::Int(vec![("low".to_string(), 0), ("high".to_string(), 10)]),
            obj_arg_label: Label::ObjLabel {
                name: "level".to_string(),
            },
        }]),
        vec![next],
        LamLoc::NONE,
    ));
    assert_eq!(compiled.prelude.len(), 1, "the call is bound first");
    let printed = print_expr(&compiler.j, compiled.expr);
    assert!(printed.contains("switch (tmp)"), "{printed}");
}
