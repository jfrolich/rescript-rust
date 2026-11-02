use super::*;

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn import_attributes_exact_lowered_lambda_keeps_aliases_before_logs_through_js_pipeline() {
    let lam = import_attributes_lowered_lambda();
    let simplified = crate::lambda::lam_compile_main::simplify_for_js_backend(&lam);
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&simplified);
    let mut block = compiled.prelude;
    let exports = extract_toplevel_exports(compiled.expr, &mut block)
        .expect("expected ImportAttributes-style lambda to end in a module export block");
    assert_import_attributes_alias_block_shape(&block, "after export extraction");

    let exports = compiler.coerce_toplevel_exports(&mut block, exports);
    let exports = resolve_export_aliases(&block, exports);
    let program = Program::new(block, exports);
    assert_import_attributes_alias_block_shape(&program.block, "after top-level export coercion");

    let deps = apply_js_flatten_pass(DepsProgram {
        program,
        modules: vec![],
        side_effect: module_side_effect_reason(&simplified),
    });
    assert_import_attributes_alias_block_shape(&deps.program.block, "after js_flatten");

    let deps = apply_external_shadow_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after external_shadow");

    let deps = apply_js_tailcall_inline_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after tailcall_inline");

    let deps = apply_js_flatten_and_mark_dead_pass(deps, false);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after flatten_and_mark_dead");

    let deps = apply_js_shake_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after js_shake");
}

#[test]
fn lowers_js_var_without_args_to_a_value() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "process".to_string(),
            arg_types: vec![],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "process".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            }),
        },
        vec![],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(compiled.prelude.is_empty());
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)),
            ..
        } if id.name() == "process"
    ));
}

#[test]
fn lowers_js_var_calls_with_runtime_args_even_without_external_arg_metadata() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "foo1".to_string(),
            arg_types: vec![],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "foo1".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            }),
        },
        vec![Lambda::Lconst(Constant::Int {
            i: 10,
            comment: None,
        })],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert_eq!(args.len(), 1);
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.name() == "foo1"
            ));
            assert!(matches!(
                args[0],
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 10, .. }),
                    ..
                }
            ));
        }
        other => panic!("expected a direct js-var call, got {other:?}"),
    }
}

#[test]
fn lowers_module_external_calls_to_namespace_imports() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "describe".to_string(),
            arg_types: vec![],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "describe".to_string(),
                },
                module_: Some(ModuleSource::ModuleNamed(external_module("mocha"))),
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![],
        Location::none(),
    );

    let deps = compiler.compile_deps_program(&lam);
    assert!(matches!(
        deps.modules.as_slice(),
        [ModuleId {
            kind: Kind::External { name, default, .. },
            ..
        }] if name == "mocha" && !default
    ));

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(field))),
                    ..
                } if field == "describe"
                    && matches!(
                        &**module,
                        ModuleId { kind: Kind::External { name, default, .. }, .. }
                            if name == "mocha" && !default
                    )
            ));
        }
        other => panic!("expected external module call, got {other:?}"),
    }
}

#[test]
fn translates_external_module_values_to_qualified_members_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let expr = compiler.translate_scoped_module_value(
        Some(&external_module("react/jsx-runtime")),
        "jsx",
        &[],
    );

    assert!(matches!(
        expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(ref module, Some(ref member))),
            ..
        } if member == "jsx"
            && matches!(
                &**module,
                ModuleId { kind: Kind::External { name, default, .. }, .. }
                    if name == "react/jsx-runtime" && !default
            )
    ));
    assert_eq!(print_expression(&expr), "JsxRuntime.jsx");
}

#[test]
fn lowers_pjs_object_get_to_method_calls() {
    let mut compiler = LambdaCompiler::new();
    let john = Ident::create_persistent("john");
    let lam = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::prim(
            Primitive::PjsObjectGet("say".to_string()),
            vec![Lambda::var(john)],
            Location::none(),
        )),
        ap_args: vec![
            Lambda::const_(Constant::String("hey".to_string())),
            Lambda::const_(Constant::String("jude".to_string())),
        ],
        ap_info: ApInfo {
            loc: Location::none(),
            status: ApplyStatus::Uncurry,
        },
    }));

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
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
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "student1.name = \"Mary\";");
}

#[test]
fn lowers_spliced_js_calls_by_flattening_literal_variadic_arrays() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "join".to_string(),
            arg_types: vec![Param::dummy()],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "join".to_string(),
                },
                module_: Some(ModuleSource::ModuleNamed(external_module("path"))),
                scopes: vec![],
                variadic: true,
                effective_arity: 1,
            }),
        },
        vec![Lambda::prim(
            Primitive::Pmakearray,
            vec![
                Lambda::const_(Constant::String(".".to_string())),
                Lambda::const_(Constant::String("Node_path_test".to_string())),
            ],
            Location::none(),
        )],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
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
        Location::none(),
    ));
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "import(\"a\").then(m => m.default);");
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn lowers_js_new_to_new_expression() {
    let mut compiler = LambdaCompiler::new();
    let arg = Ident::create_local("prim");
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "URL".to_string(),
            arg_types: vec![],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclNew {
                    name: "URL".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![Lambda::var(arg)],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::New(ctor, Some(args)),
            ..
        }) => {
            assert!(matches!(
                ctor.desc,
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "URL"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }] if id.same(&arg)
            ));
        }
        other => panic!("expected a new expression, got {other:?}"),
    }
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn lowers_js_call_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let date = Ident::create_local("date");
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "formatDate".to_string(),
            arg_types: vec![
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgEmpty,
                },
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgOptional,
                },
                Param {
                    arg_type: Attr::Nothing,
                    arg_label: LabelNoname::ArgOptional,
                },
            ],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "formatDate".to_string(),
                },
                module_: Some(ModuleSource::ModuleNamed(external_module("SomeModule"))),
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![
            Lambda::var(date),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let simplified = crate::lambda::lam_compile_main::simplify_for_js_backend(&lam);
    let compiled = compiler.compile_expr(&simplified);
    let rendered = if compiled.prelude.is_empty() {
        print_expression(&compiled.expr)
    } else {
        print_block(&compiled.prelude)
    };
    assert_eq!(rendered, "SomeModule.formatDate(date);");
}

#[test]
fn lowers_js_send_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
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
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclSend {
                    name: "toString".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 2,
            }),
        },
        vec![
            Lambda::const_(Constant::Float("42.".to_string())),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "(42).toString();");
}

#[test]
fn lowers_js_new_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
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
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclNew {
                    name: "RegExp".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![
            Lambda::const_(Constant::String("ab+c".to_string())),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "new RegExp(\"ab+c\");");
}

#[test]
fn lowers_external_polyvar_string_and_int_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
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
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "consume".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![
            Lambda::const_(Constant::Pointer("in_".to_string())),
            Lambda::const_(Constant::Pointer("on_open".to_string())),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "consume(\"in\", 3);");
}

#[test]
fn lowers_external_polyvar_payload_args_to_two_js_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "handle".to_string(),
            arg_types: vec![Param {
                arg_type: Attr::PolyVar {
                    descr: Some(vec![("b".to_string(), "renamed".to_string())]),
                },
                arg_label: LabelNoname::ArgEmpty,
            }],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "handle".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![Lambda::const_(Constant::Block {
            tag_info: Box::new(TagInfo::PolyVar("b".to_string())),
            elements: vec![Constant::Pointer("b".to_string()), Constant::int(2)],
        })],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
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
        Primitive::PjsCall {
            prim_name: "somefn".to_string(),
            arg_types: vec![Param {
                arg_type: Attr::ArgCst(Cst::ArgJsonLit("{foo:true}".to_string())),
                arg_label: LabelNoname::ArgEmpty,
            }],
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "somefn".to_string(),
                },
                module_: None,
                scopes: vec!["somescope".to_string()],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(matches!(
                func.desc,
                ExpressionDesc::StaticIndex(_, ref field, _)
                if field == "somefn"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::JsonLiteral(txt),
                    ..
                }] if txt == "{foo:true}"
            ));
        }
        other => panic!("expected a JS call, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_marshaled_fields() {
    let mut compiler = LambdaCompiler::new();
    let name_ident = Ident::create_local("name");
    let compiled = compiler.compile_expr(&Lambda::prim(
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
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(props) => {
            assert_eq!(props.len(), 3);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::JsonLiteral(txt),
                        ..
                    },
                ) if name == "objectMode" && txt == "false"
            ));
            assert!(matches!(
                &props[1],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    },
                ) if name == "name" && id.same(&name_ident)
            ));
            assert!(matches!(
                &props[2],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::JsonLiteral(txt),
                        ..
                    },
                ) if name == "someOther" && txt == "true"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_polyvar_string_field_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
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
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str(txt),
                        ..
                    },
                ) if name == "localeMatcher" && txt == "best fit"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
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
            Location::none(),
        )],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str(txt),
                        ..
                    },
                ) if name == "day" && txt == "2-digit"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn bind_switch_scrutinee_once_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let (prelude, expr) = compiler.bind_switch_scrutinee_once(
        vec![],
        Expression::call(
            Expression::var(Ident::create_local("compute")),
            vec![Expression::number(Number::int(1))],
            CallInfo::default(),
        ),
    );

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(tmp_ident)) = &expr.desc else {
        panic!("expected the bound scrutinee expression to become a temp variable");
    };
    assert_eq!(tmp_ident.name(), "tmp");

    let [stmt] = prelude.as_slice() else {
        panic!("expected a single temp binding statement");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            assert!(ident.same(tmp_ident));
            assert!(matches!(
                value,
                Some(Expression {
                    desc: ExpressionDesc::Call(_, _, _),
                    ..
                })
            ));
        }
        other => panic!("expected a temp variable declaration, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_statically_present_optional_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
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
            Location::none(),
        )],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str(txt),
                        ..
                    },
                ) if name == "alt" && txt == "pic"
            ));
        }
        other => panic!("expected an inline object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_unknown_optional_field_to_conditional_assignment_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let opt = Ident::create_local("opt");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ObjParam {
            obj_arg_type: Attr::Nothing,
            obj_arg_label: Label::ObjOptional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::var(opt)],
        Location::none(),
    ));

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(obj)) = &compiled.expr.desc else {
        panic!("expected the conditional path to return the temp object");
    };

    let [init_stmt, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected object init plus one conditional assignment");
    };

    match &init_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(props),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(obj));
            assert!(props.is_empty());
        }
        other => panic!("expected an empty object temp, got {other:?}"),
    }

    match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => {
            assert!(else_block.is_empty());
            assert!(matches!(
                &cond.desc,
                ExpressionDesc::Bin(
                    BinOp::NotEqEq,
                    left,
                    right,
                ) if matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&opt)
                ) && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { is_unit: false },
                        ..
                    }
                )
            ));

            let [assign_stmt] = then_block.as_slice() else {
                panic!("expected one conditional assignment");
            };
            match &assign_stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                    ..
                }) => {
                    assert!(matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::StaticIndex(target_obj, field, _),
                            ..
                        } if field == "alt"
                            && matches!(
                                target_obj.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(obj)
                            )
                    ));
                    assert_eq!(
                        print_expression(value),
                        "Primitive_option.valFromOption(opt)"
                    );
                }
                other => panic!("expected an object-field assignment, got {other:?}"),
            }
        }
        other => panic!("expected a conditional optional assignment, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_nonduplicable_optional_field_after_object_temp_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
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
            Location::none(),
        )],
        Location::none(),
    ));

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(obj)) = &compiled.expr.desc else {
        panic!("expected the conditional path to return the temp object");
    };
    assert_eq!(obj.name(), "tmp");

    let [init_stmt, arg_stmt, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected object init, prepared arg temp, and one conditional assignment");
    };

    match &init_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(props),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(obj));
            assert_eq!(*property, LetKind::Variable);
            assert!(props.is_empty());
        }
        other => panic!("expected an empty object temp, got {other:?}"),
    }

    let prepared = match &arg_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc:
                        ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                            code,
                            is_stmt: false,
                        }),
                    ..
                }),
            property,
            ..
        }) => {
            assert_eq!(code, "computeOption()");
            assert_eq!(*property, LetKind::Strict);
            assert!(!ident.same(obj));
            *ident
        }
        other => panic!("expected the prepared optional-value temp, got {other:?}"),
    };

    match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => {
            assert!(else_block.is_empty());
            assert!(matches!(
                &cond.desc,
                ExpressionDesc::Bin(
                    BinOp::NotEqEq,
                    left,
                    right,
                ) if matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&prepared)
                ) && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { is_unit: false },
                        ..
                    }
                )
            ));

            let [assign_stmt] = then_block.as_slice() else {
                panic!("expected one conditional assignment");
            };
            match &assign_stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, target, _value),
                    ..
                }) => {
                    assert!(matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::StaticIndex(target_obj, field, _),
                            ..
                        } if field == "alt"
                            && matches!(
                                target_obj.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(obj)
                            )
                    ));
                }
                other => panic!("expected an object-field assignment, got {other:?}"),
            }
        }
        other => panic!("expected a conditional optional assignment, got {other:?}"),
    }
}

#[test]
fn lowers_ignored_js_call_args_to_ocaml_sequence_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
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
            ffi: Box::new(ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: "somefn".to_string(),
                },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 1,
            }),
        },
        vec![
            Lambda::Lsequence(
                Box::new(Lambda::prim(
                    Primitive::PrawJsCode(JsRawInfo {
                        code: "sideEffect()".to_string(),
                        is_stmt: false,
                    }),
                    vec![],
                    Location::none(),
                )),
                Box::new(Lambda::const_(Constant::string("Float"))),
            ),
            Lambda::const_(Constant::int(3)),
        ],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(
        compiled.prelude.is_empty(),
        "expected ignored-call effects to stay in the expression, got {:?}",
        compiled.prelude
    );
    let ExpressionDesc::Seq(left, call) = &compiled.expr.desc else {
        panic!("expected outer effect sequence, got {:?}", compiled.expr);
    };
    let ExpressionDesc::Seq(effect, kind) = &left.as_ref().desc else {
        panic!("expected nested ignored-arg sequence, got {:?}", left);
    };
    assert!(matches!(
        effect.as_ref(),
        Expression {
            desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                code,
                is_stmt: false,
            }),
            ..
        } if code == "sideEffect()"
    ));
    assert!(matches!(
        kind.as_ref(),
        Expression {
            desc: ExpressionDesc::Str(txt),
            ..
        } if txt == "Float"
    ));
    match &call.as_ref().desc {
        ExpressionDesc::Call(func, args, _) => {
            assert!(matches!(func.as_ref().desc, ExpressionDesc::Var(_)));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }]
            ));
        }
        other => panic!("expected a call expression, got {other:?}"),
    };
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn lowers_ignored_js_object_fields_to_ocaml_sequence_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsObjectCreate(vec![
            ObjParam {
                obj_arg_type: Attr::Ignore,
                obj_arg_label: Label::ObjLabel {
                    name: "kind".to_string(),
                },
            },
            ObjParam {
                obj_arg_type: Attr::Nothing,
                obj_arg_label: Label::ObjLabel {
                    name: "hi".to_string(),
                },
            },
        ]),
        vec![
            Lambda::Lsequence(
                Box::new(Lambda::prim(
                    Primitive::PrawJsCode(JsRawInfo {
                        code: "sideEffect()".to_string(),
                        is_stmt: false,
                    }),
                    vec![],
                    Location::none(),
                )),
                Box::new(Lambda::const_(Constant::string("Float"))),
            ),
            Lambda::const_(Constant::int(3)),
        ],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(
        compiled.prelude.is_empty(),
        "expected ignored-object effects to stay in the expression, got {:?}",
        compiled.prelude
    );
    let ExpressionDesc::Seq(left, object) = &compiled.expr.desc else {
        panic!("expected outer effect sequence, got {:?}", compiled.expr);
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Seq(effect, kind),
            ..
        } if matches!(
            effect.as_ref(),
            Expression {
                desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code,
                    is_stmt: false,
                }),
                ..
            } if code == "sideEffect()"
        ) && matches!(
            kind.as_ref(),
            Expression {
                desc: ExpressionDesc::Str(txt),
                ..
            } if txt == "Float"
        )
    ));
    match &object.as_ref().desc {
        ExpressionDesc::Object(props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    },
                ) if name == "hi"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    };
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
                Location::none(),
            )],
            Location::none(),
        )],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        dict_ident,
        dict_value,
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![dict_ident]), Mutable::Immutable),
            vec![Lambda::var(dict_ident)],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one exported dict binding");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(props),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&dict_ident));
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                crate::js_ir::ObjectEntry::Property(
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str(txt),
                        ..
                    },
                ) if name == "first" && txt == "hello"
            ));
        }
        other => panic!("expected exported dict object literal, got {other:?}"),
    }
}

#[test]
fn compile_dict_has_primitive_emits_in_operator_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let dict = Ident::create_local("dict");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PdictHas,
        vec![Lambda::var(dict), Lambda::const_(Constant::string("key1"))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "\"key1\" in dict");
}

#[test]
fn js_pass_pipeline_preserves_dict_has_in_operator_through_typeof() {
    let dict = Ident::create_local("dict");
    let result = Ident::create_local("result");
    let deps = apply_js_shake_pass(apply_js_flatten_and_mark_dead_pass(
        apply_js_tailcall_inline_pass(apply_external_shadow_pass(apply_js_flatten_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: dict,
                            value: Some(Expression::new(ExpressionDesc::Object(vec![]))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: result,
                            value: Some(Expression::new(ExpressionDesc::Typeof(Box::new(
                                Expression::new(ExpressionDesc::In(
                                    Box::new(Expression::string("key1")),
                                    Box::new(Expression::var(dict)),
                                )),
                            )))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![result],
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
    let compiler = LambdaCompiler::new();
    let mut dead_info = IdentInfo::default();
    dead_info.used_stats = UsedStats::DeadPure;
    let block = vec![Statement::variable(VariableDeclaration {
        ident: Ident::create_local("dead_external"),
        value: Some(Expression::qualified(
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
        )),
        property: LetKind::StrictOpt,
        ident_info: dead_info,
    })];

    let modules = compiler.collect_required_modules(&block);

    assert!(
        modules.is_empty(),
        "dead pure bindings are omitted by the printer, so they must not keep module deps"
    );
}

#[test]
fn sorts_external_module_dependencies_by_module_name() {
    let compiler = LambdaCompiler::new();
    let block = vec![
        Statement::exp(Expression::qualified(
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
        )),
        Statement::exp(Expression::qualified(
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
        )),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "react-intl");
    assert_eq!(module_sort_name(&modules[1]), "react/jsx-runtime");
}

#[test]
fn sorts_required_modules_by_length_before_bytes() {
    let compiler = LambdaCompiler::new();
    let block = vec![
        Statement::exp(Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Test_utils"),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            None,
        )),
        Statement::exp(Expression::qualified(
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
        )),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "mocha");
    assert_eq!(module_sort_name(&modules[1]), "Test_utils");
}

#[test]
fn required_modules_match_ocaml_sort_across_same_name_import_pairs() {
    let compiler = LambdaCompiler::new();
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
        Statement::exp(Expression::qualified(some_default.clone(), None)),
        Statement::exp(Expression::qualified(
            some_namespace.clone(),
            Some("default2".to_string()),
        )),
        Statement::exp(Expression::qualified(ome_default.clone(), None)),
        Statement::exp(Expression::qualified(
            ome_namespace.clone(),
            Some("default2".to_string()),
        )),
        Statement::exp(Expression::qualified(
            vscode.clone(),
            Some("window".to_string()),
        )),
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
        Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
        Lambda::let_(
            LetKind::Strict,
            second,
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::unit(),
        ),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("first"));
}

#[test]
fn module_side_effect_reason_uses_binding_name_for_impure_group_bodies() {
    let match_id = Ident::create_local("match");
    let lam = Lambda::seq(
        Lambda::let_(
            LetKind::Strict,
            match_id,
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::unit(),
        ),
        Lambda::unit(),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("match"));
}

#[test]
fn module_side_effect_reason_keeps_empty_reason_for_impure_nops() {
    let lam = Lambda::seq(
        Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
        Lambda::unit(),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some(""));
}

#[test]
#[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
fn resolves_runtime_dynamic_import_to_string_path() {
    let runtime = tempdir().expect("failed to create runtime tempdir");
    let runtime_ocaml = runtime.path().join("lib").join("ocaml");
    fs::create_dir_all(&runtime_ocaml).expect("failed to create runtime ocaml dir");
    fs::write(runtime_ocaml.join("Belt_List.cmi"), []).expect("failed to stub runtime cmi");

    let project = tempdir().expect("failed to create project tempdir");
    let source = project.path().join("src").join("Import.res");
    let output = project.path().join("src").join("Import.mjs");

    let resolver = ModulePathResolver::from_compile_options(
        Some(source.to_str().expect("utf8 source path")),
        Some(output.as_path()),
        None,
        None,
        Some(runtime.path()),
        None,
        false,
    );
    let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pimport(Box::new(ImportSource::ImportModule {
            module_: Ident::create_persistent("Belt_List"),
            path: vec![],
        })),
        vec![],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single import expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(matches!(
                func.desc,
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "import"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Str(txt),
                    ..
                }] if txt == "@rescript/runtime/lib/es6/Belt_List.js"
            ));
        }
        other => panic!("expected import(\"...\") call, got {other:?}"),
    }
}

#[test]
fn resolves_local_module_paths_from_ast_metadata() {
    let project = tempdir().expect("failed to create project tempdir");
    let source_dir = project.path().join("src");
    let build_dir = project.path().join("lib").join("bs").join("src");
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

    let null_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisNull,
        vec![Lambda::var(value)],
        Location::none(),
    ));
    let undefined_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisUndefined,
        vec![Lambda::var(value)],
        Location::none(),
    ));
    let nullable_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisNullUndefined,
        vec![Lambda::var(value)],
        Location::none(),
    ));

    assert!(null_compiled.prelude.is_empty());
    match &null_compiled.expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Null,
                    ..
                }
            ));
        }
        other => panic!("expected `value === null`, got {other:?}"),
    }

    assert!(undefined_compiled.prelude.is_empty());
    match &undefined_compiled.expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { .. },
                    ..
                }
            ));
        }
        other => panic!("expected `value === undefined`, got {other:?}"),
    }

    assert!(nullable_compiled.prelude.is_empty());
    match &nullable_compiled.expr.desc {
        ExpressionDesc::IsNullOrUndefined(inner) => {
            assert!(matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
        }
        other => panic!("expected `value == null`, got {other:?}"),
    }
}
