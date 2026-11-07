use super::*;
use crate::lambda::LamLoc;

#[test]
fn equal_flattened_staticcatch_handlers_share_one_switch_body() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let report = Ident::create_local("report");
    let message = Ident::create_local("message");
    let handler = Lambda::Lsequence(
        Box::new(Lambda::apply(
            Lambda::var(report),
            vec![Lambda::var(message)],
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        )),
        Box::new(Lambda::var(message)),
    );
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond),
                Lambda::static_raise(2, vec![]),
                Lambda::static_raise(1, vec![]),
            )),
            (2, vec![]),
            Box::new(handler.clone()),
        )),
        (1, vec![]),
        Box::new(handler),
    ));
    let rendered = print_block(&block);
    assert!(
        rendered.contains("case 1 :") && rendered.contains("case 2 :"),
        "both flattened exit codes must be dispatched:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("report(message)").count(),
        1,
        "equal Lambda handlers must share their compiled switch body:\n{rendered}"
    );
}

#[test]
fn nested_return_staticcatch_preserves_exit_dispatch_in_enclosing_jump() {
    let mut compiler = LambdaCompiler::new();
    let outer_exit = Ident::create_local("outerExit");
    let state = Ident::create_local("state");
    let enabled = Ident::create_local("enabled");
    let inner = Lambda::LstaticCatch(
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(state)),
            vec![("Initial".to_string(), Lambda::static_raise(2, vec![]))],
            Some(Box::new(Lambda::if_(
                Lambda::var(enabled),
                Lambda::static_raise(1, vec![]),
                Lambda::static_raise(2, vec![]),
            ))),
        )),
        (2, vec![]),
        Box::new(Lambda::if_(
            Lambda::var(enabled),
            Lambda::const_(Constant::JsTrue),
            Lambda::const_(Constant::JsFalse),
        )),
    );
    let block = compiler.with_static_jump_handler(1, &outer_exit, &[], |compiler| {
        compiler.compile_return_block(&inner)
    });
    let rendered = print_block(&block);
    assert!(
        rendered.contains("let exit = 0;") && rendered.contains("if (exit === 2)"),
        "a nested catch must dispatch only when its exit was raised:\n{rendered}"
    );
}

#[test]
fn staticcatch_trywith_return_keeps_bound_exit_effects_outside_try_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let x = Ident::create_local("x");
    let g = Ident::create_local("g");
    let exn = Ident::create_local("exn");
    let val = Ident::create_local("val");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LtryWith(
            Box::new(Lambda::LstaticRaise(
                -2,
                vec![Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(x)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))],
            )),
            exn,
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        (-2, vec![val]),
        Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(g)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))),
    ));

    let [declare, try_stmt, ret] = block.as_slice() else {
        panic!("expected binding decl, try, and trailing return, got {block:?}");
    };

    assert!(matches!(
        &declare.desc,
        StatementDesc::Variable(VariableDeclaration { ident, value, .. })
            if ident.same(&val) && value.is_none()
    ));

    let StatementDesc::Try(body, Some((caught, handler)), None) = &try_stmt.desc else {
        panic!("expected a try statement, got {try_stmt:?}");
    };
    assert!(caught.same(&exn));
    assert!(matches!(
        body.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.as_ref().desc, &rhs.as_ref().desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Call(func, args, _)
            ) if lhs_id.same(&val)
                && args.is_empty()
                && matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(func_id)),
                        ..
                    } if func_id.same(&x)
                )
        )
    ));
    assert!(matches!(
        handler.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }),
            ..
        }]
    ));

    assert!(matches!(
        &ret.desc,
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) if args.is_empty()
            && matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(func_id)),
                    ..
                } if func_id.same(&g)
            )
    ));
}

#[test]
fn staticcatch_trywith_tail_loop_keeps_bound_exit_effects_outside_try_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let read = Ident::create_local("read");
    let next_acc = Ident::create_local("nextAcc");
    let exn = Ident::create_local("exn");
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![acc],
                Lambda::LstaticCatch(
                    Box::new(Lambda::LtryWith(
                        Box::new(Lambda::LstaticRaise(
                            -1,
                            vec![Lambda::Lapply(Box::new(Apply {
                                ap_func: Box::new(Lambda::var(read)),
                                ap_args: vec![Lambda::var(acc)],
                                ap_info: ApInfo {
                                    loc: LamLoc::NONE,
                                    status: ApplyStatus::Na,
                                },
                            }))],
                        )),
                        exn,
                        Box::new(Lambda::const_(Constant::int(0))),
                    )),
                    (-1, vec![next_acc]),
                    Box::new(Lambda::Lapply(Box::new(Apply {
                        ap_func: Box::new(Lambda::var(loop_)),
                        ap_args: vec![Lambda::var(next_acc)],
                        ap_info: ApInfo {
                            loc: LamLoc::NONE,
                            status: ApplyStatus::Na,
                        },
                    }))),
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected staticcatch trywith lowering to stay on the tail loop path:\n{rendered}"
    );
    assert!(
        rendered.contains("let nextAcc;"),
        "expected the bound staticcatch value to be declared outside the try:\n{rendered}"
    );
    assert!(
        rendered.contains("try {"),
        "expected the bound exit effect to stay inside the try body:\n{rendered}"
    );
    assert!(
        rendered.contains("nextAcc = read(")
            || rendered.contains("nextAcc = read(acc)")
            || rendered.contains("nextAcc = _read(")
            || rendered.contains("nextAcc = _read(acc)"),
        "expected the fallthrough exit value to be assigned before the loop continue:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected the recursive handler to stay as a loop continue:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected direct recursive return remained after the staticcatch handler:\n{rendered}"
    );
}

#[test]
fn nested_wrapped_staticcatch_trywith_tail_loops_lower_like_gpr_1701() {
    let mut compiler = LambdaCompiler::new();
    let outer = Ident::create_local("readLines");
    let inc = Ident::create_local("inc");
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let read = Ident::create_local("read");
    let next_acc = Ident::create_local("nextAcc");
    let exn = Ident::create_local("exn");
    let raw_exn = Ident::create_local("rawExn");
    let reverse = Ident::create_local("reverse");
    let eof = Ident::create_local("End_of_file");
    let cons = Lambda::prim(
        Primitive::Pmakeblock(
            TagInfo::Constructor {
                name: "::".to_string(),
                num_nonconst: 1,
                runtime: Box::new(crate::types::TaggedBlock {
                    tag: crate::types::VariantTag {
                        name: "::".to_string(),
                        literal: crate::types::VariantLiteralTag::String("::".to_string()),
                    },
                    tag_name: None,
                }),
            },
            Mutable::Immutable,
        ),
        vec![Lambda::var(next_acc), Lambda::var(acc)],
        LamLoc::NONE,
    );

    let lam = Lambda::letrec(
        vec![(
            outer,
            Lambda::function_(
                    1,
                    vec![inc],
                    Lambda::letrec(
                        vec![(
                            loop_,
                            Lambda::function_(
                                    1,
                                    vec![acc],
                                    Lambda::LstaticCatch(
                                        Box::new(Lambda::LtryWith(
                                            Box::new(Lambda::LstaticRaise(
                                                -1,
                                                vec![Lambda::Lapply(Box::new(Apply {
                                                    ap_func: Box::new(Lambda::var(
                                                        read,
                                                    )),
                                                    ap_args: vec![Lambda::var(inc)],
                                                    ap_info: ApInfo {
                                                        loc: LamLoc::NONE,
                                                        status: ApplyStatus::Na,
                                                    },
                                                }))],
                                            )),
                                            raw_exn,
                                            Box::new(Lambda::let_(
                                                LetKind::StrictOpt,
                                                exn,
                                                crate::raw_lambda::lower::wrap_exn(
                                                    LamLoc::NONE,
                                                    Lambda::var(raw_exn),
                                                ),
                                                Lambda::LstaticCatch(
                                                    Box::new(Lambda::if_(
                                                        Lambda::prim(
                                                            Primitive::Pstringcomp(
                                                                Comparison::Eq,
                                                            ),
                                                            vec![
                                                                Lambda::prim(
                                                                    Primitive::Pfield(
                                                                        0,
                                                                        crate::lambda::lam_compat::FieldDbgInfo::Record {
                                                                            name: "RE_EXN_ID".to_string(),
                                                                        },
                                                                    ),
                                                                    vec![Lambda::var(exn)],
                                                                    LamLoc::NONE,
                                                                ),
                                                                Lambda::var(eof),
                                                            ],
                                                            LamLoc::NONE,
                                                        ),
                                                        Lambda::Lapply(Box::new(Apply {
                                                            ap_func: Box::new(Lambda::var(
                                                                reverse,
                                                            )),
                                                            ap_args: vec![Lambda::var(
                                                                acc,
                                                            )],
                                                            ap_info: ApInfo {
                                                                loc: LamLoc::NONE,
                                                                status: ApplyStatus::Na,
                                                            },
                                                        })),
                                                        Lambda::LstaticRaise(3, vec![]),
                                                    )),
                                                    (3, vec![]),
                                                    Box::new(Lambda::prim(
                                                        Primitive::Praise,
                                                        vec![Lambda::var(exn)],
                                                        LamLoc::NONE,
                                                    )),
                                                ),
                                            )),
                                        )),
                                        (-1, vec![next_acc]),
                                        Box::new(Lambda::Lapply(Box::new(Apply {
                                            ap_func: Box::new(Lambda::var(loop_)),
                                            ap_args: vec![cons],
                                            ap_info: ApInfo {
                                                loc: LamLoc::NONE,
                                                status: ApplyStatus::Na,
                                            },
                                        }))),
                                    ),
                                    FunctionAttribute::default(), LamLoc::NONE,
                                ),
                        )],
                        Lambda::Lapply(Box::new(Apply {
                            ap_func: Box::new(Lambda::var(loop_)),
                            ap_args: vec![Lambda::const_(Constant::int(0))],
                            ap_info: ApInfo {
                                loc: LamLoc::NONE,
                                status: ApplyStatus::Na,
                            },
                        })),
                    ),
                    FunctionAttribute::default(), LamLoc::NONE,
                ),
        )],
        Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::ModuleExport(vec![outer]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(outer)],
            LamLoc::NONE,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);

    assert!(
        rendered.contains("while (true)"),
        "expected nested wrapped staticcatch tail recursion to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected nested wrapped staticcatch tail recursion to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop({") && !rendered.contains("return loop(nextAcc)"),
        "unexpected direct recursive return remained in the wrapped staticcatch path:\n{rendered}"
    );
}

#[test]
fn fallthrough_handlers_do_not_reorder_grouped_named_string_return_cases() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let case_a = Lambda::const_(Constant::int(2));
    let case_b = Lambda::const_(Constant::int(1));
    let case_c = Lambda::const_(Constant::int(2));
    let cases = vec![
        (SwitchCaseTag::String("A".to_string()), &case_a),
        (SwitchCaseTag::String("B".to_string()), &case_b),
        (SwitchCaseTag::String("C".to_string()), &case_c),
    ];

    let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
        this.compile_named_string_switch_return(Expression::var(scrutinee), &cases, None, true)
    });

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(clauses[1].clause.body.is_empty());
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
}

#[test]
fn fallthrough_handlers_do_not_reorder_grouped_string_switch_return_blocks() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
        this.compile_string_switch_return_block(
            &Lambda::var(scrutinee),
            &[
                ("A".to_string(), Lambda::const_(Constant::int(2))),
                ("B".to_string(), Lambda::const_(Constant::int(1))),
                ("C".to_string(), Lambda::const_(Constant::int(2))),
            ],
            None,
        )
    });

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(clauses[1].clause.body.is_empty());
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
}

#[test]
fn partial_int_return_switch_cases_break_to_shared_handler_like_test_set() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let cond = Ident::create_local("cond");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action)),
            Box::new(LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (
                        crate::lambda::SwitchKey::Int(1),
                        Lambda::if_(
                            Lambda::var(cond),
                            Lambda::const_(Constant::int(10)),
                            Lambda::static_raise(1, Vec::new()),
                        ),
                    ),
                    (
                        crate::lambda::SwitchKey::Int(2),
                        Lambda::const_(Constant::int(20)),
                    ),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the shared handler return");
    };
    let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the shared handler to stay outside the switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));
    assert_eq!(clauses.len(), 2);
    assert_eq!(clauses[0].0, 1);
    assert!(
        clauses[0].1.should_break,
        "expected the partial case to break to the shared handler"
    );
    assert_eq!(clauses[1].0, 2);
    assert_switch_case_returns_int_result(&clauses[1].1.body, 20);
    assert!(
        !clauses[1].1.should_break,
        "expected the fully returning case to omit break"
    );

    let rendered = print_block(&block);
    assert_eq!(
        rendered,
        "switch (action) {\n  case 1 :\n    if (cond) {\n      return 10;\n    }\n    break;\n  case 2 :\n    return 20;\n}\n\nreturn 30;"
    );

    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 30),
        other => panic!("expected the shared handler return, got {other:?}"),
    }
}

#[test]
fn nested_staticcatch_switch_forwarders_keep_collapsed_shared_return_like_gpr_3609() {
    let mut compiler = LambdaCompiler::new();
    let state = Ident::create_local("state");
    let int_value = Ident::create_local("intValue");
    let int_func = Ident::create_local("intFunc");
    let int_param = Ident::create_local("intParam");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(state)),
                Box::new(LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: "Empty".to_string(),
                                    literal: crate::types::VariantLiteralTag::String(
                                        "Empty".to_string(),
                                    ),
                                },
                            ),
                        ),
                        Lambda::const_(Constant::int(0)),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![
                        (
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                        tag: crate::types::VariantTag {
                                            name: "Int1".to_string(),
                                            literal: crate::types::VariantLiteralTag::String(
                                                "Int1".to_string(),
                                            ),
                                        },
                                        tag_name: None,
                                    }),
                                ),
                            ),
                            Lambda::static_raise(2, Vec::new()),
                        ),
                        (
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                        tag: crate::types::VariantTag {
                                            name: "Int2".to_string(),
                                            literal: crate::types::VariantLiteralTag::String(
                                                "Int2".to_string(),
                                            ),
                                        },
                                        tag_name: None,
                                    }),
                                ),
                            ),
                            Lambda::static_raise(2, Vec::new()),
                        ),
                    ],
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                        crate::types::VariantMatchingFacts {
                            tag_name: None,
                            block_types: vec![],
                            literal_tags: vec![crate::types::VariantLiteralTag::String(
                                "Empty".to_string().clone(),
                            )],
                        },
                    ),
                }),
            )),
            (2, vec![]),
            Box::new(Lambda::let_(
                LetKind::Alias,
                int_value,
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Variant),
                    vec![Lambda::var(state)],
                    LamLoc::NONE,
                ),
                Lambda::static_raise(1, vec![Lambda::var(int_value)]),
            )),
        )),
        (1, vec![int_value]),
        Box::new(Lambda::let_(
            LetKind::Strict,
            int_func,
            Lambda::function_(
                1,
                vec![int_param],
                Lambda::prim(
                    Primitive::Paddint,
                    vec![Lambda::var(int_param), Lambda::var(int_value)],
                    LamLoc::NONE,
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
            Lambda::apply(
                Lambda::var(int_func),
                vec![Lambda::const_(Constant::int(0))],
                ApInfo {
                    loc: LamLoc::NONE,
                    status: ApplyStatus::Uncurry,
                },
            ),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (typeof state !== \"object\") {"),
        "expected the outer object split to stay materialized:\n{rendered}"
    );
    assert!(
        !rendered.contains("state.TAG ==="),
        "gpr_3609-style shared payload handlers should not reintroduce a tag split:\n{rendered}"
    );
    assert!(
        rendered.contains("return intFunc(0);"),
        "expected the shared payload tail to stay forwarded through the outer handler:\n{rendered}"
    );
}

#[test]
fn unit_return_staticcatch_bindings_without_handler_exits_share_fallthrough_tail() {
    let mut compiler = LambdaCompiler::new();
    let cond1 = Ident::create_local("cond1");
    let cond2 = Ident::create_local("cond2");
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let carried = Ident::create_local("carried");
    let seen = Ident::create_local("seen");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond1),
                Lambda::static_raise(1, vec![Lambda::var(first)]),
                Lambda::LifThenElse(
                    Box::new(Lambda::var(cond2)),
                    Box::new(Lambda::static_raise(1, vec![Lambda::var(second)])),
                    Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
                ),
            )),
            (1, vec![carried]),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lassign(seen, Box::new(Lambda::var(carried)))),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            )),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "single-handler unit-return staticcatch bindings reintroduced an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("let carried;"),
        "expected the carried binding to stay declared ahead of the shared tail:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("seen = carried;").count(),
        1,
        "expected the handler tail to stay shared exactly once:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the non-matching branch to keep its early return:\n{rendered}"
    );
}

#[test]
fn return_staticcatchs_share_nontrivial_handlers_across_multiple_exit_sites() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let kind = Ident::create_local("kind");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond),
                Lambda::static_raise(2, Vec::new()),
                Lambda::LstringSwitch(
                    Box::new(Lambda::var(kind)),
                    vec![("e".to_string(), Lambda::const_(Constant::int(4)))],
                    Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                ),
            )),
            (2, vec![]),
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(kind)),
                vec![("f".to_string(), Lambda::const_(Constant::int(5)))],
                Some(Box::new(Lambda::static_raise(1, Vec::new()))),
            )),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(6))),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("let exit = 0;"),
        "expected repeated exits to share the handler behind an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("if (exit ==="),
        "expected the shared handler to stay after an explicit exit test:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("=== \"f\"").count(),
        1,
        "expected the nontrivial handler to be emitted once:\n{rendered}"
    );
}

#[test]
fn return_staticcatchs_keep_plain_handlers_inline_across_multiple_exit_sites() {
    let mut compiler = LambdaCompiler::new();
    let kind = Ident::create_local("kind");
    let do_with_b = Ident::create_local("doWithB");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(kind)),
            vec![
                ("four".to_string(), Lambda::static_raise(2, Vec::new())),
                ("five".to_string(), Lambda::static_raise(2, Vec::new())),
                ("six".to_string(), Lambda::const_(Constant::int(6))),
            ],
            Some(Box::new(Lambda::const_(Constant::int(7)))),
        )),
        (2, vec![]),
        Box::new(Lambda::apply(
            Lambda::var(do_with_b),
            vec![Lambda::var(kind)],
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "plain multi-exit handlers should stay inline without an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("case \"four\" :") && rendered.contains("case \"five\" :"),
        "expected grouped inline cases for the shared handler:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("return doWithB(kind);").count(),
        1,
        "expected the shared plain handler to stay inline in the switch:\n{rendered}"
    );
}

#[test]
fn single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action)),
                Box::new(LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: "One".to_string(),
                                    literal: crate::types::VariantLiteralTag::String(
                                        "One".to_string(),
                                    ),
                                },
                            ),
                        ),
                        Lambda::const_(Constant::int(1)),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                        crate::types::VariantMatchingFacts {
                            tag_name: None,
                            block_types: vec![],
                            literal_tags: vec![crate::types::VariantLiteralTag::String(
                                "One".to_string().clone(),
                            )],
                        },
                    ),
                }),
            )),
            (7, vec![]),
            Box::new(Lambda::const_(Constant::int(2))),
        ))
    });

    let [if_stmt, handler_return] = block.as_slice() else {
        panic!("expected an if statement followed by the handler return");
    };
    let (cond, then_block, else_block) = match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => (cond, then_block, else_block),
        StatementDesc::Block(inner) => {
            let [inner_if] = inner.as_slice() else {
                panic!("expected the staticcatch wrapper block to contain a single if");
            };
            let StatementDesc::If(cond, then_block, else_block) = &inner_if.desc else {
                panic!("expected the single-case staticcatch switch to lower to if/fallthrough");
            };
            (cond, then_block, else_block)
        }
        other => panic!(
            "expected the single-case staticcatch switch to lower to if/fallthrough, got {other:?}"
        ),
    };
    assert_string_equality_check(cond, Some(&action), None, "One");
    assert!(
        else_block.is_empty(),
        "unexpected else block: {else_block:?}"
    );
    assert_switch_case_returns_int_result(then_block, 1);
    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 2),
        other => panic!("expected the fallthrough handler return, got {other:?}"),
    }
}

#[test]
fn single_case_staticcatch_wrapped_named_variant_non_unit_return_switch_falls_through_to_handler() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action)),
            Box::new(LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "One".to_string(),
                            literal: crate::types::VariantLiteralTag::String("One".to_string()),
                        }),
                    ),
                    Lambda::const_(Constant::int(1)),
                )],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                    crate::types::VariantMatchingFacts {
                        tag_name: None,
                        block_types: vec![],
                        literal_tags: vec![crate::types::VariantLiteralTag::String(
                            "One".to_string().clone(),
                        )],
                    },
                ),
            }),
        )),
        (7, vec![]),
        Box::new(Lambda::const_(Constant::int(2))),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (action === \"One\") {"),
        "expected the single-case switch to stay as a positive guard:\n{rendered}"
    );
    assert!(
        rendered.contains("return 1;"),
        "expected the matching branch to return directly:\n{rendered}"
    );
    assert!(
        rendered.contains("return 2;"),
        "expected the handler return to fall through after the guard:\n{rendered}"
    );
    assert!(
        !rendered.contains("} else {"),
        "unexpected explicit else around the fallthrough handler:\n{rendered}"
    );
}

#[test]
fn single_case_staticcatch_wrapped_named_variant_unit_handler_falls_through_like_variant_pattern_matching_spreads()
 {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let then_seen = Ident::create_local("then_seen");
    let else_seen = Ident::create_local("else_seen");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action)),
                Box::new(LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: "One".to_string(),
                                    literal: crate::types::VariantLiteralTag::String(
                                        "One".to_string(),
                                    ),
                                },
                            ),
                        ),
                        Lambda::Lassign(then_seen, Box::new(Lambda::const_(Constant::int(1)))),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                        crate::types::VariantMatchingFacts {
                            tag_name: None,
                            block_types: vec![],
                            literal_tags: vec![crate::types::VariantLiteralTag::String(
                                "One".to_string().clone(),
                            )],
                        },
                    ),
                }),
            )),
            (7, vec![]),
            Box::new(Lambda::Lassign(
                else_seen,
                Box::new(Lambda::const_(Constant::int(2))),
            )),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (action === \"One\") {"),
        "expected the single-case handler to stay as a positive guard:\n{rendered}"
    );
    assert!(
        rendered.contains("then_seen = 1;"),
        "expected the matching branch effect to stay inside the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("else_seen = 2;"),
        "expected the non-matching handler to fall through after the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the matching branch to keep its explicit unit return:\n{rendered}"
    );
    assert!(
        !rendered.contains("} else {"),
        "unexpected explicit else around the fallthrough handler:\n{rendered}"
    );
}

#[test]
fn js_pipeline_keeps_single_case_staticcatch_unit_handler_as_fallthrough_guard() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let action = Ident::create_local("action");
    let then_seen = Ident::create_local("then_seen");
    let else_seen = Ident::create_local("else_seen");
    let lam = Lambda::let_(
        LetKind::Strict,
        run,
        Lambda::function_(
            1,
            vec![action],
            Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action)),
                    Box::new(LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![(
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Constant(
                                    crate::types::VariantTag {
                                        name: "One".to_string(),
                                        literal: crate::types::VariantLiteralTag::String(
                                            "One".to_string(),
                                        ),
                                    },
                                ),
                            ),
                            Lambda::Lassign(then_seen, Box::new(Lambda::const_(Constant::int(1)))),
                        )],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                        sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                            crate::types::VariantMatchingFacts {
                                tag_name: None,
                                block_types: vec![],
                                literal_tags: vec![crate::types::VariantLiteralTag::String(
                                    "One".to_string().clone(),
                                )],
                            },
                        ),
                    }),
                )),
                (7, vec![]),
                Box::new(Lambda::Lassign(
                    else_seen,
                    Box::new(Lambda::const_(Constant::int(2))),
                )),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            LamLoc::NONE,
        ),
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![run]), Mutable::Immutable),
            vec![Lambda::var(run)],
            LamLoc::NONE,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (action === \"One\") {"),
        "expected the final JS pipeline to keep the positive guard:\n{rendered}"
    );
    assert!(
        rendered.contains("then_seen = 1;"),
        "expected the matching branch effect to stay materialized:\n{rendered}"
    );
    assert!(
        rendered.contains("else_seen = 2;"),
        "expected the handler effect to stay after the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the matching branch to keep its explicit unit return:\n{rendered}"
    );
    assert!(
        !rendered.contains("} else {"),
        "unexpected explicit else around the final JS pipeline output:\n{rendered}"
    );
}
