use super::*;

#[test]
fn named_variant_switch_expressions_split_const_and_block_dispatch() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee)),
        Box::new(LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![(
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "A".to_string(),
                        literal: None,
                    }),
                ),
                Lambda::const_(Constant::int(1)),
            )],
            sw_blocks_full: false,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                        tag: crate::types::VariantTag {
                            name: "B".to_string(),
                            literal: None,
                        },
                        tag_name: None,
                    }),
                )),
                Lambda::const_(Constant::int(2)),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![crate::types::VariantLiteralTag::String(
                        "A".to_string().clone(),
                    )],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        }),
    ));

    let rendered = print_block(&compiled.prelude);
    assert!(
        rendered.contains("typeof scrutinee !== \"object\" ?"),
        "expected the mixed named-variant dispatch to test the const side first:\n{rendered}"
    );
    assert!(
        rendered.contains("scrutinee === \"A\" ? 1 : 3"),
        "expected the const-side conditional to stay materialized:\n{rendered}"
    );
    assert!(
        rendered.contains("scrutinee.TAG === \"B\" ? 2 : 3"),
        "expected the payload-side conditional to stay materialized:\n{rendered}"
    );
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(_)),
            ..
        }
    ));
}

#[test]
fn named_variant_constant_return_switch_skips_redundant_match_temp() {
    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::const_(Constant::int(2))),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "A".to_string(),
                            literal: Some(crate::types::VariantLiteralTag::Int(0)),
                        }),
                    ),
                    Lambda::const_(Constant::string("a")),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "B".to_string(),
                            literal: Some(crate::types::VariantLiteralTag::Int(2)),
                        }),
                    ),
                    Lambda::const_(Constant::string("b")),
                ),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::Int(2),
                        crate::types::VariantLiteralTag::Int(0),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        }),
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected a single simplified return statement");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Str(txt),
            ..
        }) => assert_eq!(txt, "b"),
        StatementDesc::Block(inner) => {
            let [inner_stmt] = inner.as_slice() else {
                panic!("expected the simplified block to contain one return");
            };
            assert!(matches!(
                &inner_stmt.desc,
                StatementDesc::Return(Expression {
                    desc: ExpressionDesc::Str(txt),
                    ..
                }) if txt == "b"
            ));
        }
        other => panic!("expected the switch to collapse to the taken branch, got {other:?}"),
    }
}

#[test]
fn named_variant_return_switches_with_only_payload_cases_skip_object_split() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "Ok".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "Error".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        }),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("return action.TAG === \"Ok\" ? 1 : 2;"),
        "expected the all-payload switch to lower directly over TAG without an object split:\n{rendered}"
    );
}

#[test]
fn named_variant_mixed_const_and_identical_payload_return_cases_drop_redundant_tag_split_like_gpr_3609()
 {
    let mut compiler = LambdaCompiler::new();
    let state = Ident::create_local("state");
    let payload = Lambda::prim(
        Primitive::Paddint,
        vec![
            Lambda::const_(Constant::int(0)),
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Variant),
                vec![Lambda::var(state)],
                Location::none(),
            ),
        ],
        Location::none(),
    );
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(state)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "Empty".to_string(),
                        literal: None,
                    }),
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
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    payload.clone(),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "Int2".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    payload,
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
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        }),
    ));

    assert_eq!(
        print_block(&block),
        "return typeof state !== \"object\" ? 0 : 0 + state._0 | 0;"
    );
}

#[test]
fn named_variant_incomplete_payload_only_return_switches_keep_default_as_negated_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action)),
        Box::new(LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                        tag: crate::types::VariantTag {
                            name: "C".to_string(),
                            literal: None,
                        },
                        tag_name: None,
                    }),
                )),
                Lambda::const_(Constant::int(7)),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("A2".to_string().clone()),
                        crate::types::VariantLiteralTag::String("A1".to_string().clone()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        }),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("return typeof action !== \"object\" || action.TAG !== \"C\" ? 42 : 7;"),
        "expected the incomplete payload-only dispatch to keep OCaml's negated default guard:\n{rendered}"
    );
}

#[test]
fn named_variant_incomplete_const_only_return_switches_keep_literal_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action)),
        Box::new(LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![(
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "A1".to_string(),
                        literal: None,
                    }),
                ),
                Lambda::const_(Constant::int(1)),
            )],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("A2".to_string().clone()),
                        crate::types::VariantLiteralTag::String("A1".to_string().clone()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        }),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("return typeof action !== \"object\" && action === \"A1\" ? 1 : 42;"),
        "expected the incomplete const-only dispatch to keep the literal-side guard:\n{rendered}"
    );
}

#[test]
fn named_variant_return_switches_keep_default_only_const_side_inside_outer_else_like_typeof_test() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_named_variant_switch_return_statements(
        Expression::var(action),
        &LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "A".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(0)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "B".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(0)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "C".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(0)),
                ),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "WithPayloadA".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "WithPayloadB".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "WithPayloadC".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(3)),
                ),
            ],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("C".to_string().clone()),
                        crate::types::VariantLiteralTag::String("B".to_string().clone()),
                        crate::types::VariantLiteralTag::String("A".to_string().clone()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        },
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single outer named-variant dispatch");
    };
    let StatementDesc::If(test, then_block, else_block) = &dispatch.desc else {
        panic!(
            "expected the mixed named-variant return dispatch to stay as an explicit if/else:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &test.desc,
            ExpressionDesc::Bin(BinOp::NotEqEq, left, right)
                if matches!(
                    (&left.as_ref().desc, &right.as_ref().desc),
                    (
                        ExpressionDesc::Typeof(inner),
                        ExpressionDesc::Str(txt)
                    ) if matches!(
                        inner.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&action)
                    ) && txt == "object"
                )
        ),
        "unexpected outer literal-vs-payload dispatch test:\n{}",
        print_block(&block)
    );

    let [const_switch] = then_block.as_slice() else {
        panic!(
            "expected the const branch to stay wrapped in a switch default:\n{}",
            print_block(&block)
        );
    };
    let StatementDesc::StringSwitch(const_test, const_clauses, Some(const_default)) =
        &const_switch.desc
    else {
        panic!(
            "expected the const branch to stay as a string switch with a default arm:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &const_test.desc,
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&action)
        ),
        "unexpected const-side switch test:\n{}",
        print_block(&block)
    );
    assert!(
        const_clauses.is_empty(),
        "expected default-duplicate const cases to filter away while keeping the switch:\n{}",
        print_block(&block)
    );
    assert_switch_default_returns_int_result(const_default, 0);

    let [payload_switch] = else_block.as_slice() else {
        panic!(
            "expected the payload branch to stay attached as the outer else block:\n{}",
            print_block(&block)
        );
    };
    let StatementDesc::StringSwitch(payload_test, payload_clauses, Some(payload_default)) =
        &payload_switch.desc
    else {
        panic!(
            "expected the payload branch to stay as a tag switch:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &payload_test.desc,
            ExpressionDesc::StaticIndex(inner, field, _)
                if matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&action)
                ) && field == "TAG"
        ),
        "expected the payload branch to switch on the variant TAG field:\n{}",
        print_block(&block)
    );
    assert_eq!(
        payload_clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("WithPayloadA".to_string()),
            SwitchCaseTag::String("WithPayloadB".to_string()),
            SwitchCaseTag::String("WithPayloadC".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&payload_clauses[0].clause.body, 1);
    assert_switch_case_returns_int_result(&payload_clauses[1].clause.body, 2);
    assert_switch_case_returns_int_result(&payload_clauses[2].clause.body, 3);
    assert_switch_default_returns_int_result(payload_default, 0);
}

#[test]
fn named_variant_return_switches_keep_shared_final_groups_inside_the_switch_without_exits() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "A".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "B".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                                tag: crate::types::VariantTag {
                                    name: "C".to_string(),
                                    literal: None,
                                },
                                tag_name: None,
                            }),
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        }),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single payload tag switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected a direct payload tag switch without a default arm");
    };
    assert_tag_field_access(test, &action);
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
    assert!(
        clauses[1].clause.body.is_empty(),
        "expected the first shared case to keep falling through"
    );
    assert!(!clauses[1].clause.should_break);
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    assert!(
        !clauses[2].clause.should_break,
        "plain shared return groups should stay in the switch without an exit-driven break"
    );
}

#[test]
fn builtin_untagged_block_switch_expressions_dispatch_on_object_runtime_shape() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(value)),
        Box::new(LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Untagged {
                        tag: crate::types::VariantTag {
                            name: "Object".to_string(),
                            literal: None,
                        },
                        block_type: crate::types::VariantBlockType::Object,
                    },
                )),
                Lambda::let_(
                    LetKind::Strict,
                    body_id,
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(body_id),
                ),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![crate::types::VariantBlockType::Object],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        }),
    ));

    let [declare, dispatch] = compiled.prelude.as_slice() else {
        panic!("expected a result declaration followed by object dispatch");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc else {
        panic!("expected the switch result declaration");
    };
    let StatementDesc::If(cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected an object runtime check around the block case");
    };

    assert_typeof_object_check(cond, &value, true);
    assert!(matches!(
        then_block.as_slice(),
        [
            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value: Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    }),
                    ..
                }),
                ..
            },
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                    ..
                }),
                ..
            }
        ] if ident.same(&body_id)
            && *i == 1
            && matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(result)
            )
            && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&body_id)
            )
    ));
    assert_switch_default_assigns_int_result(else_block, result, 0);
}

#[test]
fn object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "String".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::String,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Number".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Int,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(3)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Array".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Instance(
                                    crate::types::VariantInstance::Array,
                                ),
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(4)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                        crate::types::VariantBlockType::Object,
                        crate::types::VariantBlockType::Int,
                        crate::types::VariantBlockType::String,
                    ],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        },
    );
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch, typeof_switch] = statements else {
        panic!("expected an Array runtime split followed by a typeof switch");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_switch_case_returns_int_result(then_block, 4);
    assert!(else_block.is_empty());

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining block cases to stay inside a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("string".to_string()),
            SwitchCaseTag::String("number".to_string()),
            SwitchCaseTag::String("object".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 3);
}

#[test]
fn mixed_array_object_function_untagged_return_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Array".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Instance(
                                    crate::types::VariantInstance::Array,
                                ),
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Function".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Function,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(3)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Function,
                        crate::types::VariantBlockType::Object,
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                    ],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        },
    );
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch, typeof_switch] = statements else {
        panic!("expected an Array runtime split followed by a typeof switch");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_switch_case_returns_int_result(then_block, 1);
    assert!(else_block.is_empty());

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining object/function cases to stay in a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("object".to_string()),
            SwitchCaseTag::String("function".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 2);
    assert_switch_case_returns_int_result(&clauses[1].clause.body, 3);
}

#[test]
fn mixed_literal_and_block_untagged_return_dispatch_keeps_outer_else_block() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let string_seen = Ident::create_local("string_seen");
    let int_seen = Ident::create_local("int_seen");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let mark = |slot: &Ident, value| {
        Lambda::seq(
            Lambda::Lassign(*slot, Box::new(Lambda::const_(Constant::int(value)))),
            Lambda::unit(),
        )
    };
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "test".to_string(),
                            literal: Some(crate::types::VariantLiteralTag::String(
                                "test".to_string(),
                            )),
                        }),
                    ),
                    mark(&string_seen, 1),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "Twelve".to_string(),
                            literal: Some(crate::types::VariantLiteralTag::Int(12)),
                        }),
                    ),
                    mark(&int_seen, 2),
                ),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Array".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Instance(
                                    crate::types::VariantInstance::Array,
                                ),
                            },
                        ),
                    ),
                    mark(&array_seen, 3),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    mark(&object_seen, 4),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Object,
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                    ],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::Int(12),
                        crate::types::VariantLiteralTag::String("test".to_string()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        },
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single outer literal-vs-block dispatch");
    };
    let StatementDesc::If(_, then_block, else_block) = &dispatch.desc else {
        panic!("expected the mixed dispatch to stay as an explicit if/else");
    };
    assert!(
        matches!(
            then_block.as_slice(),
            [Statement {
                desc: StatementDesc::Block(_),
                ..
            }]
        ),
        "expected the small literal return switch to stay wrapped inside the outer dispatch:\n{}",
        print_block(&block)
    );
    assert!(
        !else_block.is_empty(),
        "expected the block branch to stay attached as an else block:\n{}",
        print_block(&block)
    );
}

#[test]
fn mixed_array_object_function_untagged_effect_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let function_seen = Ident::create_local("function_seen");
    let block = compiler.compile_effect_block(&Lambda::Lswitch(
        Box::new(Lambda::var(value)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Array".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Instance(
                                    crate::types::VariantInstance::Array,
                                ),
                            },
                        ),
                    ),
                    Lambda::Lassign(array_seen, Box::new(Lambda::const_(Constant::int(1)))),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    Lambda::Lassign(object_seen, Box::new(Lambda::const_(Constant::int(2)))),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Function".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Function,
                            },
                        ),
                    ),
                    Lambda::Lassign(function_seen, Box::new(Lambda::const_(Constant::int(3)))),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Function,
                        crate::types::VariantBlockType::Object,
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                    ],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        }),
    ));
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch] = statements else {
        panic!("expected an Array runtime split with a typeof-switch fallback");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_eq!(then_block.len(), 1);
    let StatementDesc::Exp(expr) = &then_block[0].desc else {
        panic!("expected the Array branch to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &array_seen, 1);
    let [typeof_switch] = else_block.as_slice() else {
        panic!("expected the object/function fallback to stay inside a typeof switch");
    };

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining object/function cases to stay in a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("object".to_string()),
            SwitchCaseTag::String("function".to_string()),
        ]
    );
    assert_eq!(clauses[0].clause.body.len(), 1);
    let StatementDesc::Exp(expr) = &clauses[0].clause.body[0].desc else {
        panic!("expected the object clause to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &object_seen, 2);
    assert_eq!(clauses[1].clause.body.len(), 1);
    let StatementDesc::Exp(expr) = &clauses[1].clause.body[0].desc else {
        panic!("expected the function clause to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &function_seen, 3);
}

#[test]
fn untagged_literal_dispatch_keeps_ocaml_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "One".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "Two".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "Three".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(3)),
                ),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Untagged {
                        tag: crate::types::VariantTag {
                            name: "FutureAddedValue".to_string(),
                            literal: None,
                        },
                        block_type: crate::types::VariantBlockType::String,
                    },
                )),
                Lambda::const_(Constant::int(4)),
            )],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![crate::types::VariantBlockType::String],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("Three".to_string().clone()),
                        crate::types::VariantLiteralTag::String("Two".to_string().clone()),
                        crate::types::VariantLiteralTag::String("One".to_string().clone()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains("value !== \"One\" && value !== \"Three\" && value !== \"Two\""),
        "expected the literal dispatch guard to follow the natural semantic constructor dispatch order before the FutureAddedValue fallback:\n{rendered}"
    );
    assert!(
        rendered.contains("case \"One\" :\n    return 1;")
            && rendered.contains("case \"Two\" :\n    return 2;")
            && rendered.contains("case \"Three\" :\n    return 3;"),
        "expected each literal constructor to keep its own case with its bound result in declaration order:\n{rendered}"
    );
    assert!(
        !rendered.contains("FutureAddedValue") && rendered.contains("return 4;"),
        "expected the untagged block fallback to return its bound result without emitting the synthetic tag:\n{rendered}"
    );
}

#[test]
fn mixed_untagged_literal_dispatch_keeps_ocaml_block_overlap_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "A".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "B".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "C".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(3)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "D".to_string(),
                            literal: None,
                        }),
                    ),
                    Lambda::const_(Constant::int(4)),
                ),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "String".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::String,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(5)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Int".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Int,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(6)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(7)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Object,
                        crate::types::VariantBlockType::Int,
                        crate::types::VariantBlockType::String,
                    ],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("D".to_string().clone()),
                        crate::types::VariantLiteralTag::String("C".to_string().clone()),
                        crate::types::VariantLiteralTag::String("B".to_string().clone()),
                        crate::types::VariantLiteralTag::String("A".to_string().clone()),
                    ],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered
            .contains("value === \"A\" || value === \"D\" || value === \"B\" || value === \"C\""),
        "expected the literal dispatch guard to follow the natural semantic constructor order across overlapping block kinds:\n{rendered}"
    );
    assert!(
        rendered.contains("switch (typeof value) {")
            && rendered.find("case \"string\" :").unwrap()
                < rendered.find("case \"number\" :").unwrap()
            && rendered.find("case \"number\" :").unwrap()
                < rendered.find("case \"object\" :").unwrap(),
        "expected overlapping block-kind clauses to follow the block declaration order (String, Int, Object):\n{rendered}"
    );
    for (tag, result) in [("A", 1), ("B", 2), ("C", 3), ("D", 4)] {
        assert!(
            rendered.contains(&format!("case \"{tag}\" :\n      return {result};")),
            "expected literal case {tag} to keep its bound result inside the guarded string switch:\n{rendered}"
        );
    }
    for (kind, result) in [("string", 5), ("number", 6), ("object", 7)] {
        assert!(
            rendered.contains(&format!("case \"{kind}\" :\n      return {result};")),
            "expected block-kind clause {kind} to keep its bound result inside the typeof switch:\n{rendered}"
        );
    }
}

#[test]
fn small_untagged_object_value_switches_keep_ocaml_runtime_guards() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(value)),
        Box::new(LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Untagged {
                        tag: crate::types::VariantTag {
                            name: "Object".to_string(),
                            literal: None,
                        },
                        block_type: crate::types::VariantBlockType::Object,
                    },
                )),
                Lambda::const_(Constant::int(1)),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                        crate::types::VariantBlockType::Object,
                    ],
                    literal_tags: vec![crate::types::VariantLiteralTag::Null],
                    has_null: true,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        }),
    ));

    let rendered = print_block(&compiled.prelude);
    assert!(
        rendered.contains("typeof value === \"object\" && value !== null && !Array.isArray(value)"),
        "expected the small object switch to keep OCaml's object/null/array runtime guard:\n{rendered}"
    );
}

#[test]
fn complete_object_then_array_untagged_return_switches_preserve_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Object".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Object,
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Block(
                            crate::types::VariantBlock::Untagged {
                                tag: crate::types::VariantTag {
                                    name: "Array".to_string(),
                                    literal: None,
                                },
                                block_type: crate::types::VariantBlockType::Instance(
                                    crate::types::VariantInstance::Array,
                                ),
                            },
                        ),
                    ),
                    Lambda::const_(Constant::int(2)),
                ),
            ],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                        crate::types::VariantBlockType::Object,
                    ],
                    literal_tags: vec![],
                    has_null: false,
                    has_undefined: false,
                    has_other_literal: false,
                },
            ),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains("typeof value === \"object\" && !Array.isArray(value)"),
        "expected the object-first two-case switch to keep the first case test:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (Array.isArray(value))"),
        "expected the object-first two-case switch not to flip to an Array-first split:\n{rendered}"
    );
}

#[test]
fn complete_single_untagged_array_value_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let result = Ident::create_local("result");
    let block = compiler.compile_untagged_variant_switch_assignment_statements(
        &result,
        Expression::var(value),
        &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal-vs-block dispatch");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch assignment");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
    let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
        panic!("expected a conditional expression on the assignment RHS");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_int_expr(then_expr, 0);
    assert_int_expr(else_expr, 1);
}

#[test]
fn complete_single_untagged_array_return_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal dispatch");
    };
    let StatementDesc::Return(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch return");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_int_expr(then_expr, 0);
    assert_int_expr(else_expr, 1);
}

#[test]
fn complete_single_untagged_array_effect_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let empty_seen = Ident::create_local("empty_seen");
    let cons_seen = Ident::create_local("cons_seen");
    let block = compiler.compile_untagged_variant_switch_effect_statements(
        Expression::var(value),
        &single_complete_array_block_switch(
            Lambda::Lassign(cons_seen, Box::new(Lambda::const_(Constant::int(1)))),
            Lambda::Lassign(empty_seen, Box::new(Lambda::const_(Constant::int(0)))),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal dispatch");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch effect expression");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_assignment_to_int(then_expr, &empty_seen, 0);
    assert_assignment_to_int(else_expr, &cons_seen, 1);
}

#[test]
fn default_only_untagged_boolean_assignment_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let result = Ident::create_local("result");
    let block = compiler.compile_untagged_variant_switch_assignment_statements(
        &result,
        Expression::var(value),
        &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [assign] = block.as_slice() else {
        panic!("expected a single direct switch assignment");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &assign.desc
    else {
        panic!("expected the switch assignment");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
    let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
        panic!("expected the assignment RHS to be a conditional expression");
    };
    assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
    assert_int_expr(then_expr, 1);
    assert_int_expr(else_expr, 0);
}

#[test]
fn default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single direct switch return");
    };
    let StatementDesc::Return(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the switch return to be a conditional expression");
    };
    assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
    assert_int_expr(then_expr, 1);
    assert_int_expr(else_expr, 0);
}

#[test]
fn default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value),
        &LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Untagged {
                        tag: crate::types::VariantTag {
                            name: "Object".to_string(),
                            literal: None,
                        },
                        block_type: crate::types::VariantBlockType::Object,
                    },
                )),
                Lambda::let_(
                    LetKind::Strict,
                    body_id,
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(body_id),
                ),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![
                        crate::types::VariantBlockType::Instance(
                            crate::types::VariantInstance::Array,
                        ),
                        crate::types::VariantBlockType::Object,
                    ],
                    literal_tags: vec![
                        crate::types::VariantLiteralTag::String("string".to_string()),
                        crate::types::VariantLiteralTag::Null,
                    ],
                    has_null: true,
                    has_undefined: false,
                    has_other_literal: true,
                },
            ),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered
            .contains("if (typeof value !== \"object\" || value === null || Array.isArray(value))"),
        "expected the literal/default side to stay outside the object chain:\n{rendered}"
    );
    assert!(
        rendered.contains("return 0;"),
        "expected the literal/default branch to return the fallback:\n{rendered}"
    );
    assert!(
        rendered.contains("let body = 1;") && rendered.contains("return body;"),
        "expected the object branch to stay inside the guarded path:\n{rendered}"
    );
}
