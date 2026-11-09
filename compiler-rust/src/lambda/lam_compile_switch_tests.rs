use super::*;
use crate::expect_dump;
use crate::js_ir::dump;
use crate::js_ir::printer::print_stmts;
use crate::lambda::LamLoc;

#[test]
fn named_variant_switch_expressions_split_const_and_block_dispatch() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr_lam(&Lambda::Lswitch(
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

    let rendered = print_stmts(&compiler.j, &compiled.prelude);
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
    expect_dump!(dump::expr(&compiler.j, compiled.expr), "tmp");
}

#[test]
fn named_variant_constant_return_switch_skips_redundant_match_temp() {
    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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

    expect_dump!(dump::block(&compiler.j, &block), "Return(\"b\")");
}

#[test]
fn named_variant_return_switches_with_only_payload_cases_skip_object_split() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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

    let rendered = print_stmts(&compiler.j, &block);
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
                LamLoc::NONE,
            ),
        ],
        LamLoc::NONE,
    );
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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
        print_stmts(&compiler.j, &block),
        "return typeof state !== \"object\" ? 0 : 0 + state._0 | 0;"
    );
}

#[test]
fn named_variant_incomplete_payload_only_return_switches_keep_default_as_negated_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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

    let rendered = print_stmts(&compiler.j, &block);
    assert!(
        rendered.contains("return typeof action !== \"object\" || action.TAG !== \"C\" ? 42 : 7;"),
        "expected the incomplete payload-only dispatch to keep OCaml's negated default guard:\n{rendered}"
    );
}

#[test]
fn named_variant_incomplete_const_only_return_switches_keep_literal_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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

    let rendered = print_stmts(&compiler.j, &block);
    assert!(
        rendered.contains("return typeof action !== \"object\" && action === \"A1\" ? 1 : 42;"),
        "expected the incomplete const-only dispatch to keep the literal-side guard:\n{rendered}"
    );
}

#[test]
fn named_variant_return_switches_keep_default_only_const_side_inside_outer_else_like_typeof_test() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = {
        let a0 = JE::var(action, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_named_variant_switch_return_statements_lam(a0, a1)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "If(NotEqEq(Typeof(action), \"object\")) {StringSwitch(action) {default: {Return(0)}}} else {StringSwitch(action.TAG) {case \"WithPayloadA\": {Return(1)} case \"WithPayloadB\": {Return(2)} case \"WithPayloadC\": {Return(3)} default: {Return(0)}}}"
    );
}

#[test]
fn named_variant_return_switches_keep_shared_final_groups_inside_the_switch_without_exits() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block_lam(&Lambda::Lswitch(
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

    expect_dump!(
        dump::block(&compiler.j, &block),
        "StringSwitch(action.TAG) {case \"A\": {Return(1)} case \"B\": {} case \"C\": {Return(2)} }"
    );
}

#[test]
fn builtin_untagged_block_switch_expressions_dispatch_on_object_runtime_shape() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let compiled = compiler.compile_expr_lam(&Lambda::Lswitch(
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

    expect_dump!(
        dump::block(&compiler.j, &compiled.prelude),
        "let[Strict] tmp; If(EqEqEq(Typeof(value), \"object\")) {let[Strict] body = 1; Exp(Eq(tmp, body))} else {Exp(Eq(tmp, 0))}"
    );
}

#[test]
fn object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };
    expect_dump!(
        dump::block(&compiler.j, &block),
        "If(Call[Na](Array.isArray; value)) {Return(4)} else {}; StringSwitch(Typeof(value)) {case \"string\": {Return(1)} case \"number\": {Return(2)} case \"object\": {Return(3)} }"
    );
}

#[test]
fn mixed_array_object_function_untagged_return_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };
    expect_dump!(
        dump::block(&compiler.j, &block),
        "If(Call[Na](Array.isArray; value)) {Return(1)} else {}; StringSwitch(Typeof(value)) {case \"object\": {Return(2)} case \"function\": {Return(3)} }"
    );
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
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "If(Or(EqEqEq(value, \"test\"), EqEqEq(value, 12))) {Block{If(EqEqEq(value, \"test\")) {Exp(Eq(string_seen, 1)); Return(unit)} else {}; Exp(Eq(int_seen, 2)); Return(unit)}} else {If(Call[Na](Array.isArray; value)) {Exp(Eq(array_seen, 3)); Return(unit)} else {}; Exp(Eq(object_seen, 4)); Return(unit)}"
    );
}

#[test]
fn mixed_array_object_function_untagged_effect_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let function_seen = Ident::create_local("function_seen");
    let block = compiler.compile_effect_block_lam(&Lambda::Lswitch(
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
    expect_dump!(
        dump::block(&compiler.j, &block),
        "If(Call[Na](Array.isArray; value)) {Exp(Eq(array_seen, 1))} else {StringSwitch(Typeof(value)) {case \"object\": {Exp(Eq(object_seen, 2))} break case \"function\": {Exp(Eq(function_seen, 3))} break }}"
    );
}

#[test]
fn untagged_literal_dispatch_keeps_ocaml_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    let rendered = print_stmts(&compiler.j, &block);
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
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    let rendered = print_stmts(&compiler.j, &block);
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
    let compiled = compiler.compile_expr_lam(&Lambda::Lswitch(
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

    let rendered = print_stmts(&compiler.j, &compiled.prelude);
    assert!(
        rendered.contains("typeof value === \"object\" && value !== null && !Array.isArray(value)"),
        "expected the small object switch to keep OCaml's object/null/array runtime guard:\n{rendered}"
    );
}

#[test]
fn complete_object_then_array_untagged_return_switches_preserve_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    let rendered = print_stmts(&compiler.j, &block);
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
    let block = {
        let a0 = &result;
        let a1 = JE::var(value, &mut compiler.j);
        let a2 = &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        );
        compiler.compile_untagged_variant_switch_assignment_statements_lam(a0, a1, a2)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "Exp(Eq(result, Cond(EqEqEq(value, undefined), 0, 1)))"
    );
}

#[test]
fn complete_single_untagged_array_return_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        );
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "Return(Cond(EqEqEq(value, undefined), 0, 1))"
    );
}

#[test]
fn complete_single_untagged_array_effect_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let empty_seen = Ident::create_local("empty_seen");
    let cons_seen = Ident::create_local("cons_seen");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &single_complete_array_block_switch(
            Lambda::Lassign(cons_seen, Box::new(Lambda::const_(Constant::int(1)))),
            Lambda::Lassign(empty_seen, Box::new(Lambda::const_(Constant::int(0)))),
        );
        compiler.compile_untagged_variant_switch_effect_statements_lam(a0, a1)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "Exp(Cond(EqEqEq(value, undefined), Eq(empty_seen, 0), Eq(cons_seen, 1)))"
    );
}

#[test]
fn default_only_untagged_boolean_assignment_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let result = Ident::create_local("result");
    let block = {
        let a0 = &result;
        let a1 = JE::var(value, &mut compiler.j);
        let a2 = &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        );
        compiler.compile_untagged_variant_switch_assignment_statements_lam(a0, a1, a2)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "Exp(Eq(result, Cond(EqEqEq(Typeof(value), \"boolean\"), 1, 0)))"
    );
}

#[test]
fn default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        );
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "Return(Cond(EqEqEq(Typeof(value), \"boolean\"), 1, 0))"
    );
}

#[test]
fn default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let block = {
        let a0 = JE::var(value, &mut compiler.j);
        let a1 = &LambdaSwitch {
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
        };
        compiler.compile_untagged_variant_switch_return_statements_lam(a0, a1)
    };

    let rendered = print_stmts(&compiler.j, &block);
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
