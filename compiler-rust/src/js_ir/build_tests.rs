//! Tests for the arena smart constructors (`build.rs`), ported from the
//! tree constructor tests.

use super::{exp as JE, stmt as JS};
use crate::expect_dump;
use crate::ident::Ident;
use crate::js_ir::arena::*;
use crate::js_ir::dump;
use crate::js_ir::op::*;
use crate::js_ir::printer::print_stmts;
use crate::js_ir::CallInfo;
use crate::lambda::SwitchCaseTag;
#[test]
fn test_expression_creation() {
    let mut j = JsArena::new();
    let expr = JE::bool(true, &mut j);
    expect_dump!(dump::expr(&j, expr), "true");
}

#[test]
fn test_variable_expression() {
    let mut j = JsArena::new();
    let id = Ident::create_local("x");
    let expr = JE::var(id, &mut j);
    expect_dump!(dump::expr(&j, expr), "x");
}

#[test]
fn test_string_expression() {
    let mut j = JsArena::new();
    let expr = JE::string("hello", &mut j);
    expect_dump!(dump::expr(&j, expr), "\"hello\"");
}

#[test]
fn test_binary_expression() {
    let mut j = JsArena::new();
    let left = JE::number(Number::int(1), &mut j);
    let right = JE::number(Number::int(2), &mut j);
    let expr = JE::bin(BinOp::Plus, left, right, &mut j);

    expect_dump!(dump::expr(&j, expr), "Plus(1, 2)");
}

#[test]
fn test_string_append_folds_adjacent_same_delim_literals() {
    let mut j = JsArena::new();
    let left = JE::new(ExprKind::Str(JE::str_id("hello ", &mut j)), &mut j);
    let right = JE::new(ExprKind::Str(JE::str_id("world", &mut j)), &mut j);
    let expr = JE::string_append(left, right, &mut j);

    expect_dump!(dump::expr(&j, expr), "\"hello world\"");
}

#[test]
fn test_string_append_merges_literal_prefix_into_nested_append() {
    let mut j = JsArena::new();
    let nested = JE::string_append(
        JE::new(ExprKind::Str(JE::str_id("beta", &mut j)), &mut j),
        JE::var(Ident::create_local("tail"), &mut j),
        &mut j,
    );
    let expr = JE::string_append(
        JE::new(ExprKind::Str(JE::str_id("alpha", &mut j)), &mut j),
        nested,
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "StringAppend(\"alphabeta\", tail)");
}

#[test]
fn test_plus_with_negative_int_rhs_rewrites_to_minus() {
    let mut j = JsArena::new();
    let left = JE::var(Ident::create_local("x"), &mut j);
    let right = JE::number(Number::int(-1), &mut j);
    let expr = JE::bin(BinOp::Plus, left, right, &mut j);

    expect_dump!(dump::expr(&j, expr), "Minus(x, 1)");
}

#[test]
fn test_strict_eq_null_against_number_folds_false() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::EqEqEq,
        JE::null(&mut j),
        JE::number(Number::int(5), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "false");
}

#[test]
fn test_array_length_folds_pure_array_literals_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::length(
        JE::array(
            &[
                JE::number(Number::int(1), &mut j),
                JE::number(Number::int(2), &mut j),
                JE::number(Number::int(3), &mut j),
            ],
            MutableFlag::Immutable,
            &mut j,
        ),
        LengthObject::Array,
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "3");
}

#[test]
fn test_length_ge_zero_folds_pure_targets_to_true_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::Ge,
        JE::length(
            JE::var(Ident::create_local("xs"), &mut j),
            LengthObject::Array,
            &mut j,
        ),
        JE::number(Number::int(0), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "true");
}

#[test]
fn test_length_ge_zero_keeps_impure_targets_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::Ge,
        JE::length(
            JE::call(
                JE::var(Ident::create_local("makeArray"), &mut j),
                &[],
                CallInfo::default(),
                &mut j,
            ),
            LengthObject::Array,
            &mut j,
        ),
        JE::number(Number::int(0), &mut j),
        &mut j,
    );

    expect_dump!(
        dump::expr(&j, expr),
        "Ge(Length[Array](Call[Na](makeArray; )), 0)"
    );
}

#[test]
fn test_length_gt_zero_rewrites_to_not_eq_zero_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::Gt,
        JE::length(
            JE::var(Ident::create_local("xs"), &mut j),
            LengthObject::Array,
            &mut j,
        ),
        JE::number(Number::int(0), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "NotEqEq(Length[Array](xs), 0)");
}

#[test]
fn test_string_length_folds_plain_string_literals_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::length(JE::string("hello", &mut j), LengthObject::String, &mut j);

    expect_dump!(dump::expr(&j, expr), "5");
}

#[test]
fn test_function_length_folds_fun_arity_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::length(
        crate::lambda::js_exp_make::fun_expr(
            false,
            &[Ident::create_local("x"), Ident::create_local("y")],
            &[],
            false,
            false,
            &mut j,
        ),
        LengthObject::Function,
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "2");
}

#[test]
fn test_is_null_or_undefined_folds_numbers_false_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::is_null_or_undefined(JE::number(Number::int(3), &mut j), &mut j);

    expect_dump!(dump::expr(&j, expr), "false");
}

#[test]
fn test_is_null_or_undefined_folds_null_true_like_ocaml() {
    let mut j = JsArena::new();
    let expr = JE::is_null_or_undefined(JE::null(&mut j), &mut j);

    expect_dump!(dump::expr(&j, expr), "true");
}

#[test]
fn test_strict_eq_int_literals_folds_true() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::EqEqEq,
        JE::number(Number::int(2), &mut j),
        JE::number(Number::int(2), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "true");
}

#[test]
fn test_strict_eq_optional_blocks_compares_inner_values() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::EqEqEq,
        JE::new(
            ExprKind::OptionalBlock(JE::number(Number::int(1), &mut j), true),
            &mut j,
        ),
        JE::new(
            ExprKind::OptionalBlock(JE::number(Number::int(1), &mut j), true),
            &mut j,
        ),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "true");
}

#[test]
fn test_strict_eq_simple_string_literals_fold_false() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::EqEqEq,
        JE::string("A", &mut j),
        JE::string("B", &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "false");
}

#[test]
fn test_strict_eq_null_against_variable_is_preserved() {
    let mut j = JsArena::new();
    let expr = JE::bin(
        BinOp::EqEqEq,
        JE::null(&mut j),
        JE::var(Ident::create_local("value"), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "EqEqEq(null, value)");
}

#[test]
fn test_not_simplifies_equality_negation() {
    let mut j = JsArena::new();
    let expr = JE::not(
        JE::bin(
            BinOp::EqEqEq,
            JE::var(Ident::create_local("x"), &mut j),
            JE::null(&mut j),
            &mut j,
        ),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "NotEqEq(x, null)");
}

#[test]
fn test_not_pushes_negation_through_and() {
    let mut j = JsArena::new();
    let left = JE::bin(
        BinOp::EqEqEq,
        JE::var(Ident::create_local("x"), &mut j),
        JE::number(Number::int(1), &mut j),
        &mut j,
    );
    let right = JE::bin(
        BinOp::EqEqEq,
        JE::var(Ident::create_local("y"), &mut j),
        JE::number(Number::int(2), &mut j),
        &mut j,
    );
    let expr = JE::not(JE::bin(BinOp::And, left, right, &mut j), &mut j);

    expect_dump!(dump::expr(&j, expr), "Or(NotEqEq(x, 1), NotEqEq(y, 2))");
}

#[test]
fn test_cond_true_simplifies_to_consequent() {
    let mut j = JsArena::new();
    let expr = JE::cond(
        JE::bool(true, &mut j),
        JE::number(Number::int(1), &mut j),
        JE::number(Number::int(2), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "1");
}

#[test]
fn test_cond_negated_test_swaps_non_empty_branches() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let expr = JE::cond(
        JE::new(ExprKind::JsNot(JE::var(value, &mut j)), &mut j),
        JE::number(Number::int(1), &mut j),
        JE::number(Number::int(2), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "Cond(value, 2, 1)");
}

#[test]
fn test_statement_creation() {
    let mut j = JsArena::new();
    let stmt = JS::break_(None, &mut j);
    expect_dump!(dump::stmt(&j, stmt), "Break");
}

#[test]
fn test_literal_string_switch_simplifies_to_selected_case_body_like_ocaml() {
    let mut j = JsArena::new();
    let one = JS::return_(JE::number(Number::int(1), &mut j), &mut j);
    let three = JS::return_(JE::number(Number::int(3), &mut j), &mut j);
    let four = JS::return_(JE::number(Number::int(4), &mut j), &mut j);
    let clause = |body: &[Stmt], j: &mut JsArena| Clause {
        source_loc: None,
        body: JS::list(body, j),
        should_break: false,
        comment: None,
    };
    let clauses = vec![
        StringClauseInfo {
            tag_type: SwitchCaseTag::String("y".to_string()),
            clause: clause(&[one], &mut j),
        },
        StringClauseInfo {
            tag_type: SwitchCaseTag::String("x".to_string()),
            clause: clause(&[three], &mut j),
        },
    ];
    let default = Some(JS::list(&[four], &mut j));
    let test = JE::string("x", &mut j);
    let stmt = JS::string_switch(test, clauses, default, &mut j);

    expect_dump!(dump::stmt(&j, stmt), "Return(3)");
}

#[test]
fn test_literal_int_switch_simplifies_to_default_body_like_ocaml() {
    let mut j = JsArena::new();
    let one = JS::return_(JE::number(Number::int(1), &mut j), &mut j);
    let four = JS::return_(JE::number(Number::int(4), &mut j), &mut j);
    let clauses = vec![(
        3,
        Clause {
            source_loc: None,
            body: JS::list(&[one], &mut j),
            should_break: false,
            comment: None,
        },
    )];
    let default = Some(JS::list(&[four], &mut j));
    let test = JE::number(Number::int(9), &mut j);
    let stmt = JS::int_switch(test, clauses, default, &mut j);

    expect_dump!(dump::stmt(&j, stmt), "Return(4)");
}

#[test]
fn test_if_statement_merges_two_returns_into_a_conditional_return() {
    let mut j = JsArena::new();
    let stmt = JS::if_(
        JE::var(Ident::create_local("cond"), &mut j),
        &[JS::return_(JE::number(Number::int(1), &mut j), &mut j)],
        &[JS::return_(JE::number(Number::int(2), &mut j), &mut j)],
        &mut j,
    );

    expect_dump!(dump::stmt(&j, stmt), "Return(Cond(cond, 1, 2))");
}

#[test]
fn test_if_statement_merges_matching_assignments_into_a_conditional_assignment() {
    let mut j = JsArena::new();
    let target = Ident::create_local("result");
    let stmt = JS::if_(
        JE::var(Ident::create_local("cond"), &mut j),
        &[JS::exp(
            JE::bin(
                BinOp::Eq,
                JE::var(target, &mut j),
                JE::number(Number::int(1), &mut j),
                &mut j,
            ),
            &mut j,
        )],
        &[JS::exp(
            JE::bin(
                BinOp::Eq,
                JE::var(target, &mut j),
                JE::number(Number::int(2), &mut j),
                &mut j,
            ),
            &mut j,
        )],
        &mut j,
    );

    expect_dump!(dump::stmt(&j, stmt), "Exp(Eq(result, Cond(cond, 1, 2)))");
}

#[test]
fn test_statement_exp_drops_trivial_literals_like_ocaml() {
    let mut j = JsArena::new();
    let number_stmt = JS::exp(JE::number(Number::int(1), &mut j), &mut j);
    let undefined_stmt = JS::exp(JE::undefined(false, &mut j), &mut j);

    expect_dump!(dump::stmt(&j, number_stmt), "Block{}");
    expect_dump!(dump::stmt(&j, undefined_stmt), "Block{}");
}

#[test]
fn test_statement_exp_peels_trivial_seq_wrappers_like_ocaml() {
    let mut j = JsArena::new();
    let effect = JE::call(
        JE::var(Ident::create_local("log"), &mut j),
        &[JE::string("x", &mut j)],
        CallInfo::default(),
        &mut j,
    );

    let leading = JS::exp(
        JE::new(
            ExprKind::Seq(JE::undefined(false, &mut j), effect.clone()),
            &mut j,
        ),
        &mut j,
    );
    let trailing = JS::exp(
        JE::new(
            ExprKind::Seq(effect.clone(), JE::number(Number::int(0), &mut j)),
            &mut j,
        ),
        &mut j,
    );

    expect_dump!(dump::stmt(&j, leading), "Exp(Call[Na](log; \"x\"))");
    expect_dump!(dump::stmt(&j, trailing), "Exp(Call[Na](log; \"x\"))");
    expect_dump!(dump::stmt(&j, leading), "Exp(Call[Na](log; \"x\"))");
}

#[test]
fn test_if_statement_keeps_explicit_empty_else_block_when_pure_branch_drops_like_ocaml() {
    let mut j = JsArena::new();
    let stmt = JS::if_(
        JE::var(Ident::create_local("cond"), &mut j),
        &[JS::exp(
            JE::call(
                JE::var(Ident::create_local("log"), &mut j),
                &[JE::string("side effect", &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        )],
        &[JS::exp(JE::undefined(false, &mut j), &mut j)],
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "If(cond) {Exp(Call[Na](log; \"side effect\"))} else {Block{}}"
    );
}

#[test]
fn test_if_statement_merges_nested_then_if_with_shared_else_into_and_condition() {
    let mut j = JsArena::new();
    let outer = Ident::create_local("outer");
    let inner = Ident::create_local("inner");
    let truthy = JE::call(
        JE::var(Ident::create_local("truthy"), &mut j),
        &[],
        CallInfo::default(),
        &mut j,
    );
    let falsy = JE::call(
        JE::var(Ident::create_local("falsy"), &mut j),
        &[],
        CallInfo::default(),
        &mut j,
    );
    let stmt = JS::if_(
        JE::var(outer, &mut j),
        &[JS::new(
            StmtKind::If(
                JE::var(inner, &mut j),
                JS::list(&[JS::exp(truthy.clone(), &mut j)], &mut j),
                JS::list(&[JS::exp(falsy.clone(), &mut j)], &mut j),
            ),
            &mut j,
        )],
        &[JS::exp(falsy, &mut j)],
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Exp(Cond(And(outer, inner), Call[Na](truthy; ), Call[Na](falsy; )))"
    );
}

#[test]
fn test_if_statement_rewrites_await_return_tail() {
    let mut j = JsArena::new();
    let cond = JE::var(Ident::create_local("value"), &mut j);
    let effect = JS::exp(
        JE::new(
            ExprKind::Await(JE::call(
                JE::var(Ident::create_local("load"), &mut j),
                &[],
                CallInfo::default(),
                &mut j,
            )),
            &mut j,
        ),
        &mut j,
    );
    let then_block = vec![effect, JS::return_(JE::undefined(true, &mut j), &mut j)];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );
    // js_stmt_make.ml:262-269: a single Return else becomes an early guard.
    let mut expected = vec![JS::new(
        StmtKind::If(
            JE::not(cond, &mut j),
            JS::list(&else_block, &mut j),
            j.empty_block(),
        ),
        &mut j,
    )];
    expected.extend(then_block);
    assert_eq!(print_stmts(&j, &vec![stmt]), {
        let v = vec![JS::block(&expected, &mut j)];
        print_stmts(&j, &v)
    },);
}

#[test]
fn test_if_statement_rewrites_sync_return_undefined_tail_to_negative_guard() {
    let mut j = JsArena::new();
    let cond = JE::var(Ident::create_local("value"), &mut j);
    let effect = JS::exp(
        JE::call(
            JE::var(Ident::create_local("load"), &mut j),
            &[],
            CallInfo::default(),
            &mut j,
        ),
        &mut j,
    );
    let then_block = vec![effect, JS::return_(JE::undefined(true, &mut j), &mut j)];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(cond.clone(), &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(Not(value)) {Return(unit)} else {}; Exp(Call[Na](load; )); Return(unit)}"
    );
}

#[test]
fn test_if_statement_rewrites_literal_dispatch_return_tail() {
    let mut j = JsArena::new();
    let key = Ident::create_local("key");
    let active = Ident::create_local("active");
    let dispatch = JE::raw_bin(
        BinOp::Or,
        JE::bin(
            BinOp::EqEqEq,
            JE::var(key, &mut j),
            JE::string("space", &mut j),
            &mut j,
        ),
        JE::bin(
            BinOp::EqEqEq,
            JE::var(key, &mut j),
            JE::string("a", &mut j),
            &mut j,
        ),
        &mut j,
    );
    let inner_cond = JE::bin(
        BinOp::EqEqEq,
        JE::var(key, &mut j),
        JE::string("space", &mut j),
        &mut j,
    );
    let then_block = vec![JS::new(
        StmtKind::If(
            inner_cond.clone(),
            JS::list(
                &[JS::new(
                    StmtKind::If(
                        JE::var(active, &mut j),
                        JS::list(
                            &[
                                JS::exp(
                                    JE::call(
                                        JE::var(Ident::create_local("seen"), &mut j),
                                        &[],
                                        CallInfo::default(),
                                        &mut j,
                                    ),
                                    &mut j,
                                ),
                                JS::return_(JE::undefined(true, &mut j), &mut j),
                            ],
                            &mut j,
                        ),
                        JS::list(&[JS::return_(JE::undefined(true, &mut j), &mut j)], &mut j),
                    ),
                    &mut j,
                )],
                &mut j,
            ),
            j.empty_block(),
        ),
        &mut j,
    )];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        dispatch.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );
    // js_stmt_make.ml:262-269: a single Return else becomes an early guard.
    let mut expected = vec![JS::new(
        StmtKind::If(
            JE::not(dispatch, &mut j),
            JS::list(&else_block, &mut j),
            j.empty_block(),
        ),
        &mut j,
    )];
    expected.extend(then_block);
    assert_eq!(print_stmts(&j, &vec![stmt]), {
        let v = vec![JS::block(&expected, &mut j)];
        print_stmts(&j, &v)
    },);
}

#[test]
fn test_if_statement_rewrites_block_wrapped_literal_dispatch_return_tail() {
    let mut j = JsArena::new();
    let key = Ident::create_local("key");
    let active = Ident::create_local("active");
    let dispatch = JE::raw_bin(
        BinOp::Or,
        JE::bin(
            BinOp::EqEqEq,
            JE::var(key, &mut j),
            JE::string("space", &mut j),
            &mut j,
        ),
        JE::bin(
            BinOp::EqEqEq,
            JE::var(key, &mut j),
            JE::string("a", &mut j),
            &mut j,
        ),
        &mut j,
    );
    let inner_cond = JE::bin(
        BinOp::EqEqEq,
        JE::var(key, &mut j),
        JE::string("space", &mut j),
        &mut j,
    );
    let active_guard = JS::new(
        StmtKind::If(
            JE::var(active, &mut j),
            JS::list(
                &[
                    JS::exp(
                        JE::call(
                            JE::var(Ident::create_local("seen"), &mut j),
                            &[],
                            CallInfo::default(),
                            &mut j,
                        ),
                        &mut j,
                    ),
                    JS::return_(JE::undefined(true, &mut j), &mut j),
                ],
                &mut j,
            ),
            JS::list(
                &[JS::new(
                    StmtKind::Block(JS::list(
                        &[JS::return_(JE::undefined(true, &mut j), &mut j)],
                        &mut j,
                    )),
                    &mut j,
                )],
                &mut j,
            ),
        ),
        &mut j,
    );
    let then_block = vec![JS::new(
        StmtKind::Block(JS::list(
            &[JS::new(
                StmtKind::If(
                    inner_cond.clone(),
                    JS::list(
                        &[JS::new(
                            StmtKind::Block(JS::list(&[active_guard], &mut j)),
                            &mut j,
                        )],
                        &mut j,
                    ),
                    j.empty_block(),
                ),
                &mut j,
            )],
            &mut j,
        )),
        &mut j,
    )];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        dispatch.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );
    // js_stmt_make.ml:262-269: a single Return else becomes an early guard.
    let mut expected = vec![JS::new(
        StmtKind::If(
            JE::not(dispatch, &mut j),
            JS::list(&else_block, &mut j),
            j.empty_block(),
        ),
        &mut j,
    )];
    expected.extend(then_block);
    assert_eq!(print_stmts(&j, &vec![stmt]), {
        let v = vec![JS::block(&expected, &mut j)];
        print_stmts(&j, &v)
    },);
}

#[test]
fn test_if_statement_keeps_positive_strict_null_success_return_branch() {
    let mut j = JsArena::new();
    let elem = Ident::create_local("elem");
    let cond = JE::bin(
        BinOp::NotEqEq,
        JE::var(elem, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(elem, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(JE::number(Number::int(2), &mut j), &mut j),
    ];
    let else_block = vec![JS::return_(JE::number(Number::int(1), &mut j), &mut j)];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(EqEqEq(elem, null)) {Return(1)} else {}; Exp(Call[Na](seen; elem)); Return(2)}"
    );
}

#[test]
fn test_if_statement_rewrites_loose_nullish_else_to_fallthrough() {
    let mut j = JsArena::new();
    let elem = Ident::create_local("elem");
    let cond = JE::is_null_or_undefined(JE::var(elem, &mut j), &mut j);
    let then_block = vec![JS::return_(JE::number(Number::int(1), &mut j), &mut j)];
    let else_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(elem, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(JE::number(Number::int(2), &mut j), &mut j),
    ];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );
    // js_stmt_make.ml:270-274: terminal then arm precedes the else body.
    let mut expected = vec![JS::new(
        StmtKind::If(cond, JS::list(&then_block, &mut j), j.empty_block()),
        &mut j,
    )];
    expected.extend(else_block);
    assert_eq!(print_stmts(&j, &vec![stmt]), {
        let v = vec![JS::block(&expected, &mut j)];
        print_stmts(&j, &v)
    },);
}

#[test]
fn test_if_statement_rewrites_loose_nullish_conditional_unit_success_tail_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let flag = Ident::create_local("flag");
    let cond = JE::is_null_or_undefined(JE::var(value, &mut j), &mut j);
    let unit_effect = JE::new(
        ExprKind::Seq(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(value, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            JE::undefined(true, &mut j),
        ),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("setup"), &mut j),
                &[],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(
            JE::cond(
                JE::var(flag, &mut j),
                unit_effect,
                JE::undefined(true, &mut j),
                &mut j,
            ),
            &mut j,
        ),
    ];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(Not(IsNullOrUndefined(value))) {Return(unit)} else {}; Exp(Call[Na](setup; )); Return(Cond(flag, Seq(Call[Na](seen; value), unit), unit))}"
    );
}

#[test]
fn test_if_statement_keeps_positive_strict_undefined_unit_success_tail() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let cond = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(true, &mut j),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(value, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(JE::undefined(true, &mut j), &mut j),
    ];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(EqEqEq(value, unit)) {Return(unit)} else {}; Exp(Call[Na](seen; value)); Return(unit)}"
    );
}

#[test]
fn test_if_statement_rewrites_strict_null_unit_success_tail_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let cond = JE::bin(
        BinOp::EqEqEq,
        JE::var(value, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(value, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(JE::undefined(true, &mut j), &mut j),
    ];
    let else_block = vec![JS::return_(JE::undefined(true, &mut j), &mut j)];

    let stmt = JS::if_(
        cond.clone(),
        &then_block.clone(),
        &else_block.clone(),
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(NotEqEq(value, null)) {Return(unit)} else {}; Exp(Call[Na](seen; value)); Return(unit)}"
    );
}

#[test]
fn test_if_statement_rewrites_nullish_guard_when_fallback_returns_guarded_value() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let cond = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::call(
                JE::var(Ident::create_local("seen"), &mut j),
                &[JE::var(value, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        JS::return_(JE::number(Number::int(2), &mut j), &mut j),
    ];
    let else_block = vec![JS::return_(JE::var(value, &mut j), &mut j)];

    let stmt = JS::if_(cond.clone(), &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(EqEqEq(value, undefined)) {Return(value)} else {}; Exp(Call[Na](seen; value)); Return(2)}"
    );
}

#[test]
fn test_if_statement_rewrites_strict_undefined_bound_success_tail_like_pattern_match_json() {
    let mut j = JsArena::new();
    let match_id = Ident::create_local("match");
    let tmp = Ident::create_local("tmp");
    let cond = JE::bin(
        BinOp::NotEqEq,
        JE::var(match_id, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    let then_block = vec![
        JS::variable(
            VarDecl {
                ident: tmp,
                value: Some(JE::var(match_id, &mut j)),
                property: crate::lambda::LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut j,
        ),
        JS::if_(
            JE::bin(
                BinOp::EqEqEq,
                JE::var(tmp, &mut j),
                JE::null(&mut j),
                &mut j,
            ),
            &[JS::return_(JE::string("yes", &mut j), &mut j)],
            &[],
            &mut j,
        ),
        JS::return_(JE::string("no", &mut j), &mut j),
    ];
    let else_block = vec![JS::return_(JE::string("no", &mut j), &mut j)];

    let stmt = JS::if_(cond, &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(EqEqEq(match, undefined)) {Return(\"no\")} else {}; let[Strict] tmp = match; If(EqEqEq(tmp, null)) {Return(\"yes\")} else {}; Return(\"no\")}"
    );
}

#[test]
fn test_if_statement_rewrites_strict_undefined_continue_success_tail_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let next_value = Ident::create_local("nextValue");
    let cond = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    let then_block = vec![
        JS::exp(
            JE::bin(
                BinOp::Eq,
                JE::var(next_value, &mut j),
                JE::var(value, &mut j),
                &mut j,
            ),
            &mut j,
        ),
        JS::continue_(None, &mut j),
    ];
    let else_block = vec![JS::return_(JE::number(Number::int(1), &mut j), &mut j)];

    let stmt = JS::if_(cond, &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(EqEqEq(value, undefined)) {Return(1)} else {}; Exp(Eq(nextValue, value)); Continue}"
    );
}

#[test]
fn test_if_statement_merges_nested_else_if_with_shared_then_into_or_condition() {
    let mut j = JsArena::new();
    let outer = Ident::create_local("outer");
    let inner = Ident::create_local("inner");
    let truthy = JE::call(
        JE::var(Ident::create_local("truthy"), &mut j),
        &[],
        CallInfo::default(),
        &mut j,
    );
    let falsy = JE::call(
        JE::var(Ident::create_local("falsy"), &mut j),
        &[],
        CallInfo::default(),
        &mut j,
    );
    let stmt = JS::if_(
        JE::var(outer, &mut j),
        &[JS::exp(truthy.clone(), &mut j)],
        &[JS::new(
            StmtKind::If(
                JE::var(inner, &mut j),
                JS::list(&[JS::exp(truthy, &mut j)], &mut j),
                JS::list(&[JS::exp(falsy.clone(), &mut j)], &mut j),
            ),
            &mut j,
        )],
        &mut j,
    );

    expect_dump!(
        dump::stmt(&j, stmt),
        "Exp(Cond(Or(outer, inner), Call[Na](truthy; ), Call[Na](falsy; )))"
    );
}

#[test]
fn test_if_statement_does_not_unwrap_single_block_wrapped_else_if_for_or_merge() {
    let mut j = JsArena::new();
    let outer = Ident::create_local("outer");
    let inner = Ident::create_local("inner");
    let then_block = vec![JS::return_(JE::number(Number::int(1), &mut j), &mut j)];
    let else_block = vec![JS::new(
        StmtKind::Block(JS::list(
            &[JS::new(
                StmtKind::If(
                    JE::var(inner, &mut j),
                    JS::list(&then_block.clone(), &mut j),
                    JS::list(
                        &[JS::return_(JE::number(Number::int(0), &mut j), &mut j)],
                        &mut j,
                    ),
                ),
                &mut j,
            )],
            &mut j,
        )),
        &mut j,
    )];

    let stmt = JS::if_(JE::var(outer, &mut j), &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "Block{If(outer) {Return(1)} else {}; Block{If(inner) {Return(1)} else {Return(0)}}}"
    );
}

#[test]
fn test_if_statement_does_not_treat_wrapped_return_block_as_terminal() {
    let mut j = JsArena::new();
    let cond = JE::var(Ident::create_local("cond"), &mut j);
    let then_block = vec![JS::new(
        StmtKind::Block(JS::list(
            &[JS::return_(JE::number(Number::int(1), &mut j), &mut j)],
            &mut j,
        )),
        &mut j,
    )];
    let else_block = vec![JS::exp(JE::number(Number::int(2), &mut j), &mut j)];

    let stmt = JS::if_(cond, &then_block, &else_block, &mut j);

    expect_dump!(
        dump::stmt(&j, stmt),
        "If(cond) {Block{Return(1)}} else {Block{}}"
    );
}

#[test]
fn test_js_and_simplifies_boolean_typeof_nullish_guards_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let typeof_boolean = JE::bin(
        BinOp::EqEqEq,
        JE::new(ExprKind::Typeof(JE::var(value, &mut j)), &mut j),
        JE::string("boolean", &mut j),
        &mut j,
    );

    let equals_null = JE::bin(
        BinOp::EqEqEq,
        JE::var(value, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let not_equals_null = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let equals_undefined = JE::bin(
        BinOp::EqEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    let not_equals_undefined = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );

    expect_dump!(
        {
            let v = JE::js_and(typeof_boolean.clone(), equals_null, &mut j);
            dump::expr(&j, v)
        },
        "false"
    );
    expect_dump!(
        {
            let v = JE::js_and(typeof_boolean.clone(), not_equals_null, &mut j);
            dump::expr(&j, v)
        },
        "EqEqEq(Typeof(value), \"boolean\")"
    );
    expect_dump!(
        {
            let v = JE::js_and(typeof_boolean.clone(), equals_undefined, &mut j);
            dump::expr(&j, v)
        },
        "false"
    );
    expect_dump!(
        {
            let v = JE::js_and(typeof_boolean, not_equals_undefined, &mut j);
            dump::expr(&j, v)
        },
        "EqEqEq(Typeof(value), \"boolean\")"
    );
}

#[test]
fn test_js_and_simplifies_static_array_is_array_nullish_guards_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let array_is_array = JE::call(
        JE::new(
            ExprKind::StaticIndex(
                JE::var(Ident::create_persistent("Array"), &mut j),
                JE::str_id("isArray", &mut j),
                crate::js_ir::arena::FieldPos::new(None),
            ),
            &mut j,
        ),
        &[JE::var(value, &mut j)],
        CallInfo::default(),
        &mut j,
    );
    let equals_null = JE::bin(
        BinOp::EqEqEq,
        JE::var(value, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let not_equals_null = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::null(&mut j),
        &mut j,
    );
    let equals_undefined = JE::bin(
        BinOp::EqEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    let not_equals_undefined = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );

    expect_dump!(
        {
            let v = JE::js_and(array_is_array.clone(), equals_null, &mut j);
            dump::expr(&j, v)
        },
        "false"
    );
    expect_dump!(
        {
            let v = JE::js_and(array_is_array.clone(), not_equals_null, &mut j);
            dump::expr(&j, v)
        },
        "Call[Na](Array.isArray; value)"
    );
    expect_dump!(
        {
            let v = JE::js_and(array_is_array.clone(), equals_undefined, &mut j);
            dump::expr(&j, v)
        },
        "false"
    );
    expect_dump!(
        {
            let v = JE::js_and(array_is_array, not_equals_undefined, &mut j);
            dump::expr(&j, v)
        },
        "Call[Na](Array.isArray; value)"
    );
}

#[test]
fn test_js_and_keeps_duplicate_effectful_calls_like_ocaml() {
    let mut j = JsArena::new();
    let call = JE::call(
        JE::var(Ident::create_persistent("equal"), &mut j),
        &[JE::number(Number::int(1), &mut j)],
        CallInfo::default(),
        &mut j,
    );

    expect_dump!(
        {
            let v = JE::js_and(call.clone(), call, &mut j);
            dump::expr(&j, v)
        },
        "And(Call[Na](equal; 1), Call[Na](equal; 1))"
    );
}

#[test]
fn test_js_or_keeps_duplicate_effectful_calls_like_ocaml() {
    let mut j = JsArena::new();
    let call = JE::call(
        JE::var(Ident::create_persistent("equal"), &mut j),
        &[JE::number(Number::int(1), &mut j)],
        CallInfo::default(),
        &mut j,
    );

    expect_dump!(
        {
            let v = JE::js_or(call.clone(), call, &mut j);
            dump::expr(&j, v)
        },
        "Or(Call[Na](equal; 1), Call[Na](equal; 1))"
    );
}

#[test]
fn test_cond_keeps_duplicate_effectful_calls_instead_of_collapsing_to_and() {
    let mut j = JsArena::new();
    let call = JE::call(
        JE::var(Ident::create_persistent("equal"), &mut j),
        &[JE::number(Number::int(1), &mut j)],
        CallInfo::default(),
        &mut j,
    );

    expect_dump!(
        {
            let v = JE::cond(call.clone(), call, JE::bool(false, &mut j), &mut j);
            dump::expr(&j, v)
        },
        "Cond(Call[Na](equal; 1), Call[Na](equal; 1), false)"
    );
}

#[test]
fn test_js_and_simplifies_object_guard_with_static_array_exclusion_like_ocaml() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let object_guard = JE::bin(
        BinOp::And,
        JE::bin(
            BinOp::And,
            JE::bin(
                BinOp::EqEqEq,
                JE::new(ExprKind::Typeof(JE::var(value, &mut j)), &mut j),
                JE::string("object", &mut j),
                &mut j,
            ),
            JE::bin(
                BinOp::NotEqEq,
                JE::var(value, &mut j),
                JE::null(&mut j),
                &mut j,
            ),
            &mut j,
        ),
        JE::not(
            JE::call(
                JE::new(
                    ExprKind::StaticIndex(
                        JE::var(Ident::create_persistent("Array"), &mut j),
                        JE::str_id("isArray", &mut j),
                        crate::js_ir::arena::FieldPos::new(None),
                    ),
                    &mut j,
                ),
                &[JE::var(value, &mut j)],
                CallInfo::default(),
                &mut j,
            ),
            &mut j,
        ),
        &mut j,
    );
    let not_equals_undefined = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );

    let simplified = JE::js_and(not_equals_undefined, object_guard.clone(), &mut j);
    let needle = JE::bin(
        BinOp::NotEqEq,
        JE::var(value, &mut j),
        JE::undefined(false, &mut j),
        &mut j,
    );
    assert!(
        !JE::conjunction_contains_expression(&j, simplified, needle),
        "expected the redundant undefined guard to disappear, got {}",
        dump::expr(&j, simplified)
    );
}

#[test]
fn test_js_and_simplifies_or_literal_membership_against_same_literal_like_ocaml() {
    let mut j = JsArena::new();
    let key = Ident::create_local("key");
    let space = JE::bin(
        BinOp::EqEqEq,
        JE::var(key, &mut j),
        JE::string("space", &mut j),
        &mut j,
    );
    let letter_a = JE::bin(
        BinOp::EqEqEq,
        JE::var(key, &mut j),
        JE::string("a", &mut j),
        &mut j,
    );

    let simplified = JE::js_and(
        JE::bin(BinOp::Or, space.clone(), letter_a, &mut j),
        space.clone(),
        &mut j,
    );

    expect_dump!(dump::expr(&j, simplified), "EqEqEq(key, \"space\")");
}

#[test]
fn test_js_or_absorbs_large_conjunction_membership_against_same_literal_like_ocaml() {
    let mut j = JsArena::new();
    let key = Ident::create_local("key");
    let literal = |txt: &str, j: &mut JsArena| {
        let var = JE::var(key, j);
        let txt = JE::string(txt, j);
        JE::bin(BinOp::EqEqEq, var, txt, j)
    };
    let space = literal("space", &mut j);
    let mut rest = None;
    for txt in [
        "q", "p", "o", "n", "m", "l", "k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a",
    ] {
        let expr = literal(txt, &mut j);
        rest = Some(match rest {
            None => expr,
            Some(acc) => JE::raw_bin(BinOp::Or, acc, expr, &mut j),
        });
    }
    let rest = rest.expect("expected a non-empty literal chain");

    let simplified = JE::bin(
        BinOp::Or,
        space.clone(),
        JE::raw_bin(BinOp::And, rest, space, &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, simplified), "EqEqEq(key, \"space\")");
}

#[test]
fn test_cond_merges_nested_alternate_to_drop_impossible_boolean_null_checks() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let typeof_boolean = JE::bin(
        BinOp::EqEqEq,
        JE::new(ExprKind::Typeof(JE::var(value, &mut j)), &mut j),
        JE::string("boolean", &mut j),
        &mut j,
    );
    let nested = JE::cond(
        JE::bin(
            BinOp::EqEqEq,
            JE::var(value, &mut j),
            JE::null(&mut j),
            &mut j,
        ),
        JE::number(Number::int(3), &mut j),
        JE::number(Number::int(4), &mut j),
        &mut j,
    );

    let merged = JE::cond(
        typeof_boolean,
        nested,
        JE::number(Number::int(4), &mut j),
        &mut j,
    );
    expect_dump!(dump::expr(&j, merged), "4");
}

#[test]
fn test_cond_merges_nested_alternate_to_keep_only_boolean_typeof_guard() {
    let mut j = JsArena::new();
    let value = Ident::create_local("value");
    let typeof_boolean = JE::bin(
        BinOp::EqEqEq,
        JE::new(ExprKind::Typeof(JE::var(value, &mut j)), &mut j),
        JE::string("boolean", &mut j),
        &mut j,
    );
    let nested = JE::cond(
        JE::bin(
            BinOp::NotEqEq,
            JE::var(value, &mut j),
            JE::null(&mut j),
            &mut j,
        ),
        JE::number(Number::int(3), &mut j),
        JE::number(Number::int(4), &mut j),
        &mut j,
    );

    let merged = JE::cond(
        typeof_boolean,
        nested,
        JE::number(Number::int(4), &mut j),
        &mut j,
    );
    expect_dump!(
        dump::expr(&j, merged),
        "Cond(EqEqEq(Typeof(value), \"boolean\"), 3, 4)"
    );
}

#[test]
fn test_bin_folds_relational_int_comparisons_like_ocaml() {
    let mut j = JsArena::new();
    let gt = JE::bin(
        BinOp::Gt,
        JE::number(Number::int(-299), &mut j),
        JE::number(Number::int(99), &mut j),
        &mut j,
    );
    let lt = JE::bin(
        BinOp::Lt,
        JE::number(Number::int(-311), &mut j),
        JE::number(Number::int(85), &mut j),
        &mut j,
    );
    let ge = JE::bin(
        BinOp::Ge,
        JE::number(Number::int(304), &mut j),
        JE::number(Number::int(1), &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, gt), "true");
    expect_dump!(dump::expr(&j, lt), "false");
    expect_dump!(dump::expr(&j, ge), "true");
}

#[test]
fn test_cond_folds_after_relational_int_comparison_like_gpr_3877() {
    let mut j = JsArena::new();
    let expr = JE::cond(
        JE::bin(
            BinOp::Gt,
            JE::number(Number::int(-299), &mut j),
            JE::number(Number::int(99), &mut j),
            &mut j,
        ),
        JE::string("then branch", &mut j),
        JE::string("else branch", &mut j),
        &mut j,
    );

    expect_dump!(dump::expr(&j, expr), "\"then branch\"");
}
