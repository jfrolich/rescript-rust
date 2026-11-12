use super::{equal, facts};
use crate::bir::{Bir, Constant, NodeFlags, View, bridge_j};
use crate::js_ir::{BinOp, arena::*, build};
use crate::lambda::js_exp_make;

fn check(a: JsArena, expressions: &[Expr]) {
    let mut a = a;
    let block = expressions
        .iter()
        .map(|&e| a.stmt(StmtKind::Exp(e)))
        .collect();
    let p = JsDepsProgram {
        program: JsProgram::new_in(block, vec![], a),
        modules: vec![],
        side_effect: None,
    };
    let imported = bridge_j::import_js(&p).unwrap();
    let View::SBlock { statements } = imported.arena.view(imported.root) else {
        panic!()
    };
    let values: Vec<_> = statements
        .iter()
        .map(|&s| match imported.arena.view(s) {
            View::SExp { value } => value,
            _ => panic!(),
        })
        .collect();
    let exported = bridge_j::export_js(&imported).unwrap();
    let a = &exported.program.arena;
    let expressions: Vec<_> = exported
        .program
        .block
        .iter()
        .map(|&s| match a.sk(s) {
            StmtKind::Exp(e) => e,
            _ => panic!(),
        })
        .collect();
    for (i, &v) in values.iter().enumerate() {
        assert_eq!(
            imported.arena.node(v).flags().contains(NodeFlags::PURE),
            build::expression_has_no_side_effects(a, expressions[i])
        );
        assert_eq!(
            facts::strictly_pure(&imported.arena, v),
            js_exp_make::js_expr_no_side_effects(a, expressions[i])
        );
        for (k, &w) in values.iter().enumerate() {
            assert_eq!(
                equal::equal(&imported.arena, v, w, &mut 0),
                build::ocaml_eq_expression(a, expressions[i], expressions[k]),
                "pair {i}, {k}"
            );
        }
    }
    imported.arena.validate(Some(imported.root), false).unwrap();
}

#[test]
fn numeric_throw_boundaries_match_exported_oracles() {
    use crate::js_ir::Number;
    for op in [BinOp::Eq, BinOp::Plus, BinOp::Pow, BinOp::Div, BinOp::Mod] {
        for number in [
            Number::int(0),
            Number::int(1),
            Number::int(-1),
            Number::float("0."),
            Number::float("-1."),
            Number::bigint(true, "0"),
            Number::bigint(true, "1"),
            Number::bigint(false, "1"),
        ] {
            for effect in [false, true] {
                let mut a = JsArena::new();
                let lhs = if effect {
                    let raw = a.raw_id(crate::js_ir::JsRawInfo {
                        code: "effect()".into(),
                        is_stmt: false,
                    });
                    a.expr(ExprKind::RawJsCode(raw))
                } else {
                    a.expr(ExprKind::Bool(true))
                };
                let n = a.number_id(number.clone());
                let rhs = a.expr(ExprKind::Number(n));
                let root = a.expr(ExprKind::Bin(op, lhs, rhs));
                check(a, &[root]);
            }
        }
    }
}

#[test]
fn partial_equality_distinguishes_values_and_unsupported_kinds() {
    let mut a = JsArena::new();
    let mut expressions = vec![];
    for i in [-1, 0, 1, 1] {
        let n = a.number_id(crate::js_ir::Number::int(i));
        expressions.push(a.expr(ExprKind::Number(n)));
    }
    for s in ["a", "b", "a"] {
        let s = a.str(s);
        expressions.push(a.expr(ExprKind::Str(s)));
    }
    for value in [true, false, true] {
        expressions.push(a.expr(ExprKind::Bool(value)));
    }
    expressions.push(a.expr(ExprKind::Null));
    expressions.push(a.expr(ExprKind::Undefined { is_unit: true }));
    expressions.push(a.expr(ExprKind::Undefined { is_unit: false }));
    for _ in 0..2 {
        let n = a.number_id(crate::js_ir::Number::float("1."));
        expressions.push(a.expr(ExprKind::Number(n)));
    }
    check(a, &expressions);
}

#[test]
fn equality_ten_thousand_deep_is_iterative_and_counts_pairs() {
    let mut b = Bir::default();
    b.begin_bulk();
    let n = b.intern_const(Constant::Int(1));
    let mut left = b.new_node(View::JNumber { value: n }, 0);
    let mut right = b.new_node(View::JNumber { value: n }, 0);
    for _ in 0..10_000 {
        left = b.new_node(View::JOptional { value: left }, 0);
        right = b.new_node(View::JOptional { value: right }, 0);
    }
    let mut steps = 0;
    assert!(equal::equal(&b, left, right, &mut steps));
    assert_eq!(steps, 10_001);
}

#[test]
fn replacing_divisor_repairs_strict_ancestors() {
    let mut b = Bir::default();
    let one = b.intern_const(Constant::Int(1));
    let zero = b.intern_const(Constant::Int(0));
    let lhs = b.new_node(View::JNumber { value: one }, 0);
    let rhs = b.new_node(View::JNumber { value: one }, 0);
    let div = b.new_node(
        View::JBin {
            left: lhs,
            right: rhs,
        },
        BinOp::Div as u16,
    );
    let root = b.new_node(View::JNot { value: div }, 0);
    assert!(facts::strictly_pure(&b, root));
    let new = b.new_node(View::JNumber { value: zero }, 0);
    b.replace_local(rhs, new);
    assert!(!facts::strictly_pure(&b, root));
    b.validate(Some(root), false).unwrap();
}
