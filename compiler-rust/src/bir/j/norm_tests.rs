use super::{norm as n, plain as p};
use crate::bir::{Bir, NodeId, View, bridge_j};
use crate::ident::{Ident, IdentFlags};
use crate::js_ir::{BinOp, LengthObject, arena::*, build::exp as e};

fn oracle(
    make: impl FnOnce(&mut JsArena) -> Vec<Expr>,
    old: impl FnOnce(&mut JsArena, &[Expr]) -> Expr,
    new: impl FnOnce(&mut Bir, &[NodeId]) -> NodeId,
) {
    let mut a = JsArena::new();
    let args = make(&mut a);
    let statements = args.iter().map(|&x| a.stmt(StmtKind::Exp(x))).collect();
    let mut source = JsDepsProgram {
        program: JsProgram::new_in(statements, vec![], a),
        modules: vec![],
        side_effect: None,
    };
    let mut imported = bridge_j::import_js(&source).unwrap();
    let View::SBlock { statements } = imported.arena.view(imported.root) else {
        panic!()
    };
    let inputs: Vec<_> = statements
        .iter()
        .map(|&s| match imported.arena.view(s) {
            View::SExp { value } => value,
            _ => panic!(),
        })
        .collect();
    for &v in &inputs {
        imported.arena.detach(v);
    }
    imported.arena.release(imported.root);
    let value = new(&mut imported.arena, &inputs);
    let statement = p::node(&mut imported.arena, View::SExp { value }, 0);
    imported.root = p::list(&mut imported.arena, &[statement]);
    imported.arena.validate(Some(imported.root), false).unwrap();
    let actual = bridge_j::export_js(&imported).unwrap();
    let expected = old(&mut source.program.arena, &args);
    source.program.block = vec![source.program.arena.stmt(StmtKind::Exp(expected))];
    let print = |p: &JsDepsProgram| {
        crate::js_ir::print_deps_program_with_directives_and_options(
            p,
            None,
            &[],
            false,
            false,
            false,
        )
    };
    assert_eq!(print(&actual), print(&source));
}
fn var(a: &mut JsArena, name: &str) -> Expr {
    e::var(
        Ident::new(name, if name == "x" { 1 } else { 2 }, IdentFlags::NONE),
        a,
    )
}
fn atom(a: &mut JsArena, i: usize) -> Expr {
    match i {
        0 => e::bool(false, a),
        1 => e::bool(true, a),
        2 => e::int(0, a),
        3 => e::int(-1, a),
        4 => e::int(1, a),
        5 => e::string("", a),
        6 => e::string("a", a),
        7 => e::null(a),
        8 => e::undefined(false, a),
        9 => var(a, "x"),
        10 => var(a, "y"),
        11 => {
            let raw = a.raw_id(crate::js_ir::JsRawInfo {
                code: "effect()".into(),
                is_stmt: false,
            });
            a.expr(ExprKind::RawJsCode(raw))
        }
        _ => unreachable!(),
    }
}

#[test]
fn je1_append_literals_and_reassociation() {
    for i in 0..12 {
        for j in 0..12 {
            oracle(
                |a| vec![atom(a, i), atom(a, j)],
                |a, v| e::string_append(v[0], v[1], a),
                |b, v| n::je1_string_append(b, v[0], v[1]),
            );
        }
    }
    for shape in 0..3 {
        oracle(
            |a| {
                let x = var(a, "x");
                let y = var(a, "y");
                let l = e::string("a", a);
                let r = e::string("b", a);
                match shape {
                    0 => vec![
                        a.expr(ExprKind::StringAppend(x, l)),
                        a.expr(ExprKind::StringAppend(r, y)),
                    ],
                    1 => vec![l, a.expr(ExprKind::StringAppend(r, x))],
                    _ => vec![a.expr(ExprKind::StringAppend(x, l)), r],
                }
            },
            |a, v| e::string_append(v[0], v[1], a),
            |b, v| n::je1_string_append(b, v[0], v[1]),
        );
    }
}
#[test]
fn je2_length_and_je3_nullish() {
    for i in 0..12 {
        for kind in [
            LengthObject::Array,
            LengthObject::String,
            LengthObject::Function,
        ] {
            oracle(
                |a| vec![atom(a, i)],
                |a, v| e::length(v[0], kind, a),
                |b, v| n::je2_length(b, v[0], kind),
            );
        }
        oracle(
            |a| vec![atom(a, i)],
            |a, v| e::is_null_or_undefined(v[0], a),
            |b, v| n::je3_is_null_or_undefined(b, v[0]),
        );
    }
}
#[test]
fn je4_bin_literal_matrix() {
    for op in [
        BinOp::Plus,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::EqEqEq,
        BinOp::NotEqEq,
        BinOp::And,
        BinOp::Or,
    ] {
        for i in 0..12 {
            for j in 0..12 {
                oracle(
                    |a| vec![atom(a, i), atom(a, j)],
                    |a, v| e::bin(op, v[0], v[1], a),
                    |b, v| n::je4_bin(b, op, v[0], v[1]),
                );
            }
        }
    }
}
#[test]
fn je7_cond_literal_matrix() {
    for i in 0..12 {
        for j in 0..12 {
            for k in 0..12 {
                oracle(
                    |a| vec![atom(a, i), atom(a, j), atom(a, k)],
                    |a, v| e::cond(v[0], v[1], v[2], a),
                    |b, v| n::je7_cond(b, v[0], v[1], v[2]),
                );
            }
        }
    }
}
#[test]
fn je8_not_literals_and_comparisons() {
    for i in 0..12 {
        oracle(
            |a| vec![atom(a, i)],
            |a, v| e::not(v[0], a),
            |b, v| n::je8_not(b, v[0]),
        );
    }
    for op in [
        BinOp::EqEqEq,
        BinOp::NotEqEq,
        BinOp::Lt,
        BinOp::Ge,
        BinOp::Le,
        BinOp::Gt,
        BinOp::And,
        BinOp::Or,
        BinOp::Plus,
    ] {
        oracle(
            |a| {
                let x = var(a, "x");
                let t = e::bool(true, a);
                vec![e::raw_bin(op, x, t, a)]
            },
            |a, v| e::not(v[0], a),
            |b, v| n::je8_not(b, v[0]),
        );
    }
}
fn type_test(a: &mut JsArena, name: &str) -> Expr {
    let x = var(a, "x");
    let ty = a.expr(ExprKind::Typeof(x));
    let name = e::string(name, a);
    e::raw_bin(BinOp::EqEqEq, ty, name, a)
}
#[test]
fn je9_je10_type_boundaries_and_nested_logic() {
    for or in [false, true] {
        for ty in ["boolean", "string", "number", "object"] {
            for neq in [false, true] {
                for i in 0..12 {
                    for swap in [false, true] {
                        let op = if or { BinOp::Or } else { BinOp::And };
                        oracle(
                            |a| {
                                let test = type_test(a, ty);
                                let x = var(a, "x");
                                let v = atom(a, i);
                                let cmp = e::raw_bin(
                                    if neq { BinOp::NotEqEq } else { BinOp::EqEqEq },
                                    x,
                                    v,
                                    a,
                                );
                                if swap {
                                    vec![cmp, test]
                                } else {
                                    vec![test, cmp]
                                }
                            },
                            |a, v| e::bin(op, v[0], v[1], a),
                            |b, v| n::je4_bin(b, op, v[0], v[1]),
                        );
                    }
                }
            }
        }
    }
    for op in [BinOp::And, BinOp::Or] {
        for inner in [BinOp::And, BinOp::Or] {
            for i in 0..12 {
                for j in 0..12 {
                    for k in 0..3 {
                        oracle(
                            |a| {
                                let x = atom(a, i);
                                let y = atom(a, j);
                                let z = atom(a, k);
                                vec![e::raw_bin(inner, x, y, a), z]
                            },
                            |a, v| e::bin(op, v[0], v[1], a),
                            |b, v| n::je4_bin(b, op, v[0], v[1]),
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn je9_repeated_function_owns_distinct_binders() {
    oracle(
        |a| {
            let yes = e::bool(true, a);
            let yes2 = e::bool(true, a);
            let left = e::raw_bin(BinOp::And, yes, yes2, a);
            let id = Ident::new("parameter", 3, IdentFlags::NONE);
            let param = a.ident_id(id);
            let value = a.expr(ExprKind::Var(param));
            let ret = a.stmt(StmtKind::Return(value));
            let body = a.stmt_list(&[ret]);
            let params = a.ident_list(&[id]);
            let info = a.fun_id(FunInfo {
                is_method: false,
                params,
                body,
                return_unit: false,
                async_: false,
                directive: None,
            });
            vec![left, a.expr(ExprKind::Fun(info))]
        },
        |a, v| e::bin(BinOp::And, v[0], v[1], a),
        |b, v| n::je5_js_and(b, v[0], v[1]),
    );
}
#[test]
fn je9_ten_thousand_term_chain_has_bounded_attempt_work() {
    let mut b = Bir::default();
    b.begin_bulk();
    let var = b.new_var_id(crate::name::Name::new("x"), 1);
    let mut value = p::node(&mut b, View::Var { var }, 0);
    for _ in 0..10_000 {
        let right = p::node(&mut b, View::Var { var }, 0);
        value = p::bin(&mut b, BinOp::And, value, right);
    }
    let right = p::boolean(&mut b, true);
    let mut steps = 0;
    let result = n::je9_simplify_and(&mut b, value, right, &mut steps).unwrap();
    assert_eq!(result, value);
    assert_eq!(steps, 1);
    let right = p::node(&mut b, View::Var { var }, 0);
    let mut steps = 0;
    let result = n::je9_simplify_and(&mut b, value, right, &mut steps);
    println!("J-E9 10000-term chain: {steps} inspected pairs/planner steps");
    assert!(steps < 1_000_000, "{steps}");
    if result.is_none() {
        b.release(right);
    }
}
