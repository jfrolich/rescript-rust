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
    assert!(steps <= 8192, "{steps}");
    if result.is_none() {
        b.release(right);
    }
}

fn stmt_oracle(
    make: impl FnOnce(&mut JsArena) -> Stmt,
    old: impl FnOnce(&mut JsArena, Stmt) -> Stmt,
    new: impl FnOnce(&mut Bir, NodeId) -> NodeId,
) {
    let mut a = JsArena::new();
    let input = make(&mut a);
    let mut source = JsDepsProgram {
        program: JsProgram::new_in(vec![input], vec![], a),
        modules: vec![],
        side_effect: None,
    };
    let mut imported = bridge_j::import_js(&source).unwrap();
    let View::SBlock { statements } = imported.arena.view(imported.root) else {
        panic!()
    };
    let input_b = statements[0];
    imported.arena.detach(input_b);
    imported.arena.release(imported.root);
    let output = new(&mut imported.arena, input_b);
    imported.root = p::list(&mut imported.arena, &[output]);
    imported.arena.validate(Some(imported.root), false).unwrap();
    let actual = bridge_j::export_js(&imported).unwrap();
    let expected = old(&mut source.program.arena, input);
    source.program.block = vec![expected];
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
#[test]
fn js1_statement_and_comma_boundaries() {
    for i in 0..12 {
        for j in 0..12 {
            stmt_oracle(
                |a| {
                    let l = atom(a, i);
                    let r = atom(a, j);
                    let value = e::seq(l, r, a);
                    a.stmt(StmtKind::Exp(value))
                },
                |a, s| {
                    let StmtKind::Exp(v) = a.sk(s) else { panic!() };
                    crate::js_ir::build::stmt::exp(v, a)
                },
                |b, s| {
                    let View::SExp { value } = b.view(s) else {
                        panic!()
                    };
                    p::retain(b, &[s], &[value]);
                    n::js1_exp(b, value)
                },
            );
        }
    }
}
#[test]
fn js2_js5_singleton_and_wide_blocks() {
    for depth in 0..4 {
        for width in 0..4 {
            for unnest in [false, true] {
                stmt_oracle(
                    |a| {
                        let mut ss = vec![];
                        for _ in 0..width {
                            ss.push(a.stmt(StmtKind::Debugger));
                        }
                        for _ in 0..depth {
                            let list = a.stmt_list(&ss);
                            ss = vec![a.stmt(StmtKind::Block(list))];
                        }
                        let list = a.stmt_list(&ss);
                        a.stmt(StmtKind::Block(list))
                    },
                    |a, s| {
                        let StmtKind::Block(list) = a.sk(s) else {
                            panic!()
                        };
                        let ss = a.stmts(list).to_vec();
                        if unnest {
                            let ss = crate::js_ir::build::stmt::unnest_block(ss, a);
                            let list = a.stmt_list(&ss);
                            a.stmt(StmtKind::Block(list))
                        } else {
                            crate::js_ir::build::stmt::block(&ss, a)
                        }
                    },
                    |b, s| {
                        let View::SBlock { statements } = b.view(s) else {
                            panic!()
                        };
                        let ss = statements.to_vec();
                        p::retain(b, &[s], &ss);
                        if unnest {
                            let ss = n::js5_unnest_block(b, ss);
                            p::node(b, View::SBlock { statements: &ss }, 1)
                        } else {
                            n::js2_block(b, ss)
                        }
                    },
                );
            }
        }
    }
}
fn branch(a: &mut JsArena, kind: usize) -> Vec<Stmt> {
    match kind {
        0 => vec![],
        1 | 2 => {
            let value = e::int(kind as i32, a);
            vec![a.stmt(StmtKind::Return(value))]
        }
        3 => {
            let value = var(a, "x");
            vec![a.stmt(StmtKind::Exp(value))]
        }
        4 => {
            let value = var(a, "y");
            vec![a.stmt(StmtKind::Throw(value))]
        }
        5 => vec![a.stmt(StmtKind::Break(None))],
        6 => vec![a.stmt(StmtKind::Continue(None))],
        7..=9 => {
            let left = var(a, if kind == 9 { "y" } else { "x" });
            let right = e::int(kind as i32, a);
            let value = e::raw_bin(BinOp::Eq, left, right, a);
            vec![a.stmt(StmtKind::Exp(value))]
        }
        10 => {
            let empty = a.stmt_list(&[]);
            vec![a.stmt(StmtKind::Block(empty))]
        }
        11 => vec![a.stmt(StmtKind::Debugger)],
        _ => panic!(),
    }
}
#[test]
fn js3_ordered_branch_matrix() {
    for test in 0..12 {
        for yes in 0..12 {
            for no in 0..12 {
                stmt_oracle(
                    |a| {
                        let c = atom(a, test);
                        let y = branch(a, yes);
                        let z = branch(a, no);
                        let y = a.stmt_list(&y);
                        let z = a.stmt_list(&z);
                        a.stmt(StmtKind::If(c, y, z))
                    },
                    |a, s| {
                        let StmtKind::If(c, y, z) = a.sk(s) else {
                            panic!()
                        };
                        let (y, z) = (a.stmts(y).to_vec(), a.stmts(z).to_vec());
                        crate::js_ir::build::stmt::if_(c, &y, &z, a)
                    },
                    |b, s| {
                        let View::SIf {
                            condition,
                            then_,
                            else_: Some(no),
                        } = b.view(s)
                        else {
                            panic!()
                        };
                        let View::SBlock { statements: ys } = b.view(then_) else {
                            panic!()
                        };
                        let ys = ys.to_vec();
                        let View::SBlock { statements: ns } = b.view(no) else {
                            panic!()
                        };
                        let ns = ns.to_vec();
                        let mut keep = vec![condition];
                        keep.extend_from_slice(&ys);
                        keep.extend_from_slice(&ns);
                        p::retain(b, &[s], &keep);
                        n::js3_simplify_if(b, condition, ys, ns)
                    },
                );
            }
        }
    }
}
#[test]
fn js4_literal_integer_switch_match_and_default() {
    for value in [0, 1, 2] {
        stmt_oracle(
            |a| {
                let c = e::int(value, a);
                let one = e::int(10, a);
                let two = e::int(20, a);
                let ret = a.stmt(StmtKind::Return(one));
                let alt = a.stmt(StmtKind::Return(two));
                let body = a.stmt_list(&[ret]);
                let default = a.stmt_list(&[alt]);
                let info = a.int_switch_id(IntSwitchInfo {
                    clauses: vec![(
                        1,
                        Clause {
                            body,
                            should_break: false,
                            comment: None,
                            source_loc: None,
                        },
                    )],
                    default: Some(default),
                });
                a.stmt(StmtKind::IntSwitch(c, info))
            },
            |a, s| crate::js_ir::build::stmt::new(a.sk(s), a),
            n::js4_normalize,
        );
    }
}

#[test]
fn jm1_sequences_all_literal_boundaries() {
    for i in 0..12 {
        for j in 0..12 {
            oracle(
                |a| vec![atom(a, i), atom(a, j)],
                |a, v| crate::lambda::js_exp_make::js_seq(v[0], v[1], a),
                |b, v| n::jm1_js_seq(b, v[0], v[1]),
            );
        }
    }
}
#[test]
fn jm2_nullish_and_integer_equality() {
    for i in 0..12 {
        for j in 0..12 {
            for neq in [false, true] {
                oracle(
                    |a| vec![atom(a, i), atom(a, j)],
                    |a, v| {
                        crate::lambda::js_exp_make::compile_nullish_strict_comparison(
                            if neq {
                                crate::lambda::lam_compat::Comparison::Neq
                            } else {
                                crate::lambda::lam_compat::Comparison::Eq
                            },
                            v[0],
                            v[1],
                            a,
                        )
                    },
                    |b, v| n::jm2_nullish_strict_comparison(b, neq, v[0], v[1]),
                );
            }
            oracle(
                |a| vec![atom(a, i), atom(a, j)],
                |a, v| crate::lambda::js_exp_make::compile_int_equality(v[0], v[1], a),
                |b, v| n::jm2_int_equality(b, v[0], v[1]),
            );
        }
    }
}
#[test]
fn jm3_through_jm8_arithmetic_matrix() {
    use crate::lambda::js_exp_make as old;
    type Old = fn(Expr, Expr, &mut JsArena) -> Expr;
    type New = fn(&mut Bir, NodeId, NodeId) -> NodeId;
    let rows: [(Old, New); 9] = [
        (old::int32_bor, n::jm3_int32_bor),
        (old::int32_add, |b, l, r| {
            n::jm4_int32_add_sub(b, false, l, r)
        }),
        (old::int32_minus, |b, l, r| {
            n::jm4_int32_add_sub(b, true, l, r)
        }),
        (old::int32_mul, n::jm5_int32_mul),
        (old::int32_pow, n::jm6_int32_pow),
        (old::int32_lsl, n::jm7_int32_lsl),
        (old::int32_lsr, n::jm8_int32_lsr),
        (old::int32_bxor, n::jm8_int32_bxor),
        (old::int32_band, n::jm8_int32_band),
    ];
    for (row, (old, new)) in rows.into_iter().enumerate() {
        for i in 0..12 {
            for j in 0..12 {
                if row == 6 && j == 3 {
                    continue;
                }
                oracle(
                    |a| vec![atom(a, i), atom(a, j)],
                    |a, v| old(v[0], v[1], a),
                    |b, v| new(b, v[0], v[1]),
                );
            }
        }
    }
    for shift in [0, 1, 2, 30] {
        for left in [i32::MIN, -1, 0, 1, i32::MAX] {
            oracle(
                |a| vec![e::int(left, a), e::int(shift, a)],
                |a, v| old::int32_lsr(v[0], v[1], a),
                |b, v| n::jm8_int32_lsr(b, v[0], v[1]),
            );
        }
    }
}
#[test]
fn jm0_jm9_jm10_unary_matrix() {
    for i in 0..12 {
        oracle(
            |a| vec![atom(a, i)],
            |a, v| {
                crate::lambda::js_exp_make::remove_pure_subexpression(v[0], a)
                    .unwrap_or_else(|| e::undefined(false, a))
            },
            |b, v| {
                n::jm0_remove_pure_subexpression(b, v[0])
                    .unwrap_or_else(|| p::node(b, View::JUndefined, 0))
            },
        );
        oracle(
            |a| vec![atom(a, i)],
            |a, v| crate::lambda::js_exp_make::ocaml_typeof_expr(v[0], a),
            |b, v| n::jm9_typeof(b, v[0]),
        );
        oracle(
            |a| vec![atom(a, i)],
            |a, v| crate::lambda::js_exp_make::int_bnot(v[0], a),
            |b, v| n::jm10_int_bnot(b, v[0]),
        );
    }
}
#[test]
fn jm11_array_projection_purity_and_bounds() {
    for i in 0..12 {
        for index in [-1, 0, 1, 2] {
            oracle(
                |a| {
                    let x = atom(a, i);
                    let y = e::int(9, a);
                    let items = a.expr_list(&[x, y]);
                    vec![a.expr(ExprKind::Array(items, crate::js_ir::MutableFlag::Immutable))]
                },
                |a, v| {
                    crate::lambda::js_exp_make::pure_indexed_block_item(a, v[0], index)
                        .unwrap_or_else(|| {
                            let idx = e::int(index, a);
                            a.expr(ExprKind::ArrayIndex(v[0], idx))
                        })
                },
                |b, v| {
                    n::jm11_projection(b, v[0], None, Some(index)).unwrap_or_else(|| {
                        let index = p::int(b, index);
                        p::node(
                            b,
                            View::JIndex {
                                object: v[0],
                                index,
                            },
                            0,
                        )
                    })
                },
            );
        }
    }
}
#[test]
fn jm12_template_literals_comments_and_values() {
    for i in 0..12 {
        for comment in [false, true] {
            oracle(
                |a| {
                    let value = atom(a, i);
                    vec![if comment {
                        a.with_expr_comment(value, Some("keep"))
                    } else {
                        value
                    }]
                },
                |a, v| {
                    crate::lambda::js_exp_make::interpolated_template(
                        vec![
                            crate::string_literal::template_from_semantic("before"),
                            crate::string_literal::template_from_semantic("after"),
                        ],
                        v.to_vec(),
                        a,
                    )
                },
                |b, v| {
                    n::jm12_interpolated_template(
                        b,
                        vec![
                            crate::string_literal::template_from_semantic("before"),
                            crate::string_literal::template_from_semantic("after"),
                        ],
                        v.to_vec(),
                    )
                },
            );
        }
    }
}
#[test]
fn jm13_checked_and_unchecked_division_and_modulo() {
    for modulo in [false, true] {
        for checks in [false, true] {
            for i in 0..12 {
                for j in 0..12 {
                    oracle(
                        |a| vec![atom(a, i), atom(a, j)],
                        |a, v| {
                            let mut compiler = crate::lambda::lam_compile::LambdaCompiler::new();
                            compiler.j = std::mem::take(a);
                            compiler.check_div_by_zero = checks;
                            let value = if modulo {
                                compiler.int32_mod_expr(v[0], v[1])
                            } else {
                                compiler.int32_div_expr(v[0], v[1])
                            };
                            *a = compiler.j;
                            value
                        },
                        |b, v| {
                            if modulo {
                                n::jm13_int32_mod(b, checks, v[0], v[1])
                            } else {
                                n::jm13_int32_div(b, checks, v[0], v[1])
                            }
                        },
                    );
                }
            }
        }
    }
}
#[test]
fn jm14_statement_modes_and_sequence_boundaries() {
    for mode in 0..3 {
        for i in 0..12 {
            for j in 0..12 {
                stmt_oracle(
                    |a| {
                        let l = atom(a, i);
                        let r = atom(a, j);
                        let value = e::seq(l, r, a);
                        a.stmt(StmtKind::Exp(value))
                    },
                    |a, s| {
                        let StmtKind::Exp(v) = a.sk(s) else { panic!() };
                        let mut out = vec![];
                        match mode {
                            0 => {
                                crate::lambda::lam_coercion::push_effect_expression(a, &mut out, v)
                            }
                            1 => crate::lambda::lam_coercion::push_s_exp(a, &mut out, v),
                            _ => crate::lambda::lam_coercion::push_s_if_empty(a, &mut out, v),
                        };
                        crate::js_ir::build::stmt::block(&out, a)
                    },
                    |b, s| {
                        let View::SExp { value } = b.view(s) else {
                            panic!()
                        };
                        p::retain(b, &[s], &[value]);
                        let mut out = vec![];
                        match mode {
                            0 => n::jm14_push_effect_expression(b, value, &mut out),
                            1 => n::jm14_push_s_exp(b, value, &mut out),
                            _ => n::jm14_push_s_if_empty(b, value, &mut out),
                        };
                        n::js2_block(b, out)
                    },
                );
            }
        }
    }
}

fn array(a: &mut JsArena, values: &[Expr], block: bool) -> Expr {
    let values = a.expr_list(values);
    if block {
        let tag = a.tag_id(crate::lambda::TagInfo::Tuple);
        a.expr(ExprKind::CamlBlock(
            values,
            crate::js_ir::MutableFlag::Immutable,
            tag,
        ))
    } else {
        a.expr(ExprKind::Array(
            values,
            crate::js_ir::MutableFlag::Immutable,
        ))
    }
}
fn compare(a: &mut JsArena, op: BinOp, value: usize) -> Expr {
    let x = var(a, "x");
    let value = atom(a, value);
    e::raw_bin(op, x, value, a)
}
fn is_array(a: &mut JsArena) -> Expr {
    let id = a.ident_id(Ident::create_persistent("Array"));
    let target = a.expr(ExprKind::Var(id));
    let key = a.str("isArray");
    let callee = a.expr(ExprKind::StaticIndex(target, key, FieldPos::NONE));
    let x = var(a, "x");
    let args = a.expr_list(&[x]);
    let info = a.call_id(crate::js_ir::CallInfo::default());
    a.expr(ExprKind::Call(callee, args, info))
}
#[test]
fn je1_je2_template_semantics_and_utf16() {
    for invalid in [false, true] {
        for comment in [false, true] {
            for length in [false, true] {
                oracle(
                    |a| {
                        let segment = if invalid {
                            crate::string_literal::StringLiteral::InvalidSource(
                                "\\u{invalid}".into(),
                            )
                        } else {
                            crate::string_literal::template_from_semantic("😀\n")
                        };
                        let id = a.template_id(segment);
                        let v = a.expr(ExprKind::TemplateLiteral(id));
                        let v = if comment {
                            a.with_expr_comment(v, Some("literal"))
                        } else {
                            v
                        };
                        let r = e::string("suffix", a);
                        vec![v, r]
                    },
                    |a, v| {
                        if length {
                            e::length(v[0], LengthObject::String, a)
                        } else {
                            e::string_append(v[0], v[1], a)
                        }
                    },
                    |b, v| {
                        if length {
                            b.release(v[1]);
                            n::je2_length(b, v[0], LengthObject::String)
                        } else {
                            n::je1_string_append(b, v[0], v[1])
                        }
                    },
                );
            }
        }
    }
}
#[test]
fn je2_je3_array_block_and_method_boundaries() {
    for block in [false, true] {
        for effect in [false, true] {
            for nullish in [false, true] {
                oracle(
                    |a| {
                        let v = atom(a, if effect { 11 } else { 4 });
                        vec![array(a, &[v], block)]
                    },
                    |a, v| {
                        if nullish {
                            e::is_null_or_undefined(v[0], a)
                        } else {
                            e::length(v[0], LengthObject::Array, a)
                        }
                    },
                    |b, v| {
                        if nullish {
                            n::je3_is_null_or_undefined(b, v[0])
                        } else {
                            n::je2_length(b, v[0], LengthObject::Array)
                        }
                    },
                );
            }
        }
    }
    for method in [false, true] {
        oracle(
            |a| {
                let params = a.ident_list(&[
                    Ident::new("self", 4, IdentFlags::NONE),
                    Ident::new("arg", 5, IdentFlags::NONE),
                ]);
                let body = a.stmt_list(&[]);
                let fun = a.fun_id(FunInfo {
                    params,
                    body,
                    is_method: method,
                    return_unit: false,
                    async_: false,
                    directive: None,
                });
                vec![a.expr(ExprKind::Fun(fun))]
            },
            |a, v| e::length(v[0], LengthObject::Function, a),
            |b, v| n::je2_length(b, v[0], LengthObject::Function),
        );
    }
}
#[test]
fn je4_length_optional_and_nonnull_boundaries() {
    for op in [BinOp::Ge, BinOp::Gt, BinOp::Lt] {
        for effect in [false, true] {
            for zero in [0, 1] {
                oracle(
                    |a| {
                        let x = atom(a, if effect { 11 } else { 9 });
                        let length = a.expr(ExprKind::Length(x, LengthObject::Array));
                        let rhs = e::int(zero, a);
                        vec![length, rhs]
                    },
                    |a, v| e::bin(op, v[0], v[1], a),
                    |b, v| n::je4_bin(b, op, v[0], v[1]),
                );
            }
        }
    }
    for op in [BinOp::EqEqEq, BinOp::NotEqEq] {
        for i in 0..12 {
            for depth in [0, 1, 3] {
                oracle(
                    |a| {
                        let mut l = atom(a, i);
                        let mut r = atom(a, 8);
                        for _ in 0..depth {
                            l = a.expr(ExprKind::OptionalBlock(l, true));
                            r = a.expr(ExprKind::OptionalBlock(r, false));
                        }
                        vec![l, r]
                    },
                    |a, v| e::bin(op, v[0], v[1], a),
                    |b, v| n::je4_bin(b, op, v[0], v[1]),
                );
            }
        }
    }
    for i in 0..12 {
        for optional in [false, true] {
            for swap in [false, true] {
                oracle(
                    |a| {
                        let value = atom(a, i);
                        let value = if optional {
                            a.expr(ExprKind::OptionalBlock(value, false))
                        } else {
                            array(a, &[value], false)
                        };
                        let u = e::undefined(false, a);
                        if swap { vec![value, u] } else { vec![u, value] }
                    },
                    |a, v| e::bin(BinOp::EqEqEq, v[0], v[1], a),
                    |b, v| n::je4_bin(b, BinOp::EqEqEq, v[0], v[1]),
                );
            }
        }
    }
}
#[test]
fn je5_je6_variable_and_guard_triggers() {
    for op in [BinOp::And, BinOp::Or] {
        for right_position in [false, true] {
            for same in [false, true] {
                oracle(
                    |a| {
                        let left = var(a, "x");
                        let duplicate = var(a, if same { "x" } else { "y" });
                        let other = atom(a, 11);
                        let right = if right_position {
                            e::raw_bin(op, other, duplicate, a)
                        } else {
                            e::raw_bin(op, duplicate, other, a)
                        };
                        vec![left, right]
                    },
                    |a, v| e::bin(op, v[0], v[1], a),
                    |b, v| n::je4_bin(b, op, v[0], v[1]),
                );
            }
        }
    }
    for i in 0..12 {
        for same in [false, true] {
            oracle(
                |a| {
                    let x = var(a, "x");
                    let u = e::undefined(false, a);
                    let l = e::raw_bin(BinOp::NotEqEq, x, u, a);
                    let x = var(a, if same { "x" } else { "y" });
                    let value = atom(a, i);
                    let r = e::raw_bin(BinOp::EqEqEq, x, value, a);
                    vec![l, r]
                },
                |a, v| e::bin(BinOp::And, v[0], v[1], a),
                |b, v| n::je5_js_and(b, v[0], v[1]),
            );
        }
    }
}
#[test]
fn je7_nested_conditionals_negations_and_unit_suffixes() {
    for nested_then in [false, true] {
        for equal_then in [false, true] {
            for same in [false, true] {
                oracle(
                    |a| {
                        let c = var(a, "x");
                        let inner_test = var(a, "y");
                        let matched = e::string("same", a);
                        let other = e::string("other", a);
                        let outside = e::string(if same { "same" } else { "different" }, a);
                        let nested = if equal_then {
                            a.expr(ExprKind::Cond(inner_test, matched, other))
                        } else {
                            a.expr(ExprKind::Cond(inner_test, other, matched))
                        };
                        if nested_then {
                            vec![c, nested, outside]
                        } else {
                            vec![c, outside, nested]
                        }
                    },
                    |a, v| e::cond(v[0], v[1], v[2], a),
                    |b, v| n::je7_cond(b, v[0], v[1], v[2]),
                );
            }
        }
    }
    for alternate in 0..12 {
        oracle(
            |a| {
                let x = var(a, "x");
                let test = a.expr(ExprKind::JsNot(x));
                let yes = var(a, "y");
                let no = atom(a, alternate);
                vec![test, yes, no]
            },
            |a, v| e::cond(v[0], v[1], v[2], a),
            |b, v| n::je7_cond(b, v[0], v[1], v[2]),
        );
    }
    for suffix in [false, true] {
        oracle(
            |a| {
                let test = var(a, "x");
                let y = atom(a, 11);
                let z = var(a, "y");
                let u = e::undefined(false, a);
                let v = if suffix {
                    e::undefined(true, a)
                } else {
                    e::int(0, a)
                };
                vec![test, e::seq(y, u, a), e::seq(z, v, a)]
            },
            |a, v| e::cond(v[0], v[1], v[2], a),
            |b, v| n::je7_cond(b, v[0], v[1], v[2]),
        );
    }
    for then_false in [false, true] {
        oracle(
            |a| {
                let test = type_test(a, "boolean");
                let var = var(a, "x");
                let f = e::bool(false, a);
                if then_false {
                    vec![test, f, var]
                } else {
                    vec![test, var, f]
                }
            },
            |a, v| e::cond(v[0], v[1], v[2], a),
            |b, v| n::je7_cond(b, v[0], v[1], v[2]),
        );
    }
}
#[test]
fn je8_de_morgan_success_failure_and_double_not() {
    for op in [BinOp::And, BinOp::Or] {
        for failure in [false, true] {
            oracle(
                |a| {
                    let l = compare(a, BinOp::EqEqEq, 4);
                    let r = if failure {
                        var(a, "x")
                    } else {
                        compare(a, BinOp::NotEqEq, 6)
                    };
                    vec![e::raw_bin(op, l, r, a)]
                },
                |a, v| e::not(v[0], a),
                |b, v| n::je8_not(b, v[0]),
            );
        }
    }
    oracle(
        |a| {
            let x = var(a, "x");
            vec![a.expr(ExprKind::JsNot(x))]
        },
        |a, v| e::not(v[0], a),
        |b, v| n::je8_not(b, v[0]),
    );
}
#[test]
fn je9_boolean_type_array_and_comparison_rules() {
    for shape in 0..3 {
        for swap in [false, true] {
            oracle(
                |a| {
                    let test = type_test(a, "boolean");
                    let x = var(a, "x");
                    let other = match shape {
                        0 => x,
                        1 => a.expr(ExprKind::JsNot(x)),
                        _ => {
                            let f = e::bool(false, a);
                            e::raw_bin(BinOp::NotEqEq, x, f, a)
                        }
                    };
                    if swap {
                        vec![other, test]
                    } else {
                        vec![test, other]
                    }
                },
                |a, v| e::bin(BinOp::And, v[0], v[1], a),
                |b, v| n::je5_js_and(b, v[0], v[1]),
            );
        }
    }
    for neq in [false, true] {
        for i in 0..12 {
            for swap in [false, true] {
                oracle(
                    |a| {
                        let test = is_array(a);
                        let cmp = compare(a, if neq { BinOp::NotEqEq } else { BinOp::EqEqEq }, i);
                        if swap {
                            vec![cmp, test]
                        } else {
                            vec![test, cmp]
                        }
                    },
                    |a, v| e::bin(BinOp::And, v[0], v[1], a),
                    |b, v| n::je5_js_and(b, v[0], v[1]),
                );
            }
        }
    }
    for or in [false, true] {
        for left_op in [BinOp::EqEqEq, BinOp::NotEqEq] {
            for right_op in [BinOp::EqEqEq, BinOp::NotEqEq] {
                for l in 0..9 {
                    for r in 0..9 {
                        let op = if or { BinOp::Or } else { BinOp::And };
                        oracle(
                            |a| vec![compare(a, left_op, l), compare(a, right_op, r)],
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
fn je9_je10_recursive_logic_trigger_matrix() {
    for op in [BinOp::And, BinOp::Or] {
        for inner in [BinOp::And, BinOp::Or] {
            for side in [false, true] {
                for k in 0..4 {
                    oracle(
                        |a| {
                            let test = type_test(a, "number");
                            let equal = compare(a, BinOp::EqEqEq, if k & 1 == 0 { 4 } else { 6 });
                            let other = if k & 2 == 0 {
                                compare(a, BinOp::NotEqEq, 6)
                            } else {
                                var(a, "y")
                            };
                            let nested = e::raw_bin(inner, test, other, a);
                            if side {
                                vec![equal, nested]
                            } else {
                                vec![nested, equal]
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

fn old_if(a: &mut JsArena, s: Stmt) -> Stmt {
    let StmtKind::If(c, y, z) = a.sk(s) else {
        panic!()
    };
    let (y, z) = (a.stmts(y).to_vec(), a.stmts(z).to_vec());
    crate::js_ir::build::stmt::if_(c, &y, &z, a)
}
fn new_if(b: &mut Bir, s: NodeId) -> NodeId {
    let View::SIf {
        condition,
        then_,
        else_: Some(no),
    } = b.view(s)
    else {
        panic!()
    };
    let View::SBlock { statements: ys } = b.view(then_) else {
        panic!()
    };
    let ys = ys.to_vec();
    let View::SBlock { statements: ns } = b.view(no) else {
        panic!()
    };
    let ns = ns.to_vec();
    let mut keep = vec![condition];
    keep.extend_from_slice(&ys);
    keep.extend_from_slice(&ns);
    p::retain(b, &[s], &keep);
    n::js3_simplify_if(b, condition, ys, ns)
}
#[test]
fn js3_nested_if_merges_and_negation_boundaries() {
    for nested_then in [false, true] {
        for equal_then in [false, true] {
            for same in [false, true] {
                stmt_oracle(
                    |a| {
                        let test = var(a, "x");
                        let nested_test = var(a, "y");
                        let one = a.stmt(StmtKind::Debugger);
                        let two = a.stmt(StmtKind::Debugger);
                        let three = a.stmt(StmtKind::Debugger);
                        let matched = a.stmt_list(&[one]);
                        let other = a.stmt_list(&[two, three]);
                        let nested = if equal_then {
                            a.stmt(StmtKind::If(nested_test, matched, other))
                        } else {
                            a.stmt(StmtKind::If(nested_test, other, matched))
                        };
                        let nested = a.stmt_list(&[nested]);
                        let mut outside = vec![a.stmt(StmtKind::Debugger)];
                        if !same {
                            outside.push(a.stmt(StmtKind::Debugger));
                            outside.push(a.stmt(StmtKind::Debugger));
                        }
                        let outside = a.stmt_list(&outside);
                        if nested_then {
                            a.stmt(StmtKind::If(test, nested, outside))
                        } else {
                            a.stmt(StmtKind::If(test, outside, nested))
                        }
                    },
                    old_if,
                    new_if,
                );
            }
        }
    }
    for empty_then in [false, true] {
        for empty_else in [false, true] {
            stmt_oracle(
                |a| {
                    let x = var(a, "x");
                    let test = a.expr(ExprKind::JsNot(x));
                    let yes = branch(a, if empty_then { 0 } else { 11 });
                    let no = branch(a, if empty_else { 0 } else { 11 });
                    let yes = a.stmt_list(&yes);
                    let no = a.stmt_list(&no);
                    a.stmt(StmtKind::If(test, yes, no))
                },
                old_if,
                new_if,
            );
        }
    }
}
#[test]
fn js3_assignment_target_and_literal_last_statement_boundaries() {
    for kind in 0..3 {
        for same in [false, true] {
            stmt_oracle(
                |a| {
                    let c = var(a, "x");
                    let mut branches = vec![];
                    for side in 0..2 {
                        let target = var(a, if same || side == 0 { "x" } else { "y" });
                        let target = match kind {
                            0 => target,
                            1 => {
                                let key = a.str("field");
                                a.expr(ExprKind::StaticIndex(target, key, FieldPos::NONE))
                            }
                            _ => {
                                let index = var(a, "y");
                                a.expr(ExprKind::ArrayIndex(target, index))
                            }
                        };
                        let value = e::int(side, a);
                        let assign = e::raw_bin(BinOp::Eq, target, value, a);
                        let stmt = a.stmt(StmtKind::Exp(assign));
                        branches.push(a.stmt_list(&[stmt]));
                    }
                    a.stmt(StmtKind::If(c, branches[0], branches[1]))
                },
                old_if,
                new_if,
            );
        }
    }
    stmt_oracle(
        |a| {
            let c = var(a, "x");
            let ret = branch(a, 1);
            let ret = a.stmt_list(&ret);
            let wrapped = a.stmt(StmtKind::Block(ret));
            let yes = a.stmt_list(&[wrapped]);
            let no = branch(a, 11);
            let no = a.stmt_list(&no);
            a.stmt(StmtKind::If(c, yes, no))
        },
        old_if,
        new_if,
    );
}
#[test]
fn js4_string_switch_and_nonliteral_boundaries() {
    for value in 0..3 {
        stmt_oracle(
            |a| {
                let c = if value == 2 {
                    var(a, "x")
                } else {
                    e::string(if value == 0 { "case" } else { "other" }, a)
                };
                let body = branch(a, 1);
                let default = branch(a, 2);
                let body = a.stmt_list(&body);
                let default = a.stmt_list(&default);
                let info = a.string_switch_id(StringSwitchInfo {
                    clauses: vec![StringClauseInfo {
                        tag_type: crate::lambda::SwitchCaseTag::String("case".into()),
                        clause: Clause {
                            body,
                            should_break: false,
                            comment: None,
                            source_loc: None,
                        },
                    }],
                    default: Some(default),
                });
                a.stmt(StmtKind::StringSwitch(c, info))
            },
            |a, s| crate::js_ir::build::stmt::new(a.sk(s), a),
            n::js4_normalize,
        );
    }
}
#[test]
fn jm0_jm1_nested_sequence_and_narrow_purity() {
    for shape in 0..4 {
        for i in 0..12 {
            for j in 0..12 {
                oracle(
                    |a| {
                        let l = atom(a, i);
                        let r = atom(a, j);
                        let pair = match shape {
                            0 => e::seq(l, r, a),
                            1 => a.expr(ExprKind::ArrayIndex(l, r)),
                            2 => array(a, &[l, r], false),
                            _ => {
                                let zero = e::int(0, a);
                                let inner = e::seq(l, zero, a);
                                e::seq(inner, r, a)
                            }
                        };
                        vec![pair]
                    },
                    |a, v| {
                        crate::lambda::js_exp_make::remove_pure_subexpression(v[0], a)
                            .unwrap_or_else(|| e::undefined(false, a))
                    },
                    |b, v| {
                        n::jm0_remove_pure_subexpression(b, v[0])
                            .unwrap_or_else(|| p::node(b, View::JUndefined, 0))
                    },
                );
            }
        }
    }
    for side in [false, true] {
        for trivial_first in [false, true] {
            for trivial in [2, 8] {
                oracle(
                    |a| {
                        let x = atom(a, 11);
                        let z = var(a, "y");
                        let v = atom(a, trivial);
                        let seq = if trivial_first {
                            e::seq(v, x, a)
                        } else {
                            e::seq(x, v, a)
                        };
                        if side { vec![z, seq] } else { vec![seq, z] }
                    },
                    |a, v| crate::lambda::js_exp_make::js_seq(v[0], v[1], a),
                    |b, v| n::jm1_js_seq(b, v[0], v[1]),
                );
            }
        }
    }
}
#[test]
fn jm2_throwing_rhs_and_float_spelling_boundaries() {
    for op in [BinOp::Pow, BinOp::Div, BinOp::Mod] {
        for bigint in [false, true] {
            for safe in [false, true] {
                for neq in [false, true] {
                    oracle(
                        |a| {
                            let left = var(a, "x");
                            let right = if bigint {
                                let value = a.number_id(crate::js_ir::Number::bigint(
                                    if op == BinOp::Pow { safe } else { true },
                                    if safe || op == BinOp::Pow { "1" } else { "0" },
                                ));
                                a.expr(ExprKind::Number(value))
                            } else {
                                e::int(i32::from(safe), a)
                            };
                            let value = e::raw_bin(op, left, right, a);
                            let target = array(a, &[value], false);
                            let null = e::null(a);
                            vec![null, target]
                        },
                        |a, v| {
                            crate::lambda::js_exp_make::compile_nullish_strict_comparison(
                                if neq {
                                    crate::lambda::lam_compat::Comparison::Neq
                                } else {
                                    crate::lambda::lam_compat::Comparison::Eq
                                },
                                v[0],
                                v[1],
                                a,
                            )
                        },
                        |b, v| n::jm2_nullish_strict_comparison(b, neq, v[0], v[1]),
                    );
                }
            }
        }
    }
    for right in ["1.", "1.0", "nan"] {
        oracle(
            |a| {
                let l = a.number_id(crate::js_ir::Number::float("1."));
                let r = a.number_id(crate::js_ir::Number::float(right));
                vec![a.expr(ExprKind::Number(l)), a.expr(ExprKind::Number(r))]
            },
            |a, v| crate::lambda::js_exp_make::compile_int_equality(v[0], v[1], a),
            |b, v| n::jm2_int_equality(b, v[0], v[1]),
        );
    }
    oracle(
        |a| {
            let x = e::int(1, a);
            let optional = a.expr(ExprKind::OptionalBlock(x, false));
            let u = e::undefined(false, a);
            vec![optional, u]
        },
        |a, v| {
            crate::lambda::js_exp_make::compile_nullish_strict_comparison(
                crate::lambda::lam_compat::Comparison::Eq,
                v[0],
                v[1],
                a,
            )
        },
        |b, v| n::jm2_nullish_strict_comparison(b, false, v[0], v[1]),
    );
}
#[test]
fn jm3_jm8_shift_truncation_triggers() {
    use crate::lambda::js_exp_make as old;
    type Old = fn(Expr, Expr, &mut JsArena) -> Expr;
    type New = fn(&mut Bir, NodeId, NodeId) -> NodeId;
    for (old, new) in [
        (old::int32_bor as Old, n::jm3_int32_bor as New),
        (old::int32_lsr, n::jm8_int32_lsr),
        (old::int32_bxor, n::jm8_int32_bxor),
        (old::int32_band, n::jm8_int32_band),
    ] {
        for inner in [BinOp::Lsr, BinOp::Bor] {
            for side in [false, true] {
                for zero in [0, 1] {
                    for outer in [0, 1] {
                        oracle(
                            |a| {
                                let x = var(a, "x");
                                let z = e::int(zero, a);
                                let nested = e::raw_bin(inner, x, z, a);
                                let other = e::int(outer, a);
                                if side {
                                    vec![other, nested]
                                } else {
                                    vec![nested, other]
                                }
                            },
                            |a, v| old(v[0], v[1], a),
                            |b, v| new(b, v[0], v[1]),
                        );
                    }
                }
            }
        }
    }
}
#[test]
fn jm4_jm5_jm6_jm7_integer_boundaries() {
    for subtract in [false, true] {
        for (l, r) in [(i32::MAX, 1), (i32::MIN, -1), (i32::MIN, i32::MAX)] {
            oracle(
                |a| vec![e::int(l, a), e::int(r, a)],
                |a, v| {
                    if subtract {
                        crate::lambda::js_exp_make::int32_minus(v[0], v[1], a)
                    } else {
                        crate::lambda::js_exp_make::int32_add(v[0], v[1], a)
                    }
                },
                |b, v| n::jm4_int32_add_sub(b, subtract, v[0], v[1]),
            );
        }
    }
    for factor in [2, 4, 8, 3, -4] {
        for side in [false, true] {
            oracle(
                |a| {
                    let x = var(a, "x");
                    let factor = e::int(factor, a);
                    if side {
                        vec![factor, x]
                    } else {
                        vec![x, factor]
                    }
                },
                |a, v| crate::lambda::js_exp_make::int32_mul(v[0], v[1], a),
                |b, v| n::jm5_int32_mul(b, v[0], v[1]),
            );
        }
    }
    oracle(
        |a| {
            let x = var(a, "x");
            let zero = e::int(0, a);
            let div = e::raw_bin(BinOp::Div, x, zero, a);
            let zero = e::int(0, a);
            vec![div, zero]
        },
        |a, v| crate::lambda::js_exp_make::int32_mul(v[0], v[1], a),
        |b, v| n::jm5_int32_mul(b, v[0], v[1]),
    );
    for (l, r) in [(i32::MAX, 2), (2, 31), (-2, 31), (2, -2), (0, -1)] {
        oracle(
            |a| vec![e::int(l, a), e::int(r, a)],
            |a, v| crate::lambda::js_exp_make::int32_pow(v[0], v[1], a),
            |b, v| n::jm6_int32_pow(b, v[0], v[1]),
        );
    }
    for r in [-1, 0, 31, 32, 33] {
        oracle(
            |a| vec![e::int(i32::MAX, a), e::int(r, a)],
            |a, v| crate::lambda::js_exp_make::int32_lsl(v[0], v[1], a),
            |b, v| n::jm7_int32_lsl(b, v[0], v[1]),
        );
    }
}
#[test]
fn jm9_syntactic_typeof_even_with_effects() {
    for shape in 0..3 {
        oracle(
            |a| {
                let effect = atom(a, 11);
                let value = match shape {
                    0 => array(a, &[effect], false),
                    1 => a.expr(ExprKind::Length(effect, LengthObject::Array)),
                    _ => array(a, &[effect], true),
                };
                vec![value]
            },
            |a, v| crate::lambda::js_exp_make::ocaml_typeof_expr(v[0], a),
            |b, v| n::jm9_typeof(b, v[0]),
        );
    }
}

#[test]
fn jm11_record_fields_missing_fields_and_polyvariants() {
    for field in ["first", "second", "missing"] {
        for effect in [false, true] {
            oracle(
                |a| {
                    let first = atom(a, if effect { 11 } else { 4 });
                    let second = e::string("value", a);
                    let values = a.expr_list(&[first, second]);
                    let tag = a.tag_id(crate::lambda::TagInfo::Record(Box::new(
                        crate::lambda::lam_tag_info::RecordTag {
                            fields: vec![("first".into(), false), ("second".into(), false)],
                            logical_field_count: None,
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            array: false,
                        },
                    )));
                    vec![a.expr(ExprKind::CamlBlock(
                        values,
                        crate::js_ir::MutableFlag::Immutable,
                        tag,
                    ))]
                },
                |a, v| {
                    crate::lambda::js_exp_make::pure_record_field_item(a, v[0], field, 1)
                        .unwrap_or_else(|| {
                            let key = a.str(field);
                            a.expr(ExprKind::StaticIndex(v[0], key, FieldPos::new(Some(1))))
                        })
                },
                |b, v| {
                    n::jm11_projection(b, v[0], Some(field), Some(1)).unwrap_or_else(|| {
                        let property = b.intern_text(field);
                        p::node(
                            b,
                            View::JDot {
                                object: v[0],
                                property,
                                position: FieldPos::new(Some(1)),
                            },
                            0,
                        )
                    })
                },
            );
        }
    }
    for block in [false, true] {
        for effect in [false, true] {
            for payload in [false, true] {
                oracle(
                    |a| {
                        let first = e::string("tag", a);
                        let second = atom(a, if effect { 11 } else { 4 });
                        vec![array(a, &[first, second], block)]
                    },
                    |a, v| {
                        if payload {
                            crate::lambda::js_exp_make::poly_var_value_access(v[0], a)
                        } else {
                            crate::lambda::js_exp_make::poly_var_tag_access(v[0], a)
                        }
                    },
                    |b, v| n::jm11_poly_var_access(b, v[0], payload),
                );
            }
        }
    }
}
#[test]
fn jm12_adjacent_templates_invalid_escapes_and_comments() {
    for invalid in [false, true] {
        for comment in [false, true] {
            oracle(
                |a| {
                    let first = e::string("a\n", a);
                    let segment = if invalid {
                        crate::string_literal::StringLiteral::InvalidSource("\\x".into())
                    } else {
                        crate::string_literal::template_from_semantic("😀")
                    };
                    let id = a.template_id(segment);
                    let second = a.expr(ExprKind::TemplateLiteral(id));
                    let second = if comment {
                        a.with_expr_comment(second, Some("retain"))
                    } else {
                        second
                    };
                    vec![first, second]
                },
                |a, v| {
                    crate::lambda::js_exp_make::interpolated_template(
                        vec![
                            crate::string_literal::template_from_semantic("one"),
                            crate::string_literal::template_from_semantic("two"),
                            crate::string_literal::template_from_semantic("three"),
                        ],
                        v.to_vec(),
                        a,
                    )
                },
                |b, v| {
                    n::jm12_interpolated_template(
                        b,
                        vec![
                            crate::string_literal::template_from_semantic("one"),
                            crate::string_literal::template_from_semantic("two"),
                            crate::string_literal::template_from_semantic("three"),
                        ],
                        v.to_vec(),
                    )
                },
            );
        }
    }
}
#[test]
fn jm13_length_division_precedes_literal_division() {
    for divisor in [1, 2, 3] {
        oracle(
            |a| {
                let x = var(a, "x");
                let len = a.expr(ExprKind::Length(x, LengthObject::Array));
                vec![len, e::int(divisor, a)]
            },
            |a, v| {
                let mut compiler = crate::lambda::lam_compile::LambdaCompiler::new();
                compiler.j = std::mem::take(a);
                let result = compiler.int32_div_expr(v[0], v[1]);
                *a = compiler.j;
                result
            },
            |b, v| n::jm13_int32_div(b, true, v[0], v[1]),
        );
    }
}
#[test]
fn jm14_unit_pair_location_and_comment() {
    stmt_oracle(
        |a| {
            let x = var(a, "x");
            let y = e::int(7, a);
            let assign = e::raw_bin(BinOp::Eq, x, y, a);
            let unit = e::undefined(false, a);
            let comment = Some(a.str("assignment location"));
            let pair = a.expr_with(
                ExprKind::Seq(assign, unit),
                Cold {
                    comment,
                    source_loc: Some(crate::lambda::LamLoc::for_test(19)),
                },
            );
            a.stmt(StmtKind::Exp(pair))
        },
        |a, s| {
            let StmtKind::Exp(v) = a.sk(s) else { panic!() };
            let mut out = vec![];
            crate::lambda::lam_coercion::push_effect_expression(a, &mut out, v);
            crate::js_ir::build::stmt::block(&out, a)
        },
        |b, s| {
            let View::SExp { value } = b.view(s) else {
                panic!()
            };
            p::retain(b, &[s], &[value]);
            let mut out = vec![];
            n::jm14_push_effect_expression(b, value, &mut out);
            n::js2_block(b, out)
        },
    );
}
#[test]
fn je8_js2_jm0_jm1_jm14_ten_thousand_deep_and_wide() {
    for kind in 0..4 {
        let mut b = Bir::default();
        b.begin_bulk();
        let mut root = p::boolean(&mut b, true);
        for _ in 0..10_000 {
            root = match kind {
                0 => {
                    let rhs = p::boolean(&mut b, false);
                    p::bin(&mut b, BinOp::And, root, rhs)
                }
                _ => {
                    let right = p::int(&mut b, 0);
                    p::seq(&mut b, root, right)
                }
            };
        }
        b.steps.set(0);
        let result = match kind {
            0 => n::je8_not(&mut b, root),
            1 => n::jm0_remove_pure_subexpression(&mut b, root).unwrap(),
            2 => {
                let rhs = p::int(&mut b, 1);
                n::jm1_js_seq(&mut b, root, rhs)
            }
            _ => {
                let mut statements = vec![];
                n::jm14_push_effect_expression(&mut b, root, &mut statements);
                p::list(&mut b, &statements)
            }
        };
        let steps = b.steps.get();
        println!("J deep kind {kind}: {steps} node reads");
        assert!(steps <= 1_500_000, "{steps}");
        b.finish_bulk(result);
        b.validate(Some(result), false).unwrap();
    }
    let mut b = Bir::default();
    b.begin_bulk();
    let mut ss = vec![];
    for _ in 0..10_000 {
        ss.push(p::node(&mut b, View::SDebugger, 0));
    }
    let mut root = p::node(&mut b, View::SBlock { statements: &ss }, 1);
    for _ in 0..10_000 {
        root = p::node(
            &mut b,
            View::SBlock {
                statements: &[root],
            },
            1,
        );
    }
    b.steps.set(0);
    let root = n::js2_block(&mut b, vec![root]);
    let steps = b.steps.get();
    println!("J-S2 deep/wide: {steps} node reads");
    assert!(steps <= 400_000);
    b.finish_bulk(root);
    b.validate(Some(root), false).unwrap();
}
#[test]
fn je10_ten_thousand_term_chain_uses_iterative_negation() {
    let mut b = Bir::default();
    b.begin_bulk();
    let var = b.new_var_id(crate::name::Name::new("x"), 1);
    let mut root = p::node(&mut b, View::Var { var }, 0);
    for _ in 0..10_000 {
        let right = p::node(&mut b, View::Var { var }, 0);
        root = p::bin(&mut b, BinOp::And, root, right);
    }
    let left = p::node(&mut b, View::JNot { value: root }, 0);
    let v = p::node(&mut b, View::Var { var }, 0);
    let right = p::node(&mut b, View::JNot { value: v }, 0);
    let mut steps = 0;
    let result = n::je10_simplify_or(&mut b, left, right, &mut steps);
    println!("J-E10 10000-term chain: {steps} inspected pairs/planner steps");
    assert!(steps < 100_000, "{steps}");
    let result = result.unwrap_or_else(|| p::bin(&mut b, BinOp::Or, left, right));
    b.finish_bulk(result);
    b.validate(Some(result), false).unwrap();
}

#[test]
fn je1_je7_js3_ten_thousand_reassociations() {
    for kind in 0..3 {
        let mut b = Bir::default();
        b.begin_bulk();
        let var = b.new_var_id(crate::name::Name::new("x"), 1);
        let mut root = if kind == 2 {
            p::node(&mut b, View::SDebugger, 0)
        } else {
            p::node(&mut b, View::Var { var }, 0)
        };
        for _ in 0..10_000 {
            root = match kind {
                0 => {
                    let suffix = p::string(&mut b, "a");
                    p::node(
                        &mut b,
                        View::JStrAppend {
                            left: root,
                            right: suffix,
                        },
                        0,
                    )
                }
                1 => {
                    let condition = p::node(&mut b, View::Var { var }, 0);
                    let else_ = p::string(&mut b, "same");
                    p::node(
                        &mut b,
                        View::JCond {
                            condition,
                            then_: root,
                            else_,
                        },
                        0,
                    )
                }
                _ => {
                    let condition = p::node(&mut b, View::Var { var }, 0);
                    let then_ = p::list(&mut b, &[root]);
                    let d = p::node(&mut b, View::SDebugger, 0);
                    let else_ = p::list(&mut b, &[d]);
                    p::node(
                        &mut b,
                        View::SIf {
                            condition,
                            then_,
                            else_: Some(else_),
                        },
                        0,
                    )
                }
            };
        }
        b.steps.set(0);
        let root = match kind {
            0 => {
                let suffix = p::string(&mut b, "b");
                n::je1_string_append(&mut b, root, suffix)
            }
            1 => {
                let condition = p::node(&mut b, View::Var { var }, 0);
                let else_ = p::string(&mut b, "same");
                n::je7_cond(&mut b, condition, root, else_)
            }
            _ => {
                let condition = p::node(&mut b, View::Var { var }, 0);
                let no = p::node(&mut b, View::SDebugger, 0);
                n::js3_simplify_if(&mut b, condition, vec![root], vec![no])
            }
        };
        let reads = b.steps.get();
        println!("J reassociation kind {kind}: {reads} node reads");
        assert!(reads < 3_000_000, "{reads}");
        b.finish_bulk(root);
        b.validate(Some(root), false).unwrap();
    }
}

#[test]
fn je9_literal_numeric_semantics() {
    use crate::js_ir::Number;
    for (l, r) in [
        (Number::float("1."), Number::float("1.0")),
        (Number::float("nan"), Number::float("nan")),
        (Number::int(1), Number::float("1.")),
        (Number::bigint(true, "1"), Number::bigint(true, "01")),
        (Number::bigint(true, "1"), Number::int(1)),
        (Number::bigint(true, "0"), Number::bigint(false, "0")),
    ] {
        for neq in [false, true] {
            oracle(
                |a| {
                    let x = var(a, "x");
                    let y = var(a, "x");
                    let l = a.number_id(l.clone());
                    let r = a.number_id(r.clone());
                    let l = a.expr(ExprKind::Number(l));
                    let r = a.expr(ExprKind::Number(r));
                    vec![
                        e::raw_bin(BinOp::EqEqEq, x, l, a),
                        e::raw_bin(if neq { BinOp::NotEqEq } else { BinOp::EqEqEq }, y, r, a),
                    ]
                },
                |a, v| e::bin(BinOp::And, v[0], v[1], a),
                |b, v| n::je5_js_and(b, v[0], v[1]),
            );
        }
    }
}
#[test]
fn jm9_template_typeof() {
    oracle(
        |a| {
            let id = a.template_id(crate::string_literal::template_from_semantic("literal"));
            vec![a.expr(ExprKind::TemplateLiteral(id))]
        },
        |a, v| crate::lambda::js_exp_make::ocaml_typeof_expr(v[0], a),
        |b, v| n::jm9_typeof(b, v[0]),
    );
}
#[test]
fn jm11_direct_projection_matches_index_and_field_contract() {
    for block in [false, true] {
        for field in [None, Some("ignored")] {
            for index in [None, Some(-1), Some(0), Some(2)] {
                oracle(
                    |a| {
                        let v = e::int(42, a);
                        vec![array(a, &[v], block)]
                    },
                    |a, v| {
                        crate::lambda::js_exp_make::direct_projection_from_pure_literal(
                            a, v[0], field, index,
                        )
                        .unwrap_or(v[0])
                    },
                    |b, v| n::jm11_projection(b, v[0], field, index).unwrap_or(v[0]),
                );
            }
        }
    }
}
