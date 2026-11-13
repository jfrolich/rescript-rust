use super::flatten::Flatten;
use crate::bir::{View, bridge_j, j::plain};
use crate::js_ir::arena::*;
use crate::js_ir::{BinOp, MutableFlag, build::exp as e};

fn effect(a: &mut JsArena, code: &str) -> Expr {
    let raw = a.raw_id(crate::js_ir::JsRawInfo { code: code.into(), is_stmt: false });
    a.expr(ExprKind::RawJsCode(raw))
}
fn oracle(make: impl FnOnce(&mut JsArena) -> Stmt) {
    let mut a = JsArena::new();
    let statement = make(&mut a);
    let source = JsDepsProgram { program: JsProgram::new_in(vec![statement], vec![], a), modules: vec![], side_effect: None };
    let mut imported = bridge_j::import_js(&source).unwrap();
    let View::SBlock { statements } = imported.arena.view(imported.root) else { panic!() };
    let statement = statements[0];
    imported.arena.detach(statement);
    imported.arena.release(imported.root);
    let mut out = Vec::new();
    Flatten::default().flatten_into(&mut imported.arena, statement, &mut out);
    imported.root = plain::list(&mut imported.arena, &out);
    imported.arena.validate(Some(imported.root)).unwrap();
    let actual = bridge_j::export_js(&imported).unwrap();
    let expected = crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass(source);
    let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
    assert_eq!(print(&actual), print(&expected));
}
#[test]
fn r1_effect_sequence() {
    oracle(|a| {
        let x = effect(a, "x()"); let y = effect(a, "y()");
        let value = a.expr(ExprKind::Seq(x, y)); a.stmt(StmtKind::Exp(value))
    });
}
#[test]
fn r2_block_fields() {
    oracle(|a| {
        let x = effect(a, "x()"); let y = effect(a, "y()");
        let values = a.expr_list(&[x, y]); let tag = a.tag_id(crate::lambda::TagInfo::Tuple);
        let value = a.expr(ExprKind::CamlBlock(values, MutableFlag::Immutable, tag)); a.stmt(StmtKind::Exp(value))
    });
}
#[test]
fn r3_effect_conditional() {
    for mask in 0..8 {
        oracle(|a| {
            let test = if mask & 4 != 0 { effect(a, "test()") } else { e::bool(true, a) };
            let yes = if mask & 1 != 0 { effect(a, "yes()") } else { e::int(1, a) };
            let no = if mask & 2 != 0 { effect(a, "no()") } else { e::int(2, a) };
            let value = a.expr(ExprKind::Cond(test, yes, no)); a.stmt(StmtKind::Exp(value))
        });
    }
}
#[test]
fn r4_assignment_sequence() {
    oracle(|a| {
        let target = effect(a, "target"); let x = effect(a, "x()"); let y = effect(a, "y()");
        let value = a.expr(ExprKind::Seq(x, y)); let value = a.expr(ExprKind::Bin(BinOp::Eq, target, value));
        a.stmt(StmtKind::Exp(value))
    });
}
#[test]
fn r5_return_conditional() {
    oracle(|a| {
        let test = effect(a, "test()"); let x = effect(a, "x()"); let y = e::int(2, a);
        let value = a.expr(ExprKind::Cond(test, x, y)); a.stmt(StmtKind::Return(value))
    });
}
#[test]
fn r6_return_sequence() {
    oracle(|a| {
        let x = effect(a, "x()"); let y = effect(a, "y()");
        let value = a.expr(ExprKind::Seq(x, y)); a.stmt(StmtKind::Return(value))
    });
}
#[test]
fn r7_singleton_block() {
    oracle(|a| {
        let x = effect(a, "x()"); let y = effect(a, "y()");
        let value = a.expr(ExprKind::Seq(x, y)); let statement = a.stmt(StmtKind::Exp(value));
        let list = a.stmt_list(&[statement]); a.stmt(StmtKind::Block(list))
    });
}
#[test]
fn r8_splice_block_in_list() {
    oracle(|a| {
        let x = effect(a, "x()"); let y = effect(a, "y()");
        let x = a.stmt(StmtKind::Exp(x)); let y = a.stmt(StmtKind::Exp(y));
        let list = a.stmt_list(&[x, y]); a.stmt(StmtKind::Block(list))
    });
}
