//! Statement construction helpers for JS IR.
//!
//! Port of `js_stmt_make.ml` — block termination analysis, return
//! expression extraction, and output-finishing predicates.

use crate::js_ir::arena::{Expr, JsArena, Stmt, StmtKind};

pub(crate) fn block_terminates(a: &JsArena, block: &[Stmt]) -> bool {
    block.last().is_some_and(|s| statement_terminates(a, *s))
}

/// Port of OCaml's `S.if_` rule 4 match condition (js_stmt_make.ml:244-246):
/// both branches must be `[{statement_desc = Return _}]` — strictly a
/// single-element list whose sole statement is a `Return`. No effect prefix
/// allowed. Used by `compile_test_return_block_with_fallback` to mirror
/// OCaml's rule-4 fold exactly.
pub(crate) fn strict_single_return_expr(a: &JsArena, block: &[Stmt]) -> Option<Expr> {
    let [stmt] = block else {
        return None;
    };
    match a.sk(*stmt) {
        StmtKind::Return(expr) => Some(expr),
        _ => None,
    }
}

pub(crate) fn block_finishes_output(a: &JsArena, block: &[Stmt]) -> bool {
    block
        .last()
        .is_some_and(|s| statement_finishes_output(a, *s))
}

pub(crate) fn statement_terminates(a: &JsArena, stmt: Stmt) -> bool {
    statement_ends_control(a, stmt, true)
}

pub(crate) fn statement_finishes_output(a: &JsArena, stmt: Stmt) -> bool {
    statement_ends_control(a, stmt, false)
}

/// Shared walker for `statement_terminates` (which also accepts `break` and
/// `continue`) and `statement_finishes_output` (only `return`/`throw`).
fn statement_ends_control(a: &JsArena, stmt: Stmt, allow_jumps: bool) -> bool {
    let block_ends = |block: &[Stmt]| {
        block
            .last()
            .is_some_and(|stmt| statement_ends_control(a, *stmt, allow_jumps))
    };
    match a.sk(stmt) {
        StmtKind::Block(block) => block_ends(a.stmts(block)),
        StmtKind::Return(_) | StmtKind::Throw(_) => true,
        StmtKind::Break(_) | StmtKind::Continue(_) => allow_jumps,
        StmtKind::If(_, then_block, else_block) => {
            let (then_block, else_block) = (a.stmts(then_block), a.stmts(else_block));
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_ends(then_block)
                && block_ends(else_block)
        }
        StmtKind::IntSwitch(_, info) => {
            let info = a.int_switch(info);
            info.default.is_some_and(|d| block_ends(a.stmts(d)))
                && !info.clauses.is_empty()
                && info
                    .clauses
                    .iter()
                    .all(|(_, clause)| block_ends(a.stmts(clause.body)))
        }
        StmtKind::StringSwitch(_, info) => {
            let info = a.string_switch(info);
            info.default.is_some_and(|d| block_ends(a.stmts(d)))
                && !info.clauses.is_empty()
                && info
                    .clauses
                    .iter()
                    .all(|clause| block_ends(a.stmts(clause.clause.body)))
        }
        _ => false,
    }
}
