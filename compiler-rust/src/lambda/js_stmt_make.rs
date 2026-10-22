//! Statement construction helpers for JS IR.
//!
//! Port of `js_stmt_make.ml` — block termination analysis, return
//! expression extraction, and output-finishing predicates.

use crate::js_ir::{Block, Expression, Statement, StatementDesc};

pub(crate) fn block_terminates(block: &Block) -> bool {
    block.last().is_some_and(statement_terminates)
}

/// Port of OCaml's `S.if_` rule 4 match condition (js_stmt_make.ml:244-246):
/// both branches must be `[{statement_desc = Return _}]` — strictly a
/// single-element list whose sole statement is a `Return`. No effect prefix
/// allowed. Used by `compile_test_return_block_with_fallback` to mirror
/// OCaml's rule-4 fold exactly.
pub(crate) fn strict_single_return_expr(block: &[Statement]) -> Option<&Expression> {
    let [stmt] = block else {
        return None;
    };
    match &stmt.desc {
        StatementDesc::Return(expr) => Some(expr),
        _ => None,
    }
}

pub(crate) fn block_finishes_output(block: &Block) -> bool {
    block.last().is_some_and(statement_finishes_output)
}

pub(crate) fn statement_terminates(stmt: &crate::js_ir::Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_terminates(block),
        StatementDesc::Return(_)
        | StatementDesc::Throw(_)
        | StatementDesc::Break(_)
        | StatementDesc::Continue(_) => true,
        StatementDesc::If(_, then_block, else_block) => {
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_terminates(then_block)
                && block_terminates(else_block)
        }
        StatementDesc::IntSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|(_, clause)| block_terminates(&clause.body))
        }
        StatementDesc::StringSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|clause| block_terminates(&clause.clause.body))
        }
        _ => false,
    }
}

pub(crate) fn statement_finishes_output(stmt: &crate::js_ir::Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_finishes_output(block),
        StatementDesc::Return(_) | StatementDesc::Throw(_) => true,
        StatementDesc::If(_, then_block, else_block) => {
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_finishes_output(then_block)
                && block_finishes_output(else_block)
        }
        StatementDesc::IntSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_finishes_output)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|(_, clause)| block_finishes_output(&clause.body))
        }
        StatementDesc::StringSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_finishes_output)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|clause| block_finishes_output(&clause.clause.body))
        }
        _ => false,
    }
}
