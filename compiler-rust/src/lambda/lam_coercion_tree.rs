//! Tree-IR helpers of `lam_coercion` still used by the tree producer.

use crate::ident::Ident;
use crate::js_ir::{
    Block, Expression, ExpressionDesc, Statement, StatementDesc, VariableDeclaration,
};
use crate::lambda::js_exp_make_tree::js_expr_no_side_effects;

pub(crate) fn block_declares_initialized_ident(block: &Block, target: &Ident) -> bool {
    block.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) if ident.same(target) => {
            Some(value.is_some())
        }
        _ => None,
    }) == Some(true)
}

pub(crate) fn push_effect_expression(block: &mut Block, expr: Expression) {
    let expr = effect_value_without_unit(expr);
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            push_effect_expression(block, *left);
            push_effect_expression(block, *right);
        }
        _ if js_expr_no_side_effects(&expr) => {}
        _ => block.push(Statement::exp(expr)),
    }
}

/// Mirrors OCaml's `S.exp` (js_stmt_make.ml:45-53): keeps pure expressions as
/// `Exp` statements except for literal `Number`/`Undefined` payloads, which
/// are silently dropped (along with the Number/Undefined side of a top-level
/// `Seq`). Use this wherever OCaml would construct `S.exp e` — e.g. the
/// empty-branches reduction inside `S.if_` (js_stmt_make.ml:242), and the
/// all-empty switch collapses. `push_effect_expression` is more aggressive and
/// strips every side-effect-free expression, which matches OCaml's
/// `output_of_expression` (js_output.ml:42-52) but not `S.exp`.
pub(crate) fn push_s_exp(block: &mut Block, expr: Expression) {
    let source_loc = expr.source_loc.clone();
    match expr.desc {
        ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. } => {}
        ExpressionDesc::Seq(left, right) => match (&left.desc, &right.desc) {
            (ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }, _) => {
                push_s_exp(block, *right);
            }
            (_, ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }) => {
                push_s_exp(block, *left);
            }
            _ => block.push(Statement::exp(Expression {
                source_loc,
                desc: ExpressionDesc::Seq(left, right),
                comment: expr.comment,
            })),
        },
        _ => block.push(Statement::exp(expr)),
    }
}

/// lam_compile_primitive.ml:30-36 `ensure_value_unit`: in effect position
/// (`EffectCall Not_tail`) a field or array store is the bare assignment, so
/// the primitive's `with_source_loc` lands on the assignment itself rather
/// than on a `(assignment, undefined)` sequence.
fn effect_value_without_unit(expr: Expression) -> Expression {
    match expr {
        Expression {
            desc: ExpressionDesc::Seq(left, right),
            source_loc: Some(loc),
            comment,
        } if matches!(right.desc, ExpressionDesc::Undefined { is_unit: false })
            && left.source_loc.is_none()
            && matches!(
                left.desc,
                ExpressionDesc::Bin(crate::js_ir::BinOp::Eq, _, _)
            ) =>
        {
            let mut left = *left;
            left.source_loc = Some(loc);
            if left.comment.is_none() {
                left.comment = comment;
            }
            left
        }
        expr => expr,
    }
}
