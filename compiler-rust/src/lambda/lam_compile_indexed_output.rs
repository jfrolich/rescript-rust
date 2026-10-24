//! Indexed consumer's native Js_output value/finished protocol. No Lambda
//! representation appears here. See compiler/core/js_output.ml:28-143.
use super::context::{Continuation, TailType};
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Finished {
    True,
    False,
    Dummy,
}

pub(super) struct Output {
    pub(super) block: Block,
    pub(super) value: Option<Expression>,
    pub(super) finished: Finished,
}

impl Output {
    pub(super) fn make(block: Block) -> Self {
        Self {
            block,
            value: None,
            finished: Finished::False,
        }
    }

    pub(super) fn dummy() -> Self {
        Self {
            block: vec![],
            value: None,
            finished: Finished::Dummy,
        }
    }

    pub(super) fn of_expression(
        continuation: &Continuation,
        expr: Expression,
        no_effects: impl FnOnce() -> bool,
    ) -> Self {
        if matches!(continuation, Continuation::EffectCall(TailType::NotTail)) && no_effects() {
            return Self::dummy();
        }
        Self::of_block_and_expression(continuation, vec![], expr)
    }

    pub(super) fn of_block_and_expression(
        continuation: &Continuation,
        mut block: Block,
        expr: Expression,
    ) -> Self {
        match continuation {
            Continuation::NeedValue(_) | Continuation::EffectCall(TailType::NotTail) => Self {
                block,
                value: Some(expr),
                finished: Finished::False,
            },
            Continuation::Assign(id) => {
                block.push(Statement::exp(Expression::bin(
                    BinOp::Eq,
                    Expression::var(*id),
                    expr,
                )));
                Self::make(block)
            }
            Continuation::Declare(kind, id) => {
                block.push(Statement::variable(VariableDeclaration {
                    ident: *id,
                    // Js_stmt_make.define_variable: every Undefined becomes
                    // a declaration without an initializer, unit or not.
                    value: if matches!(expr.desc, ExpressionDesc::Undefined { .. }) {
                        None
                    } else {
                        Some(expr)
                    },
                    property: *kind,
                    ident_info: IdentInfo::default(),
                }));
                Self::make(block)
            }
            Continuation::EffectCall(TailType::MaybeTailIsReturn(_)) => {
                block.push(Statement::return_(expr));
                Self {
                    block,
                    value: None,
                    finished: Finished::True,
                }
            }
        }
    }

    pub(super) fn into_block(self) -> Block {
        let mut block = unnest_block(self.block);
        if self.finished != Finished::True {
            if let Some(expr) = self.value {
                if !js_expr_no_side_effects(&expr) {
                    block.push(Statement::exp(expr));
                }
            }
        }
        block
    }

    pub(super) fn into_break_block(self) -> (Block, bool) {
        let should_break = self.finished != Finished::True;
        (self.into_block(), should_break)
    }

    pub(super) fn append(self, next: Self) -> Self {
        if self.finished == Finished::True
            || (next.block.is_empty() && next.value.is_none() && next.finished == Finished::Dummy)
        {
            return self;
        }
        if self.block.is_empty() && self.value.is_none() {
            return next;
        }
        if self.block.is_empty() && next.block.is_empty() {
            match (self.value, next.value) {
                (Some(first), None) => {
                    return Self {
                        block: vec![],
                        value: Some(first),
                        finished: self.finished,
                    };
                }
                (Some(first), Some(second)) => {
                    return Self {
                        block: vec![],
                        value: Some(if js_expr_no_side_effects(&first) {
                            second
                        } else {
                            js_seq(first, second)
                        }),
                        finished: next.finished,
                    };
                }
                _ => unreachable!("empty first output handled above"),
            }
        }
        let mut block = unnest_block(self.block);
        if let Some(expr) = self.value {
            if !js_expr_no_side_effects(&expr) {
                block.push(Statement::exp(expr));
            }
        }
        block.extend(unnest_block(next.block));
        Self {
            block,
            value: next.value,
            finished: next.finished,
        }
    }
}
