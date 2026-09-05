//! Distinct native short-circuit continuations (lam_compile.ml:1137-1220).
use super::output::Output;
use super::*;
use crate::lambda::lam_compile_context::{Continuation, TailType};

impl IndexedJsConsumer<'_> {
    fn short_circuit_parts(&self, node: NodeId) -> (ShortCircuitOp, NodeId, NodeId) {
        match self.context.store().view(node) {
            NodeView::Prim(Primitive::Psequand, [lhs, rhs], _) => (ShortCircuitOp::And, *lhs, *rhs),
            NodeView::Prim(Primitive::Psequor, [lhs, rhs], _) => (ShortCircuitOp::Or, *lhs, *rhs),
            _ => panic!("short circuit lowering requires sequand/sequor"),
        }
    }

    pub(super) fn short_circuit_return(
        &mut self,
        node: NodeId,
        same_continuation: &mut impl FnMut(&mut Self, NodeId) -> Output,
    ) -> Output {
        // Lam.sequand / Lam.sequor use Lam.if_ (lam.ml:628-631), not a
        // primitive call or a NeedValue detour. Keep the caller's tail state.
        let (op, lhs, rhs) = self.short_circuit_parts(node);
        let default = self
            .context
            .store_mut()
            .append(NodeSnapshot::Const(match op {
                ShortCircuitOp::And => Constant::JsFalse,
                ShortCircuitOp::Or => Constant::JsTrue,
            }));
        let (then_, else_) = match op {
            ShortCircuitOp::And => (rhs, default),
            ShortCircuitOp::Or => (default, rhs),
        };
        let root = append_rebuilt(
            self.context.store_mut(),
            NodeSnapshot::IfThenElse(lhs, then_, else_),
        );
        same_continuation(self, root)
    }

    pub(super) fn short_circuit_value(
        &mut self,
        node: NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let output =
            self.short_circuit_nonreturn(node, &Continuation::NeedValue(TailType::NotTail), lower);
        Compiled {
            prelude: output.block,
            expr: output.value.expect("NeedValue short circuit"),
        }
    }

    pub(super) fn short_circuit_nonreturn(
        &mut self,
        node: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Output {
        assert!(
            !continuation.is_return(),
            "return short circuit must keep its tail continuation"
        );
        let (op, lhs, rhs) = self.short_circuit_parts(node);
        let lhs = lower(self, lhs);
        let rhs = lower(self, rhs);
        if rhs.prelude.is_empty() {
            return Output::of_block_and_expression(
                continuation,
                lhs.prelude,
                Expression::bin(
                    match op {
                        ShortCircuitOp::And => BinOp::And,
                        ShortCircuitOp::Or => BinOp::Or,
                    },
                    lhs.expr,
                    rhs.expr,
                ),
            );
        }
        let (target, declare, value) = match continuation {
            Continuation::Assign(id) => (id.clone(), false, false),
            Continuation::Declare(_, id) => (id.clone(), true, false),
            Continuation::NeedValue(_) | Continuation::EffectCall(_) => {
                (self.compiler.fresh_tmp_ident(), true, true)
            }
        };
        let mut rhs_block = rhs.prelude;
        rhs_block.push(Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(target.clone()),
            rhs.expr,
        )));
        let mut block = lhs.prelude;
        let else_block = if declare {
            let declaration = Statement::variable(VariableDeclaration {
                ident: target.clone(),
                value: Some(op.default_expr()),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            });
            // NeedValue/Effect sequand prepends the declaration BEFORE l_block;
            // sequor and Declare append it AFTER l_block. This is intentional
            // in the native clauses at lam_compile.ml:1160-1180 / 1204-1220.
            if value && op == ShortCircuitOp::And {
                block.insert(0, declaration);
            } else {
                block.push(declaration);
            }
            vec![]
        } else {
            vec![Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target.clone()),
                op.default_expr(),
            ))]
        };
        block.push(Statement::if_(
            op.test_expr(lhs.expr),
            rhs_block,
            else_block,
        ));
        let mut output = Output::make(block);
        if value {
            output.value = Some(Expression::var(target));
        }
        output
    }
}
