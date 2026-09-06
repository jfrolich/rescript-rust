//! Native conditional modes, compiler/core/lam_compile.ml:1459-1606.
use super::*;
use super::context::{Continuation, TailType};
use super::output::{Output, Finished};

fn simple(output: &Output) -> bool { output.block.is_empty() && output.value.is_some() }
fn value(output: Output) -> Expression { output.value.expect("conditional NeedValue") }

impl IndexedJsConsumer<'_> {
    pub(super) fn conditional(
        &mut self,
        node: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Output {
        let (condition, then_, else_) = match self.context.store().view(node) {
            NodeView::IfThenElse(condition, then_, else_) => (condition, then_, else_),
            _ => panic!("conditional lowering requires IfThenElse"),
        };
        let predicate = lower(self, condition, &Continuation::NeedValue(TailType::NotTail));
        let mut block = predicate.block;
        let predicate = predicate.value.expect("conditional predicate value");
        match continuation {
            Continuation::NeedValue(_) => {
                // Native tuple evaluation: else before then. Both probes can
                // mutate caches/return labels even when their JS is discarded.
                let else_probe = lower(self, else_, continuation);
                let then_probe = lower(self, then_, continuation);
                if simple(&then_probe) && simple(&else_probe) {
                    return Output { block, value: Some(Expression::cond(predicate, value(then_probe), value(else_probe))), finished: Finished::False };
                }
                let id = self.compiler.fresh_tmp_ident();
                let assign = Continuation::Assign(id.clone());
                let else_output = lower(self, else_, &assign);
                let then_output = lower(self, then_, &assign);
                block.insert(0, Statement::variable(VariableDeclaration { ident: id.clone(), value: None, property: LetKind::Variable, ident_info: IdentInfo::default() }));
                block.push(Statement::if_(predicate, then_output.into_block(), else_output.into_block()));
                Output { block, value: Some(Expression::var(id)), finished: Finished::False }
            },
            Continuation::Declare(kind, id) => {
                let probe = Continuation::NeedValue(TailType::NotTail);
                let else_probe = lower(self, else_, &probe);
                let then_probe = lower(self, then_, &probe);
                if simple(&then_probe) && simple(&else_probe) {
                    return Output::of_block_and_expression(continuation, block, Expression::cond(predicate, value(then_probe), value(else_probe)));
                }
                let assign = Continuation::Assign(id.clone());
                // S.if_'s labelled else argument precedes its then argument.
                let else_output = lower(self, else_, &assign).into_block();
                let then_output = lower(self, then_, &assign).into_block();
                block.extend(self.compiler.compile_declared_if_block(*kind, id, predicate, then_output, else_output));
                Output::make(block)
            },
            Continuation::Assign(_) => {
                // These are explicit let bindings, unlike the tuple above.
                let then_output = lower(self, then_, continuation).into_block();
                let else_output = lower(self, else_, continuation).into_block();
                block.push(Statement::if_(predicate, then_output, else_output));
                Output::make(block)
            },
            Continuation::EffectCall(tail) => {
                // Copy only the mode/return slot. A named return label's
                // mutable state remains in self.return_labels for both probes.
                let probe = Continuation::NeedValue(*tail);
                let else_probe = lower(self, else_, &probe);
                let then_probe = lower(self, then_, &probe);
                match (tail, simple(&then_probe), simple(&else_probe)) {
                    (TailType::NotTail, true, true) => {
                        let then_effect = remove_pure_subexpression(value(then_probe));
                        let else_effect = remove_pure_subexpression(value(else_probe));
                        match (then_effect, else_effect) {
                            (None, None) => { block.push(Statement::exp(predicate)); Output::make(block) },
                            (Some(then_), Some(else_)) => Output { block, value: Some(Expression::cond(predicate, then_, else_)), finished: Finished::False },
                            (Some(then_), None) => { block.push(Statement::if_(predicate, vec![Statement::exp(then_)], vec![])); Output::make(block) },
                            (None, Some(else_)) => { block.push(Statement::if_(Expression::not(predicate), vec![Statement::exp(else_)], vec![])); Output::make(block) },
                        }
                    },
                    (TailType::NotTail, true, false) => {
                        if js_expr_no_side_effects(then_probe.value.as_ref().unwrap()) {
                            let else_output = lower(self, else_, continuation).into_block();
                            block.push(Statement::if_(Expression::not(predicate), else_output, vec![]));
                        } else {
                            let else_output = lower(self, else_, continuation).into_block();
                            let then_output = lower(self, then_, continuation).into_block();
                            block.push(Statement::if_(predicate, then_output, else_output));
                        }
                        Output::make(block)
                    },
                    (TailType::NotTail, false, true) => {
                        let else_output = if js_expr_no_side_effects(else_probe.value.as_ref().unwrap()) { vec![] } else { lower(self, else_, continuation).into_block() };
                        let then_output = lower(self, then_, continuation).into_block();
                        block.push(Statement::if_(predicate, then_output, else_output));
                        Output::make(block)
                    },
                    (TailType::MaybeTailIsReturn(_), true, true) => {
                        block.push(Statement::return_(Expression::cond(predicate, value(then_probe), value(else_probe))));
                        Output { block, value: None, finished: Finished::True }
                    },
                    _ => {
                        let then_output = lower(self, then_, continuation).into_block();
                        let else_output = lower(self, else_, continuation).into_block();
                        block.push(Statement::if_(predicate, then_output, else_output));
                        Output::make(block)
                    },
                }
            },
        }
    }
}
