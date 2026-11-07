//! Closed function and loop continuations for the mutable indexed owner.
use super::*;
use crate::lambda::DirectionFlag;
use crate::lambda::lam_compile_input::{LambdaInput, LambdaInputView};
use crate::lambda::lam_compile_main_indexed::has_free_variable;

impl IndexedJsConsumer<'_> {
    pub(super) fn function(
        &mut self,
        node: NodeId,
        return_body: &mut impl FnMut(&mut Self, NodeId) -> Block,
    ) -> Compiled {
        {
            let LambdaInputView::Function(function) =
                LambdaInput::indexed(self.context.store(), node).view()
            else {
                panic!("function lowering requires a function node")
            };
            if let Some(expr) = self
                .compiler
                .compile_eta_wrapped_runtime_alias_input(function)
            {
                return Compiled {
                    prelude: vec![],
                    expr,
                    finished: OutputFinished::False,
                };
            }
        }
        let (params, body, attr) = match self.context.store().view(node) {
            NodeView::Function(_, params, body, attr, _) => (
                if attr.one_unit_arg {
                    Vec::new()
                } else {
                    params.to_vec()
                },
                body,
                attr.clone(),
            ),
            _ => unreachable!(),
        };
        let identity =
            self.compiler
                .try_compile_identity_module_return_input(LambdaInput::indexed(
                    self.context.store(),
                    body,
                ));
        let body = if let Some(expr) = identity {
            vec![Statement::return_(expr)]
        } else {
            // compiler/core/lam_compile.ml:1840-1858: jump/loop state is local
            // to the function, while the allocation stream remains shared.
            let saved = self.compiler.enter_function_scope();
            self.compiler.return_unit_stack.push(attr.return_unit);
            let body = return_body(self, body);
            self.compiler.return_unit_stack.pop();
            self.compiler.leave_function_scope(saved);
            body
        };
        Compiled {
            prelude: vec![],
            expr: Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params,
                body,
                env: Default::default(),
                return_unit: attr.return_unit,
                async_: attr.async_,
                directive: (attr.directive).map(Box::new),
            }),
            finished: OutputFinished::False,
        }
    }

    pub(super) fn while_loop(
        &mut self,
        node: NodeId,
        value: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
        effect: &mut impl FnMut(&mut Self, NodeId) -> Block,
    ) -> Compiled {
        let (condition, body) = match self.context.store().view(node) {
            NodeView::While(condition, body) => (condition, body),
            _ => panic!("while lowering requires a while node"),
        };
        let condition = value(self, condition);
        let condition = block_with_return_expr_iife(condition.prelude, condition.expr);
        self.compiler.push_loop();
        let body = effect(self, body);
        let label = self.compiler.pop_loop();
        Compiled {
            prelude: vec![Statement::while_with_label(label, condition, body)],
            expr: Expression::undefined(true),
            finished: OutputFinished::False,
        }
    }

    pub(super) fn for_loop(
        &mut self,
        node: NodeId,
        value: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
        effect: &mut impl FnMut(&mut Self, NodeId) -> Block,
    ) -> Compiled {
        let (id, start, mut finish, direction, body) = match self.context.store().view(node) {
            NodeView::For(id, start, finish, direction, body) => {
                (*id, start, finish, direction, body)
            }
            _ => panic!("for lowering requires a for node"),
        };
        // compiler/core/lam_compile.ml:1935-1941: remove the inclusive -1
        // wrapper, retaining its child's ID.
        let direction = match direction {
            DirectionFlag::Downto => ForDirection::Downto,
            DirectionFlag::Upto => {
                let exclusive = match self.context.store().view(finish) {
                    NodeView::Prim(Primitive::Psubint, [inner, one], _)
                        if matches!(
                            self.context.store().view(*one),
                            NodeView::Const(Constant::Int { i: 1, .. })
                        ) =>
                    {
                        Some(*inner)
                    }
                    _ => None,
                };
                if let Some(inner) = exclusive {
                    finish = inner;
                    ForDirection::Up
                } else {
                    ForDirection::Upto
                }
            }
        };
        // The native tuple in compiler/core/lam_compile.ml:1268 evaluates
        // finish before start. Emitted effects below are still start/finish.
        let finish = value(self, finish);
        let start = value(self, start);
        self.compiler.push_loop();
        let body = effect(self, body);
        let label = self.compiler.pop_loop();
        let mut prelude = start.prelude;
        let init = if finish.prelude.is_empty() {
            Some(start.expr)
        } else if js_expr_no_side_effects(&start.expr) {
            prelude.extend(finish.prelude);
            Some(start.expr)
        } else {
            prelude.push(Statement::variable(VariableDeclaration {
                ident: id,
                value: Some(start.expr),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            }));
            prelude.extend(finish.prelude);
            None
        };
        prelude.push(Statement::for_range(
            label,
            init,
            finish.expr,
            id,
            direction,
            body,
        ));
        Compiled {
            prelude,
            expr: Expression::undefined(true),
            finished: OutputFinished::False,
        }
    }

    pub(super) fn for_of(
        &mut self,
        node: NodeId,
        value: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
        effect: &mut impl FnMut(&mut Self, NodeId) -> Block,
    ) -> Compiled {
        let (id, iterable, body, await_) = match self.context.store().view(node) {
            NodeView::ForOf(id, iterable, body) => (*id, iterable, body, false),
            NodeView::ForAwaitOf(id, iterable, body) => (*id, iterable, body, true),
            _ => panic!("for-of lowering requires a for-of node"),
        };
        // compiler/core/lam_compile.ml:1311-1316 / 1334-1339: allocate the
        // unused-binding placeholder BEFORE compiling the iterable. Membership
        // is Set_ident (all flags), not identity-only Hash_set_ident.
        let id = if has_free_variable(self.context.store(), body, &id) {
            id
        } else {
            self.compiler
                .fresh_ident(if await_ { "_for_await_of" } else { "_for_of" })
        };
        let iterable = value(self, iterable);
        self.compiler.push_loop();
        let body = effect(self, body);
        let label = self.compiler.pop_loop();
        let statement = if await_ {
            Statement::for_await_of(label, id, iterable.expr, body)
        } else {
            Statement::for_of(label, id, iterable.expr, body)
        };
        let mut prelude = iterable.prelude;
        prelude.push(statement);
        Compiled {
            prelude,
            expr: Expression::undefined(true),
            finished: OutputFinished::False,
        }
    }

    pub(super) fn loop_exit(&mut self, node: NodeId) -> Compiled {
        let is_break = match self.context.store().view(node) {
            NodeView::Break => true,
            NodeView::Continue => false,
            _ => panic!("loop exit lowering requires break or continue"),
        };
        assert!(
            !self.compiler.loop_stack.is_empty(),
            "loop exit outside loop"
        );
        let label =
            (self.compiler.switch_depth > 0).then(|| self.compiler.ensure_current_loop_label());
        let statement = if is_break {
            Statement::break_label(label)
        } else {
            Statement::continue_label(label)
        };
        // lam_compile.ml:1934, 1949: `break` and `continue` finish the
        // output.
        Compiled {
            prelude: vec![statement],
            expr: Expression::undefined(false),
            finished: OutputFinished::True,
        }
    }

    pub(super) fn assign(
        &mut self,
        node: NodeId,
        value: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let (id, child) = match self.context.store().view(node) {
            NodeView::Assign(id, child) => (*id, child),
            _ => panic!("assignment lowering requires an assign node"),
        };
        let compiled = value(self, child);
        let mut prelude = compiled.prelude;
        prelude.push(Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(id),
            compiled.expr,
        )));
        Compiled {
            prelude,
            expr: Expression::undefined(true),
            finished: OutputFinished::False,
        }
    }
}
