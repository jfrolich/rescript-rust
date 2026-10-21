//! Nonrecursive bindings and exception continuations, direct native traversal.
use super::context::{Continuation, MaybeTail, TailType};
use super::output::{Finished, Output};
use super::*;
use crate::lambda::lam_compat::SetFieldDbgInfo;

impl IndexedJsConsumer<'_> {
    pub(super) fn let_output(
        &mut self,
        node: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Output {
        let (kind, id, value, body) = match self.context.store().view(node) {
            NodeView::Let(kind, id, value, body) => (kind, id.clone(), value, body),
            _ => panic!("let lowering requires a let node"),
        };
        if let Some(output) = self.record_spread(&id, value, body, continuation, lower) {
            return output;
        }
        let first = lower(self, value, &Continuation::Declare(kind, id));
        // compile_lambda:2010-2020 compiles both operands before append_output;
        // finished output erases JS, not the tail's compile-time side effects.
        let second = lower(self, body, continuation);
        first.append(second)
    }

    pub(super) fn sequence_output(
        &mut self,
        node: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Output {
        let (first, second) = match self.context.store().view(node) {
            NodeView::Sequence(first, second) => (first, second),
            _ => panic!("sequence lowering requires a sequence node"),
        };
        let first = lower(self, first, &Continuation::EffectCall(TailType::NotTail));
        let second = lower(self, second, continuation);
        first.append(second)
    }

    pub(super) fn try_with_output(
        &mut self,
        node: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Output {
        let (body, exception, handler) = match self.context.store().view(node) {
            NodeView::TryWith(body, exception, handler) => (body, exception.clone(), handler),
            _ => panic!("try lowering requires a try node"),
        };
        let mut block = Vec::new();
        let (handler_mode, body_mode, value) = match continuation {
            Continuation::NeedValue(_) => {
                let id = self.compiler.fresh_tmp_ident();
                block.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                }));
                (
                    Continuation::Assign(id.clone()),
                    Continuation::Assign(id.clone()),
                    Some(Expression::var(id)),
                )
            }
            Continuation::Declare(kind, id) => {
                block.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: *kind,
                    ident_info: IdentInfo::default(),
                }));
                (
                    Continuation::Assign(id.clone()),
                    Continuation::Assign(id.clone()),
                    None,
                )
            }
            Continuation::Assign(_) => (continuation.clone(), continuation.clone(), None),
            Continuation::EffectCall(tail) => {
                let body_tail = match tail {
                    TailType::MaybeTailIsReturn(_) => {
                        TailType::MaybeTailIsReturn(MaybeTail::TailInTry)
                    }
                    TailType::NotTail => TailType::NotTail,
                };
                (
                    continuation.clone(),
                    Continuation::EffectCall(body_tail),
                    None,
                )
            }
        };
        // aux's S.try_ labelled handler argument is evaluated before the body.
        let handler = lower(self, handler, &handler_mode).into_block();
        let body = lower(self, body, &body_mode).into_block();
        block.push(self.compiler.try_statement(body, &exception, handler));
        Output {
            block,
            value,
            finished: Finished::False,
        }
    }

    fn record_spread(
        &mut self,
        id: &Ident,
        value: NodeId,
        mut body: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Option<Output> {
        let (init, loc) = match self.context.store().view(value) {
            NodeView::Prim(Primitive::Pduprecord, [init], loc) => (*init, *loc),
            _ => return None,
        };
        // collect_dup_overrides, lam_compile.ml:1925-1950. This is a real
        // flattening list; only field metadata and child IDs are retained.
        let mut overrides: Vec<(SetFieldDbgInfo, NodeId)> = Vec::new();
        loop {
            match self.context.store().view(body) {
                NodeView::Var(other) if id.same(other) => break,
                NodeView::Sequence(first, rest) => {
                    match self.context.store().view(first) {
                        NodeView::Prim(Primitive::Psetfield(_, info), [target, value], _) if matches!(self.context.store().view(*target), NodeView::Var(other) if id.same(other)) =>
                        {
                            overrides.push((info.clone(), *value));
                        }
                        _ => return None,
                    }
                    body = rest;
                }
                _ => return None,
            }
        }
        let mode = Continuation::NeedValue(TailType::NotTail);
        let init = lower(self, init, &mode);
        let mut block = init.block;
        let mut props = Vec::with_capacity(overrides.len());
        for (field, value) in overrides {
            let value = lower(self, value, &mode);
            block.extend(value.block);
            props.push((
                PropertyName::Lit(field.name().to_owned()),
                value.value.expect("record override value"),
            ));
        }
        props.reverse();
        let mut expr = Expression::new(ExpressionDesc::Object(
            Some(Box::new(init.value.expect("record initializer"))),
            props,
        ));
        expr.source_loc = (self.compiler.source_loc(&loc)).map(Box::new);
        Some(Output::of_block_and_expression(continuation, block, expr))
    }
}
