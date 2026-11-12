//! Exception regions, BACKEND_LOWERING §5.5.
use super::*;

/// Dense exception-frame handle; O(1) access across child visits.
#[derive(Clone, Copy)]
pub(super) struct Try(pub u32);

/// Saved operands and completed blocks; no owned collection per source node.
pub(super) struct Plan {
    nodes: [Option<NodeId>; 3],
    blocks: [Option<NodeId>; 3],
    exception: Option<VarId>,
    start: Span,
    target: Option<VarId>,
}

impl State {
    /// C:1503 try_statement / C:3129 compile_return_output. O(1), with no
    /// inspection of the body or handler to select their form.
    pub(super) fn try_statement(&mut self, cx: Cx, body: NodeId, exception: Option<VarId>, handler: Option<NodeId>, finaliser: Option<NodeId>) -> Try {
        let start = self.statements.mark();
        let target = match cx.cont {
            Cont::Value(_) => Some((LetKind::Variable, self.fresh_variable("tmp"))),
            Cont::Declare(kind, var) => Some((kind, var)),
            _ => None,
        };
        if let Some((kind, var)) = target { self.declare_empty(kind, var); }
        let frame = Try(self.tries.len() as u32);
        self.tries.push(Plan {
            nodes: [Some(body), handler, finaliser],
            blocks: [None; 3], exception, start, target: target.map(|(_, var)| var),
        });
        frame
    }

    /// C:1512 compile_try_finally. O(1): inspect only the immediate body tag
    /// to fuse try/catch/finally, never walk a body to decide the form.
    pub(super) fn compile_try_finally(&mut self, cx: Cx, body: NodeId, finaliser: NodeId) -> Try {
        let (body, exception, handler) = match self.source.view(body) {
            View::Try { body, exception, handler } => (body, Some(exception), Some(handler)),
            _ => (body, None, None),
        };
        self.try_statement(cx, body, exception, handler, Some(finaliser))
    }

    /// C:3543 with_try_body_context. O(1); keep the handler's return policy.
    pub(super) fn try_children(&self, cx: Cx, frame: Try, into: &mut Vec<(Cx, NodeId)>) {
        let plan = &self.tries[frame.0 as usize];
        for (index, node) in plan.nodes.iter().enumerate() {
            if let Some(node) = node {
                let cont = if index == 2 {
                    Cont::Effect(Tail::No)
                } else if (index == 0 || plan.nodes[2].is_some()) && matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
                    Cont::Effect(Tail::Return(Ret::InTry))
                } else { plan.target.map(Cont::Assign).unwrap_or(cx.cont) };
                into.push((Cx { cont, ..cx }, *node));
            }
        }
    }

    /// C:2770 compile_effect_block_output / C:3129 compile_return_output.
    /// O(s) for s emitted statements, copied once into their block; no L walk.
    pub(super) fn try_child(&mut self, cx: Cx, frame: Try, index: usize, child: Probed) -> Probed {
        let mut out = self.realize(cx, child);
        if let Some(value) = out.value.take() { self.drop_pure_effect(value); }
        let span = self.statements.since(Span { start: out.stmts.start, len: 0 });
        let list = self.statements.take_list(&mut self.arena, span);
        let block = self.arena.block_from_list(list);
        self.tries[frame.0 as usize].blocks[index] = Some(block);
        Probed::Out(Out { stmts: self.statements.mark(), value: None, finished: Finished::False })
    }

    /// C:1503 try_statement. O(1): at most three block handles, no body walk.
    pub(super) fn finish_try(&mut self, cx: Cx, frame: Try) -> Probed {
        let plan = &self.tries[frame.0 as usize];
        let start = plan.start;
        let target = plan.target;
        let parts = [plan.blocks[0].unwrap(), plan.blocks[1].unwrap(), plan.blocks[2].unwrap_or(plan.blocks[0].unwrap())];
        let len = if plan.blocks[2].is_some() { 3 } else { 2 };
        let statement = self.arena.new_node(View::STry { parts: &parts[..len], exception: plan.exception }, 0);
        self.statements.push(statement);
        let value = if matches!(cx.cont, Cont::Value(_)) {
            Some(self.pure_expression(View::Var { var: target.expect("value temporary") }, 0))
        } else if matches!(cx.cont, Cont::Effect(Tail::No)) {
            Some(self.pure_expression(View::JUndefined, 0))
        } else { None };
        Probed::Out(Out { stmts: self.statements.since(start), value, finished: Finished::False })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_constant::Constant;
    use crate::ident::IdentFlags;

    #[test]
    fn try_assignment_effect_return() {
        let mut a = LamArena::new();
        let body = a.const_(Constant::Int { i: 1, comment: None });
        let handler = a.const_(Constant::Int { i: 2, comment: None });
        let root = a.try_(body, Ident::new("exn", 10, IdentFlags::NONE), handler);
        super::super::oracle_tests::compare_in_contexts(a, root, None, true, &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn finally_all_continuations() {
        for catches in [false, true] {
            let mut a = LamArena::new();
            let mut body = a.const_(Constant::Int { i: 1, comment: None });
            if catches {
                let handler = a.const_(Constant::Int { i: 2, comment: None });
                body = a.try_(body, Ident::new("exn", 10, IdentFlags::NONE), handler);
            }
            let fin = a.var(Ident::new("cleanup", 11, IdentFlags::NONE));
            let root = a.try_finally(body, fin);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn frame_sizes() {
        assert_eq!(std::mem::size_of::<Try>(), 4);
        assert_eq!(std::mem::size_of::<Plan>(), 72);
    }
}
