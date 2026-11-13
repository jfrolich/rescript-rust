//! Self tail calls as loops (BACKEND_LOWERING 5.1).
use super::*;
use crate::bir::{FuncId, FuncHeader, VarSpan};

/// One function's loop state, indexed by LoopRef; parameters retain L identity.
#[derive(Clone, Copy)]
pub(super) struct Frame {
    var: VarId,
    params: VarSpan,
    triggered: bool,
}

impl State {
    /// O(1) per recursive member. The source construction fact decides whether
    /// to install a loop continuation; no body is inspected or lowered twice.
    pub(super) fn register_tail_function(&mut self, function: NodeId, var: VarId) {
        if !self.source.has_self_tail_call(function) { return; }
        let View::Fun { header, .. } = self.source.view(function) else { unreachable!() };
        let params = if self.arena.function_attributes(header).one_unit_arg {
            VarSpan::default()
        } else { self.arena.function(header).params };
        let frame = LoopRef(self.tail_frames.len() as u32);
        self.tail_frames.push(Frame { var, params, triggered: false });
        self.tail_functions.resize(self.source.nodes.len(), None);
        self.tail_functions[function.index()] = Some(frame);
    }

    /// O(1): match the callee only in the enclosing function's tail continuation.
    pub(super) fn self_call(&self, cx: Cx, callee: NodeId) -> Option<LoopRef> {
        let (Cont::Effect(Tail::Return(Ret::Named { loop_: Some(frame), .. }))
            | Cont::Value(Tail::Return(Ret::Named { loop_: Some(frame), .. }))) = cx.cont else { return None };
        matches!(self.source.view(callee), View::Var { var } if var == self.tail_frames[frame.0 as usize].var).then_some(frame)
    }

    /// O(a + p): release the sequenced callee, create copies in parameter order,
    /// and emit assignments in reverse order. Every argument reads the old
    /// iteration's bindings, not the copies being assigned.
    pub(super) fn finish_self_call(&mut self, frame: LoopRef, statements: Span, values: smallvec::SmallVec<[NodeId; 4]>) -> Probed {
        let params = self.tail_frames[frame.0 as usize].params;
        self.tail_frames[frame.0 as usize].triggered = true;
        self.tail_copies.resize(self.arena.vars.len(), None);
        let mut assignments = std::mem::take(&mut self.tail_assignments);
        for (i, value) in values.into_iter().enumerate() {
            if i == 0 || i > params.len() { self.arena.release(value); continue; }
            let param = VarId(params.start + i as u32 - 1);
            if matches!(self.arena.view(value), View::Var { var } if var == param) {
                self.arena.release(value);
                continue;
            }
            let copy = if let Some(copy) = self.tail_copies[param.index()] { copy } else {
                let name = format!("_{}", self.arena.vars.name(param).as_str());
                let copy = self.fresh_variable(&name);
                self.tail_copies[param.index()] = Some(copy);
                copy
            };
            assignments.push(crate::bir::j::assign(&mut self.arena, copy, value));
        }
        for statement in assignments.drain(..).rev() { self.statements.push(statement); }
        self.tail_assignments = assignments;
        let jump = self.arena.new_node(View::SContinue { label: None }, 0);
        self.statements.push(jump);
        Probed::Out(Out { stmts: self.statements.since(Span { start: statements.start, len: 0 }), value: None, finished: Finished::True })
    }

    /// O(p log p + s): sort only copied parameters, emit their iteration-local
    /// aliases and wrap the already-lowered body. Each statement moves once.
    pub(super) fn loop_function_body(&mut self, frame: LoopRef, header: FuncId, body: NodeId) -> NodeId {
        let frame = self.tail_frames[frame.0 as usize];
        if !frame.triggered { return body; }
        let start = self.arena.pools.function_params.len() as u32;
        let mut ordered = std::mem::take(&mut self.tail_order);
        for param in frame.params.iter() {
            let copy = self.tail_copies.get(param.index()).copied().flatten();
            self.arena.pools.function_params.push(copy.unwrap_or(param));
            if copy.is_some() { ordered.push(param); }
        }
        self.arena.pools.funcs[header.index()].params = VarSpan { start, len: frame.params.len };
        self.arena.pools.funcs[header.index()].flags |= FuncHeader::INDIRECT_PARAMS;
        ordered.sort_unstable_by(|&a, &b| {
            let vars = &self.arena.vars;
            vars.order(b).cmp(&vars.order(a))
                .then_with(|| vars.name(b).as_str().len().cmp(&vars.name(a).as_str().len()))
                .then_with(|| vars.name(b).as_str().cmp(vars.name(a).as_str()))
        });
        let mark = self.statements.mark();
        for param in ordered.drain(..) {
            let copy = self.tail_copies[param.index()].unwrap();
            let value = self.pure_expression(View::Var { var: copy }, 0);
            let statement = crate::bir::j::declare(&mut self.arena, LetKind::Alias, param, value);
            self.statements.push(statement);
        }
        self.tail_order = ordered;
        let View::SBlock { statements } = self.arena.view(body) else { unreachable!() };
        let count = statements.len();
        for i in 0..count {
            let View::SBlock { statements } = self.arena.view(body) else { unreachable!() };
            let statement = statements[i];
            self.arena.detach(statement);
            self.statements.push(statement);
        }
        self.arena.release(body);
        let list = self.statements.take_list(&mut self.arena, self.statements.since(mark));
        let body = self.arena.block_from_list(list);
        let condition = self.pure_expression(View::JBool, 1);
        let loop_ = self.arena.new_node(View::SWhile { condition, body, label: None }, 0);
        self.arena.new_node(View::SBlock { statements: &[loop_] }, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn frame_size() { assert_eq!(std::mem::size_of::<Frame>(), 16); }

    #[test]
    fn self_tail_calls_sequence_condition_and_argument_counts() {
        use crate::lambda::{arena::LamArena, ApInfo, ApplyStatus, FunctionAttribute, LamLoc};
        use crate::lambda::lam_constant::Constant;
        use crate::ident::IdentFlags;
        for shape in 0..3 {
            for argc in 0..4 {
                let mut a = LamArena::new();
                let f = Ident::new("f", 1, IdentFlags::NONE);
                let x = Ident::new("x", 2, IdentFlags::NONE);
                let y = Ident::new("y", 3, IdentFlags::NONE);
                let callee = a.var(f);
                let args: Vec<_> = (0..argc).map(|i| if i == 0 { a.var(y) } else { a.var(x) }).collect();
                let call = a.apply_raw(callee, &args, ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
                let body = match shape {
                    0 => call,
                    1 => { let head = a.const_(Constant::JsNull); a.seq_raw(head, call) },
                    _ => { let test = a.var(x); let end = a.var(y); a.if_raw(test, call, end) },
                };
                let fun = a.function_(2, &[x, y], body, FunctionAttribute::default(), LamLoc::NONE);
                let end = a.var(f);
                let root = a.letrec(&[(f, fun)], end);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

}
