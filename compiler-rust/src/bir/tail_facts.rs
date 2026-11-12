//! Construction-time tail-call candidates. Each subtree owns a bounded segment
//! of an intrusive list of callee identities; concatenation reads no body.
use super::*;
use crate::lambda::lam_primitive::Primitive;

const NONE: u32 = u32::MAX;

/// Two endpoints, not an allocated collection per source node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Candidates {
    first: u32,
    last: u32,
}
impl Default for Candidates {
    fn default() -> Self { Self { first: NONE, last: NONE } }
}

#[derive(Clone, Copy)]
pub(super) struct Candidate {
    var: VarId,
    next: u32,
}

impl Bir {
    /// O(1): read the construction fact of a recursive function.
    pub fn has_self_tail_call(&self, function: NodeId) -> bool {
        self.self_tail.get(function.index()).copied().unwrap_or(false)
    }

    /// O(1): concatenate two disjoint segments, without allocating or walking
    /// their members. The last link is deliberately outside the segment.
    fn append_tail_candidates(&mut self, into: &mut Candidates, child: NodeId) {
        let part = self.tail_candidates[child.index()];
        if part.first == NONE { return; }
        if into.first == NONE { into.first = part.first; }
        else { self.tail_calls[into.last as usize].next = part.first; }
        into.last = part.last;
    }

    /// O(d + c): d direct tail-position children, c tail-call candidates of
    /// functions bound by this LetRec. Each candidate belongs to exactly one
    /// function; construction visits it once when that binding is attached.
    /// No function body is walked. Repair also propagates a changed tail child:
    /// a callee may change while its list segment keeps the same endpoints.
    /// Cells survive node relocation, so collapsing a wrapper changes no fact.
    pub(super) fn repair_tail_candidates(&mut self, id: NodeId, changed_child: Option<NodeId>) -> bool {
        if self.js_scope.is_some() { return false; }
        self.tail_candidates.resize(self.nodes.len(), Candidates::default());
        self.self_tail.resize(self.nodes.len(), false);
        let old_self = self.self_tail[id.index()];
        // A function's bit is owned by its binding, not by its body repair.
        if self.nodes[id.index()].op() != Op::Fun { self.self_tail[id.index()] = false; }
        let old = self.tail_candidates[id.index()];
        let mut out = Candidates::default();
        let node = self.nodes[id.index()];
        let mut changed = false;
        match node.view(&self.lists) {
            View::Apply { callee, .. } => {
                if let View::Var { var } = self.nodes[callee.index()].view(&self.lists) {
                    let cell = if old.first != NONE && old.first == old.last {
                        let call = &mut self.tail_calls[old.first as usize];
                        changed = call.var != var;
                        call.var = var;
                        old.first
                    } else {
                        let cell = self.tail_calls.len() as u32;
                        self.tail_calls.push(Candidate { var, next: NONE });
                        cell
                    };
                    out = Candidates { first: cell, last: cell };
                }
            }
            View::Let { body, .. } | View::LetRec { body, .. }
            | View::Seq { second: body, .. } => self.append_tail_candidates(&mut out, body),
            View::If { then_, else_, .. } => {
                self.append_tail_candidates(&mut out, then_);
                self.append_tail_candidates(&mut out, else_);
            }
            View::Catch { body, handler, .. } => {
                self.append_tail_candidates(&mut out, body);
                self.append_tail_candidates(&mut out, handler);
            }
            View::Try { handler, .. } => self.append_tail_candidates(&mut out, handler),
            View::Prim { primitive, args } if matches!(self.primitive(primitive).primitive,
                Primitive::Psequand | Primitive::Psequor) && args.len() == 2 => {
                let right = args[1];
                self.append_tail_candidates(&mut out, right);
            }
            View::Switch { actions, .. } | View::StrSwitch { actions, .. } => {
                let len = actions.len();
                for i in 0..len {
                    let child = match node.view(&self.lists) {
                        View::Switch { actions, .. } | View::StrSwitch { actions, .. } => actions[i],
                        _ => unreachable!(),
                    };
                    self.append_tail_candidates(&mut out, child);
                }
            }
            _ => {}
        }
        self.tail_candidates[id.index()] = out;
        if let View::LetRec { first, values, .. } = node.view(&self.lists) {
            let count = values.len();
            for i in 0..count {
                let function = match node.view(&self.lists) {
                    View::LetRec { values, .. } => values[i],
                    _ => unreachable!(),
                };
                if let View::Fun { body, .. } = self.view(function) {
                    let found = self.tail_candidates_contain(body, VarId(first.0 + i as u32));
                    self.self_tail[function.index()] = found;
                }
            }
        }
        if let Some(child) = changed_child {
            changed |= match node.view(&self.lists) {
                View::Fun { body, .. } | View::Let { body, .. } | View::LetRec { body, .. }
                | View::Seq { second: body, .. } => body == child,
                View::If { then_, else_, .. } => child == then_ || child == else_,
                View::Catch { .. } => true,
                View::Try { handler, .. } => child == handler,
                View::Switch { scrutinee, .. } | View::StrSwitch { scrutinee, .. } => child != scrutinee,
                View::Prim { primitive, args } => matches!(self.primitive(primitive).primitive,
                    Primitive::Psequand | Primitive::Psequor) && args.get(1) == Some(&child),
                _ => false,
            };
        }
        old != out || changed || (old_self && node.op() != Op::Fun)
    }

    /// O(c) for c tail candidates, never the size or depth of the body. Called
    /// at a binding's construction/repair, not during lowering.
    fn tail_candidates_contain(&self, body: NodeId, target: VarId) -> bool {
        let segment = self.tail_candidates[body.index()];
        let mut cursor = segment.first;
        while cursor != NONE {
            self.visit();
            if self.tail_calls[cursor as usize].var == target { return true; }
            if cursor == segment.last { break; }
            cursor = self.tail_calls[cursor as usize].next;
        }
        false
    }

    /// Validation only: independently walk tail positions, stopping at nested
    /// functions. O(nodes in tail positions), with one reusable work vector.
    pub(super) fn validate_self_tail(&self, root: NodeId, target: VarId, work: &mut Vec<NodeId>) -> bool {
        work.clear();
        work.push(root);
        let mut found = false;
        while let Some(id) = work.pop() {
            match self.view(id) {
                View::Apply { callee, .. } => {
                    found |= matches!(self.view(callee), View::Var { var } if var == target);
                }
                View::Let { body, .. } | View::LetRec { body, .. }
                | View::Seq { second: body, .. } => work.push(body),
                View::If { then_, else_, .. } => work.extend([then_, else_]),
                View::Catch { body, handler, .. } => work.extend([body, handler]),
                View::Try { handler, .. } => work.push(handler),
                View::Switch { actions, .. } | View::StrSwitch { actions, .. } => work.extend(actions),
                View::Prim { primitive, args } if matches!(self.primitive(primitive).primitive,
                    Primitive::Psequand | Primitive::Psequor) && args.len() == 2 => work.push(args[1]),
                _ => {}
            }
        }
        found
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn candidate_size() { assert_eq!(std::mem::size_of::<Candidates>(), 8); assert_eq!(std::mem::size_of::<Candidate>(), 8); }

    #[test]
    fn construction_import_and_validation_record_only_self_tail_calls() {
        use crate::lambda::arena::LamArena;
        use crate::lambda::lam_constant::Constant;
        use crate::ident::{Ident, IdentFlags};
        for tail in [false, true] {
            let mut a = LamArena::new();
            let f = Ident::new("f", 1, IdentFlags::NONE);
            let callee = a.var(f);
            let call = a.apply_raw(callee, &[], ApInfo { status: crate::lambda::ApplyStatus::InferFull, loc: LamLoc::NONE });
            let end = a.const_(Constant::JsNull);
            let body = if tail { a.seq_raw(end, call) } else { a.seq_raw(call, end) };
            let fun = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
            let end = a.var(f);
            let root = a.letrec(&[(f, fun)], end);
            let mut imported = bridge::import_lambda(&a, root).unwrap();
            let View::LetRec { values, .. } = imported.arena.view(imported.root) else { panic!() };
            let function = values[0];
            assert_eq!(imported.arena.has_self_tail_call(function), tail);
            imported.arena.validate(Some(imported.root)).unwrap();
            imported.arena.self_tail[function.index()] = !tail;
            assert_eq!(imported.arena.validate(Some(imported.root)).unwrap_err(), "stale self-tail-call fact");
        }
    }

    #[test]
    fn ten_thousand_candidates_are_linked_without_body_walks() {
        let mut b = Bir::default();
        b.begin_bulk();
        let f = b.new_var_id(Name::new("f"), 1);
        let other = b.new_var_id(Name::new("other"), 2);
        let constant = b.intern_const(Constant::Null);
        let info = b.apply_info(ApInfo { status: crate::lambda::ApplyStatus::InferFull, loc: LamLoc::NONE });
        let callee = b.new_node(View::Var { var: f }, 0);
        let mut body = b.new_node(View::Apply { callee, args: &[], info }, 0);
        b.steps.set(0);
        for _ in 0..10_000 {
            let callee = b.new_node(View::Var { var: other }, 0);
            let then_ = b.new_node(View::Apply { callee, args: &[], info }, 0);
            let condition = b.new_node(View::Const { value: constant }, 0);
            body = b.new_node(View::If { condition, then_, else_: body }, 0);
        }
        let header = b.function_header(VarSpan::default(), FunctionAttribute::default(), LamLoc::NONE);
        let function = b.new_node(View::Fun { body, header }, 0);
        let end = b.new_node(View::Const { value: constant }, 0);
        let root = b.new_node(View::LetRec { first: f, values: &[function], body: end }, 0);
        assert!(b.has_self_tail_call(function));
        let steps = b.steps.get();
        assert!(steps < 2_000_000, "construction steps: {steps}");
        eprintln!("10,001 candidates; construction steps: {steps}");
        b.finish_bulk(root);
        b.validate(Some(root)).unwrap();
    }


    #[test]
    fn callee_edits_repair_the_binding_without_changing_list_endpoints() {
        let mut b = Bir::default();
        let f = b.new_var_id(Name::new("f"), 1);
        let g = b.new_var_id(Name::new("g"), 2);
        let info = b.apply_info(ApInfo { status: crate::lambda::ApplyStatus::InferFull, loc: LamLoc::NONE });
        let callee = b.new_node(View::Var { var: f }, 0);
        let call = b.new_node(View::Apply { callee, args: &[], info }, 0);
        let header = b.function_header(VarSpan::default(), FunctionAttribute::default(), LamLoc::NONE);
        let function = b.new_node(View::Fun { body: call, header }, 0);
        let end = b.new_node(View::Var { var: f }, 0);
        let root = b.new_node(View::LetRec { first: f, values: &[function], body: end }, 0);
        for var in [g, f, g] {
            let replacement = b.new_node(View::Var { var }, 0);
            b.replace(callee, replacement);
            assert_eq!(b.has_self_tail_call(function), var == f);
            b.validate(Some(root)).unwrap();
        }
    }

}
