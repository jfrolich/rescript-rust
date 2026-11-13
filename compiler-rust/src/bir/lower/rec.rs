//! Recursive function groups (BACKEND_LOWERING 5.3).
use super::*;

/// A group's source handle and output-pool slice; no per-member allocation.
#[derive(Clone, Copy)]
pub(super) struct Group {
    node: NodeId,
    base: u32,
    start: Span,
}

impl State {
    /// O(m) for m bindings: reject value members and reserve pooled outputs.
    /// Bodies are not examined; SourceProbe lowers each function once.
    pub(super) fn recursive_group(&mut self, node: NodeId) -> Result<Group, Unsupported> {
        let View::LetRec { values, .. } = self.source.view(node) else { unreachable!() };
        for &value in values {
            if !matches!(self.source.view(value), View::Fun { .. }) {
                return Err(Unsupported("let rec"));
            }
        }
        let base = self.rec_values.len() as u32;
        self.rec_values.resize(self.rec_values.len() + values.len(), None);
        Ok(Group { node, base, start: self.statements.mark() })
    }

    /// O(m): schedule members last first, then the body in its continuation.
    pub(super) fn recursive_children(&self, cx: Cx, group: Group, into: &mut Vec<(Cx, NodeId)>) {
        let View::LetRec { values, body, .. } = self.source.view(group.node) else { unreachable!() };
        into.extend(values.iter().rev().map(|&node| (Cx::value(), node)));
        into.push((cx, body));
    }

    /// O(1) per member except the last, which emits m declarations in source
    /// order. Function values live in one shared pool across nested groups.
    pub(super) fn recursive_child(&mut self, group: Group, index: usize, child: Probed) -> Probed {
        let View::LetRec { values, first, .. } = self.source.view(group.node) else { unreachable!() };
        let count = values.len();
        if index == count { return child; }
        let out = self.realize(Cx::value(), child);
        assert!(!self.statements.has_statements(out.stmts));
        self.rec_values[group.base as usize + count - 1 - index] = out.value;
        if index + 1 == count {
            for i in 0..count {
                let value = self.rec_values[group.base as usize + i].take().expect("recursive function value");
                let var = VarId(first.0 + i as u32);
                let declaration = super::super::j::declare(&mut self.arena, LetKind::Alias, var, value);
                self.statements.push(declaration);
            }
        }
        Probed::Out(Out { value: None, ..out })
    }

    /// O(m) to consume the completed member outputs; the declarations precede the body's already contiguous run.
    pub(super) fn finish_recursive(&mut self, cx: Cx, group: Group, children: impl Iterator<Item = Probed>) -> Probed {
        let body = children.last().expect("recursive body");
        let mut out = self.realize(cx, body);
        out.stmts = self.statements.since(group.start);
        self.rec_values.truncate(group.base as usize);
        Probed::Out(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{arena::LamArena, ApInfo, ApplyStatus, FunctionAttribute, LamLoc};
    use crate::lambda::lam_constant::Constant;

    #[test]
    fn group_size() { assert_eq!(std::mem::size_of::<Group>(), 16); }

    #[test]
    fn recursive_function_groups_in_every_continuation() {
        for mutual in [false, true] {
            let mut a = LamArena::new();
            let f = Ident::new("f", 1, IdentFlags::NONE);
            let g = Ident::new("g", 2, IdentFlags::NONE);
            let mut bindings = Vec::new();
            for (name, callee) in if mutual { vec![(f, g), (g, f)] } else { vec![(f, f)] } {
                let callee = a.var(callee);
                let call = a.apply_raw(callee, &[], ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
                let end = a.const_(Constant::JsNull);
                let body = a.seq_raw(call, end);
                let fun = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
                bindings.push((name, fun));
            }
            let body = a.var(f);
            let root = a.letrec(&bindings, body);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_members_are_lowered_once() {
        let mut a = LamArena::new();
        let mut bindings = Vec::with_capacity(10_000);
        for i in 0..10_000 {
            let id = Ident::new("member", i + 1, IdentFlags::NONE);
            let body = a.const_(Constant::JsNull);
            let function = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
            bindings.push((id, function));
        }
        let body = a.const_(Constant::JsNull);
        let root = a.letrec(&bindings, body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 20_002);
        let lowered = state.complete(Cx::value(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

}
