//! K0 output algebra: C:89–135 BlockOutput, BACKEND_LOWERING §§1.3–1.5.
use super::{Cx, ProbeInput, Realizer};
use crate::bir::{Bir, ListId, NodeId};

/// K0: C:73 OutputFinished. Dummy is distinct from ordinary fallthrough.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Finished {
    /// All paths terminate.
    True,
    /// Ordinary fallthrough.
    False,
    /// Empty output identity.
    Dummy,
}
/// A contiguous run in StatementStack, including unfilled reserved slots.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    /// First slot.
    pub start: u32,
    /// Number of slots, including holes.
    pub len: u32,
}
impl Span {
    /// K0: C:119 append, endpoint of a run (no tree walk).
    fn end(self) -> usize {
        self.start as usize + self.len as usize
    }
}
/// K0: C:139 Compiled, also representing outputs without a value.
#[derive(Debug, PartialEq, Eq)]
pub struct Out {
    /// Statement-stack run.
    pub stmts: Span,
    /// Deferred J expression.
    pub value: Option<NodeId>,
    /// Control-flow completion.
    pub finished: Finished,
}

#[derive(Debug, PartialEq, Eq)]
enum Slot {
    Statement(NodeId),
    Held(Span),
}
/// One stack per lowering. A hole is distinct from any valid node handle.
#[derive(Default)]
pub struct StatementStack {
    slots: Vec<Option<Slot>>,
    held: Vec<NodeId>,
    /// Statements written, excluding holes.
    pub pushed: usize,
    /// Statements copied into final lists.
    pub copied: usize,
}
impl StatementStack {
    /// K0: C:89 BlockOutput::make, start an empty output at the current top.
    pub fn mark(&self) -> Span {
        Span {
            start: u32::try_from(self.slots.len()).expect("statement stack capacity"),
            len: 0,
        }
    }
    /// K0: C:89 BlockOutput::make, complete the run since a saved mark.
    pub fn since(&self, mark: Span) -> Span {
        assert!(mark.end() <= self.slots.len());
        Span {
            start: mark.start,
            len: u32::try_from(self.slots.len() - mark.start as usize)
                .expect("statement span capacity"),
        }
    }
    /// A:191 sequence_arguments: skip reserved holes without copying statements.
    pub(super) fn statements(&self, span: Span) -> impl Iterator<Item = NodeId> + '_ {
        self.slots[span.start as usize..span.end()].iter().flat_map(|s| match s {
            Some(Slot::Statement(node)) => std::slice::from_ref(node),
            Some(Slot::Held(span)) => &self.held[span.start as usize..span.end()],
            None => &[],
        }).copied()
    }
    /// A:191 sequence_arguments: a reserved hold is not an argument statement.
    pub(super) fn has_statements(&self, span: Span) -> bool {
        self.statements(span).next().is_some()
    }
    /// C:1144 compile_apply_call_inner: empty reserved holds have no output.
    pub(super) fn remove_empty(&mut self, span: Span) {
        assert_eq!(span.end(), self.slots.len());
        assert!(!self.has_statements(span));
        self.slots.truncate(span.start as usize);
    }
    /// K0: C:119 append, push a statement once.
    pub fn push(&mut self, statement: NodeId) {
        self.slots.push(Some(Slot::Statement(statement)));
        self.pushed += 1;
    }
    /// K12: C:6441 emit_multi_staticcatch_prelude; reserve before a child run.
    pub fn reserve(&mut self) -> u32 {
        let slot = self.mark().start;
        self.slots.push(None);
        slot
    }
    /// K12: C:6441 emit_multi_staticcatch_prelude; fill without moving the run.
    pub fn fill(&mut self, slot: u32, statement: NodeId) {
        let hole = &mut self.slots[slot as usize];
        assert!(hole.is_none(), "reserved slot filled twice");
        *hole = Some(Slot::Statement(statement));
        self.pushed += 1;
    }
    /// A:191 sequence_arguments: fill an argument's reserved suffix after all
    /// arguments were lowered. Held statements enter the list exactly once.
    pub(super) fn fill_held(&mut self, slot: u32, statements: Vec<NodeId>) {
        assert!(self.slots[slot as usize].is_none());
        let span = Span { start: self.held.len() as u32, len: statements.len() as u32 };
        self.pushed += statements.len();
        self.held.extend(statements);
        self.slots[slot as usize] = Some(Slot::Held(span));
    }
    /// K0: C:119 append. Both children have already been lowered, even when
    /// the first finishes. Value combination belongs to K2's expression policy.
    pub fn append(&mut self, first: Out, second: Out, value: Option<NodeId>) -> Out {
        assert_eq!(first.stmts.end(), second.stmts.start as usize);
        assert_eq!(second.stmts.end(), self.slots.len());
        if first.finished == Finished::True
            || (second.stmts.len == 0 && second.finished == Finished::Dummy)
        {
            self.slots.truncate(first.stmts.end());
            return first;
        }
        Out {
            stmts: Span {
                start: first.stmts.start,
                len: first
                    .stmts
                    .len
                    .checked_add(second.stmts.len)
                    .expect("statement span capacity"),
            },
            value,
            finished: second.finished,
        }
    }
    /// K2: C:4752 compiled_to_effect_block. Copy each non-hole directly into
    /// the child-list pool once, then pop the run. Never flatten SBlock here.
    pub fn take_list(&mut self, bir: &mut Bir, span: Span) -> ListId {
        assert_eq!(
            span.end(),
            self.slots.len(),
            "only the top run can be consumed"
        );
        let count = self.statements(span).count();
        let held = &self.held;
        let id = bir.lists.push_iter(count, self.slots.drain(span.start as usize..).flat_map(|slot| {
            let (one, span) = match slot {
                Some(Slot::Statement(node)) => (Some(node), Span::default()),
                Some(Slot::Held(span)) => (None, span),
                None => (None, Span::default()),
            };
            one.into_iter().chain(held[span.start as usize..span.end()].iter().copied())
        }));
        self.copied += count;
        id
    }
}

/// A linear ownership token: deferred combinations cannot be realized twice.
#[derive(Debug, PartialEq, Eq)]
pub struct FreeId(u32);
/// Deferred combinations of J operands. No boxed trees, no L subtree retained.
#[derive(Debug, PartialEq, Eq)]
pub enum Free {
    /// Already-lowered J expression.
    Leaf(NodeId),
    /// Deferred conditional combination.
    Cond {
        /// J condition.
        test: NodeId,
        /// True branch ownership token.
        then_: FreeId,
        /// False branch ownership token.
        else_: FreeId,
    },
    /// Deferred comma/effect combination.
    Seq {
        /// J effect expression.
        first: NodeId,
        /// Tail ownership token.
        second: FreeId,
    },
}
/// Result of one probe: deferred expression or completed output.
#[derive(Debug, PartialEq, Eq)]
pub enum Probed {
    /// Statement-free result.
    Free(FreeId),
    /// Already lowered in the requested continuation.
    Out(Out),
}
/// Typed storage for deferred combinations, consumed once.
#[derive(Default)]
pub struct FreePool {
    nodes: Vec<Option<Free>>,
    /// Combinations probed.
    pub probes: usize,
    /// Deferred nodes consumed.
    pub realized: usize,
}
impl FreePool {
    /// K1/K6: C:1529 compile_expr / C:5144 compile_if_return_output; preserve
    /// the first pass's operands rather than recompiling the source subtree.
    pub(super) fn push(&mut self, free: Free) -> FreeId {
        let id = FreeId(u32::try_from(self.nodes.len()).expect("free pool capacity"));
        self.nodes.push(Some(free));
        id
    }
    /// K1/K2/K6: C:1529 compile_expr, C:4715 append_effect_output,
    /// C:5144 compile_if_return_output. Probe one combination of already-lowered
    /// children. A non-free child is realized for cx, not lowered again.
    pub fn probe(&mut self, cx: Cx, input: ProbeInput, emit: &mut impl Realizer) -> Probed {
        self.probes += 1;
        match input {
            ProbeInput::Output(out) => {
                if out.stmts.len == 0 && out.finished == Finished::False {
                    if let Some(value) = out.value {
                        return Probed::Free(self.push(Free::Leaf(value)));
                    }
                }
                Probed::Out(out)
            }
            ProbeInput::Seq { first, second } => match second {
                Probed::Free(second) => Probed::Free(self.push(Free::Seq { first, second })),
                Probed::Out(second) => Probed::Out(emit.seq(cx, first, second)),
            },
            ProbeInput::Cond { test, then_, else_ } => match (then_, else_) {
                (Probed::Free(then_), Probed::Free(else_)) => {
                    Probed::Free(self.push(Free::Cond { test, then_, else_ }))
                }
                (then_, else_) => {
                    let then_ = self.realize(cx, then_, emit);
                    let else_ = self.realize(cx, else_, emit);
                    Probed::Out(emit.cond(cx, test, then_, else_))
                }
            },
        }
    }
    /// K2/K6: C:4715 append_effect_output / C:5144 compile_if_return_output.
    /// Explicit postorder stack: each Free is consumed once, even at depth 10k.
    pub fn realize(&mut self, cx: Cx, probed: Probed, emit: &mut impl Realizer) -> Out {
        enum Work {
            Enter(FreeId),
            Seq(NodeId),
            Cond(NodeId),
        }
        let root = match probed {
            Probed::Out(out) => return out,
            Probed::Free(root) => root,
        };
        let mut work = vec![Work::Enter(root)];
        let mut outputs = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(id) => {
                    self.realized += 1;
                    match self.nodes[id.0 as usize]
                        .take()
                        .expect("Free realized twice")
                    {
                        Free::Leaf(value) => outputs.push(emit.leaf(cx, value)),
                        Free::Seq { first, second } => {
                            work.push(Work::Seq(first));
                            work.push(Work::Enter(second));
                        }
                        Free::Cond { test, then_, else_ } => {
                            work.push(Work::Cond(test));
                            work.push(Work::Enter(else_));
                            work.push(Work::Enter(then_));
                        }
                    }
                }
                Work::Seq(first) => {
                    let second = outputs.pop().expect("sequence child");
                    outputs.push(emit.seq(cx, first, second));
                }
                Work::Cond(test) => {
                    let else_ = outputs.pop().expect("else child");
                    let then_ = outputs.pop().expect("then child");
                    outputs.push(emit.cond(cx, test, then_, else_));
                }
            }
        }
        assert_eq!(outputs.len(), 1);
        outputs.pop().expect("realized output")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn output(span: Span, value: Option<NodeId>, finished: Finished) -> Out {
        Out {
            stmts: span,
            value,
            finished,
        }
    }
    #[derive(Default)]
    struct Oracle {
        visits: Vec<u32>,
    }
    impl Realizer for Oracle {
        fn leaf(&mut self, _: Cx, value: NodeId) -> Out {
            self.visits.push(value.0);
            output(Span::default(), Some(value), Finished::False)
        }
        fn seq(&mut self, _: Cx, first: NodeId, second: Out) -> Out {
            self.visits.push(first.0);
            second
        }
        fn cond(&mut self, _: Cx, test: NodeId, then_: Out, _: Out) -> Out {
            self.visits.push(test.0);
            then_
        }
    }
    #[test]
    fn output_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<Finished>(), 1);
        assert_eq!(size_of::<Span>(), 8);
        assert_eq!(size_of::<Out>(), 20);
        assert_eq!(size_of::<FreeId>(), 4);
        assert_eq!(size_of::<Free>(), 16);
        assert_eq!(size_of::<Probed>(), 20);
        assert_eq!(size_of::<StatementStack>(), 64);
        assert_eq!(size_of::<FreePool>(), 40);
    }
    #[test]
    fn a_statement_is_copied_once() {
        let mut stack = StatementStack::default();
        let mut bir = Bir::default();
        let mark = stack.mark();
        let hole = stack.reserve();
        stack.reserve();
        for n in 0..10_000 {
            stack.push(NodeId(n));
        }
        stack.fill(hole, NodeId(10_000));
        let span = stack.since(mark);
        let list = stack.take_list(&mut bir, span);
        assert_eq!(bir.lists.get(list).len(), 10_001);
        assert_eq!(bir.lists.get(list)[0], NodeId(10_000));
        assert_eq!(stack.pushed, 10_001);
        assert_eq!(stack.copied, 10_001);
        assert_eq!(stack.mark(), Span::default());
    }
    #[test]
    fn append_finished_truncates_and_dummy_preserves() {
        let mut stack = StatementStack::default();
        stack.push(NodeId(0));
        stack.push(NodeId(1));
        let first = output(Span { start: 0, len: 1 }, None, Finished::True);
        let next = output(Span { start: 1, len: 1 }, Some(NodeId(2)), Finished::False);
        let out = stack.append(first, next, None);
        assert_eq!(out.finished, Finished::True);
        assert_eq!(stack.slots, vec![Some(Slot::Statement(NodeId(0)))]);
        let dummy = output(stack.mark(), None, Finished::Dummy);
        let out = stack.append(out, dummy, None);
        assert_eq!(out.stmts.len, 1);
    }
    #[test]
    fn append_adjacent_runs_does_not_copy() {
        let mut stack = StatementStack::default();
        stack.push(NodeId(0));
        stack.push(NodeId(1));
        let a = output(Span { start: 0, len: 1 }, None, Finished::False);
        let b = output(Span { start: 1, len: 1 }, Some(NodeId(2)), Finished::False);
        let out = stack.append(a, b, Some(NodeId(2)));
        assert_eq!(out.stmts, Span { start: 0, len: 2 });
        assert_eq!(out.value, Some(NodeId(2)));
        assert_eq!(stack.copied, 0);
    }
    #[test]
    fn ten_thousand_deferred_nodes_are_probed_and_realized_once() {
        let mut pool = FreePool::default();
        let mut oracle = Oracle::default();
        let cx = Cx::value();
        let leaf = output(Span::default(), Some(NodeId(0)), Finished::False);
        let mut probed = pool.probe(cx, ProbeInput::Output(leaf), &mut oracle);
        for n in 1..=10_000 {
            probed = pool.probe(
                cx,
                ProbeInput::Seq {
                    first: NodeId(n),
                    second: probed,
                },
                &mut oracle,
            );
        }
        assert!(oracle.visits.is_empty());
        let out = pool.realize(cx, probed, &mut oracle);
        assert_eq!(out.value, Some(NodeId(0)));
        assert_eq!(pool.probes, 10_001);
        assert_eq!(pool.realized, 10_001);
        assert_eq!(oracle.visits, (0..=10_000).collect::<Vec<_>>());
    }
    #[test]
    fn nonfree_child_is_kept_without_reprobing() {
        let mut pool = FreePool::default();
        let mut oracle = Oracle::default();
        let cx = Cx::returning();
        let leaf = output(Span::default(), Some(NodeId(1)), Finished::False);
        let then_ = pool.probe(cx, ProbeInput::Output(leaf), &mut oracle);
        let else_ = Probed::Out(output(Span { start: 0, len: 1 }, None, Finished::True));
        let result = pool.probe(
            cx,
            ProbeInput::Cond {
                test: NodeId(2),
                then_,
                else_,
            },
            &mut oracle,
        );
        assert!(matches!(result, Probed::Out(_)));
        assert_eq!(pool.probes, 2);
        assert_eq!(pool.realized, 1);
        assert_eq!(oracle.visits, vec![1, 2]);
    }
}
