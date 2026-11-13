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
    /// A run consumed below the top: its first slot holds the run's length
    /// and every other slot 1, so a forward scan crosses the run in one step
    /// and a backward trim pops it slot by slot.
    Dead(u32),
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
    /// Holes and dead ranges crossed by `first`, `only`, `last` and `trim`.
    pub scanned: usize,
    /// Slots of explicit empty block statements, sorted by slot. An entry is
    /// stale once its slot was consumed; `drop_empty_blocks` checks the slot.
    empties: Vec<(u32, NodeId)>,
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
        let (mut at, end) = (span.start as usize, span.end());
        std::iter::from_fn(move || {
            while at < end {
                let slot = &self.slots[at];
                at += match slot {
                    Some(Slot::Dead(len)) => *len as usize,
                    _ => 1,
                };
                match slot {
                    Some(Slot::Statement(node)) => return Some(std::slice::from_ref(node)),
                    Some(Slot::Held(span)) => {
                        return Some(&self.held[span.start as usize..span.end()]);
                    }
                    Some(Slot::Dead(_)) | None => {}
                }
            }
            None
        })
        .flatten()
        .copied()
    }
    /// C:5241 try_fold_effect_only_return_tail folds a run from its end.
    /// One step per slot of the run.
    pub(super) fn statements_rev(&self, span: Span) -> impl Iterator<Item = NodeId> + '_ {
        (span.start as usize..span.end())
            .rev()
            .flat_map(|at| self.slot(at).iter().rev())
            .copied()
    }
    /// The statements of one slot: none for a hole, a dead slot or an empty hold.
    fn slot(&self, at: usize) -> &[NodeId] {
        match &self.slots[at] {
            Some(Slot::Statement(node)) => std::slice::from_ref(node),
            Some(Slot::Held(span)) => &self.held[span.start as usize..span.end()],
            Some(Slot::Dead(_)) | None => &[],
        }
    }
    /// The first slot of `[at, end)` that holds a statement. One step per
    /// hole, empty hold or dead range before it, counted in `scanned`.
    fn live(&mut self, mut at: usize, end: usize) -> Option<usize> {
        while at < end {
            if !self.slot(at).is_empty() {
                return Some(at);
            }
            self.scanned += 1;
            at += match self.slots[at] {
                Some(Slot::Dead(len)) => len as usize,
                _ => 1,
            };
        }
        None
    }
    /// B:1575 simplify_if reads the head of a branch. Costs the holes and
    /// dead ranges before the first statement; nothing is copied.
    pub(super) fn first(&mut self, span: Span) -> Option<NodeId> {
        let at = self.live(span.start as usize, span.end())?;
        Some(self.slot(at)[0])
    }
    /// First slot when it contains one statement. O(leading holes/dead ranges),
    /// using the same bounded scan as first; held multi-statement slots stay put.
    pub(super) fn first_single_slot(&mut self, span: Span) -> Option<(u32, NodeId)> {
        let at = self.live(span.start as usize, span.end())?;
        let &[statement] = self.slot(at) else { return None };
        Some((at as u32, statement))
    }
    /// B:1575 simplify_if, `[statement]` patterns: the slot and the statement
    /// when the run holds exactly one. Costs the holes and dead ranges of the
    /// run, which a trimmed run has only before its first statement.
    pub(super) fn only(&mut self, span: Span) -> Option<(u32, NodeId)> {
        let at = self.live(span.start as usize, span.end())?;
        let &[statement] = self.slot(at) else {
            return None;
        };
        let next = at + 1;
        self.live(next, span.end())
            .is_none()
            .then_some((at as u32, statement))
    }
    /// B:1575 simplify_if, `block_last_is_return_throw_or_continue`: the last
    /// statement. One step on a trimmed run; otherwise one per trailing hole
    /// or dead slot.
    pub(super) fn last(&mut self, span: Span) -> Option<NodeId> {
        let mut at = span.end();
        while at > span.start as usize {
            at -= 1;
            if let Some(&statement) = self.slot(at).last() {
                return Some(statement);
            }
            self.scanned += 1;
        }
        None
    }
    /// K0: C:119 append. Pop the holes and dead slots at the top, down to
    /// `floor`, so the run above `floor` ends in a statement or is empty.
    /// Each popped slot is popped once.
    pub(super) fn trim(&mut self, floor: Span) -> Span {
        while self.slots.len() > floor.start as usize
            && self.slot(self.slots.len() - 1).is_empty()
        {
            self.slots.pop();
            self.scanned += 1;
        }
        self.since(Span {
            start: floor.start,
            len: 0,
        })
    }
    /// K0: C:119 append. Forget a run whose statements were released or
    /// moved: the top run is popped, a run below the top becomes one dead
    /// range. One write per slot of the run.
    pub(super) fn kill(&mut self, span: Span) {
        if span.end() == self.slots.len() {
            self.slots.truncate(span.start as usize);
            return;
        }
        for slot in &mut self.slots[span.start as usize..span.end()] {
            *slot = Some(Slot::Dead(1));
        }
        if span.len > 0 {
            self.slots[span.start as usize] = Some(Slot::Dead(span.len));
        }
    }
    /// B:1225 block: record that `slot` holds an explicit empty block.
    /// A binary search and an insertion among the unit's empty blocks.
    pub(super) fn note_empty_block(&mut self, slot: u32, statement: NodeId) {
        let at = self.empties.partition_point(|&(other, _)| other < slot);
        self.empties.insert(at, (slot, statement));
    }
    /// B:1575 simplify_if drops the empty blocks of both branches first.
    /// Two binary searches among the unit's empty blocks, then one step per
    /// empty block of the run. The run itself is not scanned.
    pub(super) fn drop_empty_blocks(&mut self, bir: &mut Bir, span: Span) {
        let from = self.empties.partition_point(|&(slot, _)| slot < span.start);
        let to = self.empties.partition_point(|&(slot, _)| (slot as usize) < span.end());
        for (slot, statement) in self.empties.drain(from..to) {
            let slot = &mut self.slots[slot as usize];
            if *slot == Some(Slot::Statement(statement))
                && matches!(bir.view(statement), crate::bir::View::SBlock { statements } if statements.is_empty())
            {
                *slot = Some(Slot::Dead(1));
                bir.release(statement);
            }
        }
    }
    /// B:1565 unnest_block and C:7612 compiled_from_effect_block replace the
    /// only statement of an output. One write.
    pub(super) fn clear(&mut self, slot: u32) {
        self.slots[slot as usize] = Some(Slot::Dead(1));
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
    pub(super) fn fill_held(&mut self, slot: u32, statements: &[NodeId]) {
        assert!(self.slots[slot as usize].is_none());
        let span = Span { start: self.held.len() as u32, len: statements.len() as u32 };
        self.pushed += statements.len();
        self.held.extend_from_slice(statements);
        self.slots[slot as usize] = Some(Slot::Held(span));
    }
    /// C:3285 compile_static_raise_jump_output: an argument lowered after a
    /// later one comes before it in the output. Move the top run into the
    /// slot reserved for it. One step per slot of the run; a statement is
    /// moved once and still enters its list once.
    pub(super) fn hold_run(&mut self, slot: u32, run: Span) {
        assert_eq!(run.end(), self.slots.len());
        assert!(slot < run.start && self.slots[slot as usize].is_none());
        let start = self.held.len();
        let mut at = run.start as usize;
        while at < run.end() {
            at += match self.slots[at] {
                Some(Slot::Statement(node)) => {
                    self.held.push(node);
                    1
                }
                Some(Slot::Held(span)) => {
                    self.held.extend_from_within(span.start as usize..span.end());
                    1
                }
                Some(Slot::Dead(len)) => len as usize,
                None => 1,
            };
        }
        self.slots.truncate(run.start as usize);
        self.slots[slot as usize] = Some(Slot::Held(Span {
            start: start as u32,
            len: (self.held.len() - start) as u32,
        }));
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
    /// K2: C:4752 compiled_to_effect_block. Copy each statement of the run
    /// into the child-list pool once: one step per statement, hole and dead
    /// range of the run. The top run is popped; a run below the top becomes
    /// one dead range, so that what follows it is not moved. Never flattens
    /// SBlock here.
    pub fn take_list(&mut self, bir: &mut Bir, span: Span) -> ListId {
        if span.len == 0 {
            // An empty run holds no slot. Its start is above the top when
            // the run before it was the top and has been taken.
            return bir.lists.push_iter(0, std::iter::empty());
        }
        assert!(span.end() <= self.slots.len());
        let count = self.statements(span).count();
        let id = bir.lists.push_iter(count, self.statements(span));
        self.copied += count;
        self.kill(span);
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
            Enter(FreeId, Cx),
            Seq(NodeId, Cx),
            After(Span),
            Cond(NodeId, Cx),
        }
        let root = match probed {
            Probed::Out(out) => return out,
            Probed::Free(root) => root,
        };
        let mut work = vec![Work::Enter(root, cx)];
        let mut outputs = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(id, cx) => {
                    self.realized += 1;
                    match self.nodes[id.0 as usize]
                        .take()
                        .expect("Free realized twice")
                    {
                        Free::Leaf(value) => outputs.push(emit.leaf(cx, value)),
                        Free::Seq { first, second } => {
                            // 3.6: a comma where the value is kept; else the
                            // head as a statement before the converted tail.
                            if matches!(
                                cx.cont,
                                super::Cont::Value(_) | super::Cont::Effect(super::Tail::No)
                            ) {
                                work.push(Work::Seq(first, cx));
                            } else {
                                work.push(Work::After(emit.effect(first)));
                            }
                            work.push(Work::Enter(second, cx));
                        }
                        Free::Cond { test, then_, else_ } => {
                            work.push(Work::Cond(test, cx));
                            // 3.6: row R3 reads the branches as assignments;
                            // every other row reads their values.
                            let branch = match cx.cont {
                                super::Cont::Assign(_) => cx,
                                _ => Cx { cont: super::Cont::Value(super::Tail::No), ..cx },
                            };
                            work.push(Work::Enter(else_, branch));
                            work.push(Work::Enter(then_, branch));
                        }
                    }
                }
                Work::Seq(first, cx) => {
                    let second = outputs.pop().expect("sequence child");
                    outputs.push(emit.seq(cx, first, second));
                }
                Work::After(head) => {
                    let mut second = outputs.pop().expect("sequence child");
                    assert_eq!(head.end(), second.stmts.start as usize);
                    second.stmts = Span {
                        start: head.start,
                        len: head.len + second.stmts.len,
                    };
                    outputs.push(second);
                }
                Work::Cond(test, cx) => {
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
        fn effect(&mut self, first: NodeId) -> Span {
            self.visits.push(first.0);
            Span::default()
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
        assert_eq!(size_of::<StatementStack>(), 96);
        assert_eq!(size_of::<Option<Slot>>(), 12);
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
