//! K0 output algebra: C:89–135 BlockOutput, BACKEND_LOWERING §§1.3–1.5.
use super::js::{Js, Pools};
use super::js_stmt::JsStmt;
use super::{Cx, Realizer};

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
pub struct Out<B: Js> {
    /// Statement-stack run.
    pub stmts: Span,
    /// Deferred J expression.
    pub value: Option<B::E>,
    /// Control-flow completion.
    pub finished: Finished,
}

#[derive(Debug, PartialEq, Eq)]
enum Slot<S> {
    Statement(S),
    Held(Span),
    /// A run consumed below the top: its first slot holds the run's length
    /// and every slot after it 1 (the last is a `DeadEnd` when the run has
    /// more than one slot), so a forward scan crosses the run in one step.
    Dead(u32),
    /// The last slot of such a run of more than one slot, with the run's
    /// length: a read from the end and a trim cross the run in one step.
    /// A forward scan does not reach it (it enters the run at its first
    /// slot) and counts it as one slot if it does. The length is right for
    /// as long as the slot is there: nothing writes a statement into a
    /// dead slot (a fill and a hold assert a hole, a take of a dead slot
    /// panics), a later `kill` over part of the run writes dead slots
    /// only, and a truncation that cuts the run removes this slot first.
    DeadEnd(u32),
}
/// One stack per lowering. A hole is distinct from any statement. The slots
/// own the statement handles of the runs (THREE_TREES 11.4, "T6x-a: the
/// statement stack, after the probe").
pub struct StatementStack<B: JsStmt> {
    slots: Vec<Option<Slot<B::S>>>,
    /// Held statements; one that was moved out leaves `None`.
    held: Vec<Option<B::S>>,
    /// Statements written, excluding holes.
    pub pushed: usize,
    /// Statements copied into final lists.
    pub copied: usize,
    /// Holes and dead ranges crossed by `first`, `only`, `last` and `trim`.
    pub scanned: usize,
    /// Slots of explicit empty block statements with the `JsStmt::stmt_id`
    /// of each, sorted by slot. An entry is stale once its slot was
    /// consumed; `drop_empty_blocks` checks the slot and the id.
    empties: Vec<(u32, u32)>,
}
impl<B: JsStmt> Default for StatementStack<B> {
    /// An empty stack without capacity. O(1); allocates nothing.
    fn default() -> Self {
        Self { slots: Vec::new(), held: Vec::new(), pushed: 0, copied: 0, scanned: 0, empties: Vec::new() }
    }
}
impl<B: JsStmt> StatementStack<B> {
    /// Reserve statement and hole slots from the imported output-node estimate.
    /// Cost: Reserves O(N) statement/hole slots for the imported output estimate N; no
    /// statements are visited or initialized.
    pub(super) fn with_capacity(slots: usize) -> Self {
        Self { slots: Vec::with_capacity(slots), ..Self::default() }
    }

    #[cfg(test)]
    pub(super) fn reserve_repeat(&mut self) { self.held.reserve(self.held.len()); }

    #[cfg(test)]
    pub(super) fn capacities(&self) -> [usize; 3] {
        [self.slots.capacity(), self.held.capacity(), self.empties.capacity()]
    }

    /// K0: C:89 BlockOutput::make, start an empty output at the current top.
    /// O(1).
    pub fn mark(&self) -> Span {
        Span {
            start: u32::try_from(self.slots.len()).expect("statement stack capacity"),
            len: 0,
        }
    }
    /// K0: C:89 BlockOutput::make, complete the run since a saved mark. O(1).
    pub fn since(&self, mark: Span) -> Span {
        assert!(mark.end() <= self.slots.len());
        Span {
            start: mark.start,
            len: u32::try_from(self.slots.len() - mark.start as usize)
                .expect("statement span capacity"),
        }
    }
    /// The statements of a run, read in place, in order. Cost: O(slots of
    /// the run + held statements): one step per slot, a dead range crossed
    /// in one, and one per held statement.
    pub(super) fn statement_refs(&self, span: Span) -> impl Iterator<Item = &B::S> + '_ {
        self.placed_refs(span).map(|(_, s)| s)
    }
    /// `statement_refs` with the place of each statement: its slot, or its
    /// index among the held statements with [`StatementStack::HELD`] set.
    /// A place names its statement for `at_place` and `at_place_mut` until
    /// the run is taken or killed: nothing moves a statement of a run that
    /// is complete, and no function takes a statement out by its place, so
    /// the invariant of `Slot::DeadEnd` and the holds are as they were.
    /// Cost: that of `statement_refs`, O(slots of the run + held
    /// statements): one step per slot, a dead range crossed in one, and
    /// one per held statement. (THREE_TREES 11.4, "T6x-e and T6x-f: the
    /// fold reads where its rows are", decision 5: `export.rs::build_rows`
    /// keeps the place of each row of the top level.)
    pub(super) fn placed_refs(&self, span: Span) -> impl Iterator<Item = (u32, &B::S)> + '_ {
        let (mut at, end) = (span.start as usize, span.end());
        let (mut inner, mut inner_end) = (0usize, 0usize);
        std::iter::from_fn(move || loop {
            if inner < inner_end {
                inner += 1;
                let s = self.held[inner - 1].as_ref().expect("held statement");
                return Some((Self::HELD | (inner - 1) as u32, s));
            }
            if at >= end {
                return None;
            }
            let current = at;
            let slot = &self.slots[at];
            at += match slot {
                Some(Slot::Dead(len)) => *len as usize,
                _ => 1,
            };
            debug_assert!(current < Self::HELD as usize, "a slot beyond the places of a stack");
            match slot {
                Some(Slot::Statement(s)) => return Some((current as u32, s)),
                Some(Slot::Held(span)) => (inner, inner_end) = (span.start as usize, span.end()),
                Some(Slot::Dead(_) | Slot::DeadEnd(_)) | None => {}
            }
        })
    }
    /// The bit of a place (`placed_refs`) that names a held statement. A
    /// stack has fewer than 2^31 slots and holds fewer than 2^31
    /// statements (`mark` and `fill_held_since` count both in 32 bits and
    /// a statement is at least 4 bytes).
    pub(super) const HELD: u32 = 1 << 31;
    /// The statement at `place`, read in place. O(1). Panics when the
    /// place holds no statement. (Slice T6x-e3 removes the attribute with
    /// its first caller in `export.rs`.)
    #[cfg(test)]
    pub(super) fn at_place(&self, place: u32) -> &B::S {
        if place & Self::HELD != 0 {
            return self.held[(place & !Self::HELD) as usize].as_ref().expect("held statement");
        }
        match &self.slots[place as usize] {
            Some(Slot::Statement(s)) => s,
            _ => panic!("place {place} holds no statement"),
        }
    }
    /// `at_place`, lent to be read through a function that takes the
    /// statement mutably (`JsStmt::lend_block_stmt`, `JsStmt::substitute`,
    /// `JsStmt::take_block_stmt` of a block). The statement stays at its
    /// place: nothing is written into the slot. O(1). (Slice T6x-e3
    /// removes the attribute with its first caller in `export.rs`.)
    #[cfg(test)]
    pub(super) fn at_place_mut(&mut self, place: u32) -> &mut B::S {
        if place & Self::HELD != 0 {
            return self.held[(place & !Self::HELD) as usize].as_mut().expect("held statement");
        }
        match &mut self.slots[place as usize] {
            Some(Slot::Statement(s)) => s,
            _ => panic!("place {place} holds no statement"),
        }
    }
    /// The statement at `place` moved out, to the caller, who owns it from
    /// here. A slot is left `Dead(1)`, as `take` leaves it, and the run
    /// gives nothing for it afterwards. A held statement cannot leave its
    /// hold (the hold's span counts it, and every function that reads or
    /// takes a hold expects each of its entries): it is exchanged for what
    /// `stand_in` makes, which the run gives in its stead when it is taken
    /// and which the caller of `take_run` releases. `stand_in` is called
    /// for a held statement only. The other places of the run stay valid.
    /// O(1): one write; counts no step and allocates nothing. Panics when
    /// the place holds no statement. (THREE_TREES 11.4, "T6x-e and T6x-f:
    /// the fold reads where its rows are", decision 13:
    /// `export.rs::release_row`, a removed row of the top level. Slice
    /// T6x-e3 removes the attribute with that caller.)
    #[cfg(test)]
    pub(super) fn take_placed(&mut self, place: u32, stand_in: impl FnOnce() -> B::S) -> B::S {
        if place & Self::HELD != 0 {
            let held = self.held[(place & !Self::HELD) as usize].as_mut().expect("held statement");
            return std::mem::replace(held, stand_in());
        }
        match self.slots[place as usize].replace(Slot::Dead(1)) {
            Some(Slot::Statement(s)) => s,
            _ => panic!("place {place} holds no statement"),
        }
    }
    /// The statements of a run moved out of their slots, in order; a slot
    /// or a hold that gave its statements is left a hole, and the caller
    /// kills the run. Cost: O(slots of the run + held statements), each
    /// statement moved once.
    pub(super) fn take_run(&mut self, span: Span) -> impl Iterator<Item = B::S> + '_ {
        let (mut at, end) = (span.start as usize, span.end());
        let (mut inner, mut inner_end) = (0usize, 0usize);
        std::iter::from_fn(move || loop {
            if inner < inner_end {
                inner += 1;
                return Some(self.held[inner - 1].take().expect("held statement"));
            }
            if at >= end {
                return None;
            }
            let current = at;
            at += match self.slots[current] {
                Some(Slot::Dead(len)) => len as usize,
                _ => 1,
            };
            match self.slots[current].take() {
                Some(Slot::Statement(s)) => return Some(s),
                Some(Slot::Held(span)) => (inner, inner_end) = (span.start as usize, span.end()),
                other => self.slots[current] = other,
            }
        })
    }
    /// C:5241 try_fold_effect_only_return_tail folds a run from its end:
    /// the statements of a run moved out, last first; a slot or a hold that
    /// gave its statements is left a hole, and the caller kills the run.
    /// Cost: O(slots of the run + held statements), one step per slot and
    /// per held statement, a dead range crossed in one, each statement
    /// moved once.
    pub(super) fn take_run_rev(&mut self, span: Span) -> impl Iterator<Item = B::S> + '_ {
        let (start, mut at) = (span.start as usize, span.end());
        let (mut inner_start, mut inner) = (0usize, 0usize);
        std::iter::from_fn(move || loop {
            if inner > inner_start {
                inner -= 1;
                return Some(self.held[inner].take().expect("held statement"));
            }
            if at <= start {
                return None;
            }
            at -= 1;
            match self.slots[at].take() {
                Some(Slot::Statement(s)) => return Some(s),
                Some(Slot::Held(span)) => (inner_start, inner) = (span.start as usize, span.end()),
                other => {
                    let range = Self::dead_end(&other);
                    self.slots[at] = other;
                    at = (at + 1).saturating_sub(range).max(start);
                }
            }
        })
    }
    /// The slots a read from the end crosses at `slot`: the length of the
    /// dead range that ends there, one for any other slot. O(1).
    fn dead_end(slot: &Option<Slot<B::S>>) -> usize {
        match slot {
            Some(Slot::DeadEnd(len)) => *len as usize,
            _ => 1,
        }
    }
    /// The number of statements of one slot: none for a hole, a dead slot or
    /// an empty hold. O(1).
    fn slot_len(&self, at: usize) -> usize {
        match &self.slots[at] {
            Some(Slot::Statement(_)) => 1,
            Some(Slot::Held(span)) => span.len as usize,
            Some(Slot::Dead(_) | Slot::DeadEnd(_)) | None => 0,
        }
    }
    /// Statement `index` of slot `at`, which holds more than `index`
    /// statements, read in place. O(1).
    fn slot_ref(&self, at: usize, index: usize) -> &B::S {
        match &self.slots[at] {
            Some(Slot::Statement(s)) => s,
            Some(Slot::Held(span)) => {
                self.held[span.start as usize + index].as_ref().expect("held statement")
            }
            Some(Slot::Dead(_) | Slot::DeadEnd(_)) | None => unreachable!("a slot without a statement"),
        }
    }
    /// The first slot of `[at, end)` that holds a statement. One step per
    /// hole, empty hold or dead range before it, counted in `scanned`.
    fn live(&mut self, mut at: usize, end: usize) -> Option<usize> {
        while at < end {
            if self.slot_len(at) != 0 {
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
    /// The statement of a slot that holds one, read in place: a statement
    /// slot or a hold of exactly one, the slots `only` and
    /// `first_single_slot` give. O(1). Panics on any other slot.
    pub(super) fn at(&self, slot: u32) -> &B::S {
        assert!(self.slot_len(slot as usize) == 1, "slot {slot} holds no single statement");
        self.slot_ref(slot as usize, 0)
    }
    /// B:1565 unnest_block and C:7612 compiled_from_effect_block replace the
    /// only statement of an output: the statement of a slot that holds one,
    /// moved out; the slot becomes `Dead(1)`. A hold of exactly one
    /// statement is such a slot (`only` and `first_single_slot` give it),
    /// and its statement is moved out of the hold. O(1): one write, two
    /// for a hold. Panics on any other slot.
    pub(super) fn take(&mut self, slot: u32) -> B::S {
        match self.slots[slot as usize].replace(Slot::Dead(1)) {
            Some(Slot::Statement(s)) => s,
            Some(Slot::Held(span)) if span.len == 1 => {
                self.held[span.start as usize].take().expect("held statement")
            }
            _ => panic!("slot {slot} holds no single statement"),
        }
    }
    /// The first statement of a slot that holds one or a hold that is not
    /// empty, read in place. O(1).
    pub(super) fn head(&self, slot: u32) -> &B::S {
        self.slot_ref(slot as usize, 0)
    }
    /// `head`, to be changed in place (`JsStmt::locate_stmt`). O(1).
    pub(super) fn head_mut(&mut self, slot: u32) -> &mut B::S {
        match &mut self.slots[slot as usize] {
            Some(Slot::Statement(s)) => s,
            Some(Slot::Held(span)) => self.held[span.start as usize].as_mut().expect("held statement"),
            Some(Slot::Dead(_) | Slot::DeadEnd(_)) | None => unreachable!("a slot without a statement"),
        }
    }
    /// B:1575 simplify_if reads the head of a branch, in place. Costs the
    /// holes and dead ranges before the first statement, one step each;
    /// nothing is copied.
    pub(super) fn first(&mut self, span: Span) -> Option<&B::S> {
        let at = self.live(span.start as usize, span.end())?;
        Some(self.slot_ref(at, 0))
    }
    /// The slot of the first statement of a run, as `first` finds it. Costs
    /// the holes and dead ranges before it, one step each.
    pub(super) fn first_slot(&mut self, span: Span) -> Option<u32> {
        self.live(span.start as usize, span.end()).map(|at| at as u32)
    }
    /// First slot when it contains one statement, with that statement read
    /// in place. O(leading holes/dead ranges), using the same bounded scan
    /// as first; held multi-statement slots stay put.
    pub(super) fn first_single_slot(&mut self, span: Span) -> Option<(u32, &B::S)> {
        let at = self.live(span.start as usize, span.end())?;
        if self.slot_len(at) != 1 {
            return None;
        }
        Some((at as u32, self.slot_ref(at, 0)))
    }
    /// B:1575 simplify_if, `[statement]` patterns: the slot and the statement
    /// read in place when the run holds exactly one. Costs the holes and
    /// dead ranges of the run, one step each, which a trimmed run has only
    /// before its first statement.
    pub(super) fn only(&mut self, span: Span) -> Option<(u32, &B::S)> {
        let at = self.live(span.start as usize, span.end())?;
        if self.slot_len(at) != 1 || self.live(at + 1, span.end()).is_some() {
            return None;
        }
        Some((at as u32, self.slot_ref(at, 0)))
    }
    /// The slot of the last statement of a run and its index in the slot.
    /// One step on a trimmed run; otherwise one per trailing hole, empty
    /// hold or dead range, counted in `scanned`: a dead range is crossed
    /// from its last slot in one step, whatever its length.
    fn last_at(&mut self, span: Span) -> Option<(usize, usize)> {
        let start = span.start as usize;
        let mut at = span.end();
        while at > start {
            at -= 1;
            let len = self.slot_len(at);
            if len != 0 {
                return Some((at, len - 1));
            }
            self.scanned += 1;
            at = (at + 1).saturating_sub(Self::dead_end(&self.slots[at])).max(start);
        }
        None
    }
    /// B:1575 simplify_if, `block_last_is_return_throw_or_continue`: the last
    /// statement, read in place. One step on a trimmed run; otherwise one
    /// per trailing hole or dead range.
    pub(super) fn last(&mut self, span: Span) -> Option<&B::S> {
        let (at, index) = self.last_at(span)?;
        Some(self.slot_ref(at, index))
    }
    /// The slot of the last statement of a run, as `last` finds it. Cost:
    /// O(1) on a trimmed run; otherwise one step per trailing hole or dead
    /// range.
    pub(super) fn last_slot(&mut self, span: Span) -> Option<u32> {
        self.last_at(span).map(|(at, _)| at as u32)
    }
    /// K0: C:119 append. Pop the holes and dead ranges at the top, down to
    /// `floor`, so the run above `floor` ends in a statement or is empty.
    /// One step per popped hole and per popped dead range, which goes in
    /// one truncation whatever its length; each is popped once.
    pub(super) fn trim(&mut self, floor: Span) -> Span {
        let floor_at = floor.start as usize;
        while self.slots.len() > floor_at && self.slot_len(self.slots.len() - 1) == 0 {
            let top = self.slots.len();
            let range = Self::dead_end(&self.slots[top - 1]);
            self.slots.truncate(top.saturating_sub(range).max(floor_at));
            self.scanned += 1;
        }
        self.since(Span {
            start: floor.start,
            len: 0,
        })
    }
    /// K0: C:119 append. Forget a run whose statements were released or
    /// moved: the top run is popped, a run below the top becomes one dead
    /// range, marked at both ends with its length. One write per slot of
    /// the run.
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
        if span.len > 1 {
            self.slots[span.end() - 1] = Some(Slot::DeadEnd(span.len));
        }
    }
    /// B:1225 block: record that `slot` holds an explicit empty block whose
    /// `JsStmt::stmt_id` is `id`, read by the caller before the block was
    /// pushed or filled. Cost: O(log E) for a binary search among the
    /// unit's E noted empty blocks, and an insertion that moves the entries
    /// after its place: O(E) in the worst case, nothing for a block noted
    /// above every other (the common case, a block at the top of the stack).
    pub(super) fn note_empty_block(&mut self, slot: u32, id: u32) {
        let at = self.empties.partition_point(|&(other, _)| other < slot);
        self.empties.insert(at, (slot, id));
    }
    /// B:1575 simplify_if drops the empty blocks of both branches first.
    /// Cost: two binary searches among the unit's E noted empty blocks, then
    /// one step per empty block of the run, each read through
    /// `JsStmt::stmt_id` and released through `JsStmt::release_stmt`, and
    /// the drain that moves the entries after the run's: O(E) in the worst
    /// case, nothing when the run's are the last. The run itself is not
    /// scanned.
    pub(super) fn drop_empty_blocks(&mut self, js: &mut B, a: &mut Pools, span: Span) {
        let from = self.empties.partition_point(|&(slot, _)| slot < span.start);
        let to = self.empties.partition_point(|&(slot, _)| (slot as usize) < span.end());
        for (slot, id) in self.empties.drain(from..to) {
            let slot = &mut self.slots[slot as usize];
            let Some(Slot::Statement(held)) = slot else { continue };
            if js.stmt_id(a, held) == id && js.is_empty_block(a, held) {
                let Some(Slot::Statement(held)) = slot.replace(Slot::Dead(1)) else {
                    unreachable!("a statement slot")
                };
                js.release_stmt(a, held);
            }
        }
    }
    /// A:191 sequence_arguments: a reserved hold is not an argument
    /// statement. O(holes and dead ranges before the first statement).
    pub(super) fn has_statements(&self, span: Span) -> bool {
        self.statement_refs(span).next().is_some()
    }
    /// C:1144 compile_apply_call_inner: empty reserved holds have no output.
    /// O(slots of the run).
    pub(super) fn remove_empty(&mut self, span: Span) {
        assert_eq!(span.end(), self.slots.len());
        assert!(!self.has_statements(span));
        self.slots.truncate(span.start as usize);
    }
    /// K0: C:119 append, push a statement once. One write.
    pub fn push(&mut self, statement: B::S) {
        self.slots.push(Some(Slot::Statement(statement)));
        self.pushed += 1;
    }
    /// K12: C:6441 emit_multi_staticcatch_prelude; reserve before a child
    /// run. One write.
    pub fn reserve(&mut self) -> u32 {
        let slot = self.mark().start;
        self.slots.push(None);
        slot
    }
    /// K12: C:6441 emit_multi_staticcatch_prelude; fill without moving the
    /// run. One write.
    pub fn fill(&mut self, slot: u32, statement: B::S) {
        let hole = &mut self.slots[slot as usize];
        assert!(hole.is_none(), "reserved slot filled twice");
        *hole = Some(Slot::Statement(statement));
        self.pushed += 1;
    }
    /// A:191 sequence_arguments: fill an argument's reserved suffix after all
    /// arguments were lowered. Held statements enter the list exactly once.
    /// Cost: one step per statement, each moved once.
    pub(super) fn fill_held(&mut self, slot: u32, statements: impl IntoIterator<Item = B::S>) {
        let mark = self.held_mark();
        self.held.extend(statements.into_iter().map(Some));
        self.fill_held_since(slot, mark);
    }
    /// Where the statements given to `hold` start: a mark for
    /// `fill_held_since`. O(1).
    pub(super) fn held_mark(&self) -> usize {
        self.held.len()
    }
    /// One statement for the hold `fill_held_since` places. O(1).
    pub(super) fn hold(&mut self, statement: B::S) {
        self.held.push(Some(statement));
    }
    /// `fill_held` with the statements given to `hold` since
    /// `mark`. O(1).
    pub(super) fn fill_held_since(&mut self, slot: u32, mark: usize) {
        assert!(self.slots[slot as usize].is_none());
        let len = self.held.len() - mark;
        self.pushed += len;
        self.slots[slot as usize] = Some(Slot::Held(Span { start: mark as u32, len: len as u32 }));
    }
    /// C:3285 compile_static_raise_jump_output: an argument lowered after a
    /// later one comes before it in the output. Move the top run into the
    /// slot reserved for it. Cost: one step per slot of the run and per
    /// statement of a hold inside it; a statement is moved once and still
    /// enters its list once.
    pub(super) fn hold_run(&mut self, slot: u32, run: Span) {
        assert_eq!(run.end(), self.slots.len());
        assert!(slot < run.start && self.slots[slot as usize].is_none());
        let start = self.held.len();
        let mut at = run.start as usize;
        while at < run.end() {
            at += match self.slots[at].take() {
                Some(Slot::Statement(statement)) => {
                    self.held.push(Some(statement));
                    1
                }
                Some(Slot::Held(span)) => {
                    for i in span.start as usize..span.end() {
                        let statement = self.held[i].take();
                        self.held.push(statement);
                    }
                    1
                }
                Some(Slot::Dead(len)) => len as usize,
                Some(Slot::DeadEnd(_)) | None => 1,
            };
        }
        self.slots.truncate(run.start as usize);
        self.slots[slot as usize] = Some(Slot::Held(Span {
            start: start as u32,
            len: (self.held.len() - start) as u32,
        }));
    }
    /// K0: C:119 append. Both children have already been lowered, even when
    /// the first finishes. Value combination belongs to K2's expression
    /// policy. O(1), and one write per slot of the second run when a
    /// finished first run pops it.
    pub fn append(&mut self, first: Out<B>, second: Out<B>, value: Option<B::E>) -> Out<B> {
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
    /// K2: C:4752 compiled_to_effect_block. Move each statement of the run
    /// into a list in flight once ([`JsStmt::list`]): one step per
    /// statement, hole and dead range of the run to count them, and one per
    /// slot and statement to move them. The top run is popped; a run below
    /// the top becomes one dead range, so that what follows it is not
    /// moved. Never flattens SBlock here. The list is closed
    /// (`close::decide`: one more step per statement) when the arena counts
    /// JavaScript occurrences.
    pub fn take_list(&mut self, js: &mut B, a: &mut Pools, span: Span) -> B::L {
        let list = self.take_actions(js, a, span);
        self.close(js, a, list);
        list
    }
    /// The actions of a switch, pushed or filled above the runs
    /// they were made from, as one list: `take_list` without the
    /// close. An action is a block, and `close::decide` reads
    /// `return`s and declarations only. One step per slot of the
    /// run and per statement, each moved once.
    pub(super) fn take_actions(&mut self, js: &mut B, a: &mut Pools, span: Span) -> B::L {
        if span.len == 0 {
            // An empty run holds no slot. Its start is above the top when
            // the run before it was the top and has been taken.
            return js.list(a, 0, std::iter::empty());
        }
        assert!(span.end() <= self.slots.len());
        let count = self.statement_refs(span).count();
        let list = js.list(a, count as u32, self.take_run(span));
        self.copied += count;
        self.kill(span);
        list
    }
    /// THREE_TREES 11.4, step A: decide the declarations of a copied list.
    /// Cost: that of `close::decide`; nothing on an arena without counts.
    pub(super) fn close(&mut self, js: &B, a: &mut Pools, list: B::L) {
        if a.js_scope.is_some() {
            super::close::decide(js, a, list);
        }
    }
}

#[cfg(test)]
impl StatementStack<crate::bir::j::rows::Rows> {
    /// The rows of the statements of a run. One step per
    /// slot of the run.
    pub(super) fn statements(&self, span: Span) -> impl Iterator<Item = crate::bir::NodeId> + '_ {
        self.statement_refs(span).map(|s| s.row())
    }
}

/// For the tests: the row of an output's value on rows. O(1).
#[cfg(test)]
pub(super) fn row(value: <crate::bir::j::rows::Rows as Js>::E) -> crate::bir::NodeId {
    crate::bir::j::rows::Rows::node(value)
}
/// For the tests: an output's value on rows from its row. O(1).
#[cfg(test)]
pub(super) fn of_row(node: crate::bir::NodeId) -> <crate::bir::j::rows::Rows as Js>::E {
    crate::bir::j::rows::Rows::from_node(node)
}

/// For the tests: the row of an output's value on rows, read in place. O(1).
#[cfg(test)]
pub(super) fn row_of(a: &Pools, value: &<crate::bir::j::rows::Rows as Js>::E) -> crate::bir::NodeId {
    let rows = crate::bir::j::rows::Rows::default();
    crate::bir::NodeId(rows.id(a, crate::bir::j::rows::Rows::of(value)))
}

/// The stack's runs for `JsStmt::if_head`: a run is a span of slots, and a
/// branch that is kept stays where it was lowered.
impl<B: JsStmt> super::js_stmt::Runs<B> for StatementStack<B> {
    type Run = Span;
    /// `drop_empty_blocks`: two binary searches, one step per noted empty
    /// block of the run, and the drain that moves the entries noted after
    /// the run's: O(E) for the unit's E noted empty blocks in the worst
    /// case, nothing when the run's are the last.
    fn trim(&mut self, js: &mut B, a: &mut Pools, run: Span) {
        self.drop_empty_blocks(js, a, run);
    }
    /// A span of no slot. O(1).
    fn empty(&mut self) -> Span {
        Span::default()
    }
    /// The stack's `last`: O(1) on a run that ends in a statement, else one
    /// step per trailing hole, empty hold or dead range.
    fn last(&mut self, run: Span) -> Option<&B::S> {
        StatementStack::last(self, run)
    }
    /// The statement of the stack's `only`: the holes and dead ranges of the
    /// run, one step each.
    fn only(&mut self, run: Span) -> Option<&B::S> {
        StatementStack::only(self, run).map(|(_, statement)| statement)
    }
    /// Each statement moved out with `take_run` and released
    /// (`JsStmt::release_stmt`), then the run killed: one step per slot and
    /// per node released, one write per slot.
    fn release(&mut self, js: &mut B, a: &mut Pools, run: Span) {
        for statement in self.take_run(run) {
            js.release_stmt(a, statement);
        }
        self.kill(run);
    }
    /// `take_list`: one step per slot and per statement, each moved once,
    /// and the list closed (`close::decide`: one more step per statement)
    /// when the arena counts JavaScript occurrences.
    fn take(&mut self, js: &mut B, a: &mut Pools, run: Span) -> B::L {
        self.take_list(js, a, run)
    }
}

/// A linear ownership token: deferred combinations cannot be realized twice.
#[derive(Debug, PartialEq, Eq)]
pub struct FreeId(u32);
/// Deferred combinations of J operands. No boxed trees, no L subtree retained.
pub enum Free<B: Js> {
    /// Already-lowered J expression.
    Leaf(B::E),
    /// Deferred conditional combination.
    Cond {
        /// J condition.
        test: B::E,
        /// True branch ownership token.
        then_: FreeId,
        /// False branch ownership token.
        else_: FreeId,
    },
    /// Deferred comma/effect combination.
    Seq {
        /// J effect expression.
        first: B::E,
        /// Tail ownership token.
        second: FreeId,
    },
}
/// Result of one probe: deferred expression or completed output.
pub enum Probed<B: Js> {
    /// Statement-free result.
    Free(FreeId),
    /// Already lowered in the requested continuation.
    Out(Out<B>),
}
/// Typed storage for deferred combinations, consumed once.
pub struct FreePool<B: Js> {
    nodes: Vec<Option<Free<B>>>,
    work: Vec<RealizeWork<B>>,
    outputs: Vec<Out<B>>,
    /// Deferred nodes consumed.
    pub realized: usize,
}
enum RealizeWork<B: Js> {
    Enter(FreeId, Cx),
    Seq(B::E, Cx),
    After(Span),
    Cond(B::E, Cx),
}
impl<B: Js> Default for FreePool<B> {
    /// An empty pool without capacity. O(1); allocates nothing.
    fn default() -> Self {
        Self { nodes: Vec::new(), work: Vec::new(), outputs: Vec::new(), realized: 0 }
    }
}
impl<B: Js> FreePool<B> {
    /// Deferred expressions and their iterative realization share the source
    /// occurrence bound; no separate allocation is needed for each expression.
    /// Cost: Reserves O(N) deferred-node/work/output slots for N imported occurrences; no
    /// deferred expressions are visited or initialized.
    pub(super) fn with_source_capacity(nodes: usize) -> Self {
        Self { nodes: Vec::with_capacity(nodes), work: Vec::with_capacity(nodes),
            outputs: Vec::with_capacity(nodes), ..Self::default() }
    }

    #[cfg(test)]
    pub(super) fn reserve_repeat(&mut self) {
        self.nodes.reserve(self.nodes.len());
    }
    #[cfg(test)]
    pub(super) fn capacities(&self) -> [usize; 3] {
        [
            self.nodes.capacity(),
            self.work.capacity(),
            self.outputs.capacity(),
        ]
    }

    /// K1/K6: C:1529 compile_expr / C:5144 compile_if_return_output; preserve
    /// the first pass's operands rather than recompiling the source subtree.
    /// Cost: O(1): one record in a slot the pool reserved.
    pub(super) fn push(&mut self, free: Free<B>) -> FreeId {
        let id = FreeId(u32::try_from(self.nodes.len()).expect("free pool capacity"));
        self.nodes.push(Some(free));
        id
    }
    /// K2/K6: C:4715 append_effect_output / C:5144 compile_if_return_output.
    /// Explicit postorder stack: each Free is consumed once, even at depth 10k.
    /// Cost: O(F + S + J): consumes F deferred occurrences with iterative postorder frames,
    /// transfers S statement slots and pays J normalization/release visits. A consumed Free
    /// is never realized again.
    pub fn realize(&mut self, cx: Cx, probed: Probed<B>, emit: &mut impl Realizer<B>) -> Out<B> {
        let root = match probed {
            Probed::Out(out) => return out,
            Probed::Free(root) => root,
        };
        let work = &mut self.work;
        let outputs = &mut self.outputs;
        work.push(RealizeWork::Enter(root, cx));
        while let Some(task) = work.pop() {
            match task {
                RealizeWork::Enter(id, cx) => {
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
                                work.push(RealizeWork::Seq(first, cx));
                            } else {
                                work.push(RealizeWork::After(emit.effect(first)));
                            }
                            work.push(RealizeWork::Enter(second, cx));
                        }
                        Free::Cond { test, then_, else_ } => {
                            work.push(RealizeWork::Cond(test, cx));
                            // 3.6: row R3 reads the branches as assignments;
                            // every other row reads their values.
                            let branch = match cx.cont {
                                super::Cont::Assign(_) => cx,
                                _ => Cx { cont: super::Cont::Value(super::Tail::No), ..cx },
                            };
                            work.push(RealizeWork::Enter(else_, branch));
                            work.push(RealizeWork::Enter(then_, branch));
                        }
                    }
                }
                RealizeWork::Seq(first, cx) => {
                    let second = outputs.pop().expect("sequence child");
                    outputs.push(emit.seq(cx, first, second));
                }
                RealizeWork::After(head) => {
                    let mut second = outputs.pop().expect("sequence child");
                    assert_eq!(head.end(), second.stmts.start as usize);
                    second.stmts = Span {
                        start: head.start,
                        len: head.len + second.stmts.len,
                    };
                    outputs.push(second);
                }
                RealizeWork::Cond(test, cx) => {
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
    use crate::bir::j::rows::Rows;
    use crate::bir::{Bir, NodeId};
    fn output(span: Span, value: Option<NodeId>, finished: Finished) -> Out<Rows> {
        Out {
            stmts: span,
            value: value.map(Rows::from_node),
            finished,
        }
    }
    #[derive(Default)]
    struct Oracle {
        visits: Vec<u32>,
    }
    impl Realizer<Rows> for Oracle {
        fn leaf(&mut self, _: Cx, value: <Rows as Js>::E) -> Out<Rows> {
            let value = Rows::node(value);
            self.visits.push(value.0);
            output(Span::default(), Some(value), Finished::False)
        }
        fn seq(&mut self, _: Cx, first: <Rows as Js>::E, second: Out<Rows>) -> Out<Rows> {
            self.visits.push(Rows::node(first).0);
            second
        }
        fn effect(&mut self, first: <Rows as Js>::E) -> Span {
            self.visits.push(Rows::node(first).0);
            Span::default()
        }
        fn cond(&mut self, _: Cx, test: <Rows as Js>::E, then_: Out<Rows>, _: Out<Rows>) -> Out<Rows> {
            self.visits.push(Rows::node(test).0);
            then_
        }
    }
    #[test]
    fn output_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<Finished>(), 1);
        assert_eq!(size_of::<Span>(), 8);
        assert_eq!(size_of::<Out<Rows>>(), 20);
        assert_eq!(size_of::<FreeId>(), 4);
        assert_eq!(size_of::<Free<Rows>>(), 16);
        assert_eq!(size_of::<Probed<Rows>>(), 20);
        assert_eq!(size_of::<StatementStack<Rows>>(), 96);
        assert_eq!(size_of::<Option<Slot<<Rows as JsStmt>::S>>>(), 12);
        assert_eq!(size_of::<FreePool<Rows>>(), 80);
    }
    #[test]
    fn a_statement_is_copied_once() {
        let mut stack = StatementStack::<Rows>::default();
        let mut bir = Bir::default();
        let mark = stack.mark();
        let hole = stack.reserve();
        stack.reserve();
        for n in 0..10_000 {
            stack.push(Rows::stmt_from_node(NodeId(n)));
        }
        stack.fill(hole, Rows::stmt_from_node(NodeId(10_000)));
        let span = stack.since(mark);
        let list = stack.take_list(&mut Rows::default(), &mut bir, span);
        assert_eq!(bir.lists.get(list).len(), 10_001);
        assert_eq!(bir.lists.get(list)[0], NodeId(10_000));
        assert_eq!(stack.pushed, 10_001);
        assert_eq!(stack.copied, 10_001);
        assert_eq!(stack.mark(), Span::default());
    }
    /// A hold of one statement is a slot `only` and `first_single_slot`
    /// give, so `at` reads it and `take` moves it out, as a statement slot.
    #[test]
    fn a_hold_of_one_statement_is_read_and_taken_as_a_slot_of_one() {
        let mut stack = StatementStack::<Rows>::default();
        let mark = stack.mark();
        let slot = stack.reserve();
        stack.fill_held(slot, [Rows::stmt_from_node(NodeId(7))]);
        let run = stack.since(mark);
        assert_eq!(stack.only(run).map(|(at, s)| (at, s.row())), Some((slot, NodeId(7))));
        assert_eq!(stack.first_single_slot(run).map(|(at, s)| (at, s.row())), Some((slot, NodeId(7))));
        assert_eq!(stack.at(slot).row(), NodeId(7));
        assert_eq!(stack.take(slot).row(), NodeId(7));
        assert!(!stack.has_statements(run));
        assert_eq!(stack.only(run).map(|(at, _)| at), None);
    }
    /// The list of a hold of `n` statements: (i) pushed above a reserved
    /// slot and moved into it with `hold_run`, or (ii) given to `hold` and
    /// placed with `fill_held_since`. Each enters its list once.
    #[test]
    fn a_hold_of_ten_thousand_statements_enters_its_list_once() {
        for n in [1_000u32, 10_000] {
            for sink in [false, true] {
                let mut stack = StatementStack::<Rows>::default();
                let mut bir = Bir::default();
                let before = stack.mark();
                let slot = stack.reserve();
                if sink {
                    let mark = stack.held_mark();
                    for i in 0..n {
                        stack.hold(Rows::stmt_from_node(NodeId(i)));
                    }
                    stack.fill_held_since(slot, mark);
                } else {
                    let mark = stack.mark();
                    for i in 0..n {
                        stack.push(Rows::stmt_from_node(NodeId(i)));
                    }
                    let run = stack.since(mark);
                    stack.hold_run(slot, run);
                }
                let span = stack.since(before);
                let list = stack.take_list(&mut Rows::default(), &mut bir, span);
                let rows = bir.lists.get(list);
                assert_eq!(rows.len(), n as usize);
                assert_eq!(rows[0], NodeId(0));
                assert_eq!(rows[n as usize - 1], NodeId(n - 1));
                assert_eq!(stack.pushed, n as usize);
                assert_eq!(stack.copied, n as usize);
                assert_eq!(stack.mark(), Span::default());
            }
        }
    }
    /// The slots `switches` switches leave in one run when the actions of
    /// each are reserved above the runs of its clauses, filled as each
    /// clause run is taken and then taken as one list (THREE_TREES 11.4,
    /// "T6x-a: the statement stack, after the probe" (c)): each switch has
    /// a default and `clauses` clauses of `width` statements. Returns the
    /// slots of the run before it is taken and what reading its last
    /// statement scanned.
    fn switches_with_actions_on_the_stack(switches: u32, clauses: u32, width: u32) -> (u32, usize) {
        let mut stack = StatementStack::<Rows>::default();
        let mut bir = Bir::default();
        let body = stack.mark();
        let mut node = 0;
        let mut next = || {
            node += 1;
            NodeId(node)
        };
        for _ in 0..switches {
            let before = stack.mark().start;
            let head = stack.reserve();
            let runs: Vec<Span> = (0..=clauses)
                .map(|_| {
                    let mark = stack.mark();
                    for _ in 0..width {
                        stack.push(Rows::stmt_from_node(next()));
                    }
                    stack.since(mark)
                })
                .collect();
            let actions = stack.mark();
            for _ in 0..=clauses {
                stack.reserve();
            }
            // The clauses in order, then the default, as `untagged.rs`.
            for (at, &run) in runs[1..].iter().chain(&runs[..1]).enumerate() {
                let list = stack.take_list(&mut Rows::default(), &mut bir, run);
                assert_eq!(bir.lists.get(list).len(), width as usize);
                stack.fill(actions.start + at as u32, Rows::stmt_from_node(next()));
            }
            let list = stack.take_list(&mut Rows::default(), &mut bir, stack.since(actions));
            assert_eq!(bir.lists.get(list).len(), clauses as usize + 1);
            stack.fill(head, Rows::stmt_from_node(next()));
            // The switch and the dead ranges of its runs: the holes of the
            // actions are gone, and nothing else stays.
            assert_eq!(stack.mark().start, before + 1 + (clauses + 1) * width);
        }
        let run = stack.since(body);
        let scanned = stack.scanned;
        assert!(stack.last(run).is_some());
        let scanned = stack.scanned - scanned;
        let list = stack.take_list(&mut Rows::default(), &mut bir, run);
        assert_eq!(bir.lists.get(list).len(), switches as usize);
        assert_eq!(stack.mark(), Span::default());
        (run.len, scanned)
    }
    #[test]
    fn the_actions_of_ten_thousand_switches_leave_only_the_slots_of_their_runs() {
        let (clauses, width) = (3, 2);
        let per_switch = 1 + (clauses + 1) * width;
        let (thousand, scanned_thousand) = switches_with_actions_on_the_stack(1_000, clauses, width);
        let (ten_thousand, scanned) = switches_with_actions_on_the_stack(10_000, clauses, width);
        // A switch leaves its statement and the slots its runs had: linear
        // in the statements pushed, and all of it gone with the run.
        assert_eq!((thousand, ten_thousand), (1_000 * per_switch, 10_000 * per_switch));
        // A read from the end crosses the dead ranges of the last switch,
        // not those of the switches before it: one step per range (the
        // runs of its clauses and of its default), whatever their width.
        assert_eq!(scanned, scanned_thousand);
        assert_eq!(scanned, (clauses + 1) as usize);
    }
    /// One slot that holds `n` statements between two plain slots, read in
    /// place in order (`statement_refs`) and then taken last first
    /// (`take_run_rev`): each read gives every statement of the hold once,
    /// in its order, and allocates nothing, at 1,000 and at 10,000; a
    /// taken hold has nothing left to read. The iterators count no step:
    /// what the test pins is one item per held statement and no storage.
    #[test]
    fn a_hold_of_ten_thousand_statements_is_read_and_taken_once_each() {
        for n in [1_000u32, 10_000] {
            let mut stack = StatementStack::<Rows>::default();
            stack.push(Rows::stmt_from_node(NodeId(0)));
            let hole = stack.reserve();
            stack.push(Rows::stmt_from_node(NodeId(n + 1)));
            stack.fill_held(hole, (1..=n).map(|row| Rows::stmt_from_node(NodeId(row))));
            let run = stack.since(Span::default());
            assert_eq!(run.len, 3);
            let read = allocation_counter::measure(|| {
                let mut next = 0;
                for statement in stack.statement_refs(run) {
                    assert_eq!(statement.row(), NodeId(next));
                    next += 1;
                }
                assert_eq!(next, n + 2);
            });
            assert_eq!(read.count_total, 0, "{n}: {read:?}");
            let taken = allocation_counter::measure(|| {
                let mut next = n + 2;
                for statement in stack.take_run_rev(run) {
                    next -= 1;
                    assert_eq!(Rows::stmt_node(statement), NodeId(next));
                }
                assert_eq!(next, 0);
            });
            assert_eq!(taken.count_total, 0, "{n}: {taken:?}");
            assert_eq!(stack.statement_refs(run).count(), 0);
            stack.kill(run);
            assert_eq!(stack.mark(), Span::default());
        }
    }
    /// The places `placed_refs` gives name the statements `statement_refs`
    /// gives, in order, in a slot and in a hold, across a hole and a dead
    /// range; `at_place` and `at_place_mut` read each at its place without
    /// a step, an allocation or a change of the run, at 1,000 and at
    /// 10,000 held statements; the run is then taken whole.
    #[test]
    fn a_place_names_a_statement_of_a_run_until_the_run_is_taken() {
        for n in [1_000u32, 10_000] {
            let mut bir = Bir::default();
            bir.begin_bulk();
            let mut js = Rows::default();
            let mut stack = StatementStack::<Rows>::default();
            let mut ids = Vec::new();
            let make = |js: &mut Rows, bir: &mut Bir, ids: &mut Vec<u32>| {
                let statement = js.debugger(bir);
                ids.push(js.stmt_id(bir, &statement));
                statement
            };
            stack.push(make(&mut js, &mut bir, &mut ids));
            let hole = stack.reserve();
            // A run consumed below the top: a dead range of two slots.
            let dead = stack.mark();
            stack.push(js.debugger(&mut bir));
            stack.push(js.debugger(&mut bir));
            let dead = stack.since(dead);
            let last = make(&mut js, &mut bir, &mut ids);
            let held: Vec<_> = (0..n).map(|_| make(&mut js, &mut bir, &mut ids)).collect();
            // In run order the hold comes before the last statement.
            let moved = ids.remove(1);
            ids.push(moved);
            stack.reserve();
            stack.push(last);
            stack.fill_held(hole, held);
            for statement in stack.take_run(dead) {
                js.release_stmt(&mut bir, statement);
            }
            stack.kill(dead);
            let run = stack.since(Span::default());
            let places: Vec<u32> = stack.placed_refs(run).map(|(place, _)| place).collect();
            assert_eq!(places.len(), ids.len());
            assert_eq!(places[0], 0);
            assert_eq!(places[1], StatementStack::<Rows>::HELD);
            assert_eq!(places[n as usize], StatementStack::<Rows>::HELD | (n - 1));
            let scanned = stack.scanned;
            let read = allocation_counter::measure(|| {
                for (&place, &id) in places.iter().zip(&ids) {
                    assert_eq!(js.stmt_id(&bir, stack.at_place(place)), id);
                    assert_eq!(js.stmt_id(&bir, stack.at_place_mut(place)), id);
                }
            });
            assert_eq!(read.count_total, 0, "{n}: {read:?}");
            assert_eq!(stack.scanned, scanned);
            let taken: Vec<u32> = stack.take_run(run).map(|s| js.stmt_id(&bir, &s)).collect();
            assert_eq!(taken, ids);
            stack.kill(run);
            assert_eq!(stack.mark(), Span::default());
        }
    }
    /// THREE_TREES 11.4, "T6x-e and T6x-f: the fold reads where its rows
    /// are", decision 13. A statement taken out by its place: a slot is
    /// left dead and the run gives nothing for it; a held statement is
    /// exchanged for a stand-in, which the run gives where the statement
    /// stood. The other places keep naming their statements, every reader
    /// of the run and of its slots accepts what is left, and nothing is
    /// scanned or allocated, with 1,000 and with 10,000 statements held.
    #[test]
    fn a_statement_taken_by_its_place_leaves_the_run_readable() {
        for n in [1_000u32, 10_000] {
            let mut bir = Bir::default();
            bir.begin_bulk();
            let mut js = Rows::default();
            let mut stack = StatementStack::<Rows>::default();
            let mut ids = Vec::new();
            let make = |js: &mut Rows, bir: &mut Bir, ids: &mut Vec<u32>| {
                let statement = js.debugger(bir);
                ids.push(js.stmt_id(bir, &statement));
                statement
            };
            let hole = stack.reserve();
            let held: Vec<_> = (0..n).map(|_| make(&mut js, &mut bir, &mut ids)).collect();
            stack.fill_held(hole, held);
            for _ in 0..3 {
                stack.push(make(&mut js, &mut bir, &mut ids));
            }
            let run = stack.since(Span::default());
            let places: Vec<u32> = stack.placed_refs(run).map(|(place, _)| place).collect();
            // A slot in the middle of three, and a statement in the middle
            // of the hold.
            let (slot, inner) = (n as usize + 1, n as usize / 2);
            assert_eq!(places[slot], 2);
            assert_eq!(places[inner], StatementStack::<Rows>::HELD | inner as u32);
            let stand_in = js.debugger(&mut bir);
            let stand_in_id = js.stmt_id(&bir, &stand_in);
            let (scanned, steps) = (stack.scanned, js.steps());
            let mut stand_in = Some(stand_in);
            let taken = allocation_counter::measure(|| {
                let from_slot = stack.take_placed(places[slot], || unreachable!("a slot needs no stand-in"));
                assert_eq!(js.stmt_id(&bir, &from_slot), ids[slot]);
                let from_hold = stack.take_placed(places[inner], || stand_in.take().expect("asked once"));
                assert_eq!(js.stmt_id(&bir, &from_hold), ids[inner]);
            });
            assert_eq!(taken.count_total, 0, "{n}: {taken:?}");
            assert!(stand_in.is_none());
            assert_eq!((stack.scanned, js.steps()), (scanned, steps));
            // What is left: every other place still names its statement.
            let mut left = ids.clone();
            left[inner] = stand_in_id;
            left.remove(slot);
            for (&place, &id) in places.iter().zip(&ids) {
                if place != places[slot] && place != places[inner] {
                    assert_eq!(js.stmt_id(&bir, stack.at_place(place)), id);
                }
            }
            assert_eq!(js.stmt_id(&bir, stack.at_place(places[inner])), stand_in_id);
            // The readers of a run and of its ends accept the dead slot and
            // the hold, which still has every entry.
            let read: Vec<u32> = stack.statement_refs(run).map(|s| js.stmt_id(&bir, s)).collect();
            assert_eq!(read, left);
            assert_eq!(js.stmt_id(&bir, stack.first(run).unwrap()), left[0]);
            assert_eq!(js.stmt_id(&bir, stack.last(run).unwrap()), *left.last().unwrap());
            assert!(stack.only(run).is_none());
            assert!(stack.has_statements(run));
            let given: Vec<u32> = stack.take_run(run).map(|s| js.stmt_id(&bir, &s)).collect();
            assert_eq!(given, left);
            stack.kill(run);
            assert_eq!(stack.mark(), Span::default());
        }
    }
    /// The same from the end of the run: `take_run_rev` crosses the dead
    /// slot and gives the stand-in where the held statement stood.
    #[test]
    fn a_run_with_a_statement_taken_by_its_place_is_taken_from_its_end() {
        let mut bir = Bir::default();
        bir.begin_bulk();
        let mut js = Rows::default();
        let mut stack = StatementStack::<Rows>::default();
        let hole = stack.reserve();
        let held: Vec<_> = (0..3).map(|_| js.debugger(&mut bir)).collect();
        let mut ids: Vec<u32> = held.iter().map(|s| js.stmt_id(&bir, s)).collect();
        stack.fill_held(hole, held);
        for _ in 0..2 {
            let statement = js.debugger(&mut bir);
            ids.push(js.stmt_id(&bir, &statement));
            stack.push(statement);
        }
        let run = stack.since(Span::default());
        let places: Vec<u32> = stack.placed_refs(run).map(|(place, _)| place).collect();
        let stand_in = js.debugger(&mut bir);
        ids[1] = js.stmt_id(&bir, &stand_in);
        stack.take_placed(places[1], || stand_in);
        stack.take_placed(places[3], || unreachable!("a slot needs no stand-in"));
        ids.remove(3);
        ids.reverse();
        let given: Vec<u32> = stack.take_run_rev(run).map(|s| js.stmt_id(&bir, &s)).collect();
        assert_eq!(given, ids);
    }
    /// A place whose statement was taken is not taken again.
    #[test]
    #[should_panic(expected = "place 0 holds no statement")]
    fn a_place_is_taken_once() {
        let mut bir = Bir::default();
        let mut js = Rows::default();
        let mut stack = StatementStack::<Rows>::default();
        stack.push(js.debugger(&mut bir));
        stack.take_placed(0, || unreachable!("a slot needs no stand-in"));
        stack.take_placed(0, || unreachable!("a slot needs no stand-in"));
    }
    /// A place that holds no statement is not read.
    #[test]
    #[should_panic(expected = "place 0 holds no statement")]
    fn a_place_without_a_statement_is_not_read() {
        let mut stack = StatementStack::<Rows>::default();
        stack.reserve();
        stack.at_place(0);
    }
    /// A statement, a dead range of `n` slots and a dead slot above it: a
    /// read from the end (`last`), a take from the end (`take_run_rev`) and
    /// a trim each cross the range in one step, at 1,000 and at 10,000
    /// slots. Walking the range slot by slot costs `n` and fails each.
    #[test]
    fn a_dead_range_of_ten_thousand_slots_is_crossed_from_its_end_in_one_step() {
        let crossed = |n: u32| {
            let mut stack = StatementStack::<Rows>::default();
            stack.push(Rows::stmt_from_node(NodeId(0)));
            let mark = stack.mark();
            for row in 1..=n {
                stack.push(Rows::stmt_from_node(NodeId(row)));
            }
            let range = stack.since(mark);
            stack.push(Rows::stmt_from_node(NodeId(n + 1)));
            // The run below the top is taken and becomes one dead range;
            // the statement above it is taken and leaves one dead slot.
            assert_eq!(stack.take_run(range).count(), n as usize);
            stack.kill(range);
            assert_eq!(stack.take(n + 1), Rows::stmt_from_node(NodeId(n + 1)));
            let run = stack.since(Span::default());
            assert_eq!(run.len, n + 2);
            let before = stack.scanned;
            assert_eq!(stack.last(run).map(|statement| statement.row()), Some(NodeId(0)));
            assert_eq!(stack.last_slot(run), Some(0));
            let read = stack.scanned - before;
            // The take puts the dead slots back as it found them.
            let mut taken = 0;
            for statement in stack.take_run_rev(run) {
                assert_eq!(Rows::stmt_node(statement), NodeId(0));
                taken += 1;
            }
            assert_eq!(taken, 1);
            let before = stack.scanned;
            let trimmed = stack.trim(Span::default());
            // The hole the take left goes with the dead slots.
            assert_eq!(trimmed.len, 0);
            (read, stack.scanned - before)
        };
        // Two reads of the end (`last`, `last_slot`), each one step for the
        // dead slot and one for the range; the trim pops the dead slot, the
        // range and the hole of the taken statement.
        assert_eq!(crossed(1_000), (4, 3));
        assert_eq!(crossed(10_000), (4, 3));
    }
    #[test]
    fn append_finished_truncates_and_dummy_preserves() {
        let mut stack = StatementStack::<Rows>::default();
        stack.push(Rows::stmt_from_node(NodeId(0)));
        stack.push(Rows::stmt_from_node(NodeId(1)));
        let first = output(Span { start: 0, len: 1 }, None, Finished::True);
        let next = output(Span { start: 1, len: 1 }, Some(NodeId(2)), Finished::False);
        let out = stack.append(first, next, None);
        assert_eq!(out.finished, Finished::True);
        assert_eq!(stack.slots, vec![Some(Slot::Statement(Rows::stmt_from_node(NodeId(0))))]);
        let dummy = output(stack.mark(), None, Finished::Dummy);
        let out = stack.append(out, dummy, None);
        assert_eq!(out.stmts.len, 1);
    }
    #[test]
    fn append_adjacent_runs_does_not_copy() {
        let mut stack = StatementStack::<Rows>::default();
        stack.push(Rows::stmt_from_node(NodeId(0)));
        stack.push(Rows::stmt_from_node(NodeId(1)));
        let a = output(Span { start: 0, len: 1 }, None, Finished::False);
        let b = output(Span { start: 1, len: 1 }, Some(NodeId(2)), Finished::False);
        let out = stack.append(a, b, Some(Rows::from_node(NodeId(2))));
        assert_eq!(out.stmts, Span { start: 0, len: 2 });
        assert_eq!(out.value.map(Rows::node), Some(NodeId(2)));
        assert_eq!(stack.copied, 0);
    }
    /// A chain of 10,000 deferred sequences over one leaf, pushed as the
    /// lowering pushes them (`Free` records, the tail first), is realized
    /// once per record on the explicit stack: the leaf, then each head.
    #[test]
    fn ten_thousand_deferred_nodes_are_realized_once() {
        let mut pool = FreePool::default();
        let mut oracle = Oracle::default();
        let cx = Cx::value();
        let mut free = pool.push(Free::Leaf(Rows::from_node(NodeId(0))));
        for n in 1..=10_000 {
            free = pool.push(Free::Seq { first: Rows::from_node(NodeId(n)), second: free });
        }
        assert!(oracle.visits.is_empty());
        let out = pool.realize(cx, Probed::Free(free), &mut oracle);
        assert_eq!(out.value.map(Rows::node), Some(NodeId(0)));
        assert_eq!(pool.realized, 10_001);
        assert_eq!(oracle.visits, (0..=10_000).collect::<Vec<_>>());
    }
    /// A deferred conditional is realized after its branches, the then
    /// branch first; an output that is not deferred is returned as it is
    /// and realizes nothing.
    #[test]
    fn a_deferred_conditional_is_realized_after_its_branches() {
        let mut pool = FreePool::default();
        let mut oracle = Oracle::default();
        let cx = Cx::returning();
        let then_ = pool.push(Free::Leaf(Rows::from_node(NodeId(1))));
        let else_ = pool.push(Free::Leaf(Rows::from_node(NodeId(3))));
        let free = pool.push(Free::Cond { test: Rows::from_node(NodeId(2)), then_, else_ });
        let out = pool.realize(cx, Probed::Free(free), &mut oracle);
        assert_eq!(out.value.map(Rows::node), Some(NodeId(1)));
        assert_eq!(pool.realized, 3);
        assert_eq!(oracle.visits, vec![1, 3, 2]);
        let kept = pool.realize(cx, Probed::Out(output(Span { start: 0, len: 1 }, None, Finished::True)), &mut oracle);
        assert_eq!(kept.finished, Finished::True);
        assert_eq!(pool.realized, 3);
    }
}
