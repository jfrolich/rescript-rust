//! Symbolic label scheduling for discarded conditional probes (§4.5).
//! Only the retained lowering builds J. This pooled program records control
//! events and their six continuation costs during that same source traversal.
use super::*;
use crate::bir::{NodeFlags, StrId};

const NONE: u32 = u32::MAX;
const V: usize = 0;
const A: usize = 1;
const E: usize = 2;
const R: usize = 3;
const T: usize = 4;
const D: usize = 5;

/// Internal allocations and the first request for the enclosing loop. An
/// enclosing request is counted once across all passes, not once per pass.
#[derive(Clone, Copy)]
struct Cost {
    internal: u32,
    first: u32,
}
impl Cost {
    const EMPTY: Self = Self {
        internal: 0,
        first: NONE,
    };
    /// O(1): compose events sharing one enclosing loop frame.
    fn then(self, next: Self) -> Self {
        Self {
            internal: self
                .internal
                .checked_add(next.internal)
                .expect("label count capacity"),
            first: if self.first != NONE {
                self.first
            } else if next.first != NONE {
                self.internal
                    .checked_add(next.first)
                    .expect("label offset capacity")
            } else {
                NONE
            },
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Fixed,
    Forward,
    Group,
    If,
    Short,
    Switch,
    Try,
    Finally,
    Loop,
    Request,
}
#[derive(Clone, Copy)]
struct Edge {
    step: u32,
    outer: u32,
    class: u8,
    free: bool,
    pure: bool,
}
#[derive(Clone, Copy)]
struct Step {
    start: u32,
    len: u32,
    kind: Kind,
}
#[derive(Clone, Copy)]
struct Frame {
    base: u32,
    outer: u32,
    class: u8,
    kind: Kind,
    pure: bool,
}

/// A scheduling task stays within the 16-byte traversal budget.
#[derive(Clone, Copy)]
struct Work {
    edge: Edge,
    mode: u8,
}
impl Work {
    /// O(1): request an event in one continuation without copying its tree.
    fn new(mut edge: Edge, class: usize, skip: bool) -> Self {
        edge.class = class as u8;
        Self {
            edge,
            mode: u8::from(skip),
        }
    }
    /// O(1): a top-level group resets, then restores its parent's counter.
    fn reset(number: u32) -> Self {
        Self {
            edge: Edge {
                step: number,
                outer: 0,
                class: 0,
                free: false,
                pure: false,
            },
            mode: 2,
        }
    }
}

/// Per-unit pools. No hash lookup or allocation per visited source node.
#[derive(Default)]
pub(super) struct Schedule {
    frames: Vec<Frame>,
    values: Vec<Edge>,
    edges: Vec<Edge>,
    steps: Vec<Step>,
    costs: Vec<[Cost; 6]>,
    numbers: Vec<Option<u32>>,
    work: Vec<Work>,
    resolved_loops: usize,
    pub(super) visits: usize,
}

/// O(1): declarations use V's probe schedule, not A's single pass (§3.6 R2).
fn class(cont: Cont) -> usize {
    match cont {
        Cont::Value(_) => V,
        Cont::Declare(..) => D,
        Cont::Assign(_) => A,
        Cont::Effect(Tail::No) => E,
        Cont::Effect(Tail::Return(Ret::Named { loop_: Some(_), .. })) => T,
        Cont::Effect(Tail::Return(_)) => R,
    }
}
impl Schedule {
    /// Initial traversal capacity from the imported occurrence count. Event
    /// tables stay lazy: units without labels do not need those rows.
    pub(super) fn with_source_capacity(nodes: usize) -> Self {
        Self { frames: Vec::with_capacity(nodes), values: Vec::with_capacity(nodes),
            edges: Vec::with_capacity(nodes), ..Self::default() }
    }

    /// O(1): a missing event subtree has no label effects.
    fn cost(&self, edge: Edge, class: usize) -> Cost {
        if edge.step == NONE {
            Cost::EMPTY
        } else {
            self.costs[edge.step as usize][class]
        }
    }
    /// O(1): select the continuation of an immediate operand.
    fn child_class(kind: Kind, index: usize, len: usize, requested: usize, actual: usize) -> usize {
        match kind {
            Kind::Forward | Kind::Group if index + 1 == len => requested,
            Kind::Switch if index != 0 => {
                if requested == V || requested == D {
                    A
                } else {
                    requested
                }
            }
            Kind::Try | Kind::Finally if index == 0 => match requested {
                V | D => A,
                T => R,
                c => c,
            },
            Kind::Try if index == 1 => {
                if requested == V || requested == D {
                    A
                } else {
                    requested
                }
            }
            _ => actual,
        }
    }
    /// O(1): which conditional branches the retained pass lowers. A free pure
    /// branch in E is used only by the value probe; it is not lowered again.
    fn retained(edge: Edge, requested: usize, both_free: bool) -> Option<usize> {
        if requested == A {
            Some(A)
        } else if both_free {
            Some(V)
        } else if requested == E && edge.free && edge.pure {
            None
        } else {
            Some(if requested == V || requested == D {
                A
            } else {
                requested
            })
        }
    }
    /// O(arity): compute all six costs while source children complete. The
    /// number of continuation classes is fixed; no source body is revisited.
    fn complete(&mut self, free: bool) {
        let frame = self.frames.pop().expect("label frame");
        let start = self.edges.len();
        self.edges.extend(self.values.drain(frame.base as usize..));
        let len = self.edges.len() - start;
        let mut costs = [Cost::EMPTY; 6];
        for (c, cost) in costs.iter_mut().enumerate() {
            let mut total = Cost::EMPTY;
            if frame.kind == Kind::Request {
                total.first = 0;
            } else if matches!(frame.kind, Kind::If | Kind::Short) && len > 1 {
                let test = self.edges[start];
                total = self.cost(test, V);
                let branches = &self.edges[start + 1..start + len];
                let both_free = branches.iter().all(|b| b.free);
                if frame.kind == Kind::Short && c != R && c != T {
                    for &b in branches {
                        total = total.then(self.cost(b, V));
                    }
                } else {
                    if c != A && !both_free {
                        for &b in branches {
                            total = total.then(self.cost(b, V));
                        }
                    }
                    for &b in branches {
                        if let Some(k) = Self::retained(b, c, both_free) {
                            total = total.then(self.cost(b, k));
                        }
                    }
                }
            } else if frame.kind == Kind::Group && c == V && len != 0 {
                total = self.cost(self.edges[start + len - 1], V);
            } else {
                for i in 0..len {
                    let b = self.edges[start + i];
                    let k = Self::child_class(frame.kind, i, len, c, b.class as usize);
                    let mut cost = self.cost(b, k);
                    if frame.kind == Kind::Loop && i + 1 == len {
                        cost.internal += u32::from(cost.first != NONE);
                        cost.first = NONE;
                    }
                    total = total.then(cost);
                }
            }
            *cost = total;
        }
        let step = if costs.iter().all(|c| c.internal == 0 && c.first == NONE) {
            self.edges.truncate(start);
            NONE
        } else {
            let step = self.steps.len() as u32;
            self.steps.push(Step {
                start: start as u32,
                len: len as u32,
                kind: frame.kind,
            });
            self.costs.push(costs);
            step
        };
        self.values.push(Edge {
            step,
            outer: frame.outer,
            class: frame.class,
            free,
            pure: frame.pure,
        });
        self.visits += 1;
    }

    /// O(1): a discarded pass advances the counter and resolves its first
    /// request for the already-existing outer frame, without visiting its tree.
    fn skip(&mut self, edge: Edge, c: usize, counter: &mut u32) {
        let cost = self.cost(edge, c);
        let new_request = cost.first != NONE
            && edge.outer != 0
            && self.numbers[edge.outer as usize - 1].is_none();
        if new_request {
            self.numbers[edge.outer as usize - 1] = Some(*counter + cost.first);
        }
        *counter += cost.internal + u32::from(new_request);
    }

    /// O(retained events): render only retained paths. Skipped passes use the
    /// six cached costs; an explicit stack handles 10,000 nested loops.
    fn number(&mut self, counter: &mut u32, loops: usize) {
        self.numbers.resize(loops, None);
        let Some(root) = self.values.pop() else {
            return;
        };
        if root.step == NONE {
            return;
        }
        let mut work = std::mem::take(&mut self.work);
        work.push(Work::new(root, root.class as usize, false));
        while let Some(Work { edge, mode }) = work.pop() {
            if mode == 2 {
                *counter = edge.step;
                continue;
            }
            let c = edge.class as usize;
            if edge.step == NONE {
                continue;
            }
            if mode == 1 {
                self.skip(edge, c, counter);
                continue;
            }
            self.visits += 1;
            let step = self.steps[edge.step as usize];
            let start = step.start as usize;
            let len = step.len as usize;
            if step.kind == Kind::Request {
                self.skip(edge, c, counter);
            } else if matches!(step.kind, Kind::If | Kind::Short) && len > 1 {
                let both_free = self.edges[start + 1..start + len].iter().all(|e| e.free);
                if step.kind == Kind::Short && c != R && c != T {
                    for i in (0..len).rev() {
                        work.push(Work::new(self.edges[start + i], V, false));
                    }
                } else {
                    for i in (1..len).rev() {
                        let b = self.edges[start + i];
                        if let Some(k) = Self::retained(b, c, both_free) {
                            work.push(Work::new(b, k, false));
                        }
                    }
                    if c != A && !both_free {
                        for i in (1..len).rev() {
                            work.push(Work::new(self.edges[start + i], V, true));
                        }
                    }
                    work.push(Work::new(self.edges[start], V, false));
                }
            } else if step.kind == Kind::Group && c == V && len != 0 {
                work.push(Work::new(self.edges[start + len - 1], V, false));
                work.push(Work::reset(*counter));
                for i in (0..len - 1).rev() {
                    let b = self.edges[start + i];
                    work.push(Work::new(b, b.class as usize, false));
                }
                work.push(Work::reset(0));
            } else {
                for i in (0..len).rev() {
                    let b = self.edges[start + i];
                    let k = Self::child_class(step.kind, i, len, c, b.class as usize);
                    work.push(Work::new(b, k, false));
                }
            }
        }
        self.work = work;
        self.edges.clear();
        self.steps.clear();
        self.costs.clear();
    }
}

impl State {
    /// O(1): capture a source control event before its one lowering visit.
    pub(super) fn label_enter(&mut self, cx: Cx, node: NodeId) {
        let group_body = match self.source.view(node) {
            View::Let { body, .. } | View::LetRec { body, .. } | View::Seq { second: body, .. } => {
                Some(body)
            }
            _ => None,
        };
        let group = cx.loops.0 == 0
            && group_body.is_some_and(|body| match self.source.view(body) {
                View::Let { .. } | View::LetRec { .. } | View::Seq { .. } => true,
                View::Prim { primitive, .. } => matches!(
                    self.arena.primitive(primitive).primitive,
                    crate::lambda::lam_primitive::Primitive::Pmakeblock(
                        crate::lambda::TagInfo::ModuleExport(_),
                        _
                    )
                ),
                _ => false,
            });
        let kind = match self.source.view(node) {
            View::If { .. } => Kind::If,
            View::Prim { primitive, .. }
                if matches!(
                    self.arena.primitive(primitive).primitive,
                    crate::lambda::lam_primitive::Primitive::Psequand
                        | crate::lambda::lam_primitive::Primitive::Psequor
                ) =>
            {
                Kind::Short
            }
            View::Let { .. } | View::LetRec { .. } | View::Seq { .. } => {
                if group {
                    Kind::Group
                } else {
                    Kind::Forward
                }
            }
            View::Switch { .. } | View::StrSwitch { .. } => Kind::Switch,
            View::Try { .. } => Kind::Try,
            View::TryFinally { .. } => Kind::Finally,
            View::While { .. }
            | View::For { .. }
            | View::ForOf { .. }
            | View::ForAwaitOf { .. } => Kind::Loop,
            View::Break | View::Continue if cx.switch_depth != 0 => Kind::Request,
            _ => Kind::Fixed,
        };
        self.labels.frames.push(Frame {
            base: self.labels.values.len() as u32,
            outer: cx.loops.0,
            class: class(cx.cont) as u8,
            kind,
            pure: self.source.node(node).flags().contains(NodeFlags::PURE),
        });
    }
    /// O(arity): finish this event with already-computed child costs.
    pub(super) fn label_leave(&mut self, output: &Probed) {
        self.labels.complete(matches!(output, Probed::Free(_)));
    }
    /// O(decimal digits), using a bounded stack buffer rather than a String.
    pub(super) fn numbered_label(&mut self, number: u32) -> StrId {
        use std::io::Write;
        let mut buffer = [0u8; 24];
        let mut cursor = std::io::Cursor::new(&mut buffer[..]);
        write!(&mut cursor, "loop_{number}").expect("label fits buffer");
        let len = cursor.position() as usize;
        self.arena
            .intern_text(std::str::from_utf8(&buffer[..len]).expect("decimal label"))
    }
    /// O(1): reserve a non-interned symbolic string handle. Copies of a J
    /// subtree retain this handle, so they need no separate fixup registration.
    pub(super) fn symbolic_label(&mut self) -> StrId {
        let label = StrId(self.arena.pools.strings.len() as u32);
        self.arena.pools.strings.push((0, 0));
        label
    }

    /// O(retained events + new loops): resolve each symbol to its numbered
    /// spelling once. Non-interned aliases do not alter the text interner's keys.
    pub(super) fn finish_labels(&mut self) {
        if !self.labels.frames.is_empty() {
            return;
        }
        self.labels
            .number(&mut self.next_loop_label, self.loops.len());
        for frame in self.labels.resolved_loops..self.loops.len() {
            if let Some(symbol) = self.loops[frame].label {
                let number = self.labels.numbers[frame].expect("requested label numbered");
                let spelling = self.numbered_label(number);
                self.arena.pools.strings[symbol.index()] =
                    self.arena.pools.strings[spelling.index()];
            }
        }
        self.labels.resolved_loops = self.loops.len();
    }
}

#[cfg(test)]
impl Schedule {
    /// Reserve another warmed pass's append-only event and loop-number storage.
    pub(super) fn reserve_repeat(&mut self) {
        self.edges.reserve(self.edges.len());
        self.steps.reserve(self.steps.len());
        self.costs.reserve(self.costs.len());
        self.numbers.reserve(self.numbers.len());
    }
    pub(super) fn capacities(&self) -> [usize; 7] {
        [self.frames.capacity(), self.values.capacity(), self.edges.capacity(), self.steps.capacity(),
         self.costs.capacity(), self.numbers.capacity(), self.work.capacity()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{
        arena::{Lam, LamArena},
        lam_constant::Constant,
    };

    fn generated(a: &mut LamArena, seed: &mut u32, depth: u32, in_loop: bool) -> Lam {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 17;
        *seed ^= *seed << 5;
        let choice = *seed;
        let x = a.var(Ident::new("condition", 1, IdentFlags::NONE));
        if depth == 0 {
            return if in_loop {
                let jump = if choice & 1 == 0 {
                    a.break_()
                } else {
                    a.continue_()
                };
                if choice & 2 == 0 {
                    jump
                } else {
                    let unit = a.const_(Constant::JsUndefined { is_unit: true });
                    a.string_switch(x, &[("a", jump), ("b", unit), ("c", x)], Some(jump))
                }
            } else {
                a.const_(Constant::int(0))
            };
        }
        match choice % 4 {
            0 => {
                let body = generated(a, seed, depth - 1, true);
                a.while_(x, body)
            }
            1 => {
                let yes = generated(a, seed, depth - 1, in_loop);
                let no = generated(a, seed, depth - 1, in_loop);
                a.if_(x, yes, no)
            }
            2 => {
                let body = generated(a, seed, depth - 1, in_loop);
                let other = generated(a, seed, depth - 1, in_loop);
                let default = a.const_(Constant::int(0));
                a.string_switch(x, &[("a", body), ("b", other), ("c", x)], Some(default))
            }
            _ => {
                let body = generated(a, seed, depth - 1, true);
                a.for_(
                    Ident::new("index", a.ident_stamp_bound() + 100, IdentFlags::NONE),
                    x,
                    x,
                    crate::lambda::DirectionFlag::Upto,
                    body,
                )
            }
        }
    }

    #[test]
    fn generated_label_schedules_match_legacy() {
        for shape in 1..=512u32 {
            let mut a = LamArena::new();
            let mut seed = shape;
            let body = generated(&mut a, &mut seed, 2 + shape % 3, true);
            let x = a.var(Ident::new("outer", 2, IdentFlags::NONE));
            let loop_ = a.while_(x, body);
            let unit = a.const_(Constant::JsUndefined { is_unit: true });
            let root = a.if_(x, loop_, unit);

            super::super::oracle_tests::compare(a, root);
        }
    }

    fn labelled(a: &mut LamArena) -> Lam {
        let x = a.var(Ident::new("x", 3, IdentFlags::NONE));
        let jump = a.break_();
        let unit = a.const_(Constant::int(0));
        let body = a.string_switch(x, &[("a", jump), ("b", x), ("c", unit)], Some(unit));
        a.while_(x, body)
    }

    #[test]
    fn top_level_group_counter_is_restored() {
        let mut a = LamArena::new();
        let first = labelled(&mut a);
        let second = labelled(&mut a);
        let zero = a.const_(Constant::int(0));
        let body = a.seq_raw(second, zero);
        let root = a.let_(
            LetKind::Strict,
            Ident::new("result", 4, IdentFlags::NONE),
            first,
            body,
        );
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn recursive_function_label_schedule() {
        use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc};
        let mut a = LamArena::new();
        let f = Ident::new("f", 10, IdentFlags::NONE);
        let condition = a.var(Ident::new("condition", 1, IdentFlags::NONE));
        let callee = a.var(f);
        let call = a.apply_raw(
            callee,
            &[],
            ApInfo {
                status: ApplyStatus::InferFull,
                loc: LamLoc::NONE,
            },
        );
        let other = labelled(&mut a);
        let body = a.if_(condition, call, other);
        let fun = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
        let root = a.letrec(&[(f, fun)], callee);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn labelled_loops_with_captured_iteration_variables() {
        use crate::lambda::{ApInfo, ApplyStatus, DirectionFlag, FunctionAttribute, LamLoc};
        for form in 0..3 {
            let mut a = LamArena::new();
            let id = Ident::new("index", 20, IdentFlags::NONE);
            let value = a.var(id);
            let inner = labelled(&mut a);
            let function_body = a.seq_raw(inner, value);
            let closure = a.function_(
                0,
                &[],
                function_body,
                FunctionAttribute::default(),
                LamLoc::NONE,
            );
            let sink = a.var(Ident::new("sink", 21, IdentFlags::NONE));
            let call = a.apply_raw(
                sink,
                &[closure],
                ApInfo {
                    status: ApplyStatus::InferFull,
                    loc: LamLoc::NONE,
                },
            );
            let zero = a.const_(Constant::int(0));
            let jump = a.break_();
            let switch =
                a.string_switch(value, &[("a", jump), ("b", value), ("c", zero)], Some(zero));
            let body = a.seq_raw(call, switch);
            let limit = a.var(Ident::new("limit", 22, IdentFlags::NONE));
            let root = match form {
                0 => a.for_(id, zero, limit, DirectionFlag::Upto, body),
                1 => a.for_of(id, limit, body),
                _ => a.for_await_of(id, limit, body),
            };
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_nested_labelled_loops_lower_without_allocations() {
        let mut a = LamArena::new();
        let mut root = labelled(&mut a);
        let condition = a.const_(Constant::JsTrue);
        for _ in 1..10_000 { root = a.while_(condition, root); }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let output = s.probe(Cx::effect(), root).unwrap();
            let output = s.realize(Cx::effect(), output);
            for node in s.statements.statements(output.stmts) { s.arena.release(node); }
            if let Some(value) = output.value { s.arena.release(value); }
            s.statements.kill(output.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        run(&mut state);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        state.loops.reserve(state.loops.len());
        state.labels.reserve_repeat();
        state.group_indices.reserve(state.group_indices.len());
        state.group_nodes.reserve(state.group_nodes.len());
        state.switch_output_nodes.reserve(state.switch_output_nodes.len());
        state.switch_output_clauses.reserve(state.switch_output_clauses.len());
        state.arena.pools.switch_keys.reserve(state.arena.pools.switch_keys.len());
        state.arena.pools.switch_clauses.reserve(state.arena.pools.switch_clauses.len());
        state.arena.pools.switches.reserve(1);
        state.arena.pools.strings.reserve(2);
        state.arena.pools.text.reserve(24);
        state.arena.pools.text_index.reserve(1, |&(hash, _)| hash);
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(),
            s.arena.free_nodes.capacity(), s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1,
            s.loops.capacity(), s.arena.pools.strings.capacity(), s.arena.pools.text.capacity(),
            s.arena.pools.text_index.capacity(), s.group_indices.capacity(), s.group_nodes.capacity(),
            s.switch_output_nodes.capacity(), s.switch_output_clauses.capacity(), s.arena.pools.switch_keys.capacity(),
            s.arena.pools.switch_clauses.capacity(), s.arena.pools.switches.capacity()];
        let before = capacities(&state);
        let labels = state.labels.capacities();
        let visits = state.source_steps;
        let scheduled = state.labels.visits;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("whole labelled loops: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.labels.capacities(), labels);
        assert_eq!(state.source_steps - visits, 20_005);
        assert_eq!(state.labels.visits - scheduled, 30_007);
        assert_eq!(state.next_loop_label, 2);
    }

    #[test]
    fn ten_thousand_nested_loops_with_labelled_break_are_linear() {
        let mut a = LamArena::new();
        let mut root = labelled(&mut a);
        let condition = a.const_(Constant::JsTrue);
        for _ in 1..10_000 {
            root = a.while_(condition, root);
        }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::effect(), root).unwrap();
        assert_eq!(state.loops.len(), 10_000);
        assert_eq!(state.next_loop_label, 1);
        assert_eq!(state.loops.iter().filter(|p| p.label.is_some()).count(), 1);
        assert!(state.loops.last().unwrap().label.is_some());
        assert_eq!(state.source_steps, 20_005);
        assert_eq!(state.labels.visits, 30_007);
        let lowered = state.complete(Cx::effect(), output);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
    }

    #[test]
    fn layout() {
        assert_eq!(std::mem::size_of::<Work>(), 16);
        assert_eq!(std::mem::size_of::<Cost>(), 8);
        assert_eq!(std::mem::size_of::<Edge>(), 12);
        assert_eq!(std::mem::size_of::<Step>(), 12);
        assert_eq!(std::mem::size_of::<Frame>(), 12);
        assert_eq!(std::mem::size_of::<Kind>(), 1);
    }
}
