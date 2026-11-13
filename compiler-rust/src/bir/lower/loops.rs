//! Loop statements (BACKEND_LOWERING §3.11).
use super::*;
use crate::bir::{ListId, NodeFlags, Op, StrId};
use crate::js_ir::ForDirection;

/// O(1) index into the unit's loop-plan pool.
#[derive(Clone, Copy)]
pub(super) struct Loop(pub u32);

/// Saved child outputs in arena blocks, not per-loop owned collections.
pub(super) struct Plan {
    node: NodeId,
    nodes: [Option<NodeId>; 3],
    blocks: [Option<ListId>; 3],
    values: [Option<NodeId>; 2],
    start: Span,
    var: Option<VarId>,
    direction: u16,
    pub(super) label: Option<StrId>,
    needs_label: bool,
}

impl State {
    /// O(1): decode loop operands; the upward exclusive-bound rule inspects
    /// only the end primitive and its literal operand (C:6390).
    pub(super) fn loop_statement(&mut self, cx: Cx, node: NodeId) -> Loop {
        let (nodes, var, direction) = match self.source.view(node) {
            View::While { condition, body } => ([Some(condition), Some(body), None], None, 0),
            View::For { var, parts } => {
                let mut end = parts[1];
                let mut direction = if self.source.node(node).aux() == crate::lambda::DirectionFlag::Upto as u16 {
                    ForDirection::Upto
                } else { ForDirection::Downto };
                if direction == ForDirection::Upto {
                    if let View::Prim { primitive, args } = self.source.view(end) {
                        if matches!(self.arena.primitive(primitive).primitive, crate::lambda::lam_primitive::Primitive::Psubint)
                            && args.len() == 2
                            && matches!(self.source.view(args[1]), View::Const { value } if matches!(self.arena.constant(value), crate::bir::Constant::Int(1))) {
                            end = args[0];
                            direction = ForDirection::Up;
                        }
                    }
                }
                ([Some(end), Some(parts[0]), Some(parts[2])], Some(var), direction as u16)
            }
            View::ForOf { var, iterable, body } | View::ForAwaitOf { var, iterable, body } => {
                ([Some(iterable), Some(body), None], Some(var), 0)
            }
            _ => unreachable!("loop dispatch"),
        };
        let frame = Loop(self.loops.len() as u32);
        self.loops.push(Plan { node, nodes, blocks: [None; 3], values: [None; 2],
            start: self.statements.mark(), var, direction, label: None,
            needs_label: self.source.loop_needs_label_in_context(node, cx.switch_depth != 0) });
        frame
    }

    /// O(1): at most three children, end before start for integer ranges.
    pub(super) fn loop_children(&self, cx: Cx, frame: Loop, into: &mut Vec<(Cx, NodeId)>) {
        let plan = &self.loops[frame.0 as usize];
        let body_index = if plan.nodes[2].is_some() { 2 } else { 1 };
        for (index, &node) in plan.nodes.iter().enumerate() {
            if let Some(node) = node {
                let body = index == body_index;
                let switch_depth = if body { cx.switch_depth } else if plan.var.is_none() { cx.switch_depth + 1 } else { cx.switch_depth };
                into.push((Cx { cont: if body { Cont::Effect(Tail::No) } else { Cont::Value(Tail::No) },
                    switch_depth, loops: if body { LoopTop(frame.0 + 1) } else { cx.loops }, probing: false, ..cx }, node));
            }
        }
    }

    /// O(s) for the child's emitted statements: seal them once into a block.
    /// For loops the end and start are lowered in allocation order, then their
    /// saved blocks are attached in execution order without moving statements.
    pub(super) fn loop_child(&mut self, cx: Cx, frame: Loop, index: usize, child: Probed) -> Probed {
        let mut out = self.realize(cx, child);
        let body_index = if self.loops[frame.0 as usize].nodes[2].is_some() { 2 } else { 1 };
        if index == body_index {
            if let Some(value) = out.value.take() { self.drop_pure_effect(value); }
        } else {
            self.loops[frame.0 as usize].values[index] = out.value;
        }
        let span = self.statements.since(Span { start: out.stmts.start, len: 0 });
        let list = self.statements.take_list(&mut self.arena, span);
        self.loops[frame.0 as usize].blocks[index] = Some(list);
        if index == 0 {
            let plan = &self.loops[frame.0 as usize];
            let op = self.source.node(plan.node).op();
            if matches!(op, Op::ForOf | Op::ForAwaitOf) && self.source.vars.uses(plan.var.unwrap()) == 0 {
                let var = self.fresh_variable(if op == Op::ForOf { "_for_of" } else { "_for_await_of" });
                self.loops[frame.0 as usize].var = Some(var);
            }
        }
        Probed::Out(Out { stmts: self.statements.mark(), value: None, finished: Finished::False })
    }

    /// O(1), apart from formatting a newly requested label's bounded integer.
    /// A jump only consults its innermost frame and the switch depth.
    pub(super) fn loop_jump(&mut self, cx: Cx, continue_: bool) -> Result<Probed, Unsupported> {
        assert!(cx.loops.0 != 0, "jump outside a loop");
        let index = cx.loops.0 as usize - 1;
        let label = if cx.switch_depth == 0 { None } else {
            assert!(self.loops[index].needs_label, "missing construction-time loop label fact");
            if self.loops[index].label.is_none() {
                let label = self.symbolic_label();
                self.loops[index].label = Some(label);
            }
            self.loops[index].label
        };
        let start = self.statements.mark();
        let statement = self.arena.new_node(if continue_ { View::SContinue { label } } else { View::SBreak { label } }, 0);
        self.statements.push(statement);
        let value = self.pure_expression(View::JUndefined, 0);
        Ok(Probed::Out(Out { stmts: self.statements.since(start), value: Some(value), finished: Finished::True }))
    }

    /// O(s): attach s saved prelude statements in execution order. Each
    /// prelude is replayed once; nested loop bodies remain one statement.
    fn push_loop_list(&mut self, list: ListId) {
        for index in 0..self.arena.lists.get(list).len() {
            self.statements.push(self.arena.lists.get(list)[index]);
        }
    }

    /// O(s) for the saved preludes and (only for statement-valued while
    /// conditions) the body's immediate statements; never walks subtrees.
    pub(super) fn finish_loop(&mut self, cx: Cx, frame: Loop) -> Probed {
        let plan = &self.loops[frame.0 as usize];
        let start = plan.start;
        let blocks = plan.blocks;
        let values = plan.values;
        let var = plan.var;
        let direction = plan.direction;
        let label = plan.label;
        let op = self.source.node(plan.node).op();
        let end = values[0].unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
        let statement = if op == Op::While {
            let body_list = blocks[1].unwrap();
            let body;
            let mut condition = end;
            let prelude = blocks[0].unwrap();
            if !self.arena.lists.get(prelude).is_empty() {
                let negated = crate::bir::j::norm::je8_not(&mut self.arena, condition);
                let mark = self.statements.mark();
                let break_ = self.arena.new_node(View::SBreak { label: None }, 0);
                self.statements.push(break_);
                let yes = self.statements.since(mark);
                let no = self.statements.mark();
                let guard = self.if_statement(negated, yes, no);
                let mark = self.statements.mark();
                self.push_loop_list(prelude);
                self.statements.push(guard);
                self.push_loop_list(body_list);
                let list = self.statements.take_list(&mut self.arena, self.statements.since(mark));
                body = self.arena.block_from_list(list);
                condition = crate::bir::j::plain::boolean(&mut self.arena, true);
            } else { body = self.arena.block_from_list(body_list); }
            self.arena.new_node(View::SWhile { condition, body, label }, 0)
        } else if matches!(op, Op::ForOf | Op::ForAwaitOf) {
            self.push_loop_list(blocks[0].unwrap());
            let body = self.arena.block_from_list(blocks[1].unwrap());
            let var = var.unwrap();
            let parts = [end, body];
            self.arena.new_node(if op == Op::ForOf {
                View::SForOf { var, parts: &parts, label }
            } else { View::SForAwaitOf { var, parts: &parts, label } }, 0)
        } else {
            let var = var.unwrap();
            let init = values[1].unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
            let end_block = blocks[0].unwrap();
            self.push_loop_list(blocks[1].unwrap());
            let hold = !self.arena.lists.get(end_block).is_empty()
                && !self.arena.node(init).flags().contains(NodeFlags::DELAY_SAFE);
            if hold {
                let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Variable, var, init);
                self.statements.push(declaration);
            }
            self.push_loop_list(end_block);
            let body = self.arena.block_from_list(blocks[2].unwrap());
            if hold {
                self.arena.new_node(View::SForRange { var, parts: &[end, body], label }, direction)
            } else {
                self.arena.new_node(View::SForRange { var, parts: &[init, end, body], label }, direction)
            }
        };
        self.statements.push(statement);
        let unit = self.pure_expression(View::JUndefined, 0);
        let mut out = self.leaf(cx, unit);
        out.stmts = self.statements.since(start);
        Probed::Out(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{arena::LamArena, lam_constant::Constant, DirectionFlag, LamLoc};
    use crate::lambda::lam_primitive::Primitive;

    #[test]
    fn while_and_for_in_every_continuation() {
        for form in 0..3 {
            for statement in [false, true] {
                let mut a = LamArena::new();
                let var = Ident::new("i", 1, IdentFlags::NONE);
                let body = a.const_(Constant::JsUndefined { is_unit: true });
                let start = a.const_(Constant::int(0));
                let mut end = a.const_(Constant::int(10));
                if statement {
                    let assign = a.assign(var, start);
                    end = a.seq_raw(assign, end);
                }
                let root = match form {
                    0 => a.while_(end, body),
                    1 => a.for_(var, start, end, DirectionFlag::Upto, body),
                    _ => a.for_(var, start, end, DirectionFlag::Downto, body),
                };
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn for_of_and_await_in_every_continuation() {
        for await_ in [false, true] {
            for used in [false, true] {
                let mut a = LamArena::new();
                let var = Ident::new("element", 1, IdentFlags::NONE);
                let iterable = a.var(Ident::new("iterable", 2, IdentFlags::NONE));
                let body = if used { a.var(var) } else { a.const_(Constant::JsUndefined { is_unit: true }) };
                let root = if await_ { a.for_await_of(var, iterable, body) } else { a.for_of(var, iterable, body) };
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn jumps_in_innermost_loops() {
        for continue_ in [false, true] {
            for form in 0..4 {
                for wrapper in 0..6 {
                    for nested in [false, true] {
                        let mut a = LamArena::new();
                        let id = Ident::new("i", 1, IdentFlags::NONE);
                        let x = a.var(Ident::new("x", 2, IdentFlags::NONE));
                        let unit = a.const_(Constant::JsUndefined { is_unit: true });
                        let jump = if continue_ { a.continue_() } else { a.break_() };
                        let body = match wrapper {
                            0 => jump,
                            1 => a.if_(x, jump, unit),
                            2 => a.string_switch(x, &[("a", jump), ("b", unit), ("c", x), ("d", jump)], Some(unit)),
                            3 => a.try_(jump, Ident::new("exn", 3, IdentFlags::NONE), unit),
                            4 => {
                                let raise = a.static_raise(7, &[]);
                                a.static_catch(raise, 7, &[], jump)
                            }
                            _ => a.try_finally(jump, unit),
                        };
                        let mut root = match form {
                            0 => a.while_(x, body),
                            1 => a.for_(id, x, x, DirectionFlag::Upto, body),
                            2 => a.for_of(id, x, body),
                            _ => a.for_await_of(id, x, body),
                        };
                        if nested { root = a.while_(x, root); }
                        super::super::oracle_tests::compare(a, root);
                    }
                }
            }
        }
    }

    #[test]
    fn inner_while_condition_targets_outer_loop() {
        for continue_ in [false, true] {
            let mut a = LamArena::new();
            let x = a.var(Ident::new("x", 2, IdentFlags::NONE));
            let jump = if continue_ { a.continue_() } else { a.break_() };
            let condition = a.if_(x, jump, x);
            let inner = a.while_(condition, x);
            let root = a.while_(x, inner);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn loop_plan_layout() {
        assert_eq!(std::mem::size_of::<Loop>(), 4);
        assert_eq!(std::mem::size_of::<Plan>(), 96);
    }

    #[test]
    fn range_holds_start_before_statement_end() {
        use crate::lambda::{ApInfo, ApplyStatus};
        let mut a = LamArena::new();
        let var = Ident::new("i", 1, IdentFlags::NONE);
        let callee = a.var(Ident::new("start", 2, IdentFlags::NONE));
        let start = a.apply_raw(callee, &[], ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
        let ten = a.const_(Constant::int(10));
        let assign = a.assign(Ident::new("other", 3, IdentFlags::NONE), ten);
        let end = a.seq_raw(assign, ten);
        let body = a.var(var);
        let root = a.for_(var, start, end, DirectionFlag::Upto, body);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn ten_thousand_while_nodes_are_lowered_once() {
        let mut a = LamArena::new();
        let mut root = a.const_(Constant::JsUndefined { is_unit: true });
        let condition = a.const_(Constant::JsTrue);
        for _ in 0..10_000 { root = a.while_(condition, root); }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::effect(), root).unwrap();
        assert_eq!(state.source_steps, 20_001);
        assert_eq!(state.loops.len(), 10_000);
        let lowered = state.complete(Cx::effect(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

    #[test]
    fn ten_thousand_while_nodes_lower_without_allocations() {
        let mut a = LamArena::new();
        let mut root = a.const_(Constant::JsUndefined { is_unit: true });
        let condition = a.const_(Constant::JsTrue);
        for _ in 0..10_000 { root = a.while_(condition, root); }
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
        state.loops.reserve(state.loops.len());
        state.labels.reserve_repeat();
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(),
            s.arena.free_nodes.capacity(), s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1,
            s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity(), s.loops.capacity()];
        let before = capacities(&state);
        let labels = state.labels.capacities();
        let visits = state.source_steps;
        let allocations = allocation_counter::measure(|| run(&mut state));
        println!("whole while loops: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.labels.capacities(), labels);
        assert_eq!(state.source_steps - visits, 20_001);
        assert_eq!(state.loops.len(), 20_000);
    }

    #[test]
    fn range_exclusive_end() {
        let mut a = LamArena::new();
        let start = a.const_(Constant::int(0));
        let limit = a.var(Ident::new("limit", 2, IdentFlags::NONE));
        let one = a.const_(Constant::int(1));
        let end = a.prim_raw(Primitive::Psubint, &[limit, one], LamLoc::NONE);
        let body = a.const_(Constant::JsUndefined { is_unit: true });
        let root = a.for_(Ident::new("i", 1, IdentFlags::NONE), start, end, DirectionFlag::Upto, body);
        super::super::oracle_tests::compare(a, root);
    }
}
