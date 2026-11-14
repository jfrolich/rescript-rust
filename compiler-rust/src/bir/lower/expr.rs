//! K1–K6: C:1529 compile_expr and its Let/Sequence/Function context arms.
use super::*;
use crate::bir::{FuncId, VarSpan};

/// Decoded structural operands saved across child visits; no source re-read.
pub(super) enum Resume {
    Loop(super::loops::Loop),
    Rec(super::rec::Group),
    Try(super::try_::Try),
    Assign { var: VarId, value: NodeId },
    Switch(super::switch::Switch),
    Variant(super::variant::Variant),
    Untagged(super::untagged::Untagged),
    If(super::cond::Conditional),
    Call(super::call::Call),
    Prim(super::prim::Prim),
    Record(super::record::Record),
    Catch(super::exit::Catch),
    Exit(super::exit::Exit),
    Let {
        var: VarId,
        kind: LetKind,
        value: Option<NodeId>,
        body: NodeId,
    },
    Seq {
        first: NodeId,
        second: NodeId,
    },
    Fun {
        body: NodeId,
        header: FuncId,
        loop_: Option<LoopRef>,
    },
}
impl State {
    /// K4/K2/K10: C:2411 compile_let_binding_output, C:4603 compile_effect_output,
    /// C:1997 with_function_scope. Preserve order and reset function boundaries.
    /// Cost: O(C): appends the C immediate children selected by the resume kind (arguments,
    /// scheduled bodies, or fixed let/sequence operands). Does not recursively lower those
    /// children.
    pub(super) fn expression_children(
        &self,
        cx: Cx,
        resume: &Resume,
        into: &mut Vec<(Cx, NodeId)>,
    ) {
        if let Resume::Loop(frame) = resume { self.loop_children(cx, *frame, into); return; }
        if let Resume::Rec(group) = resume { self.recursive_children(cx, *group, into); return; }
        if let Resume::Try(frame) = resume { self.try_children(cx, *frame, into); return; }
        if let Resume::Untagged(frame) = resume { self.untagged_children(cx, *frame, into); return; }
        if let Resume::Variant(frame) = resume { self.variant_children(cx, *frame, into); return; }
        if let Resume::Catch(frame) = resume { self.catch_children(cx, *frame, into); return; }
        if let Resume::Exit(exit) = resume { self.exit_children(cx, exit, into); return; }
        if let Resume::Switch(frame) = resume {
            self.switch_children(cx, *frame, into);
            return;
        }
        if let Resume::Record(record) = resume {
            self.record_children(cx, record, into);
            return;
        }
        if let Resume::Prim(prim) = resume {
            let cont = if matches!(self.arena.primitive(prim.primitive).primitive, crate::lambda::lam_primitive::Primitive::Pdebugger) {
                Cont::Effect(Tail::No)
            } else { Cont::Value(Tail::No) };
            into.extend(self.source.lists.get(prim.operands).iter().map(|&node| (Cx { cont, ..cx }, node)));
            return;
        }
        if let Resume::Call(call) = resume {
            let call = self.call_plan(*call);
            into.extend(self.source.lists.get(call.operands).iter().map(|&node| (Cx { cont: Cont::Value(Tail::No), ..cx }, node)));
            return;
        }
        if let Resume::If(conditional) = resume {
            self.conditional_children(cx, conditional, into);
            return;
        }
        match *resume {
            Resume::Rec(_) | Resume::Loop(_) => unreachable!("group or loop handled above"),
            Resume::Assign { value, .. } => into.push((Cx { cont: Cont::Value(Tail::No), ..cx }, value)),
            Resume::Try(_) | Resume::If(_) | Resume::Switch(_) | Resume::Variant(_) | Resume::Untagged(_)
            | Resume::Catch(_) | Resume::Exit(_) => unreachable!("control handled above"),
            Resume::Call(_) | Resume::Prim(_) | Resume::Record(_) => unreachable!("arguments handled above"),
            Resume::Let {
                var,
                kind,
                value,
                body,
            } => {
                if let Some(value) = value {
                    into.push((
                        Cx {
                            cont: Cont::Declare(kind, var),
                            ..cx
                        },
                        value,
                    ));
                }
                into.push((cx, body));
            }
            Resume::Seq { first, second, .. } => {
                into.push((
                    Cx {
                        cont: Cont::Effect(Tail::No),
                        ..cx
                    },
                    first,
                ));
                into.push((cx, second));
            }
            Resume::Fun { body, header, loop_ } => {
                let mut function = Cx::returning();
                function.return_unit = self.arena.function_attributes(header).return_unit;
                function.cont = Cont::Effect(Tail::Return(Ret::Named { loop_, in_catch: false }));
                into.push((function, body));
            }
        }
    }
    /// K4/K2/K10: C:2411 compile_let_binding_output / C:4603 compile_effect_output /
    /// C:1997 with_function_scope. Consume each non-speculative child before the
    /// next sibling; a declaration cannot be delayed past the body's statements.
    pub(super) fn expression_child(
        &mut self,
        cx: Cx,
        resume: &Resume,
        index: usize,
        child: Probed,
    ) -> Probed {
        if let Resume::Loop(frame) = resume { return self.loop_child(cx, *frame, index, child); }
        if let Resume::Rec(group) = resume { return self.recursive_child(cx, *group, index, child); }
        if let Resume::Try(frame) = resume { return self.try_child(cx, *frame, index, child); }
        if let Resume::If(conditional) = resume {
            return self.conditional_child(cx, conditional, index, child);
        }
        if let Resume::Untagged(frame) = resume { return self.untagged_child(cx, *frame, index, child); }
        if let Resume::Variant(frame) = resume { return self.variant_child(cx, *frame, index, child); }
        if let Resume::Switch(frame) = resume { return self.switch_child(cx, *frame, index, child); }
        if let Resume::Catch(frame) = resume { return self.catch_child(cx, *frame, index, child); }
        if let Resume::Exit(exit) = resume { return self.exit_child(cx, exit, index, child); }
        if matches!(resume, Resume::Call(_) | Resume::Prim(_) | Resume::Record(_)) {
            let mut out = self.realize(cx, child);
            if let Resume::Prim(prim) = resume {
                if matches!(self.arena.primitive(prim.primitive).primitive, crate::lambda::lam_primitive::Primitive::Pdebugger) {
                    if let Some(value) = out.value.take() { self.drop_pure_effect(value); }
                    out.value = Some(crate::bir::j::plain::node(&mut self.arena, View::JUndefined, 1));
                }
            }
            self.statements.reserve();
            out.stmts = self.statements.since(Span { start: out.stmts.start, len: 0 });
            return Probed::Out(out);
        }
        if let Resume::Seq { .. } = resume {
            if index == 0 {
                // The head's value is held in every continuation: whether it
                // becomes a statement depends on the tail (1.5).
                let mut out = self.realize(cx, child);
                self.statements.reserve();
                out.stmts = self.statements.since(Span { start: out.stmts.start, len: 0 });
                return Probed::Out(out);
            }
        }
        let force = match resume {
            Resume::Rec(_) | Resume::Loop(_) => unreachable!("group or loop handled above"),
            Resume::Try(_) | Resume::If(_) | Resume::Switch(_) | Resume::Variant(_) | Resume::Untagged(_)
            | Resume::Catch(_) | Resume::Exit(_) => unreachable!("control handled above"),
            Resume::Call(_) | Resume::Prim(_) | Resume::Record(_) => unreachable!("arguments handled above"),
            Resume::Assign { .. } => false,
            Resume::Let { value, .. } => value.is_some() && index == 0,
            Resume::Seq { .. } => index == 0,
            Resume::Fun { .. } => true,
        };
        if force {
            Probed::Out(self.realize(cx, child))
        } else {
            child
        }
    }
    /// K0/K2/K10: C:119 append, C:4715 append_effect_output, C:562 function_expr.
    /// Cost: O(C + S + F + J): consumes completed child outputs C, transfers statement slots
    /// S, realizes deferred nodes F, and pays J selected construct-finisher/JS-
    /// normalizer/release work. Dispatch itself does not rewalk source children.
    pub(super) fn finish_expression(
        &mut self,
        cx: Cx,
        resume: Resume,
        mut children: impl Iterator<Item = Probed>,
    ) -> Probed {
        match resume {
            Resume::Loop(frame) => self.finish_loop(cx, frame),
            Resume::Rec(group) => self.finish_recursive(cx, group, children),
            Resume::Try(frame) => self.finish_try(cx, frame),
            Resume::Assign { var, .. } => self.finish_assignment(cx, var, children.next().expect("assignment operand")),
            Resume::Switch(frame) => self.finish_switch(cx, frame),
            Resume::Variant(frame) => self.finish_variant(cx, frame),
            Resume::Untagged(frame) => self.finish_untagged(cx, frame),
            Resume::Catch(frame) => self.finish_catch(cx, frame),
            Resume::Exit(exit) => self.finish_exit(cx, exit, children),
            Resume::If(conditional) => self.finish_conditional(cx, conditional, children),
            Resume::Call(call) => self.finish_application(cx, call, children),
            Resume::Prim(_) | Resume::Record(_) => unreachable!("primitive finished by dispatch"),
            Resume::Let { value, .. } => {
                let first = value.map(|_| match children.next().expect("binding output") {
                    Probed::Out(out) => out,
                    Probed::Free(_) => unreachable!("binding was realized before body"),
                });
                let mut body = self.realize(cx, children.next().expect("let body"));
                if first.as_ref().is_some_and(|first| first.finished == Finished::True)
                    && matches!(cx.cont, Cont::Value(_)) {
                    // C: compile_expr Let retains the unreachable body's value,
                    // unlike compile_effect_output and append_effect_output.
                    let value = body.value.take();
                    let mut out = self.append_outputs(first.unwrap(), body, None);
                    out.value = value;
                    return Probed::Out(out);
                }
                let value = body.value;
                Probed::Out(match first {
                    Some(first) => self.append_outputs(first, body, value),
                    None => body,
                })
            }
            Resume::Seq { .. } => {
                let Probed::Out(mut first) = children.next().expect("sequence head") else {
                    unreachable!("head realized before tail")
                };
                let tail = children.next().expect("sequence tail");
                let keeps_value = matches!(cx.cont, Cont::Value(_) | Cont::Effect(Tail::No));
                let slot = first.stmts.start + first.stmts.len - 1;
                if first.finished == Finished::True {
                    let second = self.realize(cx, tail);
                    if !keeps_value && let Some(value) = first.value.take() {
                        self.hold_effect(slot, value);
                    }
                    return Probed::Out(self.append_outputs(first, second, None));
                }
                let head = first.value.take();
                let tail = match (head, tail) {
                    // 1.5: a free tail after a head without statements is free
                    // in the continuations that convert a value (1.4) too.
                    (Some(head), Probed::Free(tail))
                        if !keeps_value && !self.statements.has_statements(first.stmts) =>
                    {
                        self.statements.remove_empty(first.stmts);
                        if self.arena.node(head).flags().contains(crate::bir::NodeFlags::STRICT) {
                            self.arena.release(head);
                            return Probed::Free(tail);
                        }
                        return Probed::Free(self.free.push(Free::Seq { first: head, second: tail }));
                    }
                    (_, tail) => tail,
                };
                let mut second = self.realize(cx, tail);
                if let Some(value) = head {
                    if keeps_value && !self.statements.has_statements(second.stmts) {
                        let second_value = second.value.expect("value continuation");
                        let value = if self.arena.node(value).flags().contains(crate::bir::NodeFlags::STRICT) {
                            self.arena.release(value);
                            second_value
                        } else { crate::bir::j::norm::jm1_js_seq(&mut self.arena, value, second_value) };
                        second.value = Some(value);
                    } else {
                        self.hold_effect(slot, value);
                    }
                }
                let value = second.value;
                let out = self.append_outputs(first, second, value);
                if !self.statements.has_statements(out.stmts) && let Some(value) = out.value {
                    self.statements.remove_empty(out.stmts);
                    self.probe_leaf(cx, value)
                } else { Probed::Out(out) }
            }
            Resume::Fun { header, loop_, .. } => {
                let Probed::Out(body) = children.next().expect("function body") else {
                    unreachable!("return was realized")
                };
                assert!(body.value.is_none());
                let list = self.statements.take_list(&mut self.arena, body.stmts);
                let body = self.arena.block_from_list(list);
                let body = if let Some(frame) = loop_ { self.loop_function_body(frame, header, body) } else { body };
                let source_loc = self
                    .located_functions
                    .get(header.index())
                    .copied()
                    .unwrap_or(false)
                    .then_some(self.arena.function(header).loc);
                let attr = self.arena.function_attributes(header);
                let header = if attr.one_unit_arg {
                    self.arena.function_header_from(header, VarSpan::default())
                } else {
                    header
                };
                let value = self.pure_expression(View::JFun { body, header }, 0);
                super::names::close(&mut self.arena, &self.idents, header);
                if let Some(loc) = source_loc {
                    self.arena
                        .set_cold(value, crate::bir::Cold { loc, comment: None });
                    let mut flags = self.arena.node(value).flags();
                    flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
                    self.arena.nodes[value.index()].set_flags(flags);
                }
                self.probe_leaf(cx, value)
            }
        }
    }
    /// K2: O:339 push_effect_expression into the slot reserved after the head
    /// of a sequence. One step per comma operand of the value.
    fn hold_effect(&mut self, slot: u32, value: NodeId) {
        let mut held = std::mem::take(&mut self.scratch);
        crate::bir::j::norm::jm14_push_effect_expression(&mut self.arena, value, &mut held);
        self.statements.fill_held(slot, &held);
        held.clear();
        self.scratch = held;
    }
    /// K2: O:339 push_effect_expression. Calls may have effects; pure values
    /// are removed and comma values are split before statements are emitted.
    /// Cost: O(R): releases the R nodes owned by a discarded strict expression; the purity
    /// decision reads one cached flag.
    pub(super) fn drop_pure_effect(&mut self, value: NodeId) {
        let mut effects = std::mem::take(&mut self.scratch);
        crate::bir::j::norm::jm14_push_effect_expression(&mut self.arena, value, &mut effects);
        for statement in effects.drain(..) {
            self.statements.push(statement);
        }
        self.scratch = effects;
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;
    use crate::lambda::{FunctionAttribute, LamLoc, arena::LamArena, lam_constant::Constant, lam_primitive::Primitive};

    #[test]
    fn unit_argument_directive_matches_legacy() {
        let mut a = LamArena::new();
        let param = Ident::new("unit", 1, crate::ident::IdentFlags::NONE);
        let body = a.const_(Constant::Int { i: 42, comment: None });
        let root = a.function_(1, &[param], body, FunctionAttribute {
            one_unit_arg: true, directive: Some("use server".into()), ..Default::default()
        }, LamLoc::NONE);
        oracle_tests::compare(a, root);
    }

    #[test]
    fn ten_thousand_unit_argument_functions_share_directives_without_allocations() {
        let mut a = LamArena::new();
        let functions: Vec<_> = (0..10_000).map(|i| {
            let param = Ident::new("unit", i + 1, crate::ident::IdentFlags::NONE);
            let body = a.const_(Constant::Int { i, comment: None });
            a.function_(1, &[param], body, FunctionAttribute {
                one_unit_arg: true, directive: Some("use server".into()), ..Default::default()
            }, LamLoc::NONE)
        }).collect();
        let root = a.prim_raw(Primitive::Pmakearray, &functions, LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let out = s.probe(Cx::returning(), root).unwrap();
            let out = s.realize(Cx::returning(), out);
            for node in s.statements.statements(out.stmts) { s.arena.release(node); }
            if let Some(value) = out.value { s.arena.release(value); }
            s.statements.kill(out.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        let functions = state.arena.vars.funcs.len();
        let attributes = state.arena.pools.attrs.len();
        run(&mut state);
        assert_eq!(state.arena.pools.attrs.len(), attributes);
        assert_eq!(state.arena.vars.funcs.len() - functions, 10_000);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.arena.vars.funcs.reserve(10_000);
        state.arena.func_owners.reserve(10_000);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
            s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.vars.funcs.capacity(),
            s.arena.func_owners.capacity(), s.arena.pools.attrs.capacity(), s.traversal.work.capacity(),
            s.traversal.values.capacity(), s.traversal.children.capacity()];
        let before = capacities(&state);
        let free_before = state.free.capacities();
        let statements_before = state.statements.capacities();
        let visits = state.source_steps;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("unit-function headers: {allocations:?}, visits={}", state.source_steps - visits);
        assert_eq!(allocations.count_total, 0);
        assert_eq!(state.arena.pools.attrs.len(), attributes);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.statements.capacities(), statements_before);
        assert_eq!(state.source_steps - visits, 20_001);
        assert_eq!(std::mem::size_of::<crate::bir::FuncHeader>(), 20);
    }
}
