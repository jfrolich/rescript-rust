//! H13: A:28–249, argument sequencing after left-to-right value lowering.
use super::*;
use crate::bir::{NodeFlags, Op};

enum Work {
    Enter(NodeId),
    Rebuild(NodeId, usize),
}
#[derive(Default)]
pub(super) struct Evaluation {
    work: Vec<Work>,
    values: Vec<NodeId>,
    statements: Vec<NodeId>,
}

impl State {
    /// A:28 delay_safe: a cached fact, never a subtree walk.
    fn delay_safe(&self, value: NodeId) -> bool {
        self.arena
            .node(value)
            .flags()
            .contains(NodeFlags::DELAY_SAFE)
    }

    /// A:90 runs_no_code: inspect each owned member spine without recursion.
    fn runs_no_code(&self, value: NodeId) -> bool {
        crate::bir::j::facts::runs_no_code(&self.arena, value)
    }

    /// A:96 defines_pure_values: each statement is examined once by sequencing.
    fn defines_pure_values(&self, statements: &[NodeId]) -> bool {
        statements.iter().all(|&statement| {
            if let View::SDecl { value, .. } = self.arena.view(statement) {
                value.is_none_or(|value| self.runs_no_code(value))
            } else {
                false
            }
        })
    }

    /// X:1445 fresh_ident: unit-local naming order, without a global counter.
    pub(super) fn fresh_variable(&mut self, name: &str) -> VarId {
        let order = self.next_order;
        self.next_order = order.checked_add(1).expect("identifier order capacity");
        let name = crate::name::Name::new(name);
        let var = self.arena.new_var_id(name, order);
        self.idents.push(Ident::new(
            name.as_str(),
            order as i32,
            crate::ident::IdentFlags::NONE,
        ));
        var
    }

    /// A:116 evaluate_now and A:178 evaluate_all_now. An explicit work stack
    /// preserves literal shape and visits held literal elements left to right.
    fn evaluate_now(&mut self, root: NodeId) -> (Span, NodeId) {
        let mut evaluation = std::mem::take(&mut self.evaluation);
        let Evaluation { work, values, statements } = &mut evaluation;
        assert!(work.is_empty() && values.is_empty() && statements.is_empty(), "argument evaluation scratch must be empty");
        let statement_start = statements.len();
        work.push(Work::Enter(root));
        while let Some(task) = work.pop() {
            self.sequence_steps += 1;
            match task {
                Work::Enter(value) => {
                    if self.delay_safe(value) {
                        values.push(value);
                        continue;
                    }
                    if let View::JSeq { first, second } = self.arena.view(value) {
                        self.arena.detach(first);
                        self.arena.detach(second);
                        self.arena.release(value);
                        if self.arena.node(first).flags().contains(NodeFlags::STRICT) {
                            self.arena.release(first);
                        } else {
                            statements.push(crate::bir::j::norm::js1_exp(&mut self.arena, first));
                        }
                        work.push(Work::Enter(second));
                        continue;
                    }
                    let op = self.arena.node(value).op();
                    let literal = matches!(op, Op::JOptional | Op::JArray | Op::JBlockLit)
                        || if let View::JObject { info, .. } = self.arena.view(value) {
                            let crate::bir::JsPayload::Object(keys) =
                                &self.arena.pools.js[info.index()]
                            else {
                                unreachable!("object payload")
                            };
                            self.arena.property_keys(*keys).iter().all(|key| {
                                matches!(
                                    key,
                                    crate::bir::PropertyKey::Literal(_)
                                        | crate::bir::PropertyKey::Symbol
                                )
                            })
                        } else {
                            false
                        };
                    if literal {
                        let count = self.arena.view(value).child_count();
                        work.push(Work::Rebuild(value, count));
                        for i in (0..count).rev() {
                            let child = self.arena.view(value).child_at(i);
                            self.arena.detach(child);
                            work.push(Work::Enter(child));
                        }
                    } else {
                        let var = self.fresh_variable("tmp");
                        statements.push(crate::bir::j::declare(
                            &mut self.arena,
                            LetKind::Strict,
                            var,
                            value,
                        ));
                        values.push(self.pure_expression(View::Var { var }, 0));
                    }
                }
                Work::Rebuild(old, count) => {
                    let begin = values.len() - count;
                    let children = &values[begin..];
                    let aux = self.arena.node(old).aux();
                    let cold = self.arena.cold(old);
                    let located = self.arena.node(old).flags().contains(NodeFlags::JS_LOC_PRESENT);
                    let view = self.arena.view(old);
                    let value = if let View::JOptional { .. } = view {
                        self.pure_expression(View::JOptional { value: children[0] }, aux)
                    } else if let View::JArray { .. } = view {
                        self.pure_expression(View::JArray { values: children }, aux)
                    } else if let View::JBlockLit { info, .. } = view {
                        self.pure_expression(
                            View::JBlockLit {
                                values: children,
                                info,
                            },
                            aux,
                        )
                    } else if let View::JObject { info, .. } = view {
                        self.pure_expression(
                            View::JObject {
                                values: children,
                                info,
                            },
                            aux,
                        )
                    } else {
                        unreachable!("held literal")
                    };
                    if let Some(cold) = cold {
                        self.arena.set_cold(value, cold);
                        if located {
                            let mut flags = self.arena.node(value).flags();
                            flags.0 |= NodeFlags::JS_LOC_PRESENT;
                            self.arena.nodes[value.index()].set_flags(flags);
                        }
                    }
                    self.arena.release(old);
                    values.truncate(begin);
                    values.push(value);
                }
            }
        }
        assert_eq!(values.len(), 1);
        let span = Span {
            start: crate::bir::index(statement_start),
            len: crate::bir::index(statements.len() - statement_start),
        };
        let value = values.pop().expect("held value");
        self.evaluation = evaluation;
        (span, value)
    }

    /// A:191 sequence_arguments: allocate holds right to left after all operands
    /// have been lowered. Reserved slots keep their execution left to right.
    /// O(arguments + statement slots + held literal nodes), proven by the
    /// 10,000-wide call/block tests. The caller retains both buffers.
    pub(super) fn sequence_arguments(
        &mut self,
        method_callee: bool,
        args: &[Out],
        values: &mut Vec<NodeId>,
    ) -> Span {
        let start = args.first().map_or_else(
            || self.statements.mark(),
            |arg| Span {
                start: arg.stmts.start,
                len: 0,
            },
        );
        let needs_holds = args
            .iter()
            .skip(1)
            .any(|arg| self.statements.has_statements(arg.stmts));
        let mut has_code = false;
        let mut later_defines_pure = true;
        assert!(values.is_empty(), "argument value scratch must be empty");
        for (i, arg) in args.iter().enumerate().rev() {
            self.sequence_steps += 1;
            let value = arg.value.expect("argument value");
            let (held, value) =
                if !needs_holds || !has_code || (later_defines_pure && self.runs_no_code(value)) {
                    (Span::default(), value)
                } else if method_callee && i == 0 && self.arena.node(value).op() == Op::JDot {
                    let View::JDot {
                        object,
                        property,
                        position,
                    } = self.arena.view(value)
                    else {
                        unreachable!("member callee")
                    };
                    let aux = self.arena.node(value).aux();
                    let cold = self.arena.cold(value);
                    let located = self.arena.node(value).flags().contains(NodeFlags::JS_LOC_PRESENT);
                    self.arena.detach(object);
                    self.arena.release(value);
                    let (held, object) = self.evaluate_now(object);
                    let value =
                        crate::bir::j::member(&mut self.arena, object, property, position, aux);
                    if let Some(cold) = cold {
                        self.arena.set_cold(value, cold);
                        if located {
                            let mut flags = self.arena.node(value).flags();
                            flags.0 |= NodeFlags::JS_LOC_PRESENT;
                            self.arena.nodes[value.index()].set_flags(flags);
                        }
                    }
                    (held, value)
                } else {
                    self.evaluate_now(value)
                };
            has_code |= self.statements.has_statements(arg.stmts) || held.len != 0;
            later_defines_pure &= self.defines_pure_values(&self.evaluation.statements[held.start as usize..(held.start + held.len) as usize])
                && self.statements.statements(arg.stmts).all(|statement| {
                    if let View::SDecl { value, .. } = self.arena.view(statement) {
                        value.is_none_or(|value| self.runs_no_code(value))
                    } else {
                        false
                    }
                });
            if held.len != 0 {
                self.statements
                    .fill_held(arg.stmts.start + arg.stmts.len - 1, &self.evaluation.statements[held.start as usize..(held.start + held.len) as usize]);
            }
            self.evaluation.statements.truncate(held.start as usize);
            values.push(value);
        }
        values.reverse();
        self.statements.since(start)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{JsPayload, bridge, bridge_j};
    use crate::js_ir::{
        CallInfo,
        arena::{JsDepsProgram, JsProgram, StmtKind},
        build::exp,
    };
    use crate::lambda::{
        arena::LamArena, lam_compile::LambdaCompiler, lam_compile_arguments::HeldArgs,
    };

    #[test]
    #[should_panic(expected = "argument evaluation scratch must be empty")]
    fn evaluate_now_rejects_unconsumed_statement_scratch() {
        let mut a = LamArena::new();
        let root = a.const_(crate::lambda::lam_constant::Constant::JsNull);
        let mut state = State::new(bridge::import_lambda(&a, root).unwrap());
        let value = state.arena.new_node(View::JNull, 0);
        let statement = state.arena.new_node(View::SDebugger, 0);
        state.evaluation.statements.push(statement);
        state.evaluate_now(value);
    }

    #[test]
    fn ten_thousand_held_literal_elements_lower_without_allocations() {
        use crate::lambda::{LamLoc, lam_primitive::Primitive as P};
        let mut a = LamArena::new();
        let elements: Vec<_> = (0..10_000).map(|_| {
            let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
            a.apply_raw(x, &[], crate::lambda::ApInfo { loc: LamLoc::NONE, status: crate::lambda::ApplyStatus::Na })
        }).collect();
        let array = a.prim_raw(P::Pmakearray, &elements, LamLoc::NONE);
        let effect = a.prim_raw(P::PinitMod, &[], LamLoc::NONE);
        let local = Ident::new("later", 100, crate::ident::IdentFlags::NONE);
        let value = a.var(local);
        let later = a.let_(LetKind::Strict, local, effect, value);
        let root = a.prim_raw(P::Pmakearray, &[array, later], LamLoc::NONE);
        let input = bridge::import_lambda(&a, root).unwrap();
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
        let vars = state.arena.vars.len();
        let js = state.arena.pools.js.len();
        run(&mut state);
        let extra = state.arena.vars.len() - vars;
        assert_eq!(extra, 10_000);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.arena.pools.js.reserve(state.arena.pools.js.len() - js);
        state.idents.reserve(extra);
        state.arena.capture_binders.reserve(extra);
        state.arena.bulk_binders.reserve(extra);
        state.arena.js_scope.as_mut().unwrap().uses.reserve(extra);
        let vars = &mut state.arena.vars;
        vars.j_origin.reserve(extra); vars.name.reserve(extra); vars.order.reserve(extra);
        vars.flags.reserve(extra); vars.uses.reserve(extra); vars.binder.reserve(extra);
        vars.fact.reserve(extra); vars.printed.reserve(extra);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        state.statements.reserve_repeat();
        let capacities = |s: &State| {
            let e = &s.evaluation; let v = &s.arena.vars;
            [e.work.capacity(), e.values.capacity(), e.statements.capacity(),
                s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.pools.js.capacity(),
                s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity(),
                s.idents.capacity(), s.arena.capture_binders.capacity(), s.arena.bulk_binders.capacity(),
                s.arena.js_scope.as_ref().unwrap().uses.capacity(),
                v.j_origin.capacity(), v.name.capacity(), v.order.capacity(), v.flags.capacity(), v.uses.capacity(),
                v.binder.capacity(), v.fact.capacity(), v.printed.capacity()]
        };
        let before = capacities(&state);
        let statements_before = state.statements.capacities();
        let free_before = state.free.capacities();
        let visits = state.source_steps;
        let sequencing = state.sequence_steps;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("held literal: {allocations:?}, visits={}, sequencing={}", state.source_steps-visits, state.sequence_steps-sequencing);
        assert_eq!(allocations.count_total, 0);
        assert_eq!(state.source_steps - visits, 20_005);
        assert_eq!(state.sequence_steps - sequencing, 30_004);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.statements.capacities(), statements_before);
        assert_eq!(state.free.capacities(), free_before);
        assert!(state.evaluation.work.is_empty() && state.evaluation.values.is_empty() && state.evaluation.statements.is_empty());
        assert_eq!(std::mem::size_of::<Span>(), 8);
        assert_eq!(std::mem::size_of::<Work>(), 16);
    }

    #[test]
    fn normalized_arithmetic_stays_after_later_argument_statements() {
        use crate::lambda::{LamLoc, lam_constant::Constant, lam_primitive::Primitive as P};
        let mut a = LamArena::new();
        let x = a.var(Ident::new("x",10,crate::ident::IdentFlags::NONE));
        let number = a.prim_raw(P::Pintoffloat,&[x],LamLoc::NONE);
        let effect = a.prim_raw(P::PinitMod,&[],LamLoc::NONE);
        let value = a.const_(Constant::Int { i: 1, comment: None });
        let later = a.seq_raw(effect,value);
        let root = a.prim_raw(P::Pmakearray,&[number,later],LamLoc::NONE);
        oracle_tests::compare(a,root);
    }

    /// A:408 sequence_arguments_allocates_temporaries_right_to_left, and A:378
    /// sequence_arguments_holds_method_object_not_property_read.
    #[test]
    fn sequencing_matches_legacy_and_allocates_right_to_left() {
        for (shape, method) in [
            (0, false),
            (0, true),
            (1, false),
            (2, false),
            (3, false),
            (4, false),
        ] {
            let mut source = LamArena::new();
            let root = source.const_(crate::lambda::lam_constant::Constant::JsNull);
            let mut state = State::new(bridge::import_lambda(&source, root).unwrap());
            let mut legacy = LambdaCompiler::new();
            let object = Ident::new("o", 10, crate::ident::IdentFlags::NONE);
            let var = state.arena.new_var_id(object.name_atom(), 10);
            state.idents.push(object);
            state.next_order = 11;
            let mut args = Vec::new();
            let mut expected_args = HeldArgs::new();
            for name in ["a", "b"] {
                let obj = state.pure_expression(View::Var { var }, 0);
                let property = state.arena.intern_text(name);
                let value = crate::bir::j::member(
                    &mut state.arena,
                    obj,
                    property,
                    crate::js_ir::arena::FieldPos::NONE,
                    0,
                );
                let obj = exp::var(object, &mut legacy.j);
                let old_value = exp::static_index(obj, name, None, &mut legacy.j);
                use crate::js_ir::arena::{ExprKind, PropName};
                use crate::js_ir::op::MutableFlag;
                let (value, old_value) = match shape {
                    0 => (value, old_value),
                    1 => (
                        state.pure_expression(View::JOptional { value }, 1),
                        legacy.j.expr(ExprKind::OptionalBlock(old_value, true)),
                    ),
                    2 => (
                        state.pure_expression(View::JArray { values: &[value] }, 0),
                        exp::array(&[old_value], MutableFlag::Immutable, &mut legacy.j),
                    ),
                    3 => {
                        let tag = crate::lambda::lam_tag_info::TagInfo::Tuple;
                        let info = state.arena.js_info(JsPayload::Block(tag.clone()));
                        (
                            state.pure_expression(
                                View::JBlockLit {
                                    values: &[value],
                                    info,
                                },
                                0,
                            ),
                            exp::caml_block(
                                &[old_value],
                                MutableFlag::Immutable,
                                tag,
                                &mut legacy.j,
                            ),
                        )
                    }
                    4 => {
                        let key = state.arena.intern_text("field");
                        let info = state.arena.object_info(&[
                            crate::bir::PropertyKey::Literal(key),
                        ]);
                        let key = legacy.j.str("field");
                        let props = legacy.j.prop_list(&[(PropName::Lit(key), old_value)]);
                        (
                            state.pure_expression(
                                View::JObject {
                                    values: &[value],
                                    info,
                                },
                                0,
                            ),
                            legacy.j.expr(ExprKind::Object(props)),
                        )
                    }
                    _ => unreachable!(),
                };
                state.arena.set_cold(value, crate::bir::Cold { loc: crate::lambda::LamLoc::NONE, comment: None });
                let mut flags = state.arena.node(value).flags();
                flags.0 |= NodeFlags::JS_LOC_PRESENT;
                state.arena.nodes[value.index()].set_flags(flags);
                let old_value = legacy.j.with_expr_loc(old_value, Some(crate::lambda::LamLoc::NONE));
                let start = state.statements.mark();
                state.statements.reserve();
                args.push(Out {
                    stmts: state.statements.since(start),
                    value: Some(value),
                    finished: Finished::False,
                });
                expected_args.push((vec![], old_value));
            }
            let effect_id = Ident::new("effect", 20, crate::ident::IdentFlags::NONE);
            let effect_var = state.arena.new_var_id(effect_id.name_atom(), 20);
            state.idents.push(effect_id);
            state.next_order = 21;
            let callee = state.pure_expression(View::Var { var: effect_var }, 0);
            let info = state.arena.js_info(JsPayload::Call(CallInfo::default()));
            let value = state.arena.new_node(
                View::JCall {
                    callee,
                    args: &[],
                    info,
                },
                0,
            );
            let statement = state.arena.new_node(View::SExp { value }, 0);
            let start = state.statements.mark();
            state.statements.push(statement);
            state.statements.reserve();
            let text = state.arena.intern_text("v");
            let value = state.pure_expression(View::JStr { text }, 0);
            args.push(Out {
                stmts: state.statements.since(start),
                value: Some(value),
                finished: Finished::False,
            });
            let callee = exp::var(effect_id, &mut legacy.j);
            let effect = exp::call(callee, &[], CallInfo::default(), &mut legacy.j);
            let statement = legacy.j.stmt(StmtKind::Exp(effect));
            let value = exp::string("v", &mut legacy.j);
            expected_args.push((vec![statement], value));
            let mut values = Vec::new();
            let span = state.sequence_arguments(method, &args, &mut values);
            if method || shape != 0 {
                assert!(state.arena.node(values[0]).flags().contains(NodeFlags::JS_LOC_PRESENT));
            }
            if !method && shape == 0 {
                let View::Var { var: first } = state.arena.view(values[0]) else {
                    panic!("held first")
                };
                let View::Var { var: second } = state.arena.view(values[1]) else {
                    panic!("held second")
                };
                assert!(state.arena.vars.order(second) < state.arena.vars.order(first));
            }
            let info = state.arena.js_info(JsPayload::Call(CallInfo::default()));
            let value = state.arena.new_node(
                View::JCall {
                    callee: values[0],
                    args: &values[1..],
                    info,
                },
                0,
            );
            let lowered = state.complete(
                Cx::value(),
                Probed::Out(Out {
                    stmts: span,
                    value: Some(value),
                    finished: Finished::False,
                }),
            );
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root))
                .unwrap();
            let actual = bridge_j::export_js(&lowered.program).unwrap();
            let (mut block, values) = legacy.sequence_arguments(method, expected_args);
            let value = exp::call(values[0], &values[1..], CallInfo::default(), &mut legacy.j);
            block.push(legacy.j.stmt(StmtKind::Exp(value)));
            let expected = JsDepsProgram {
                program: JsProgram::new_in(block, vec![], legacy.j),
                modules: vec![],
                side_effect: None,
            };
            let print = |p: &JsDepsProgram| {
                crate::js_ir::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &[],
                    false,
                    false,
                    false,
                )
            };
            assert_eq!(print(&actual), print(&expected));
        }
    }
}
