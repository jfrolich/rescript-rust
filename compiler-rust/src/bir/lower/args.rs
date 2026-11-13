//! H13: A:28–249, argument sequencing after left-to-right value lowering.
use super::*;
use crate::bir::{NodeFlags, Op};

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
    fn evaluate_now(&mut self, root: NodeId) -> (Vec<NodeId>, NodeId) {
        enum Work {
            Enter(NodeId),
            Rebuild(NodeId, usize),
        }
        let mut work = vec![Work::Enter(root)];
        let mut values = Vec::new();
        let mut statements = Vec::new();
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
                        let children = self.arena.view(value).children();
                        work.push(Work::Rebuild(value, children.len()));
                        for child in children.into_iter().rev() {
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
                    let children: Vec<_> = values.drain(values.len() - count..).collect();
                    let aux = self.arena.node(old).aux();
                    let cold = self.arena.cold(old);
                    let located = self.arena.node(old).flags().contains(NodeFlags::JS_LOC_PRESENT);
                    let view = self.arena.view(old);
                    let value = if let View::JOptional { .. } = view {
                        self.pure_expression(View::JOptional { value: children[0] }, aux)
                    } else if let View::JArray { .. } = view {
                        self.pure_expression(View::JArray { values: &children }, aux)
                    } else if let View::JBlockLit { info, .. } = view {
                        self.pure_expression(
                            View::JBlockLit {
                                values: &children,
                                info,
                            },
                            aux,
                        )
                    } else if let View::JObject { info, .. } = view {
                        self.pure_expression(
                            View::JObject {
                                values: &children,
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
                    values.push(value);
                }
            }
        }
        assert_eq!(values.len(), 1);
        (statements, values.pop().expect("held value"))
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
        debug_assert!(values.is_empty());
        for (i, arg) in args.iter().enumerate().rev() {
            self.sequence_steps += 1;
            let value = arg.value.expect("argument value");
            let (held, value) =
                if !needs_holds || !has_code || (later_defines_pure && self.runs_no_code(value)) {
                    (Vec::new(), value)
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
            has_code |= self.statements.has_statements(arg.stmts) || !held.is_empty();
            later_defines_pure &= self.defines_pure_values(&held)
                && self.statements.statements(arg.stmts).all(|statement| {
                    if let View::SDecl { value, .. } = self.arena.view(statement) {
                        value.is_none_or(|value| self.runs_no_code(value))
                    } else {
                        false
                    }
                });
            if !held.is_empty() {
                self.statements
                    .fill_held(arg.stmts.start + arg.stmts.len - 1, &held);
            }
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
