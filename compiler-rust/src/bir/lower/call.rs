//! H1: C:1144 compile_apply_call_inner, local application lowering.
use super::*;
use crate::bir::ApplyId;
use crate::lambda::ApplyStatus;

/// C:1144 compile_apply_call_inner: operands saved before their single visit.
#[derive(Clone, Copy)]
pub(super) struct Call(pub u32);

/// Immutable arity groups in the unit pool, without per-call ownership.
#[derive(Clone, Copy)]
pub(super) struct AritySpan { start: u32, len: u32 }

/// One imported immutable body and its closed-parameter statistics.
#[derive(Clone, Copy)]
pub(super) struct InlineTemplate { function: NodeId, stats_start: u32, stats_len: u32 }

/// Cold call metadata; the source walk carries only its four-byte handle.
pub(super) struct Plan {
    pub tail: Option<LoopRef>,
    pub operands: crate::bir::ListId,
    pub inline: bool,
    pub status: ApplyStatus,
    pub loc: crate::lambda::LamLoc,
    pub external: Option<(
        crate::bir::ImportId,
        crate::bir::StrId,
        Option<AritySpan>,
    )>,
}

impl State {
    /// O(1): inspect cold call metadata without copying it down the walk.
    pub(super) fn call_plan(&self, call: Call) -> &Plan {
        self.calls[call.0 as usize].as_ref().expect("live call plan")
    }
    /// Amortized O(1): append a call plan to the retained unit pool.
    fn save_call(&mut self, plan: Plan) -> Call {
        let call = Call(u32::try_from(self.calls.len()).expect("call plan capacity"));
        self.calls.push(Some(plan));
        call
    }
    /// C:1144 compile_apply_call_inner: flatten Na spines without repeatedly
    /// copying the growing argument prefix. Arguments retain left-to-right order.
    /// Cost: O(A + D) spine flattening and operand pushes for A arguments across D nested
    /// applications, plus resolver lookup/decoding and any inline_external_function work.
    /// Each argument enters the reversed buffer once.
    pub(super) fn application(
        &mut self,
        cx: Cx,
        mut callee: NodeId,
        args: crate::bir::ListId,
        info: ApplyId,
    ) -> Result<Call, Unsupported> {
        let loc = self.arena.pools.apply[info.index()].loc;
        let status = self.arena.pools.apply[info.index()].status;
        let mut reversed = std::mem::take(&mut self.call_reversed);
        reversed.extend(self.source.lists.get(args).iter().rev().copied());
        if status == ApplyStatus::Na {
            while let View::Apply {
                callee: inner,
                args,
                info,
            } = self.source.view(callee)
            {
                if self.arena.pools.apply[info.index()].status != ApplyStatus::Na {
                    break;
                }
                self.source_steps += 1;
                reversed.extend(args.iter().rev().copied());
                callee = inner;
            }
        }
        let mut operands = self.source.lists.push_iter(1 + reversed.len(),
            std::iter::once(callee).chain(reversed.drain(..).rev()));
        self.call_reversed = reversed;
        let external = self.module_field_apply_target(callee);
        let external = if let Some((module, member)) = external {
            let name = self.arena.text(member);
            let module_name = self.arena.pools.j_modules[module.index()].id.name();
            if self.cross_module_inline {
                if let Some(exports) = self
                    .resolver
                    .as_ref()
                    .and_then(|r| r.module_cmj_export_lambdas(module_name))
                {
                    if let Some(crate::lambda::Lambda::Lfunction(function)) = exports.get(name) {
                        if function.params.len() == self.source.lists.get(operands).len() - 1
                            && crate::lambda::lam_analysis::attr_can_be_inlined(&function.attr)
                        {
                            let mut args = std::mem::take(&mut self.call_reversed);
                            args.extend_from_slice(&self.source.lists.get(operands)[1..]);
                            let reduced = self.inline_external_function(cx, (module, member), function, &args);
                            args.clear();
                            self.call_reversed = args;
                            let reduced = reduced?;
                            let operands = self.source.lists.push(&[reduced]);
                            return Ok(self.save_call(Plan { tail: None, operands, inline: true, status, loc, external: None }));
                        }
                    }
                }
            }
            let arity = self.resolve_cmj_module_field_arity(module, member);
            operands = self.source.lists.slice(operands, 1, self.source.lists.get(operands).len() - 1);
            self.source_steps += 2; // recognized field and global callee
            Some((module, member, arity))
        } else {
            None
        };
        Ok(self.save_call(Plan {
            tail: None,
            operands,
            inline: false,
            status,
            loc,
            external,
        }))
    }

    /// Exchange, between the source and the lowering's arena, the tables an
    /// imported fragment appends to: the cold pools, and the function headers
    /// with their parameter runs (they live in the variable table). A header
    /// made while a fragment is imported or reduced must get the next
    /// identity of the arena the lowering reads headers from. O(1).
    fn swap_fragment_tables(&mut self) {
        std::mem::swap(&mut self.source.pools, &mut self.arena.pools);
        std::mem::swap(&mut self.source.vars.funcs, &mut self.arena.vars.funcs);
        std::mem::swap(&mut self.source.vars.function_params, &mut self.arena.vars.function_params);
    }

    /// C:1377 compile_external_field_apply; reuses immutable imported templates.
    /// Cost: O(F + A + V + G + R): F template nodes imported/analysed on first use, A
    /// arguments detached, V newly synchronized/renamed variables, G newly seen globals, R
    /// beta-copy and normalization node visits. Rewrites may revisit nodes; R is not claimed
    /// linear in the original body.
    fn inline_external_function(&mut self, _cx: Cx, key: (crate::bir::ImportId, crate::bir::StrId), function: &crate::lambda::LFunction, args: &[NodeId]) -> Result<NodeId, Unsupported> {
        use crate::bir::{bridge, engine::Engine, l::beta};
        // Align source identities with temporaries already allocated by J.
        while self.source.vars.len() < self.arena.vars.len() {
            let var = VarId(self.source.vars.len() as u32);
            self.source.new_var_id(self.arena.vars.name(var), self.arena.vars.order(var));
            self.source.vars.flags[var.index()] = self.arena.vars.flags[var.index()];
        }
        let first_var = self.source.vars.len();
        self.inline_globals.extend(self.arena.pools.j_modules[self.inline_globals.len()..].iter().map(|module| module.id));
        let mut globals = std::mem::take(&mut self.inline_globals);
        let mut foreign = std::mem::take(&mut self.inline_foreign);
        debug_assert!(foreign.is_empty());
        self.swap_fragment_tables();
        // J lowering can append function headers before another L fragment is
        // imported. Its dense owner table must cover those header identities.
        self.source.func_owners.resize(self.source.vars.funcs.len(), None);
        let result = (|| {
            let template = if let Some(&template) = self.inline_templates.get(&key) { template } else {
                // Import only once per immutable export. Beta reduction copies
                // the body; it does not consume this detached source template.
                let mut lambda = crate::lambda::arena::LamArena::new();
                let body = lambda.import(&function.body);
                let root = lambda.function_(function.arity, &function.params, body, function.attr.clone(), function.loc);
                let function = bridge::import_fragment(&mut self.source, &mut globals, &mut foreign, &lambda, root)?;
                let View::Fun { body, header } = self.source.view(function) else { unreachable!("imported external function") };
                let params = self.source.function(header).params;
                let engine = Engine::new(&mut self.source);
                let (_, stats) = beta::closed_with_stats(&engine, &mut self.inline_scratch, params, body);
                let stats_start = crate::bir::index(self.inline_param_stats.len());
                self.inline_param_stats.extend_from_slice(&stats);
                let template = InlineTemplate { function, stats_start, stats_len: crate::bir::index(stats.len()) };
                self.inline_templates.insert(key, template);
                self.inline_imports += 1;
                template
            };
            let function = template.function;
            let View::Fun { body, header } = self.source.view(function) else { unreachable!("imported external function") };
            let params = self.source.function(header).params;
            for &arg in args { self.source.detach(arg); }
            let mut engine = Engine::new(&mut self.source);
            engine.exchange_reuse(&mut self.inline_engine);
            engine.stats.unsupported = None;
            engine.set_current_stamp(self.next_order - 1);
            let stats = &self.inline_param_stats[template.stats_start as usize..(template.stats_start + template.stats_len) as usize];
            let reduced = beta::reduce(&mut engine, &mut self.inline_scratch, params, body, args, Some(stats), 1, &mut |_, _, _| {});
            self.next_order = engine.current_stamp() + 1;
            engine.exchange_reuse(&mut self.inline_engine);
            self.inline_reductions += 1;
            reduced
        })();
        self.swap_fragment_tables();
        self.idents.append(&mut foreign);
        self.inline_foreign = foreign;
        self.inline_globals = globals;
        let reduced = result?;
        for (var, origin) in self.inline_engine.stats.renames.drain(..) {
            assert_eq!(var.index(), self.idents.len());
            let old = self.idents[origin.index()];
            self.idents.push(Ident::new(old.name_atom(), self.source.vars.order(var) as i32, old.flags()));
        }
        self.inline_engine.stats.labels.clear();
        for i in first_var..self.source.vars.len() {
            let var = VarId(i as u32);
            let made = self.arena.new_var_id(self.source.vars.name(var), self.source.vars.order(var));
            assert_eq!(made, var);
            self.arena.vars.flags[i] = self.source.vars.flags[i];
        }
        for &id in &self.inline_globals[self.arena.pools.j_modules.len()..] {
            self.arena.pools.j_modules.push(crate::js_ir::ModuleId { id, kind: crate::js_ir::Kind::Ml, dynamic_import: false });
            self.module_constants.push(ModuleConstants::Unread);
        }
        self.arena.func_owners.resize(self.arena.vars.funcs.len(), None);
        self.awaited_units.resize(self.arena.vars.len(), false);
        self.invalid_module_paths.resize(self.source.nodes.len(), false);
        self.switch_facts.resize(self.source.nodes.len(), super::switch::Facts::default());
        Ok(reduced)
    }

    /// C:320 call_info_of_apply_status. Local calls never consult export arity.
    fn call_info_of_apply_status(status: ApplyStatus) -> crate::js_ir::CallInfo {
        use crate::js_ir::{CallArity, CallInfo, CallKind};
        let (kind, arity) = match status {
            ApplyStatus::InferFull => (CallKind::MlCall, CallArity::Full),
            ApplyStatus::Na => (CallKind::MlCall, CallArity::Na),
            ApplyStatus::Uncurry => (CallKind::Na, CallArity::Full),
        };
        CallInfo {
            kind,
            arity,
            ..CallInfo::default()
        }
    }

    /// C:1129 compile_apply_call, C:6648 declare_compiled, C:6667
    /// assign_compiled, C:6658 return_compiled: one call, then continuation.
    /// Cost: O(A + H + S + J): consumes A child outputs, pops H dead call slots, sequences S
    /// held/statement slots, then call/eta/tail construction and J JS-normalizer/release
    /// visits. Each argument is appended to retained buffers, not cloned as a subtree.
    pub(super) fn finish_application(
        &mut self,
        cx: Cx,
        call: Call,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let call = self.calls[call.0 as usize].take().expect("live call plan");
        while self.calls.last().is_some_and(Option::is_none) { self.calls.pop(); }
        let mut outputs = std::mem::take(&mut self.argument_outputs);
        outputs.extend(children.map(|child| match child {
            Probed::Out(out) => out,
            Probed::Free(_) => unreachable!("argument realized before its next sibling"),
        }));
        let mut values = std::mem::take(&mut self.argument_values);
        let method_callee = !call.inline && call.external.is_none()
            && matches!(self.source.view(self.source.lists.get(call.operands)[0]), View::Prim { primitive, .. }
                if matches!(self.arena.primitive(primitive).primitive, crate::lambda::lam_primitive::Primitive::PjsObjectGet(_)));
        let statements = self.sequence_arguments(method_callee, &outputs, &mut values);
        outputs.clear();
        self.argument_outputs = outputs;
        let result = (|| {
        if let Some(frame) = call.tail { return self.finish_self_call(frame, statements, &values); }
        if call.inline {
            return self.primitive_result(cx, statements, values[0]);
        }
        let value = if let Some((module, member, arity)) = call.external {
            let callee = self.pure_expression(
                View::JQualified {
                    module,
                    member: Some(member),
                },
                0,
            );
            match call.status {
                ApplyStatus::InferFull | ApplyStatus::Uncurry => self.call_node(
                    callee,
                    &values,
                    Self::call_info_of_apply_status(call.status),
                ),
                ApplyStatus::Na => {
                    if let Some(arity) = arity {
                        self.apply_with_arity(callee, arity, &values)
                    } else {
                        self.call_node(callee, &values, crate::js_ir::CallInfo::default())
                    }
                }
            }
        } else {
            self.call_node(
                values[0],
                &values[1..],
                Self::call_info_of_apply_status(call.status),
            )
        };
        // C:1129 compile_apply_call: attach only a real, non-ghost location.
        if self.locations.as_ref().and_then(|locations| locations.get(call.loc))
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0) {
            self.arena.set_cold(value, crate::bir::Cold { loc: call.loc, comment: None });
            let mut flags = self.arena.node(value).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[value.index()].set_flags(flags);
        }
        if !self.statements.has_statements(statements) {
            // Holes carry no effects; pop them before returning a free value.
            self.statements.remove_empty(statements);
            self.probe_leaf(cx, value)
        } else {
            let out = self.leaf(cx, value);
            Probed::Out(Out {
                stmts: self.statements.since(Span {
                    start: statements.start,
                    len: 0,
                }),
                ..out
            })
        }
        })();
        values.clear();
        self.argument_values = values;
        result
    }
    /// C:1243 module_field_apply_target: only named module exports of globals.
    fn module_field_apply_target(
        &mut self,
        callee: NodeId,
    ) -> Option<(crate::bir::ImportId, crate::bir::StrId)> {
        let View::Prim { args, primitive } = self.source.view(callee) else {
            return None;
        };
        let crate::lambda::lam_primitive::Primitive::Pfield(
            _,
            crate::lambda::FieldDbgInfo::Module { name },
        ) = self.arena.primitive(primitive).primitive
        else {
            return None;
        };
        let [global] = args else {
            return None;
        };
        let View::Global { module } = self.source.view(*global) else {
            return None;
        };
        Some((module, self.arena.intern_text(name.as_str())))
    }

    /// C:1222 resolve_cmj_module_field_arity. Missing and submodule entries are
    /// unknown arity; no hash iteration contributes to output order.
    /// Cost: Expected O(1) identity-cache probe; on a miss adds field-name hashing, resolver
    /// module lookup/decoding, and O(K) copying of the K arity segments. Cache iteration
    /// never determines output.
    fn resolve_cmj_module_field_arity(
        &mut self,
        module: crate::bir::ImportId,
        field: crate::bir::StrId,
    ) -> Option<AritySpan> {
        if let Some(arity) = self.call_arity_index.get(&(module, field)) { return *arity; }
        let name = self.arena.pools.j_modules[module.index()].id.name();
        let table = self.resolver.as_ref().and_then(|resolver| resolver.module_cmj_export_arities(name));
        let arity = match table.as_ref().and_then(|table| table.get(self.arena.text(field))) {
            Some(crate::cmi::persistent_env::CmjExportArity::Single(arity)) => self.store_call_arity(arity),
            _ => None,
        };
        self.call_arity_index.insert((module, field), arity);
        arity
    }

    /// Cost: O(K): appends the K arity segments and returns their span; unknown arity
    /// performs no append.
    fn store_call_arity(&mut self, arity: &crate::lambda::lam_arity::Arity) -> Option<AritySpan> {
        let crate::lambda::lam_arity::Arity::Info { arities, .. } = arity else { return None };
        let start = u32::try_from(self.call_arities.len()).expect("arity pool");
        self.call_arities.extend_from_slice(arities);
        Some(AritySpan { start, len: arities.len() as u32 })
    }

    /// C:1144 compile_apply_call_inner: the call constructor performs no rewrite.
    pub(super) fn call_node(
        &mut self,
        callee: NodeId,
        args: &[NodeId],
        info: crate::js_ir::CallInfo,
    ) -> NodeId {
        let info = self.arena.js_info(crate::bir::JsPayload::Call(info));
        crate::bir::j::plain::node(&mut self.arena, View::JCall { callee, args, info }, 0)
    }

    /// C:1341 apply_with_arity: consume saturated groups once, then eta-expand
    /// a strictly pure partial application with fresh parameters left to right.
    /// Cost: O(A + G + P): reads G arity groups, appends A supplied operands to call lists,
    /// and creates P missing parameters/Var nodes for a pure partial application. Saturated
    /// groups consume disjoint argument slices.
    fn apply_with_arity(
        &mut self,
        mut callee: NodeId,
        arity: AritySpan,
        args: &[NodeId],
    ) -> NodeId {
        let mut offset = 0;
        let full = Self::call_info_of_apply_status(ApplyStatus::InferFull);
        for index in arity.start..arity.start + arity.len {
            let group = self.call_arities[index as usize];
            if offset == args.len() {
                return callee;
            }
            let count = if group == 0 { 1 } else { group as usize };
            let remaining = &args[offset..];
            if remaining.len() >= count {
                callee = self.call_node(callee, &remaining[..count], full.clone());
                offset += count;
            } else if remaining.iter().all(|&node| {
                self.arena
                    .node(node)
                    .flags()
                    .contains(crate::bir::NodeFlags::STRICT)
            }) {
                let missing = count - remaining.len();
                let params = crate::bir::VarSpan {
                    start: self.arena.vars.len() as u32,
                    len: missing as u32,
                };
                let mut full_args = std::mem::take(&mut self.eta_arguments);
                debug_assert!(full_args.is_empty());
                full_args.extend_from_slice(remaining);
                super::names::open(&mut self.arena);
                for _ in 0..missing {
                    let var = self.fresh_variable("param");
                    full_args.push(self.pure_expression(View::Var { var }, 0));
                }
                // The callee and the arguments were built before the
                // function's scope opened and move into it (G10).
                super::names::adopt(&mut self.arena, &self.idents, callee);
                for &node in remaining {
                    super::names::adopt(&mut self.arena, &self.idents, node);
                }
                let call = self.call_node(callee, &full_args, full);
                full_args.clear(); self.eta_arguments = full_args;
                let ret = crate::bir::j::return_value(&mut self.arena, call);
                let body = self.arena.new_node(View::SBlock { statements: &[ret] }, 0);
                let header = self.arena.function_header(
                    params,
                    Default::default(),
                    crate::lambda::LamLoc::NONE,
                );
                let function = self.pure_expression(View::JFun { body, header }, 0);
                super::names::close(&mut self.arena, &self.idents, header);
                return function;
            } else {
                return self.call_node(callee, remaining, crate::js_ir::CallInfo::default());
            }
        }
        if offset == args.len() {
            callee
        } else {
            self.call_node(callee, &args[offset..], crate::js_ir::CallInfo::default())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{bridge, bridge_j};
    use crate::js_ir::{
        arena::{JsDepsProgram, JsProgram, StmtKind},
        build::exp,
    };
    use crate::lambda::{
        arena::LamArena, lam_arity::Arity, lam_compile::LambdaCompiler, lam_constant::Constant,
    };

    /// C:1341 apply_with_arity: saturation, partial expansion and unknown tails.
    #[test]
    fn arity_groups_match_legacy() {
        for groups in [vec![], vec![0], vec![2], vec![1, 2], vec![2, 1, 3], vec![1, 1, 1, 1, 2, 1]] {
            for count in 0..7 {
                for effectful in [false, true] {
                    let mut source = LamArena::new();
                    let root = source.const_(Constant::JsNull);
                    let mut state = State::new(bridge::import_lambda(&source, root).unwrap());
                    let var = state.fresh_variable("f");
                    let id = state.idents[var.index()];
                    let func = state.pure_expression(View::Var { var }, 0);
                    let mut legacy = LambdaCompiler::new();
                    let old_func = exp::var(id, &mut legacy.j);
                    let mut args = Vec::new();
                    let mut old_args = Vec::new();
                    for _ in 0..count {
                        let value = state.pure_expression(View::JNull, 0);
                        let old = exp::null(&mut legacy.j);
                        if effectful {
                            args.push(state.call_node(value, &[], Default::default()));
                            old_args.push(exp::call(old, &[], Default::default(), &mut legacy.j));
                        } else {
                            args.push(value);
                            old_args.push(old);
                        }
                    }
                    let arity = Arity::info(groups.clone(), false);
                    let span = state.store_call_arity(&arity).unwrap();
                    let value = state.apply_with_arity(func, span, &args);
                    let lowered = state.complete(
                        Cx::value(),
                        Probed::Out(Out {
                            stmts: Span::default(),
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
                    let expected = legacy.bir_apply_arity_oracle(old_func, arity, old_args);
                    let statement = legacy.j.stmt(StmtKind::Exp(expected));
                    let expected = JsDepsProgram {
                        program: JsProgram::new_in(vec![statement], vec![], legacy.j),
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
                    assert_eq!(
                        print(&actual),
                        print(&expected),
                        "groups={groups:?} count={count} effectful={effectful}"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;
    use crate::lambda::{ApInfo, LamLoc, FieldDbgInfo, arena::LamArena, lam_constant::Constant, lam_primitive::Primitive, lam_arity::Arity};

    #[test]
    fn ten_thousand_wide_arity_partial_calls_lower_without_allocations() {
        let resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        resolver.set_bir_test_export("Other", "run", crate::cmi::persistent_env::CmjExportArity::Single(Arity::info(vec![1, 1, 1, 1, 2, 1], false)), None);
        let mut a = LamArena::new();
        let calls: Vec<_> = (0..10_000).map(|_| {
            let global = a.global_module(Ident::create_persistent("Other"));
            let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
            let args: Vec<_> = (0..5).map(|_| a.const_(Constant::JsNull)).collect();
            a.apply_raw(callee, &args, ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE })
        }).collect();
        let root = a.prim_raw(Primitive::Pmakearray, &calls, LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root; let mut state = State::new(input); state.resolver = Some(resolver);
        let run = |s: &mut State| {
            let out = s.probe(Cx::returning(), root).unwrap(); let out = s.realize(Cx::returning(), out);
            for node in s.statements.statements(out.stmts) { s.arena.release(node); }
            if let Some(value) = out.value { s.arena.release(value); }
            s.statements.kill(out.stmts);
        };
        let lists = state.arena.lists.storage_shape().0; let source_lists = state.source.lists.storage_shape().0;
        let funcs = state.arena.vars.funcs.len(); let attrs = state.arena.pools.attrs.len();
        let infos = state.arena.pools.js.len(); let vars = state.arena.vars.len();
        run(&mut state);
        assert_eq!(state.call_arities.len(), 6); assert_eq!(state.call_arity_index.len(), 1);
        assert_eq!(state.arena.vars.len() - vars, 10_000);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.source.lists.reserve_test_growth(state.source.lists.storage_shape().0 - source_lists);
        state.arena.vars.funcs.reserve(state.arena.vars.funcs.len() - funcs);
        state.arena.func_owners.reserve(state.arena.vars.funcs.len() - funcs);
        state.arena.pools.attrs.reserve(state.arena.pools.attrs.len() - attrs);
        state.arena.pools.js.reserve(state.arena.pools.js.len() - infos);
        state.arena.vars.j_origin.reserve(10_000); state.arena.vars.name.reserve(10_000);
        state.arena.vars.order.reserve(10_000); state.arena.vars.flags.reserve(10_000);
        state.arena.vars.uses.reserve(10_000); state.arena.vars.binder.reserve(10_000);
        state.arena.vars.fact.reserve(10_000); state.arena.vars.printed.reserve(10_000);
        state.arena.js_scope.as_mut().unwrap().uses.reserve(10_000);
        state.arena.capture_binders.reserve(10_000); state.arena.bulk_binders.reserve(10_000); state.idents.reserve(10_000);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
            s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.source.lists.storage_shape().1,
            s.arena.vars.funcs.capacity(), s.arena.func_owners.capacity(), s.arena.pools.attrs.capacity(), s.arena.pools.js.capacity(),
            s.call_arities.capacity(), s.call_arity_index.capacity(), s.eta_arguments.capacity(), s.call_reversed.capacity(), s.calls.capacity(),
            s.arena.vars.j_origin.capacity(), s.arena.vars.name.capacity(), s.arena.vars.order.capacity(), s.arena.vars.flags.capacity(),
            s.arena.vars.uses.capacity(), s.arena.vars.binder.capacity(), s.arena.vars.fact.capacity(), s.arena.vars.printed.capacity(),
            s.arena.capture_binders.capacity(), s.arena.bulk_binders.capacity(), s.idents.capacity(), s.arena.js_scope.as_ref().unwrap().uses.capacity(),
            s.argument_outputs.capacity(), s.argument_values.capacity(), s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity()];
        let before = capacities(&state); let free_before = state.free.capacities(); let stmts = state.statements.capacities();
        let visits = state.source_steps; let sequences = state.sequence_steps;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("partial calls: {allocations:?}, source={}, sequencing={}", state.source_steps-visits, state.sequence_steps-sequences);
        assert_eq!(capacities(&state), before); assert_eq!(state.free.capacities(), free_before); assert_eq!(state.statements.capacities(), stmts);
        assert_eq!(allocations.count_total, 0);
        assert_eq!(state.arena.vars.len() - vars, 20_000); assert_eq!(state.call_arities.len(), 6);
        assert!(state.eta_arguments.is_empty());
        assert_eq!((state.source_steps - visits, state.sequence_steps - sequences), (80_001, 60_000));
        assert_eq!(std::mem::size_of::<AritySpan>(), 8);
    }
}

#[cfg(test)]
mod inline_allocation_tests {
    use super::*;
    use crate::lambda::{ApInfo, LamLoc, Lambda, LetKind, FieldDbgInfo, arena::LamArena, lam_constant::Constant, lam_primitive::Primitive, lam_arity::Arity};

    #[test]
    fn ten_thousand_copied_external_bodies_reuse_storage() {
        for width in [1, 16] {
            let params: Vec<_> = (0..width).map(|i| Ident::new("arg", 100 + i, crate::ident::IdentFlags::NONE)).collect();
            let local = Ident::new("local", 200, crate::ident::IdentFlags::NONE);
            let mut body = LamArena::new(); let arg = body.var(params[0]);
            let init = body.prim_raw(Primitive::PinitMod, &[arg], LamLoc::NONE);
            let mut values = vec![body.var(local), body.var(local)];
            values.extend(params[1..].iter().map(|&p| body.var(p)));
            let result = body.prim_raw(Primitive::Pmakearray, &values, LamLoc::NONE);
            let root = body.let_(LetKind::Strict, local, init, result);
            let resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
            resolver.set_bir_test_export("Other", "run", crate::cmi::persistent_env::CmjExportArity::Single(Arity::info(vec![width], false)),
                Some(Lambda::function_(width, params, body.export(root), Default::default(), LamLoc::NONE)));
            let mut a = LamArena::new();
            // Inlining consumes argument nodes. Import two independent units
            // before warming; never rerun a source whose arguments were consumed.
            let mut roots = Vec::new();
            for _ in 0..2 {
                let calls: Vec<_> = (0..10_000).map(|_| {
                    let global = a.global_module(Ident::create_persistent("Other"));
                    let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }), &[global], LamLoc::NONE);
                    let args: Vec<_> = (0..width).map(|i| {
                        let value = a.const_(Constant::JsNull);
                        if width > 1 && i % 3 == 0 { a.prim_raw(Primitive::PinitMod, &[value], LamLoc::NONE) } else { value }
                    }).collect();
                    a.apply_raw(callee, &args, ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE })
                }).collect();
                roots.push(a.prim_raw(Primitive::Pmakearray, &calls, LamLoc::NONE));
            }
            let root = a.prim_raw(Primitive::Pmakearray, &roots, LamLoc::NONE);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap(); let root = input.root;
            let mut state = State::new(input); state.resolver = Some(resolver); state.cross_module_inline = true;
            let View::Prim { args: [warm, measured], .. } = state.source.view(root) else { unreachable!() };
            let (warm, measured) = (*warm, *measured);
            let run = |s: &mut State, root| {
                let out = s.probe(Cx::returning(), root).unwrap(); let out = s.realize(Cx::returning(), out);
                for n in s.statements.statements(out.stmts) { s.arena.release(n); }
                if let Some(n) = out.value { s.arena.release(n); } s.statements.kill(out.stmts);
            };
            macro_rules! stores { ($m:ident, $s:ident) => {
                $m!($s, arena.nodes); $m!($s, arena.parents); $m!($s, arena.free_nodes); $m!($s, arena.release_stack);
                $m!($s, source.nodes); $m!($s, source.parents); $m!($s, source.free_nodes); $m!($s, source.release_stack);
                $m!($s, arena.cold); $m!($s, arena.j_duplicable); $m!($s, arena.death_candidates); $m!($s, arena.tail_candidates); $m!($s, arena.tail_calls); $m!($s, arena.self_tail); $m!($s, arena.loop_facts); $m!($s, arena.weights); $m!($s, arena.weight_path); $m!($s, arena.count_stack); $m!($s, arena.effect_work); $m!($s, arena.capture_chain); $m!($s, arena.capture_stack); $m!($s, arena.capture_uses);
                $m!($s, source.cold); $m!($s, source.j_duplicable); $m!($s, source.death_candidates); $m!($s, source.tail_candidates); $m!($s, source.tail_calls); $m!($s, source.self_tail); $m!($s, source.loop_facts); $m!($s, source.weights); $m!($s, source.weight_path); $m!($s, source.count_stack); $m!($s, source.effect_work); $m!($s, source.capture_chain); $m!($s, source.capture_stack); $m!($s, source.capture_uses);
                $m!($s, arena.vars.funcs); $m!($s, arena.func_owners); $m!($s, source.func_owners); $m!($s, arena.pools.attrs); $m!($s, arena.pools.js);
                $m!($s, arena.vars.j_origin); $m!($s, arena.vars.name); $m!($s, arena.vars.order); $m!($s, arena.vars.flags);
                $m!($s, arena.vars.uses); $m!($s, arena.vars.binder); $m!($s, arena.vars.fact); $m!($s, arena.vars.printed);
                $m!($s, source.vars.j_origin); $m!($s, source.vars.name); $m!($s, source.vars.order); $m!($s, source.vars.flags);
                $m!($s, source.vars.uses); $m!($s, source.vars.binder); $m!($s, source.vars.fact); $m!($s, source.vars.printed);
                $m!($s, arena.capture_binders); $m!($s, arena.bulk_binders); $m!($s, source.capture_binders); $m!($s, source.bulk_binders);
                $m!($s, idents); $m!($s, awaited_units); $m!($s, invalid_module_paths); $m!($s, switch_facts);
                $m!($s, argument_outputs); $m!($s, argument_values); $m!($s, traversal.work); $m!($s, traversal.values); $m!($s, traversal.children);
                #[cfg(debug_assertions)] { $m!($s, arena.checked_children); $m!($s, source.checked_children); }
            }; }
            let mut lengths = std::collections::HashMap::new();
            macro_rules! length { ($s:ident, $($p:ident).+) => { lengths.insert(stringify!($($p).+), $s.$($p).+.len()); }; }
            stores!(length, state);
            let lists = state.arena.lists.storage_shape().0; let source_lists = state.source.lists.storage_shape().0;
            let nodes = state.source.nodes.len();
            run(&mut state, warm);
            macro_rules! reserve { ($s:ident, $($p:ident).+) => { $s.$($p).+.reserve($s.$($p).+.len().saturating_sub(lengths[stringify!($($p).+)])); }; }
            stores!(reserve, state);
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.source.lists.reserve_test_growth(state.source.lists.storage_shape().0 - source_lists);
            state.inline_engine.reserve_node_growth(state.source.nodes.len() - nodes);
            state.free.reserve_repeat(); state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            let capacities = |s: &State| {
                let mut out = Vec::new();
                macro_rules! capacity { ($s:ident, $($p:ident).+) => { out.push((stringify!($($p).+), $s.$($p).+.capacity())); }; }
                stores!(capacity, s); out
            };
            let before = capacities(&state); let source_before = state.source_steps;
            let sequence_before = state.sequence_steps; let primitive_before = state.primitive_steps;
            let inline_capacities = |s: &State| [s.inline_templates.capacity(), s.inline_param_stats.capacity(), s.inline_foreign.capacity(),
                s.inline_globals.capacity(), s.inline_engine.stats.rules.len(), s.arena.lists.storage_shape().1, s.source.lists.storage_shape().1];
            let inline_before = inline_capacities(&state); let beta_before = state.inline_scratch.capacities(); let engine_before = state.inline_engine.capacities();
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities(); let free_before = state.free.capacities(); let statements_before = state.statements.capacities();
            let allocations = allocation_counter::measure(|| run(&mut state, measured));
            let costs = (state.source_steps-source_before, state.sequence_steps-sequence_before, state.primitive_steps-primitive_before);
            println!("inline width={width}: {allocations:?}, costs={costs:?}");
            assert_eq!(costs, if width == 1 { (70_001, 59_999, 60_001) } else { (400_001, 269_999, 330_001) });
            assert_eq!(inline_capacities(&state), inline_before); assert_eq!(state.inline_scratch.capacities(), beta_before);
            assert_eq!(state.inline_engine.capacities(), engine_before); assert!(state.inline_scratch.is_clear());
            assert!(state.inline_foreign.is_empty() && state.inline_engine.stats.renames.is_empty() && state.inline_engine.stats.labels.is_empty());
            assert_eq!(state.inline_param_stats.len(), width as usize); assert_eq!(state.inline_templates.len(), 1);
            assert_eq!(std::mem::size_of::<InlineTemplate>(), 12);
            assert_eq!(capacities(&state), before); assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            assert_eq!(state.free.capacities(), free_before); assert_eq!(state.statements.capacities(), statements_before);
            assert_eq!(state.inline_imports, 1); assert_eq!(state.inline_reductions, 20_000); assert_eq!(allocations.count_total, 0);
        }
    }
}
