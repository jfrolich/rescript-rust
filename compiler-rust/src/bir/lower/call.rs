//! H1: C:1144 compile_apply_call_inner, local application lowering.
use super::*;
use crate::bir::ApplyId;
use crate::lambda::ApplyStatus;

/// C:1144 compile_apply_call_inner: operands saved before their single visit.
pub(super) struct Call {
    pub tail: Option<LoopRef>,
    pub operands: Vec<NodeId>,
    pub inline: bool,
    pub status: ApplyStatus,
    pub loc: crate::lambda::LamLoc,
    pub external: Option<(
        crate::bir::ImportId,
        crate::bir::StrId,
        Option<crate::lambda::lam_arity::Arity>,
    )>,
}

impl State {
    /// C:1144 compile_apply_call_inner: flatten Na spines without repeatedly
    /// copying the growing argument prefix. Arguments retain left-to-right order.
    pub(super) fn application(
        &mut self,
        cx: Cx,
        mut callee: NodeId,
        args: &[NodeId],
        info: ApplyId,
    ) -> Result<Call, Unsupported> {
        let loc = self.arena.pools.apply[info.index()].loc;
        let status = self.arena.pools.apply[info.index()].status;
        let mut reversed: Vec<_> = args.iter().rev().copied().collect();
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
        let mut operands = Vec::with_capacity(1 + reversed.len());
        operands.push(callee);
        operands.extend(reversed.into_iter().rev());
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
                        if function.params.len() == operands.len() - 1
                            && crate::lambda::lam_analysis::attr_can_be_inlined(&function.attr)
                        {
                            let reduced = self.inline_external_function(cx, function, &operands[1..])?;
                            return Ok(Call { tail: None, operands: vec![reduced], inline: true, status, loc, external: None });
                        }
                    }
                }
            }
            let arity = self.resolve_cmj_module_field_arity(module, name);
            operands.remove(0);
            self.source_steps += 2; // recognized field and global callee
            Some((module, member, arity))
        } else {
            None
        };
        Ok(Call {
            tail: None,
            operands,
            inline: false,
            status,
            loc,
            external,
        })
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

    /// C:1377 compile_external_field_apply. O(imported function + beta work
    /// + newly allocated variables), using the existing L beta reducer.
    fn inline_external_function(&mut self, _cx: Cx, function: &crate::lambda::LFunction, args: &[NodeId]) -> Result<NodeId, Unsupported> {
        use crate::bir::{bridge, engine::Engine, l::beta};
        let mut lambda = crate::lambda::arena::LamArena::new();
        let body = lambda.import(&function.body);
        let root = lambda.function_(function.arity, &function.params, body, function.attr.clone(), function.loc);
        // Align source identities with temporaries already allocated by J.
        while self.source.vars.len() < self.arena.vars.len() {
            let var = VarId(self.source.vars.len() as u32);
            self.source.new_var_id(self.arena.vars.name(var), self.arena.vars.order(var));
            self.source.vars.flags[var.index()] = self.arena.vars.flags[var.index()];
        }
        let first_var = self.source.vars.len();
        self.inline_globals.extend(self.arena.pools.j_modules[self.inline_globals.len()..].iter().map(|module| module.id));
        let mut globals = std::mem::take(&mut self.inline_globals);
        let mut foreign = Vec::new();
        self.swap_fragment_tables();
        // J lowering can append function headers before another L fragment is
        // imported. Its dense owner table must cover those header identities.
        self.source.func_owners.resize(self.source.vars.funcs.len(), None);
        let result = (|| {
            let function = bridge::import_fragment(&mut self.source, &mut globals, &mut foreign, &lambda, root)?;
            let View::Fun { body, header } = self.source.view(function) else { unreachable!("imported external function") };
            let params = self.source.function(header).params;
            for &arg in args { self.source.detach(arg); }
            let mut engine = Engine::new(&mut self.source);
            engine.set_current_stamp(self.next_order - 1);
            let (_, stats) = beta::closed_with_stats(&engine, &mut self.inline_scratch, params, body);
            let reduced = beta::reduce(&mut engine, &mut self.inline_scratch, params, body, args, Some(&stats), 1, &mut |_, _, _| {})?;
            self.next_order = engine.current_stamp() + 1;
            Ok((reduced, std::mem::take(&mut engine.stats.renames)))
        })();
        self.swap_fragment_tables();
        let (reduced, renames) = result?;
        self.idents.extend(foreign);
        for (var, origin) in renames {
            assert_eq!(var.index(), self.idents.len());
            let old = self.idents[origin.index()];
            self.idents.push(Ident::new(old.name_atom(), self.source.vars.order(var) as i32, old.flags()));
        }
        for i in first_var..self.source.vars.len() {
            let var = VarId(i as u32);
            let made = self.arena.new_var_id(self.source.vars.name(var), self.source.vars.order(var));
            assert_eq!(made, var);
            self.arena.vars.flags[i] = self.source.vars.flags[i];
        }
        for &id in &globals[self.arena.pools.j_modules.len()..] {
            self.arena.pools.j_modules.push(crate::js_ir::ModuleId { id, kind: crate::js_ir::Kind::Ml, dynamic_import: false });
            self.module_constants.push(ModuleConstants::Unread);
        }
        self.inline_globals = globals;
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
    pub(super) fn finish_application(
        &mut self,
        cx: Cx,
        call: Call,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let outputs = children
            .map(|child| match child {
                Probed::Out(out) => out,
                Probed::Free(_) => unreachable!("argument realized before its next sibling"),
            })
            .collect();
        let method_callee = !call.inline && call.external.is_none()
            && matches!(self.source.view(call.operands[0]), View::Prim { primitive, .. }
                if matches!(self.arena.primitive(primitive).primitive, crate::lambda::lam_primitive::Primitive::PjsObjectGet(_)));
        let (statements, values) = self.sequence_arguments(method_callee, outputs);
        if let Some(frame) = call.tail { return self.finish_self_call(frame, statements, values); }
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
                    if let Some(arity) = arity.filter(|arity| !arity.is_na()) {
                        self.apply_with_arity(callee, arity, values.into_vec())
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
    fn resolve_cmj_module_field_arity(
        &self,
        module: crate::bir::ImportId,
        field: &str,
    ) -> Option<crate::lambda::lam_arity::Arity> {
        let name = self.arena.pools.j_modules[module.index()].id.name();
        let table = self.resolver.as_ref()?.module_cmj_export_arities(name)?;
        match table.get(field)? {
            crate::cmi::persistent_env::CmjExportArity::Single(arity) => Some(arity.clone()),
            crate::cmi::persistent_env::CmjExportArity::Submodule(_) => None,
        }
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
    fn apply_with_arity(
        &mut self,
        mut callee: NodeId,
        arity: crate::lambda::lam_arity::Arity,
        args: Vec<NodeId>,
    ) -> NodeId {
        let mut offset = 0;
        let full = Self::call_info_of_apply_status(ApplyStatus::InferFull);
        for group in arity.extract_arity() {
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
                let mut full_args = remaining.to_vec();
                for _ in 0..missing {
                    let var = self.fresh_variable("param");
                    full_args.push(self.pure_expression(View::Var { var }, 0));
                }
                let call = self.call_node(callee, &full_args, full);
                let ret = crate::bir::j::return_value(&mut self.arena, call);
                let body = self.arena.new_node(View::SBlock { statements: &[ret] }, 0);
                let header = self.arena.function_header(
                    params,
                    Default::default(),
                    crate::lambda::LamLoc::NONE,
                );
                return self.pure_expression(View::JFun { body, header }, 0);
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
        for groups in [vec![], vec![0], vec![2], vec![1, 2], vec![2, 1, 3]] {
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
                    let value = state.apply_with_arity(func, arity.clone(), args);
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
