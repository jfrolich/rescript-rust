//! Static catches and exits (BACKEND_LOWERING section 4).
//!
//! One rule for every continuation. The legacy lowering has one copy of the
//! explicit form per continuation family (C: compile_staticcatch_*_output),
//! one of the flattened form (C: compile_multi_staticcatch_*_output) and the
//! cheap form (C: compile_fallthrough_staticcatch_return_output). The choice
//! between the forms reads the continuation, the length of the flattened
//! table and one flag of the handler (C: staticcatch_takes_pseudo_jump).
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, CatchId, ClauseMeta, ListId, NodeFlags};

/// `order` of an entry whose catch is being flattened: no real order yet.
const PENDING: i32 = i32::MIN;
/// `order` of the cheap form (OCaml `Lam_compile_context.add_pseudo_jmp`):
/// an exit assigns the handler's parameters and falls through.
const CHEAP: i32 = -1;

/// The jump-table entry of a catch (OCaml `Lam_compile_context.jmp_table`),
/// in a table indexed by the catch header. A label is bound by one catch of
/// a unit (4.2 invariant 1), so the entry is written when its catch is
/// entered and read only by the exits of that catch's body. The handler's
/// parameters are the header's.
#[derive(Clone, Copy)]
pub(super) struct Jump {
    /// The `exit` variable all entries of one flattened table share.
    exit: VarId,
    /// `PENDING`, `CHEAP`, or the value `exit` takes for this handler.
    order: i32,
}

impl Jump {
    /// The entry of a catch that was not entered yet.
    const NONE: Jump = Jump { exit: VarId(u32::MAX), order: 0 };
}

/// A source-traversal frame of a catch: a handle into the catch-plan pool.
#[derive(Clone, Copy)]
pub(super) struct Catch(pub u32);

/// The operands of an exit, saved while its arguments are lowered.
#[derive(Clone, Copy)]
pub(super) struct Exit {
    catch: CatchId,
    args: ListId,
    /// Where the output starts; the slots of the arguments when `kept > 1`.
    start: u32,
    /// Arguments that are lowered: all, less those the cheap form skips.
    kept: u32,
}

/// Cold data of one catch, not copied down the source walk.
pub(super) struct Plan {
    start: Span,
    /// The handlers of the flattened table, innermost first: a run of
    /// `State::catch_table`.
    table: u32,
    len: u32,
    /// The body below the flattened catches.
    body: NodeId,
    /// The explicit form's `exit` variable; `None` is the cheap form.
    exit: Option<VarId>,
    /// `order` of the first handler of the table.
    first: i32,
    /// The variable the body and the handlers assign in V and D.
    target: Option<VarId>,
    /// Top of the statement stack after the body.
    mid: u32,
    body_finished: Finished,
    /// The cheap form's handler output.
    handler_finished: Finished,
    handler_empty: bool,
    /// More than one handler: the groups of equal handlers (3.9 step 2), as
    /// `State::group_switch_cases` returns them, and their lowered clauses.
    groups: Vec<usize>,
    next: Vec<usize>,
    bodies: Vec<NodeId>,
    output: Vec<NodeId>,
    clauses: Vec<ClauseMeta>,
}

impl State {
    fn has_exit(&self, node: NodeId) -> bool {
        self.source.node(node).flags().contains(NodeFlags::HAS_EXIT)
    }

    /// The catch an exit leaves. An `Exit` names its handler by label, and
    /// labels are sparse, so this is the arena's label index: one hash
    /// lookup.
    fn catch_of(&self, label: u32) -> CatchId {
        self.arena.pools.catch_labels[&label]
    }

    /// 4.1 step 1, `has_exit_code handler (fun exit -> mem exit acc)` of
    /// OCaml `Lam_compile.flat_catches`: does `handler` hold an exit to a
    /// label being flattened. Called only for a handler that has `HAS_EXIT`.
    /// One step
    /// per node of the handler that has the flag, and one label lookup per
    /// exit among them; a subtree without the flag is not entered, and
    /// nothing is allocated per node.
    fn exits_to_pending(&mut self, handler: NodeId) -> bool {
        let mut work = std::mem::take(&mut self.catch_work);
        work.push(handler);
        let mut found = false;
        while let Some(node) = work.pop() {
            self.catch_walk_steps += 1;
            let mut visit = |child: NodeId| {
                if self.source.node(child).flags().contains(NodeFlags::HAS_EXIT) {
                    work.push(child);
                }
            };
            match self.source.view(node) {
                View::Exit { label, args } => {
                    if self.jumps[self.catch_of(label).index()].order == PENDING {
                        found = true;
                        break;
                    }
                    args.iter().copied().for_each(visit);
                }
                View::Apply { callee, args, .. } => {
                    visit(callee);
                    args.iter().copied().for_each(visit);
                }
                View::Let { value, body, .. } => {
                    value.into_iter().for_each(&mut visit);
                    visit(body);
                }
                View::LetRec { values, body, .. } => {
                    values.iter().copied().for_each(&mut visit);
                    visit(body);
                }
                View::Prim { args, .. } => args.iter().copied().for_each(visit),
                View::Switch { scrutinee, actions, .. }
                | View::StrSwitch { scrutinee, actions, .. } => {
                    visit(scrutinee);
                    actions.iter().copied().for_each(visit);
                }
                View::Catch { body, handler, .. } | View::Try { body, handler, .. } => {
                    visit(body);
                    visit(handler);
                }
                View::TryFinally { body, finaliser } => {
                    visit(body);
                    visit(finaliser);
                }
                View::If { condition, then_, else_ } => {
                    visit(condition);
                    visit(then_);
                    visit(else_);
                }
                View::Seq { first, second } => {
                    visit(first);
                    visit(second);
                }
                View::While { condition, body } => {
                    visit(condition);
                    visit(body);
                }
                View::For { parts, .. } => parts.iter().copied().for_each(visit),
                View::ForOf { iterable, body, .. } | View::ForAwaitOf { iterable, body, .. } => {
                    visit(iterable);
                    visit(body);
                }
                View::Assign { value, .. } => visit(value),
                // A function never has the flag; the rest have no children.
                _ => {}
            }
        }
        work.clear();
        self.catch_work = work;
        found
    }

    /// The continuation of the body and of the dispatched handlers (4.1 step
    /// 3, `k'`): the result variable in V and D, else `cont` with `in_catch`
    /// set when it returns. Constant.
    fn catch_cont(cont: Cont, target: Option<VarId>) -> Cont {
        match (target, cont) {
            (Some(target), _) => Cont::Assign(target),
            (None, Cont::Effect(Tail::Return(Ret::Named { loop_, .. }))) => {
                Cont::Effect(Tail::Return(Ret::Named { loop_, in_catch: true }))
            }
            (None, cont) => cont,
        }
    }

    /// `let var;` with a declaration kind (B: variable, no value). Constant.
    fn declare_empty(&mut self, kind: LetKind, var: VarId) {
        let declaration = plain::node(
            &mut self.arena,
            View::SDecl { var, value: None },
            kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
        );
        self.statements.push(declaration);
    }

    /// 4.1 `lower_catch` on entering the node (OCaml
    /// `Lam_compile.compile_staticcatch`; C: flatten_nested_caches,
    /// compile_staticcatch_in_return, emit_multi_staticcatch_prelude).
    ///
    /// Cost: one flag read per catch that is flattened into the table, plus
    /// `exits_to_pending` for a handler that has `HAS_EXIT`; one declaration
    /// per handler parameter; for more than one handler, the grouping of
    /// 3.9 step 2 over the handlers. The form is chosen from `cx.cont`, the
    /// length of the table and one flag: no body or handler is walked for it.
    pub(super) fn catch(&mut self, cx: Cx, node: NodeId) -> Result<Catch, Unsupported> {
        if self.jumps.is_empty() {
            self.jumps.resize(self.arena.pools.catches.len(), Jump::NONE);
        }
        // Step 1: flatten. The table is collected outermost first.
        let table = self.catch_table.len();
        let mut body = node;
        while let View::Catch { body: inner, handler, header } = self.source.view(body) {
            if body != node {
                self.catch_flag_reads += 1;
                if self.has_exit(handler) && self.exits_to_pending(handler) {
                    break;
                }
                // A flattened catch is not entered by the traversal.
                self.source_steps += 1;
            }
            self.jumps[header.index()].order = PENDING;
            self.catch_table.push((handler, header));
            body = inner;
        }
        self.catch_table[table..].reverse();
        let len = self.catch_table.len() - table;
        if len > 1 {
            // Several handlers in one dispatch: the next slice of this file.
            return Err(Unsupported("static catch"));
        }

        let start = self.statements.mark();
        // Step 2: the cheap form, the first arm of `compile_staticcatch`.
        let cheap = len == 1
            && matches!(
                cx.cont,
                Cont::Effect(Tail::Return(Ret::Named { in_catch: false, .. }))
            )
            && {
                self.catch_flag_reads += 1;
                !self.has_exit(self.catch_table[table].0)
            };
        if cheap {
            // The handler after the body: decided with `in_catch`, later.
            return Err(Unsupported("static catch"));
        }
        let (target, exit) = {
            let target = match cx.cont {
                // C: compile_staticcatch_expr: the result precedes `exit`.
                Cont::Value(_) => Some((LetKind::Strict, self.fresh_variable("tmp"))),
                Cont::Declare(kind, var) => Some((kind, var)),
                _ => None,
            };
            if let Some((kind, var)) = target {
                self.declare_empty(kind, var);
            }
            let exit = self.fresh_variable("exit");
            let zero = plain::int(&mut self.arena, 0);
            let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Variable, exit, zero);
            self.statements.push(declaration);
            (target.map(|(_, var)| var), Some(exit))
        };
        // 4.2 invariant 3: a table starts above every visible entry.
        let first = i32::try_from(cx.jumps.0 + 1).expect("exit order capacity");
        for index in 0..len {
            let header = self.catch_table[table + index].1;
            self.jumps[header.index()] = Jump {
                exit: exit.unwrap_or(VarId(u32::MAX)),
                order: if cheap { CHEAP } else { first + index as i32 },
            };
            for var in self.arena.catch(header).params.iter() {
                self.declare_empty(LetKind::Variable, var);
            }
        }
        let (groups, next, bodies) = if len > 1 {
            // C: compile_grouped_staticcatch_handlers.
            let mut handlers = std::mem::take(&mut self.scratch);
            handlers.extend(self.catch_table[table..].iter().map(|&(handler, _)| handler));
            let list = self.source.lists.push(&handlers);
            handlers.clear();
            self.scratch = handlers;
            self.prepare_switch_hashes();
            self.group_switch_cases(list, len, None)
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };
        let frame = Catch(self.catches.len() as u32);
        self.catches.push(Some(Plan {
            start,
            table: table as u32,
            len: len as u32,
            body,
            exit,
            first,
            target,
            mid: 0,
            body_finished: Finished::False,
            handler_finished: Finished::False,
            handler_empty: true,
            groups,
            next,
            bodies,
            output: Vec::new(),
            clauses: Vec::new(),
        }));
        Ok(frame)
    }

    fn catch_plan(&self, frame: Catch) -> &Plan {
        self.catches[frame.0 as usize].as_ref().expect("live catch frame")
    }

    /// 4.1: the body with the entries visible, then the handlers. The cheap
    /// form's handler is lowered in `cx` itself; the explicit form's
    /// handlers in the body's continuation, the last of each group of equal
    /// handlers only. One step per handler that is lowered.
    pub(super) fn catch_children(&self, cx: Cx, frame: Catch, into: &mut Vec<(Cx, NodeId)>) {
        let plan = self.catch_plan(frame);
        let inner = Cx {
            cont: Self::catch_cont(cx.cont, plan.target),
            jumps: JumpTop(cx.jumps.0 + plan.len),
            ..cx
        };
        into.push((inner, plan.body));
        if plan.exit.is_none() {
            into.push((cx, self.catch_table[plan.table as usize].0));
        } else if plan.len == 1 {
            into.push((inner, self.catch_table[plan.table as usize].0));
        } else {
            into.extend(plan.bodies.iter().map(|&handler| (inner, handler)));
        }
    }

    /// As the body and each handler complete; `cx` is the child's. In E the
    /// child is a block (K3: C: compile_effect_block_output). A handler
    /// of a table with several becomes its clause: one step per statement of
    /// the handler, copied to its list once.
    pub(super) fn catch_child(&mut self, cx: Cx, frame: Catch, index: usize, child: Probed) -> Probed {
        let mut out = self.realize(cx, child);
        if let Some(value) = out.value.take() {
            debug_assert!(matches!(cx.cont, Cont::Effect(Tail::No)));
            self.drop_pure_effect(value);
        }
        let run = self.statements.trim(Span { start: out.stmts.start, len: 0 });
        let finished = out.finished;
        let top = self.statements.mark().start;
        let plan = self.catches[frame.0 as usize].as_mut().expect("live catch frame");
        if index == 0 {
            plan.mid = top;
            plan.body_finished = finished;
        } else if plan.len == 1 {
            plan.handler_finished = finished;
            plan.handler_empty = run.len == 0;
        } else {
            let handler = plan.bodies[index - 1];
            // C: compile_exit_dispatch: a return continuation keeps the
            // break only when the handler holds an exit (4.2 invariant 5).
            let should_break = finished != Finished::True
                && (!matches!(cx.cont, Cont::Effect(Tail::Return(_))) || self.has_exit(handler));
            let list = self.statements.take_list(&mut self.arena, run);
            let block = self.arena.block_from_list(list);
            let plan = self.catches[frame.0 as usize].as_mut().expect("live catch frame");
            plan.output.push(block);
            plan.clauses.push(ClauseMeta { should_break, comment: None, loc: None });
        }
        Probed::Out(Out { stmts: self.statements.mark(), value: None, finished })
    }

    /// 4.1 after the children: `append(declarations, append(body,
    /// handler))` for the cheap form, else the dispatch on `exit` (C:6674
    /// compile_exit_dispatch). Constant for one handler, plus one
    /// `if_statement` over its statements; one step per handler of a table
    /// with several. A finished body drops what follows it, releasing each
    /// dropped statement once.
    pub(super) fn finish_catch(&mut self, cx: Cx, frame: Catch) -> Probed {
        let plan = self.catches[frame.0 as usize].take().expect("live catch frame");
        while self.catches.last().is_some_and(Option::is_none) {
            self.catches.pop();
        }
        self.catch_table.truncate(plan.table as usize);
        let after_body = Span { start: plan.mid, len: 0 };
        let finished = if plan.body_finished == Finished::True {
            // Js_output.append_output: nothing follows a finished output.
            let dropped = self.statements.since(after_body);
            self.release_run(dropped);
            for &block in &plan.output {
                self.arena.release(block);
            }
            Finished::True
        } else if plan.exit.is_none() {
            if plan.handler_empty && plan.handler_finished == Finished::Dummy {
                plan.body_finished
            } else {
                plan.handler_finished
            }
        } else {
            self.exit_dispatch(&plan);
            Finished::False
        };
        let stmts = self.statements.since(plan.start);
        Probed::Out(match cx.cont {
            // C: compile_staticcatch_expr: never finished.
            Cont::Value(_) => Out {
                stmts,
                value: Some(self.pure_expression(
                    View::Var { var: plan.target.expect("value catch result") },
                    0,
                )),
                finished: Finished::False,
            },
            // K2: C: compile_effect_output keeps `undefined` as the value.
            Cont::Effect(Tail::No) => Out {
                stmts,
                value: Some(self.pure_expression(View::JUndefined, 0)),
                finished,
            },
            _ => Out { stmts, value: None, finished },
        })
    }

    /// C: compile_exit_dispatch on the lowered handlers: `if (exit ===
    /// order) { handler }` for one, nothing when its block is empty; a
    /// switch on `exit` without a default for several. One step per handler.
    fn exit_dispatch(&mut self, plan: &Plan) {
        let exit = plan.exit.expect("explicit catch");
        if plan.len == 1 {
            let run = self.statements.trim(Span { start: plan.mid, len: 0 });
            if self.statements.first(run).is_none() {
                self.statements.kill(run);
                return;
            }
            let exit = self.pure_expression(View::Var { var: exit }, 0);
            let order = plain::int(&mut self.arena, plan.first);
            let test = norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, exit, order);
            let statement = self.if_statement(test, run, super::cond::EMPTY);
            self.statements.push(statement);
            return;
        }
        let mut keys = Vec::with_capacity(plan.len as usize);
        let mut clauses = Vec::with_capacity(plan.len as usize);
        let mut actions = Vec::with_capacity(plan.len as usize);
        for (group, &head) in plan.groups.iter().enumerate() {
            let mut case = head;
            loop {
                keys.push(CaseKey::Lambda(crate::lambda::SwitchKey::Int(plan.first + case as i32)));
                if plan.next[case] == super::switch::NONE {
                    actions.push(plan.output[group]);
                    clauses.push(plan.clauses[group]);
                    break;
                }
                let empty = self.arena.lists.push(&[]);
                actions.push(self.arena.block_from_list(empty));
                clauses.push(ClauseMeta { should_break: false, comment: None, loc: None });
                case = plan.next[case];
            }
        }
        let header = self.arena.switch_header(crate::bir::SwitchHeader {
            constants: keys.len() as u32,
            keys,
            clauses,
            has_default: false,
            consts_full: false,
            blocks_full: false,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let scrutinee = self.pure_expression(View::Var { var: exit }, 0);
        let statement = plain::node(
            &mut self.arena,
            View::SSwitch { scrutinee, actions: &actions, header },
            0,
        );
        self.statements.push(statement);
    }

    /// 4.1 `lower_exit` on entering the node (OCaml
    /// `Lam_compile.compile_staticraise`; C: compile_static_raise_jump_output,
    /// compile_fallthrough_static_raise_return_output). One label
    /// lookup, one table read, and one step per argument to count those the
    /// cheap form skips.
    pub(super) fn exit(&mut self, label: u32, args: ListId) -> Exit {
        let catch = self.catch_of(label);
        let jump = self.jumps[catch.index()];
        let params = self.arena.catch(catch).params;
        let arguments = self.source.lists.get(args);
        assert_eq!(arguments.len(), params.len(), "exit arity");
        let kept = if jump.order == CHEAP {
            arguments
                .iter()
                .zip(params.iter())
                .filter(|&(&arg, param)| !self.is_variable(arg, param))
                .count()
        } else {
            arguments.len()
        } as u32;
        let start = self.statements.mark().start;
        if kept > 1 {
            for _ in 0..kept {
                self.statements.reserve();
            }
        }
        Exit { catch, args, start, kept }
    }

    /// C: compile_fallthrough_static_raise_return_output: an argument that
    /// is the parameter itself. Constant.
    fn is_variable(&self, node: NodeId, var: VarId) -> bool {
        matches!(self.source.view(node), View::Var { var: other } if other == var)
    }

    /// The arguments, last first, each assigning its parameter. One step
    /// per argument.
    pub(super) fn exit_children(&self, cx: Cx, exit: &Exit, into: &mut Vec<(Cx, NodeId)>) {
        let jump = self.jumps[exit.catch.index()];
        let params = self.arena.catch(exit.catch).params;
        let arguments = self.source.lists.get(exit.args);
        let at = into.len();
        for (&arg, param) in arguments.iter().zip(params.iter()) {
            if jump.order == CHEAP && self.is_variable(arg, param) {
                continue;
            }
            into.push((Cx { cont: Cont::Assign(param), ..cx }, arg));
        }
        into[at..].reverse();
    }

    /// As each argument completes. With several arguments the run moves to
    /// the argument's slot, so that the output is in source order: one step
    /// per statement of the argument.
    pub(super) fn exit_child(&mut self, cx: Cx, exit: &Exit, index: usize, child: Probed) -> Probed {
        let out = self.realize(cx, child);
        debug_assert!(out.value.is_none());
        if exit.kept > 1 {
            let slot = exit.start + exit.kept - 1 - index as u32;
            self.statements.hold_run(slot, out.stmts);
            return Probed::Out(Out {
                stmts: self.statements.mark(),
                value: None,
                finished: out.finished,
            });
        }
        Probed::Out(out)
    }

    /// The argument outputs in source order, then `exit = order` in the
    /// explicit form, joined by `append`: a finished argument drops what
    /// follows it. The continuation is ignored, except for the value the
    /// legacy families read: `undefined` in V and E, and its declaration in
    /// D (C: compile_expr, compile_let_binding_output). The output is not finished (4.2 invariant 5).
    /// One step per argument.
    pub(super) fn finish_exit(
        &mut self,
        cx: Cx,
        exit: Exit,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        // Children arrive last argument first: the last match is the first
        // finished argument in source order.
        let mut finished_at = None;
        for (index, child) in children.enumerate() {
            let Probed::Out(out) = child else { unreachable!("argument was realized") };
            if out.finished == Finished::True {
                finished_at = Some(exit.kept - 1 - index as u32);
            }
        }
        let jump = self.jumps[exit.catch.index()];
        let finished = match finished_at {
            Some(at) => {
                if exit.kept > 1 {
                    let dropped = Span { start: exit.start + at + 1, len: exit.kept - at - 1 };
                    self.release_run(dropped);
                }
                Finished::True
            }
            None => {
                if jump.order != CHEAP {
                    let order = plain::int(&mut self.arena, jump.order);
                    let statement = crate::bir::j::assign(&mut self.arena, jump.exit, order);
                    self.statements.push(statement);
                }
                Finished::False
            }
        };
        if matches!(cx.cont, Cont::Effect(_)) {
            // B: unnest_block of C: compile_return_output and C:2664
            // compile_effect_block_output: one argument whose output is one
            // block is its statements.
            self.unnest(exit.start);
        }
        let value = match cx.cont {
            Cont::Value(_) | Cont::Effect(Tail::No) => {
                Some(self.pure_expression(View::JUndefined, 0))
            }
            Cont::Declare(kind, var) => {
                if finished != Finished::True {
                    let undefined = self.pure_expression(View::JUndefined, 0);
                    let statement = crate::bir::j::declare(&mut self.arena, kind, var, undefined);
                    self.statements.push(statement);
                }
                None
            }
            Cont::Assign(_) | Cont::Effect(Tail::Return(_)) => None,
        };
        Probed::Out(Out {
            stmts: self.statements.since(Span { start: exit.start, len: 0 }),
            value,
            finished,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::{LamLoc, SwitchDispatch, SwitchKey};

    /// The continuations this file lowers a catch in so far.
    const SUPPORTED: &[u8] = &[0, 1, 2, 3];

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn int(a: &mut LamArena, i: i32) -> Lam {
        a.const_(C::Int { i, comment: None })
    }

    /// A call with an effect and a value.
    fn effect(a: &mut LamArena, i: i32) -> Lam {
        let n = int(a, i);
        a.prim_raw(P::PinitMod, &[n], LamLoc::NONE)
    }

    fn raise(a: &mut LamArena, i: i32) -> Lam {
        let n = int(a, i);
        a.prim_raw(P::Praise, &[n], LamLoc::NONE)
    }

    fn x(a: &mut LamArena) -> Lam {
        a.var(id("x", 10))
    }

    /// `switch x { keys[i] => actions[i]; default }` on integers.
    fn switch(a: &mut LamArena, actions: &[Lam], default: Option<Lam>) -> Lam {
        let scrutinee = x(a);
        let all: Vec<Lam> = actions.iter().copied().chain(default).collect();
        let list = a.add_list(&all);
        let info = a.add_switch(
            false,
            (0..actions.len() as i32).map(SwitchKey::Int),
            false,
            std::iter::empty(),
            default.is_some(),
            SwitchDispatch::Direct,
        );
        a.switch_raw(scrutinee, list, info)
    }

    fn compare(a: LamArena, root: Lam, contexts: &[u8]) {
        super::super::oracle_tests::compare_in_contexts(a, root, None, true, contexts);
    }

    /// `catch (if x then exit 1 else <other>) with (1) <handler>`.
    fn one_handler(a: &mut LamArena, other: Lam, handler: Lam) -> Lam {
        let test = x(a);
        let exit = a.static_raise(1, &[]);
        let body = a.if_(test, exit, other);
        a.static_catch(body, 1, &[], handler)
    }

    #[test]
    fn one_handler_in_value_declaration_effect_and_assignment() {
        // A handler with an effect, a constant handler, an empty handler, a
        // body that finishes, and a handler that finishes.
        for case in 0..5 {
            let mut a = LamArena::new();
            let other = if case == 3 { raise(&mut a, 2) } else { effect(&mut a, 2) };
            let handler = match case {
                0 | 3 => effect(&mut a, 3),
                1 => int(&mut a, 3),
                2 => a.const_(C::JsUndefined { is_unit: true }),
                _ => raise(&mut a, 3),
            };
            let root = one_handler(&mut a, other, handler);
            compare(a, root, SUPPORTED);
        }
    }

    #[test]
    fn handler_parameters_in_value_declaration_effect_and_assignment() {
        // One parameter given a variable, a call, a conditional that needs
        // statements, and a raise; then two parameters, lowered last first
        // and emitted in source order; then a finished first argument.
        for case in 0..6 {
            let mut a = LamArena::new();
            let n = id("n", 20);
            let m = id("m", 21);
            let params: &[Ident] = if case < 4 { &[n] } else { &[n, m] };
            let args: Vec<Lam> = match case {
                0 => vec![a.var(id("y", 11))],
                1 => vec![effect(&mut a, 5)],
                2 => {
                    let test = a.var(id("y", 11));
                    let yes = raise(&mut a, 6);
                    let no = effect(&mut a, 7);
                    vec![a.if_(test, yes, no)]
                }
                3 => vec![raise(&mut a, 8)],
                4 => {
                    let test = a.var(id("y", 11));
                    let yes = raise(&mut a, 6);
                    let no = effect(&mut a, 7);
                    let first = a.if_(test, yes, no);
                    let test = a.var(id("z", 12));
                    let yes = raise(&mut a, 16);
                    let no = effect(&mut a, 17);
                    vec![first, a.if_(test, yes, no)]
                }
                _ => vec![raise(&mut a, 8), effect(&mut a, 9)],
            };
            let test = x(&mut a);
            let exit = a.static_raise(1, &args);
            let other = effect(&mut a, 2);
            let body = a.if_(test, exit, other);
            let uses: Vec<Lam> = params.iter().map(|&p| a.var(p)).collect();
            let handler = a.prim_raw(P::PinitMod, &uses[..1], LamLoc::NONE);
            let handler = if uses.len() > 1 { a.seq_raw(handler, uses[1]) } else { handler };
            let root = a.static_catch(body, 1, params, handler);
            compare(a, root, SUPPORTED);
        }
    }

    #[test]
    fn exits_under_a_switch_in_value_declaration_effect_and_assignment() {
        let mut a = LamArena::new();
        let cases = [a.static_raise(1, &[]), effect(&mut a, 2), a.static_raise(1, &[])];
        let default = a.static_raise(1, &[]);
        let body = switch(&mut a, &cases, Some(default));
        let handler = effect(&mut a, 3);
        let root = a.static_catch(body, 1, &[], handler);
        compare(a, root, SUPPORTED);
    }

    #[test]
    fn a_handler_that_holds_an_exit_takes_the_explicit_form_in_return_position() {
        // The handler is a catch of its own: it has an exit, so the outer
        // catch needs no `in_catch` to take the explicit form.
        let mut a = LamArena::new();
        let test = a.var(id("y", 11));
        let (exit, other) = (a.static_raise(3, &[]), effect(&mut a, 5));
        let inner = a.if_(test, exit, other);
        let inner_handler = raise(&mut a, 6);
        let handler = a.static_catch(inner, 3, &[], inner_handler);
        let other = effect(&mut a, 2);
        let root = one_handler(&mut a, other, handler);
        compare(a, root, &[4]);
    }
}
