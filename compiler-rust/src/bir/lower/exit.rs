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
    pub(super) fn catch(&mut self, cx: Cx, node: NodeId) -> Catch {
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
        let (target, exit) = if cheap {
            (None, None)
        } else {
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
        frame
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

    const ALL: &[u8] = &[0, 1, 2, 3, 4];

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
    fn one_handler_in_every_continuation() {
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
            compare(a, root, ALL);
        }
    }

    /// Three nested catches whose handlers hold no exit: one table.
    fn three_handlers(a: &mut LamArena, handlers: [Lam; 3], default: Lam) -> Lam {
        let exits: Vec<Lam> = (1..=3).map(|label| a.static_raise(label, &[])).collect();
        let mut root = switch(a, &exits, Some(default));
        for (label, handler) in (1..=3).zip(handlers) {
            root = a.static_catch(root, label, &[], handler);
        }
        root
    }

    #[test]
    fn three_handlers_in_one_dispatch_in_every_continuation() {
        // Distinct handlers; two equal handlers (one clause group); a
        // handler that finishes; equal first and last handlers.
        for case in 0..4 {
            let mut a = LamArena::new();
            let handlers = match case {
                0 => [effect(&mut a, 11), effect(&mut a, 12), effect(&mut a, 13)],
                1 => [effect(&mut a, 11), effect(&mut a, 11), effect(&mut a, 13)],
                2 => [effect(&mut a, 11), raise(&mut a, 12), int(&mut a, 13)],
                _ => [effect(&mut a, 11), effect(&mut a, 12), effect(&mut a, 11)],
            };
            let default = effect(&mut a, 9);
            let root = three_handlers(&mut a, handlers, default);
            compare(a, root, ALL);
        }
    }

    /// `catch (catch (if x then exit 1 else e2) with (1) (if y then exit 2
    /// else e3)) with (2) e4`: the inner handler exits to the outer label,
    /// so the two do not share a table.
    fn exit_to_outer(a: &mut LamArena) -> Lam {
        let other = effect(a, 2);
        let test = a.var(id("y", 11));
        let out = a.static_raise(2, &[]);
        let stay = effect(a, 3);
        let handler = a.if_(test, out, stay);
        let inner = one_handler(a, other, handler);
        let outer = effect(a, 4);
        a.static_catch(inner, 2, &[], outer)
    }

    #[test]
    fn a_handler_that_exits_to_an_outer_handler_in_every_continuation() {
        let mut a = LamArena::new();
        let root = exit_to_outer(&mut a);
        compare(a, root, ALL);
    }

    #[test]
    fn handler_parameters_in_every_continuation() {
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
            compare(a, root, ALL);
        }
    }

    #[test]
    fn a_conditional_in_return_position_does_not_fold_over_a_catch() {
        // C: lambda_contains_statement_value_form keeps `if (c) { e;
        // return h }` where the branch is a catch, although its statements
        // are effects followed by one return.
        let mut a = LamArena::new();
        let head = effect(&mut a, 1);
        let test = a.var(id("y", 11));
        let first = a.static_raise(1, &[]);
        let second = a.static_raise(1, &[]);
        let exits = a.if_(test, first, second);
        let body = a.seq_raw(head, exits);
        let handler = int(&mut a, 5);
        let caught = a.static_catch(body, 1, &[], handler);
        let test = x(&mut a);
        let other = int(&mut a, 2);
        let root = a.if_(test, caught, other);
        compare(a, root, ALL);
    }

    #[test]
    fn exits_under_a_switch_and_a_catch_under_a_switch_in_every_continuation() {
        // One handler: exits from two cases and the default of a switch.
        let mut a = LamArena::new();
        let cases = [a.static_raise(1, &[]), effect(&mut a, 2), a.static_raise(1, &[])];
        let default = a.static_raise(1, &[]);
        let body = switch(&mut a, &cases, Some(default));
        let handler = effect(&mut a, 3);
        let root = a.static_catch(body, 1, &[], handler);
        compare(a, root, ALL);
        // A catch in a switch case, whose handler exits to the catch around
        // the switch: the case breaks in a return continuation.
        let mut a = LamArena::new();
        let other = effect(&mut a, 2);
        let out = a.static_raise(2, &[]);
        let inner = one_handler(&mut a, other, out);
        let cases = [inner, effect(&mut a, 5), a.static_raise(2, &[])];
        let body = switch(&mut a, &cases, None);
        let handler = effect(&mut a, 4);
        let root = a.static_catch(body, 2, &[], handler);
        compare(a, root, ALL);
    }

    /// One catch of label 1 in return position, by the shapes the predicates
    /// of row K14 read: the body, the handler, the parameters, what
    /// encloses the catch, and whether the function returns unit.
    #[derive(Clone, Copy, Debug)]
    struct Shape {
        body: u8,
        handler: u8,
        params: bool,
        around: u8,
        return_unit: bool,
    }
    const BODIES: u8 = 10;
    const HANDLERS: u8 = 8;
    const AROUND: u8 = 4;

    fn shape(a: &mut LamArena, s: Shape) -> Option<Lam> {
        let n = id("n", 20);
        let enclosed = s.around > 0;
        let exit = |a: &mut LamArena| {
            let args = if s.params { vec![effect(a, 30)] } else { vec![] };
            a.static_raise(1, &args)
        };
        let y = |a: &mut LamArena| a.var(id("y", 11));
        // Bodies: every one exits to label 1; some to the enclosing label 9.
        let body = match s.body {
            // lambda_contains_static_raise_to_label on a conditional.
            0 => {
                let (t, e, o) = (x(a), exit(a), effect(a, 2));
                a.if_(t, e, o)
            }
            // uses_fallthrough: one case and a default that is the exit.
            1 => {
                let (c, d) = (effect(a, 2), exit(a));
                switch(a, &[c], Some(d))
            }
            // lambda_has_multiple_static_raises_to_label.
            2 => {
                let (c0, c1, d) = (exit(a), effect(a, 2), exit(a));
                switch(a, &[c0, c1], Some(d))
            }
            // switch_cases_contain_nontrivial_static_raise_to_label.
            3 => {
                let (h, e) = (effect(a, 3), exit(a));
                let c0 = a.seq_raw(h, e);
                let c1 = effect(a, 2);
                switch(a, &[c0, c1], None)
            }
            // lambda_contains_static_raise_to_other_label.
            4 if enclosed => {
                let (c0, c1, d) = (exit(a), a.static_raise(9, &[]), effect(a, 2));
                switch(a, &[c0, c1], Some(d))
            }
            // The string switch twins of 1 and 3.
            5 => {
                let (scrutinee, c, d) = (x(a), effect(a, 2), exit(a));
                a.string_switch(scrutinee, &[("a", c)], Some(d))
            }
            6 => {
                let (h, e) = (effect(a, 3), exit(a));
                let c0 = a.seq_raw(h, e);
                let (scrutinee, c1) = (x(a), effect(a, 2));
                a.string_switch(scrutinee, &[("a", c0), ("b", c1)], None)
            }
            // A sequence and a binding before the exit.
            7 => {
                let (h, t, e, o) = (effect(a, 3), x(a), exit(a), effect(a, 2));
                let tail = a.if_(t, e, o);
                a.seq_raw(h, tail)
            }
            // The body is a catch whose handler exits to label 1 (they do
            // not share a table): `compile_staticcatch_in_return`'s arm on
            // `lambda_contains_static_raise(nested_handler)`.
            8 => {
                let (t, e, o) = (y(a), a.static_raise(2, &[]), effect(a, 2));
                let inner = a.if_(t, e, o);
                let handler = exit(a);
                a.static_catch(inner, 2, &[], handler)
            }
            // The same, with an exit to the enclosing label in the body.
            9 if enclosed => {
                let (c0, c1) = (a.static_raise(2, &[]), a.static_raise(9, &[]));
                let d = effect(a, 2);
                let inner = switch(a, &[c0, c1], Some(d));
                let handler = exit(a);
                a.static_catch(inner, 2, &[], handler)
            }
            _ => return None,
        };
        let use_param = |a: &mut LamArena, i: i32| {
            if s.params {
                let v = a.var(n);
                a.prim_raw(P::PinitMod, &[v], LamLoc::NONE)
            } else {
                effect(a, i)
            }
        };
        let handler = match s.handler {
            0 => use_param(a, 4),
            // handler_returns_unit_undefined.
            1 => a.const_(C::JsUndefined { is_unit: true }),
            // pure_return_static_raise_dispatch_has_terminal_value.
            2 => int(a, 4),
            // staticcatch_handler_is_identity_binding.
            3 if s.params => a.var(n),
            // handler_is_pure_outward_static_raise_forwarder,
            // active_static_raise_target_exists.
            4 if enclosed => a.static_raise(9, &[]),
            // return_handler_requires_explicit_staticcatch_jump.
            5 if enclosed => {
                let (t, e, o) = (y(a), a.static_raise(9, &[]), use_param(a, 4));
                a.if_(t, e, o)
            }
            // lambda_contains_staticcatch: a catch under a function in the
            // handler. Its exit does not leave the function.
            6 => {
                let (t, e, o) = (y(a), a.static_raise(3, &[]), int(a, 5));
                let inner = a.if_(t, e, o);
                let h = int(a, 6);
                let caught = a.static_catch(inner, 3, &[], h);
                a.function_(0, &[], caught, Default::default(), LamLoc::NONE)
            }
            // A catch in the handler itself: the handler has an exit.
            7 => {
                let (t, e, o) = (y(a), a.static_raise(3, &[]), use_param(a, 5));
                let inner = a.if_(t, e, o);
                let h = effect(a, 6);
                a.static_catch(inner, 3, &[], h)
            }
            _ => return None,
        };
        let params: &[Ident] = if s.params { &[n] } else { &[] };
        let caught = a.static_catch(body, 1, params, handler);
        let z = a.var(id("z", 12));
        let around = match s.around {
            0 => caught,
            // In the body of a cheap catch.
            1 => {
                let out = a.static_raise(9, &[]);
                let body = a.if_(z, caught, out);
                let handler = effect(a, 90);
                a.static_catch(body, 9, &[], handler)
            }
            // In the body of an explicit catch (two handlers in one table).
            2 => {
                let w = a.var(id("w", 13));
                let (o9, o8) = (a.static_raise(9, &[]), a.static_raise(8, &[]));
                let outs = a.if_(w, o9, o8);
                let body = a.if_(z, caught, outs);
                let h9 = effect(a, 90);
                let inner = a.static_catch(body, 9, &[], h9);
                let h8 = effect(a, 80);
                a.static_catch(inner, 8, &[], h8)
            }
            // In the handler of a cheap catch: not in a catch again.
            _ => {
                let (o, e) = (a.static_raise(9, &[]), effect(a, 91));
                let body = a.if_(z, o, e);
                if matches!(s.body, 4 | 9) || matches!(s.handler, 4 | 5) {
                    return None;
                }
                a.static_catch(body, 9, &[], caught)
            }
        };
        let attr = crate::lambda::FunctionAttribute { return_unit: s.return_unit, ..Default::default() };
        Some(a.function_(0, &[], around, attr, LamLoc::NONE))
    }

    fn all_shapes() -> impl Iterator<Item = Shape> {
        (0..BODIES).flat_map(|body| {
            (0..HANDLERS).flat_map(move |handler| {
                (0..AROUND).flat_map(move |around| {
                    [false, true].into_iter().flat_map(move |params| {
                        [false, true].into_iter().map(move |return_unit| Shape {
                            body,
                            handler,
                            params,
                            around,
                            return_unit,
                        })
                    })
                })
            })
        })
    }

    #[test]
    fn the_form_of_a_catch_in_return_position_agrees_with_row_k14() {
        let mut differing = Vec::new();
        let mut compared = 0;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        for s in all_shapes() {
            let mut a = LamArena::new();
            let Some(root) = shape(&mut a, s) else { continue };
            compared += 1;
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                compare(a, root, &[0]);
            }));
            if result.is_err() {
                differing.push(s);
            }
        }
        std::panic::set_hook(hook);
        eprintln!("compared {compared} shapes");
        assert!(differing.is_empty(), "{} differ: {differing:#?}", differing.len());
    }

    use crate::lambda::lam_compat::FieldDbgInfo;
    use crate::lambda::{ApInfo, ApplyStatus};
    use crate::types::{VariantConstructorCase as Case, VariantLiteralTag as Literal};

    fn call(a: &mut LamArena, name: &str, stamp: i32, args: &[Lam]) -> Lam {
        let f = a.var(id(name, stamp));
        a.apply_raw(f, args, ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE })
    }
    fn field(a: &mut LamArena, index: i32, of: Lam) -> Lam {
        a.prim_raw(P::Pfield(index, FieldDbgInfo::Variant), &[of], LamLoc::NONE)
    }
    fn binary(a: &mut LamArena, p: P, left: Lam, right: Lam) -> Lam {
        a.prim_raw(p, &[left, right], LamLoc::NONE)
    }
    /// `switch* scrutinee` on `type t = A | B(int) | C(int, int) | D`.
    fn named(
        a: &mut LamArena,
        scrutinee: Lam,
        constants: &[(&str, Lam)],
        blocks: &[(&str, Lam)],
        default: Option<Lam>,
    ) -> Lam {
        let tag = |name: &str| crate::types::VariantTag {
            name: crate::name::Name::new(name),
            literal: Literal::String(name.into()),
        };
        let constant_keys: Vec<_> = constants
            .iter()
            .map(|(name, _)| SwitchKey::Constructor(Case::Constant(tag(name))))
            .collect();
        let block_keys: Vec<_> = blocks
            .iter()
            .map(|(name, _)| {
                SwitchKey::Constructor(Case::Block(crate::types::VariantBlock::Tagged(
                    crate::types::variant_runtime::TaggedBlock { tag: tag(name), tag_name: None },
                )))
            })
            .collect();
        let actions: Vec<Lam> =
            constants.iter().chain(blocks).map(|&(_, action)| action).chain(default).collect();
        let actions = a.add_list(&actions);
        let info = a.add_switch(
            constants.len() == 2,
            constant_keys,
            blocks.len() == 2,
            block_keys,
            default.is_some(),
            SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
                tag_name: None,
                literal_tags: vec![Literal::String("A".into()), Literal::String("D".into())],
                block_types: vec![],
            }),
        );
        a.switch_raw(scrutinee, actions, info)
    }

    /// Section 4.3: the Lambda after the passes, with `big` and `log` as
    /// local functions (an external is lowered by another slice).
    #[test]
    fn worked_example_three_handlers_in_one_dispatch_in_return_position() {
        let mut a = LamArena::new();
        let (xv, yv) = (id("x", 10), id("y", 11));
        let (n, m) = (id("n", 20), id("m", 21));
        let int_ = |a: &mut LamArena, i| int(a, i);
        // case "A": switch y { "B": exit 2 y._0; default: 0 }
        let y = a.var(yv);
        let m_value = field(&mut a, 0, y);
        let to_m = a.static_raise(2, &[m_value]);
        let zero = int_(&mut a, 0);
        let y = a.var(yv);
        let case_a = named(&mut a, y, &[], &[("B", to_m)], Some(zero));
        // case "D": switch y { "C": exit 2 y._1; default: exit 3 }
        let y = a.var(yv);
        let m_value = field(&mut a, 1, y);
        let to_m = a.static_raise(2, &[m_value]);
        let fail = a.static_raise(3, &[]);
        let y = a.var(yv);
        let case_d = named(&mut a, y, &[], &[("C", to_m)], Some(fail));
        // case "B": switch y { "A": exit 1 x._0; default: exit 3 }
        let x_ = a.var(xv);
        let n_value = field(&mut a, 0, x_);
        let to_n = a.static_raise(1, &[n_value]);
        let fail = a.static_raise(3, &[]);
        let y = a.var(yv);
        let case_b = named(&mut a, y, &[("A", to_n)], &[], Some(fail));
        // case "C": switch y { "D": exit 1 x._0; default: exit 3 }
        let x_ = a.var(xv);
        let n_value = field(&mut a, 0, x_);
        let to_n = a.static_raise(1, &[n_value]);
        let fail = a.static_raise(3, &[]);
        let y = a.var(yv);
        let case_c = named(&mut a, y, &[("D", to_n)], &[], Some(fail));
        let x_ = a.var(xv);
        let dispatch =
            named(&mut a, x_, &[("A", case_a), ("D", case_d)], &[("B", case_b), ("C", case_c)], None);
        // with (3) big(1,2,3) + big(4,5,6) + big(7,8,9)
        let triple = |a: &mut LamArena, from: i32| {
            let args = [int(a, from), int(a, from + 1), int(a, from + 2)];
            call(a, "big", 30, &args)
        };
        let (b1, b2, b3) = (triple(&mut a, 1), triple(&mut a, 4), triple(&mut a, 7));
        let sum = binary(&mut a, P::Paddint, b1, b2);
        let handler3 = binary(&mut a, P::Paddint, sum, b3);
        let caught3 = a.static_catch(dispatch, 3, &[], handler3);
        // with (1 n) (log n; big(n, n + 1, n + 2))
        let nv = a.var(n);
        let log_n = call(&mut a, "log", 31, &[nv]);
        let (n0, n1, n2) = (a.var(n), a.var(n), a.var(n));
        let (one, two) = (int_(&mut a, 1), int_(&mut a, 2));
        let plus1 = binary(&mut a, P::Paddint, n1, one);
        let plus2 = binary(&mut a, P::Paddint, n2, two);
        let big_n = call(&mut a, "big", 30, &[n0, plus1, plus2]);
        let handler1 = a.seq_raw(log_n, big_n);
        let caught1 = a.static_catch(caught3, 1, &[n], handler1);
        // with (2 m) (log m; big(m, m * 2, m * 3))
        let mv = a.var(m);
        let log_m = call(&mut a, "log", 31, &[mv]);
        let (m0, m1, m2) = (a.var(m), a.var(m), a.var(m));
        let (two, three) = (int_(&mut a, 2), int_(&mut a, 3));
        let times2 = binary(&mut a, P::Pmulint, m1, two);
        let times3 = binary(&mut a, P::Pmulint, m2, three);
        let big_m = call(&mut a, "big", 30, &[m0, times2, times3]);
        let handler2 = a.seq_raw(log_m, big_m);
        let root = a.static_catch(caught1, 2, &[m], handler2);
        // The table of 4.3 is `[3, 1, 2]`: one dispatch, no handler walked.
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let source_root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::returning(), source_root).unwrap();
        state.realize(Cx::returning(), probed);
        assert_eq!((state.catch_flag_reads, state.catch_walk_steps), (2, 0));
        compare(a, root, ALL);
    }

    /// Section 4.4: the catch in the body of the loop, in an effect
    /// continuation. `break` and the assignment of `total` wait for the
    /// loop slice; a call stands in for each.
    #[test]
    fn worked_example_an_exit_from_a_nested_switch() {
        let mut a = LamArena::new();
        let (matched, k, total, n) = (id("match", 10), id("k", 11), id("total", 12), id("n", 20));
        let guarded = |a: &mut LamArena, against: i32| {
            let (kv, bound) = (a.var(k), int(a, against));
            let test = binary(a, P::Pintcomp(crate::lambda::lam_compat::Comparison::Neq), kv, bound);
            let kv = a.var(k);
            let log_k = call(a, "log", 31, &[kv]);
            let scrutinee = a.var(matched);
            let value = field(a, 0, scrutinee);
            let exit = a.static_raise(1, &[value]);
            a.if_(test, log_k, exit)
        };
        let zero = int(&mut a, 0);
        let case_a = call(&mut a, "log", 31, &[zero]);
        let case_d = call(&mut a, "stop", 32, &[]);
        let (case_b, case_c) = (guarded(&mut a, 1), guarded(&mut a, 2));
        let scrutinee = a.var(matched);
        let body = named(
            &mut a,
            scrutinee,
            &[("A", case_a), ("D", case_d)],
            &[("B", case_b), ("C", case_c)],
            None,
        );
        let (t, nv) = (a.var(total), a.var(n));
        let sum = binary(&mut a, P::Paddint, t, nv);
        let add = call(&mut a, "add", 33, &[sum]);
        let nv = a.var(n);
        let log_n = call(&mut a, "log", 31, &[nv]);
        let handler = a.seq_raw(add, log_n);
        let root = a.static_catch(body, 1, &[n], handler);
        compare(a, root, ALL);
    }

    #[test]
    fn a_handler_parameter_is_not_an_assigned_variable_for_argument_sequencing() {
        // A: delay_safe reads C: `assignable`, the targets of level-L
        // assignments. `n` is assigned by the exit, in J only: it is not
        // held in a temporary when a later argument needs statements.
        let mut a = LamArena::new();
        let n = id("n", 20);
        let test = x(&mut a);
        let value = effect(&mut a, 5);
        let exit = a.static_raise(1, &[value]);
        let other = effect(&mut a, 2);
        let body = a.if_(test, exit, other);
        let first = a.var(n);
        let test = a.var(id("y", 11));
        let (yes, no) = (raise(&mut a, 6), effect(&mut a, 7));
        let second = a.if_(test, yes, no);
        let handler = call(&mut a, "f", 30, &[first, second]);
        let root = a.static_catch(body, 1, &[n], handler);
        compare(a, root, ALL);
    }
}
