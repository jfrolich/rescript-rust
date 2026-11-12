//! Direct switch lowering: C: compile_switch_assignment_block_inner,
//! compile_switch_effect_block_inner and compile_switch_return_block_inner.
//! Group bodies are scheduled once by SourceProbe, never recursively lowered.
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, ClauseMeta, SwitchId};

/// A source-traversal frame is a handle into the switch-plan pool.
#[derive(Clone, Copy)]
pub(super) struct Switch(pub u32);

/// Legacy small string cases are selected before grouping.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Form {
    General,
    Body,
    If,
}

/// Runtime dispatch representation; named sides share the general string code.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Integer,
    String,
    Named,
}

/// Cold per-switch data, not copied down the source walk.
pub(super) struct Plan {
    pub(super) scrutinee: NodeId,
    pub(super) header: SwitchId,
    groups: Vec<usize>,
    next: Vec<usize>,
    pub(super) bodies: Vec<NodeId>,
    pub(super) default: Option<NodeId>,
    output: Vec<NodeId>,
    clauses: Vec<ClauseMeta>,
    pub(super) start: Span,
    pub(super) value: Option<NodeId>,
    target: Option<VarId>,
    runs: [Span; 2],
    declaration: Option<u32>,
    pub(super) head: u32,
    pub(super) form: Form,
    kind: Kind,
    pending_value: bool,
}

impl State {
    /// C: compile_switch_*_block_inner. O(c + compared nodes), apart from
    /// fingerprint indexing. Children are queued in grouped order, then default.
    pub(super) fn integer_switch(
        &mut self,
        cx: Cx,
        scrutinee: NodeId,
        operands: crate::bir::ListId,
        header: SwitchId,
    ) -> Result<Switch, Unsupported> {
        let h = self.arena.switch(header);
        if h.constants as usize != h.keys.len()
            || !matches!(h.dispatch, crate::lambda::SwitchDispatch::Direct)
            || !h
                .keys
                .iter()
                .all(|k| matches!(k, CaseKey::Lambda(crate::lambda::SwitchKey::Int(_))))
        {
            return Err(Unsupported("switch"));
        }
        self.plan_switch(cx, scrutinee, operands, header, Kind::Integer)
    }

    /// V: compile_string_switch_inner and C: compile_string_switch_*_block_inner.
    /// O(c + compared nodes + new payload bytes); no branch is probed.
    pub(super) fn string_switch(
        &mut self,
        cx: Cx,
        scrutinee: NodeId,
        operands: crate::bir::ListId,
        header: SwitchId,
    ) -> Result<Switch, Unsupported> {
        self.plan_switch(cx, scrutinee, operands, header, Kind::String)
    }

    /// Select the legacy form and prepare its single child schedule.
    /// O(c + compared nodes), with amortized payload fingerprinting.
    pub(super) fn plan_switch(
        &mut self,
        cx: Cx,
        scrutinee: NodeId,
        operands: crate::bir::ListId,
        header: SwitchId,
        kind: Kind,
    ) -> Result<Switch, Unsupported> {
        let h = self.arena.switch(header);
        let count = h.keys.len();
        let default = h
            .has_default
            .then(|| self.source.lists.get(operands)[count]);
        let string = kind != Kind::Integer;
        let complete = default.is_none()
            && (kind == Kind::Named || !matches!(cx.cont, Cont::Effect(Tail::No)));
        let form = if !string {
            Form::General
        } else if count == 0 || count == 1 && complete {
            Form::Body
        } else if count == 1 || count == 2 && complete {
            Form::If
        } else {
            Form::General
        };
        let (groups, next, bodies) = if form == Form::General {
            self.prepare_switch_hashes();
            self.group_switch_cases(operands, count, default)
        } else {
            (
                (0..count).collect(),
                vec![NONE; count],
                self.source.lists.get(operands)[..count].to_vec(),
            )
        };
        let start = self.statements.mark();
        let binding = match cx.cont {
            Cont::Value(_) if !string => Some((LetKind::Strict, self.fresh_variable("tmp"))),
            Cont::Declare(kind, var) => Some((kind, var)),
            _ => None,
        };
        let declaration = (string && binding.is_some()).then(|| self.statements.reserve());
        if let Some((kind, var)) = binding.filter(|_| !string) {
            let declaration = plain::node(
                &mut self.arena,
                View::SDecl { var, value: None },
                kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
            );
            self.statements.push(declaration);
        }
        let frame = Switch(self.switches.len() as u32);
        self.switches.push(Some(Plan {
            scrutinee,
            header,
            groups,
            next,
            bodies,
            default,
            output: Vec::new(),
            clauses: Vec::new(),
            start,
            value: None,
            target: binding.map(|(_, var)| var),
            runs: [Span::default(); 2],
            declaration,
            head: 0,
            form,
            kind,
            pending_value: string && matches!(cx.cont, Cont::Value(_)),
        }));
        Ok(frame)
    }
}

const NONE: usize = usize::MAX;

/// Cached by source node, shared by enclosing switches. Sixteen bytes per node.
#[derive(Clone, Copy, Default)]
pub(super) struct Facts {
    hash: u64,
    ready: bool,
    comparable: bool,
    exit: bool,
}

impl State {
    /// V: stable_group_switch_cases, C: filtered_switch_case_refs. Expected
    /// O(c + reachable nodes + confirmed equal nodes); collision candidates
    /// are confirmed by eq_approx. Dense case-indexed links preserve the head
    /// and last-member order without allocating one list per group.
    fn group_switch_cases(
        &mut self,
        operands: crate::bir::ListId,
        count: usize,
        default: Option<NodeId>,
    ) -> (Vec<usize>, Vec<usize>, Vec<NodeId>) {
        for i in 0..count {
            self.switch_facts(self.source.lists.get(operands)[i]);
        }
        if let Some(default) = default {
            self.switch_facts(default);
        }
        let cases = self.source.lists.get(operands)[..count].to_vec();
        let fingerprints: Vec<_> = cases.iter().map(|n| self.switch_facts[n.index()]).collect();
        // Fingerprints have no arena handle. The table contains case indices;
        // all actual state is in the dense arrays indexed by those indices.
        let mut table = hashbrown::HashTable::<usize>::with_capacity(cases.len());
        let mut groups = Vec::new();
        let mut next = vec![NONE; cases.len()];
        let mut heads: Vec<usize> = (0..cases.len()).collect();
        for i in (0..cases.len()).rev() {
            let facts = fingerprints[i];
            if let Some(default) = default {
                let d = self.switch_facts[default.index()];
                if facts.comparable
                    && d.comparable
                    && facts.hash == d.hash
                    && self.switch_equal(cases[i], default)
                {
                    continue;
                }
            }
            let matching = if facts.comparable {
                table
                    .find(facts.hash, |&j| {
                        fingerprints[j].hash == facts.hash
                            && self.switch_equal(cases[i], cases[heads[j]])
                    })
                    .copied()
            } else {
                None
            };
            if let Some(j) = matching {
                next[i] = heads[j];
                heads[j] = i;
            } else {
                groups.push(i);
                if facts.comparable {
                    table.insert_unique(facts.hash, i, |&j| fingerprints[j].hash);
                }
            }
        }
        groups.reverse();
        let bodies = groups.iter().map(|&i| cases[i]).collect();
        for group in &mut groups {
            *group = heads[*group];
        }
        (groups, next, bodies)
    }

    /// One iterative bottom-up visit per source node, memoized across switches.
    /// O(new reachable nodes + edges + immediate payload bytes). No recursion
    /// or allocation per node: traversal and operand scratch are reused.
    fn switch_facts(&mut self, root: NodeId) {
        use std::hash::{Hash, Hasher};
        let mut work = std::mem::take(&mut self.switch_work);
        work.push((root, false));
        while let Some((node, done)) = work.pop() {
            if self.switch_facts[node.index()].ready {
                continue;
            }
            let view = self.source.view(node);
            let comparable = matches!(
                view,
                View::Var { .. }
                    | View::Global { .. }
                    | View::Const { .. }
                    | View::Apply { .. }
                    | View::If { .. }
                    | View::Seq { .. }
                    | View::While { .. }
                    | View::Assign { .. }
                    | View::Exit { .. }
                    | View::Prim { .. }
                    | View::StrSwitch { .. }
                    | View::Break
                    | View::Continue
            );
            if !done {
                work.push((node, true));
                Self::switch_operands(view, |child| work.push((child, false)));
                continue;
            }
            self.switch_visits += 1;
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            (self.source.node(node).op() as u8).hash(&mut hash);
            let mut facts = Facts {
                hash: 0,
                ready: true,
                comparable,
                exit: matches!(view, View::Exit { .. }),
            };
            match view {
                View::Var { var } | View::Assign { var, .. } => var.hash(&mut hash),
                View::Global { module } => module.hash(&mut hash),
                View::Const { value } => self.switch_constant_hashes[value.index()].hash(&mut hash),
                View::Exit { label, .. } => label.hash(&mut hash),
                View::Prim { primitive, .. } => {
                    let p = &self.arena.primitive(primitive).primitive;
                    // PrawJsCode is deliberately not reflexive in eq_approx.
                    facts.comparable &=
                        !matches!(p, crate::lambda::lam_primitive::Primitive::PrawJsCode(_));
                    self.switch_primitive_hashes[primitive.index()].hash(&mut hash);
                }
                View::StrSwitch { header, .. } => {
                    let h = self.arena.switch(header);
                    h.has_default.hash(&mut hash);
                    for key in &h.keys {
                        let CaseKey::String(key) = key else {
                            unreachable!()
                        };
                        key.hash(&mut hash);
                    }
                }
                _ => {}
            }
            Self::switch_operands(view, |child| {
                let child = self.switch_facts[child.index()];
                child.hash.hash(&mut hash);
                facts.comparable &= child.comparable;
                facts.exit |= child.exit;
            });
            facts.hash = hash.finish();
            self.switch_facts[node.index()] = facts;
        }
        self.switch_work = work;
    }

    /// Children relevant to eq_approx, in order. O(arity), with borrowed lists.
    fn switch_operands(view: View<'_>, mut visit: impl FnMut(NodeId)) {
        match view {
            View::Apply { callee, args, .. } => {
                visit(callee);
                for &n in args {
                    visit(n);
                }
            }
            View::Prim { args, .. } | View::Exit { args, .. } => {
                for &n in args {
                    visit(n);
                }
            }
            View::If {
                condition,
                then_,
                else_,
            } => {
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
            View::Assign { value, .. } => visit(value),
            View::StrSwitch {
                scrutinee, actions, ..
            } => {
                visit(scrutinee);
                for &n in actions {
                    visit(n);
                }
            }
            _ => {}
        }
    }

    /// LamArena::eq_approx, confirmed on L nodes after the hash prefilter.
    /// O(compared nodes + payload equality); the work vector is reused.
    fn switch_equal(&mut self, left: NodeId, right: NodeId) -> bool {
        self.switch_comparisons += 1;
        let mut work = std::mem::take(&mut self.switch_pairs);
        work.push((left, right));
        let mut same = true;
        while let Some((left, right)) = work.pop() {
            self.switch_compared += 1;
            let l = self.source.view(left);
            let r = self.source.view(right);
            same = match (l, r) {
                (View::Var { var: a }, View::Var { var: b }) => a == b,
                (View::Global { module: a }, View::Global { module: b }) => a == b,
                (View::Const { value: a }, View::Const { value: b }) => {
                    self.switch_constants_equal(a, b)
                }
                (
                    View::Apply {
                        callee: a,
                        args: aa,
                        ..
                    },
                    View::Apply {
                        callee: b,
                        args: bb,
                        ..
                    },
                ) => {
                    work.push((a, b));
                    aa.len() == bb.len()
                }
                (
                    View::Prim {
                        primitive: a,
                        args: aa,
                    },
                    View::Prim {
                        primitive: b,
                        args: bb,
                    },
                ) => {
                    aa.len() == bb.len()
                        && self
                            .arena
                            .primitive(a)
                            .primitive
                            .eq_approx(&self.arena.primitive(b).primitive)
                }
                (View::Exit { label: a, args: aa }, View::Exit { label: b, args: bb }) => {
                    a == b && aa.len() == bb.len()
                }
                (View::Assign { var: a, value: av }, View::Assign { var: b, value: bv }) => {
                    work.push((av, bv));
                    a == b
                }
                (
                    View::If {
                        condition: a,
                        then_: b,
                        else_: c,
                    },
                    View::If {
                        condition: x,
                        then_: y,
                        else_: z,
                    },
                ) => {
                    work.extend([(a, x), (b, y), (c, z)]);
                    true
                }
                (
                    View::Seq {
                        first: a,
                        second: b,
                    },
                    View::Seq {
                        first: x,
                        second: y,
                    },
                )
                | (
                    View::While {
                        condition: a,
                        body: b,
                    },
                    View::While {
                        condition: x,
                        body: y,
                    },
                ) => {
                    work.extend([(a, x), (b, y)]);
                    true
                }
                (
                    View::StrSwitch {
                        scrutinee: a,
                        header: ah,
                        actions: aa,
                    },
                    View::StrSwitch {
                        scrutinee: b,
                        header: bh,
                        actions: bb,
                    },
                ) => {
                    work.push((a, b));
                    let (a, b) = (self.arena.switch(ah), self.arena.switch(bh));
                    aa.len() == bb.len() && a.has_default == b.has_default && a.keys.len() == b.keys.len()
                        && a.keys.iter().zip(&b.keys).all(|(a,b)| matches!((a,b), (CaseKey::String(a), CaseKey::String(b)) if a == b))
                }
                (View::Break, View::Break) | (View::Continue, View::Continue) => true,
                _ => false,
            };
            if !same {
                break;
            }
            match (l, r) {
                (View::Apply { args: a, .. }, View::Apply { args: b, .. })
                | (View::Prim { args: a, .. }, View::Prim { args: b, .. })
                | (View::Exit { args: a, .. }, View::Exit { args: b, .. })
                | (View::StrSwitch { actions: a, .. }, View::StrSwitch { actions: b, .. }) => {
                    work.extend(a.iter().copied().zip(b.iter().copied()))
                }
                _ => {}
            }
        }
        work.clear();
        self.switch_pairs = work;
        same
    }

    /// Read a live cold switch plan by its dense handle. O(1).
    pub(super) fn switch_plan(&self, frame: Switch) -> &Plan {
        self.switches[frame.0 as usize].as_ref().unwrap()
    }

    /// Resolve the result allocated after a string scrutinee. O(1).
    pub(super) fn switch_child_context(&self, cx: Cx, frame: Switch, index: usize) -> Cx {
        if index == 0 {
            cx
        } else {
            Cx {
                cont: self.switch_plan(frame).target.map_or(cx.cont, Cont::Assign),
                ..cx
            }
        }
    }

    /// C: compile_switch_*_block_inner: scrutinee V, then groups, then default.
    /// O(number of groups); no body is offered to the traversal twice.
    pub(super) fn switch_children(&self, cx: Cx, frame: Switch, into: &mut Vec<(Cx, NodeId)>) {
        let plan = self.switch_plan(frame);
        into.push((
            Cx {
                cont: Cont::Value(Tail::No),
                ..cx
            },
            plan.scrutinee,
        ));
        let body_cx = Cx {
            cont: plan.target.map_or(cx.cont, Cont::Assign),
            switch_depth: cx.switch_depth
                + u32::from(plan.kind != Kind::Named || plan.form == Form::General),
            ..cx
        };
        into.extend(
            plan.bodies
                .iter()
                .chain(plan.default.iter())
                .map(|&n| (body_cx, n)),
        );
    }

    /// C: compile_switch_value_block / return_case_needs_break. O(statements)
    /// to transfer a completed group's run once to its final child list.
    pub(super) fn switch_child(
        &mut self,
        cx: Cx,
        frame: Switch,
        index: usize,
        child: Probed,
    ) -> Probed {
        let mut out = self.realize(cx, child);
        let plan = self.switches[frame.0 as usize].as_mut().unwrap();
        if index == 0 {
            plan.value = out.value.take();
            if plan.pending_value {
                let target = self.fresh_variable("tmp");
                let declaration = self.statements.reserve();
                let plan = self.switches[frame.0 as usize].as_mut().unwrap();
                plan.target = Some(target);
                plan.declaration = Some(declaration);
            }
            if self.switch_plan(frame).form != Form::General {
                self.switches[frame.0 as usize].as_mut().unwrap().head = self.statements.reserve();
            }
        } else {
            let start = out.stmts.start;
            if let Some(value) = out.value.take() {
                self.drop_pure_effect(value);
            }
            if self.switch_plan(frame).form != Form::General {
                let run = self.statements.trim(Span { start, len: 0 });
                self.switches[frame.0 as usize].as_mut().unwrap().runs[index - 1] = run;
                return Probed::Out(Out {
                    stmts: self.statements.mark(),
                    value: None,
                    finished: out.finished,
                });
            }
            let plan = self.switch_plan(frame);
            let is_default = index > plan.bodies.len();
            let should_break = !is_default
                && out.finished != Finished::True
                && match cx.cont {
                    Cont::Effect(Tail::Return(_)) => {
                        self.switch_facts[plan.bodies[index - 1].index()].exit
                    }
                    _ => true,
                };
            // A emits an explicit break inside the body; E and R carry clause
            // metadata. This distinction matters to the legacy JS printer.
            let explicit = should_break && matches!(cx.cont, Cont::Assign(_));
            if explicit {
                self.statements.push(plain::node(
                    &mut self.arena,
                    View::SBreak { label: None },
                    0,
                ));
            }
            let run = self.statements.since(Span { start, len: 0 });
            let list = self.statements.take_list(&mut self.arena, run);
            let block = self.arena.block_from_list(list);
            let plan = self.switches[frame.0 as usize].as_mut().unwrap();
            plan.output.push(block);
            plan.clauses.push(ClauseMeta {
                should_break: should_break && !explicit,
                comment: None,
                loc: None,
            });
        }
        // All child statements now belong to their group, except the scrutinee
        // prelude, which stays on the outer statement run.
        Probed::Out(Out {
            stmts: self.statements.mark(),
            value: None,
            finished: out.finished,
        })
    }

    /// C: compile_switch_assignment/effect/return_block_inner. O(case count).
    /// Direct integers retain switch syntax, including zero/one/two cases.
    pub(super) fn finish_switch(&mut self, cx: Cx, frame: Switch) -> Probed {
        let plan = self.switches[frame.0 as usize]
            .take()
            .expect("live switch frame");
        while self.switches.last().is_some_and(Option::is_none) {
            self.switches.pop();
        }
        if plan.form != Form::General {
            return self.finish_small_switch(cx, plan);
        }
        let scrutinee = plan.value.expect("lowered scrutinee");
        let body_cont = plan.target.map_or(cx.cont, Cont::Assign);
        let empty = plan.output.iter().all(|&body| matches!(self.arena.view(body), View::SBlock { statements } if statements.is_empty()));
        if empty && plan.kind != Kind::Named && matches!(cx.cont, Cont::Effect(Tail::No)) {
            for &body in &plan.output {
                self.arena.release(body);
            }
            self.statements
                .push(norm::js1_exp(&mut self.arena, scrutinee));
        } else {
            let mut keys = Vec::new();
            let mut clauses = Vec::new();
            let mut actions = Vec::new();
            for (group, &head) in plan.groups.iter().enumerate() {
                let mut case = head;
                loop {
                    let key = &self.arena.switch(plan.header).keys[case];
                    keys.push(match key {
                        CaseKey::String(text) => CaseKey::JavaScript(
                            crate::lambda::SwitchCaseTag::String(self.arena.text(*text).to_owned()),
                        ),
                        key => key.clone(),
                    });
                    if plan.next[case] == NONE {
                        actions.push(plan.output[group]);
                        clauses.push(plan.clauses[group]);
                        break;
                    }
                    let empty = self.arena.lists.push(&[]);
                    actions.push(self.arena.block_from_list(empty));
                    clauses.push(ClauseMeta {
                        should_break: false,
                        comment: None,
                        loc: None,
                    });
                    case = plan.next[case];
                }
            }
            let mut has_default = plan.default.is_some();
            if has_default {
                let body = *plan.output.last().unwrap();
                if !matches!(body_cont, Cont::Assign(_))
                    && matches!(self.arena.view(body), View::SBlock { statements } if statements.is_empty())
                {
                    self.arena.release(body);
                    has_default = false;
                } else {
                    actions.push(body);
                    clauses.push(*plan.clauses.last().unwrap());
                }
            }
            let header = self.arena.switch_header(crate::bir::SwitchHeader {
                constants: keys.len() as u32,
                keys,
                clauses,
                has_default,
                consts_full: false,
                blocks_full: false,
                dispatch: crate::lambda::SwitchDispatch::Direct,
            });
            let statement = plain::node(
                &mut self.arena,
                View::SSwitch {
                    scrutinee,
                    actions: &actions,
                    header,
                },
                u16::from(plan.kind != Kind::Integer),
            );
            self.statements.push(statement);
        }
        self.switch_result(cx, &plan)
    }

    /// C: prepend_declaration_or_fold_final_assignment; V: compile_string_switch_inner.
    /// O(trailing holes), amortized linear: trim pops each hole once.
    fn switch_result(&mut self, cx: Cx, plan: &Plan) -> Probed {
        if let Some(slot) = plan.declaration {
            let target = plan.target.unwrap();
            let kind = match cx.cont {
                Cont::Declare(kind, _) => kind,
                _ => LetKind::Strict,
            };
            // The declaration hole must survive even when the body is empty.
            let floor = Span {
                start: slot + 1,
                len: 0,
            };
            let run = self.statements.trim(floor);
            let candidate = if matches!(cx.cont, Cont::Value(_)) {
                if plan.form != Form::General && self.statements.mark().start > plan.head {
                    Some(self.statements.since(Span {
                        start: plan.head,
                        len: 0,
                    }))
                } else {
                    None
                }
            } else if run.len > 0 {
                Some(Span {
                    start: run.start + run.len - 1,
                    len: 1,
                })
            } else {
                None
            };
            if let Some((statement, value)) =
                candidate.and_then(|run| self.single_assignment(run, target))
            {
                self.arena.detach(value);
                self.arena.release(statement);
                self.statements.kill(candidate.unwrap());
                let statement = crate::bir::j::declare(&mut self.arena, kind, target, value);
                self.statements.push(statement);
            } else {
                let declaration = plain::node(
                    &mut self.arena,
                    View::SDecl {
                        var: target,
                        value: None,
                    },
                    kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
                );
                self.statements.fill(slot, declaration);
            }
        }
        if plan.kind != Kind::Named && matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
            self.unnest(plan.start.start);
        }
        let value = match cx.cont {
            Cont::Value(_) => Some(self.pure_expression(
                View::Var {
                    var: plan.target.unwrap(),
                },
                0,
            )),
            Cont::Effect(Tail::No) => Some(plain::node(&mut self.arena, View::JUndefined, 0)),
            _ => None,
        };
        Probed::Out(Out {
            stmts: self.statements.since(plan.start),
            value,
            finished: Finished::False,
        })
    }
}

impl State {
    /// Prepare dense payload-indexed hashes once, at the first switch.
    /// O(payload bytes + constant edges); a single serialization buffer is
    /// reused, not allocated per payload or per source occurrence.
    fn prepare_switch_hashes(&mut self) {
        use crate::bir::Constant as C;
        use crate::lambda::lam_primitive::Primitive;
        use std::hash::{Hash, Hasher};
        let mut bytes = Vec::new();
        for p in &self.arena.pools.prims[self.switch_primitive_hashes.len()..] {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            match &p.primitive {
                Primitive::PjsCall(call) => crate::binser::to_vec_reuse(
                    &(&call.prim_name, &call.arg_types, &call.ffi),
                    &mut bytes,
                )
                .unwrap(),
                p => crate::binser::to_vec_reuse(p, &mut bytes).unwrap(),
            }
            bytes.hash(&mut h);
            self.switch_primitive_hashes.push(h.finish());
        }
        for c in &self.arena.pools.consts[self.switch_constant_hashes.len()..] {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            match c {
                C::Int(value)
                | C::DecoratedInt {
                    value,
                    native: false,
                    ..
                } => {
                    0u8.hash(&mut h);
                    value.hash(&mut h);
                }
                C::NativeInt(value)
                | C::DecoratedInt {
                    value,
                    native: true,
                    ..
                } => {
                    1u8.hash(&mut h);
                    value.hash(&mut h);
                }
                C::Some(value) => {
                    2u8.hash(&mut h);
                    self.switch_constant_hashes[value.index()].hash(&mut h);
                }
                C::Block { tag, fields } => {
                    3u8.hash(&mut h);
                    crate::binser::to_vec_reuse(tag, &mut bytes).unwrap();
                    bytes.hash(&mut h);
                    for field in self.arena.constant_fields(*fields) {
                        self.switch_constant_hashes[field.index()].hash(&mut h);
                    }
                }
                c => {
                    4u8.hash(&mut h);
                    crate::binser::to_vec_reuse(c, &mut bytes).unwrap();
                    bytes.hash(&mut h);
                }
            }
            self.switch_constant_hashes.push(h.finish());
        }
    }

    /// Lam constant eq_approx. O(compared constant nodes), with an iterative
    /// small work stack, never materializing legacy constant trees.
    fn switch_constants_equal(&self, a: crate::bir::ConstId, b: crate::bir::ConstId) -> bool {
        use crate::bir::Constant as C;
        let mut work = smallvec::SmallVec::<[(crate::bir::ConstId, crate::bir::ConstId); 8]>::new();
        work.push((a, b));
        while let Some((a, b)) = work.pop() {
            if a == b {
                continue;
            }
            let same = match (self.arena.constant(a), self.arena.constant(b)) {
                (
                    C::Int(a)
                    | C::DecoratedInt {
                        value: a,
                        native: false,
                        ..
                    },
                    C::Int(b)
                    | C::DecoratedInt {
                        value: b,
                        native: false,
                        ..
                    },
                )
                | (
                    C::NativeInt(a)
                    | C::DecoratedInt {
                        value: a,
                        native: true,
                        ..
                    },
                    C::NativeInt(b)
                    | C::DecoratedInt {
                        value: b,
                        native: true,
                        ..
                    },
                ) => a == b,
                (C::Block { tag: a, fields: af }, C::Block { tag: b, fields: bf }) => {
                    let (af, bf) = (
                        self.arena.constant_fields(*af),
                        self.arena.constant_fields(*bf),
                    );
                    if a != b || af.len() != bf.len() {
                        false
                    } else {
                        work.extend(af.iter().copied().zip(bf.iter().copied()));
                        true
                    }
                }
                (C::Some(a), C::Some(b)) => {
                    work.push((*a, *b));
                    true
                }
                // All other constants are canonically interned by full payload.
                _ => false,
            };
            if !same {
                return false;
            }
        }
        true
    }
}

impl State {
    /// V: compile_small_string_switch_assignment/return/effect, one Cx path.
    /// O(statements consumed by J-S3); the direct-body form copies no run.
    fn finish_small_switch(&mut self, cx: Cx, plan: Plan) -> Probed {
        let scrutinee = plan.value.unwrap();
        if plan.form == Form::Body {
            self.arena.release(scrutinee);
        } else {
            let key = self.arena.switch(plan.header).keys[0].clone();
            let key = self.switch_key_expression(&key);
            let test = norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, scrutinee, key);
            let yes = plan.runs[0];
            let no = if plan.bodies.len() + usize::from(plan.default.is_some()) == 2 {
                plan.runs[1]
            } else {
                self.statements.mark()
            };
            let statement = match plan.target.map_or(cx.cont, Cont::Assign) {
                Cont::Assign(target) => {
                    let merged = self.merge_assignments(test, target, yes, no);
                    self.assignment_statement(target, merged)
                }
                Cont::Effect(_) => self.if_statement(test, yes, no),
                _ => unreachable!("small switch branches assign their result"),
            };
            if matches!(cx.cont, Cont::Effect(Tail::No))
                && matches!(self.arena.view(statement), View::SBlock { statements } if statements.is_empty())
            {
                self.arena.release(statement);
            } else {
                self.statements.fill(plan.head, statement);
            }
        }
        self.switch_result(cx, &plan)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::{
        LamLoc, SwitchDispatch, SwitchKey, arena::LamArena, lam_constant::Constant as C,
    };

    fn check(
        keys: &[i32],
        values: &[i32],
        default: Option<i32>,
        complete: bool,
        effect: bool,
        throwing: bool,
        contexts: &[u8],
    ) {
        let mut a = LamArena::new();
        let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
        let actions: Vec<_> = values
            .iter()
            .copied()
            .chain(default)
            .map(|i| {
                let n = a.const_(C::Int { i, comment: None });
                if throwing {
                    a.prim_raw(P::Praise, &[n], LamLoc::NONE)
                } else if effect {
                    a.prim_raw(P::PinitMod, &[n], LamLoc::NONE)
                } else {
                    n
                }
            })
            .collect();
        let actions = a.add_list(&actions);
        let info = a.add_switch(
            complete,
            keys.iter().copied().map(SwitchKey::Int),
            false,
            std::iter::empty(),
            default.is_some(),
            SwitchDispatch::Direct,
        );
        let root = a.switch_raw(x, actions, info);
        super::super::oracle_tests::compare_in_contexts(a, root, None, true, contexts);
    }

    fn string_case(
        count: usize,
        default: bool,
        shared: bool,
        effect: bool,
        throwing: bool,
        nested_scrutinee: bool,
    ) {
        let mut a = LamArena::new();
        let mut x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
        if nested_scrutinee {
            let y = a.const_(C::String("a".into()));
            let z = a.const_(C::String("b".into()));
            let actions = a.add_list(&[y, z]);
            let info = a.add_switch(
                true,
                [SwitchKey::Int(0), SwitchKey::Int(1)],
                false,
                std::iter::empty(),
                false,
                SwitchDispatch::Direct,
            );
            x = a.switch_raw(x, actions, info);
        }
        let actions: Vec<_> = (0..count + usize::from(default))
            .map(|i| {
                let n = a.const_(C::Int {
                    i: if shared { 42 } else { i as i32 },
                    comment: None,
                });
                if throwing {
                    a.prim_raw(P::Praise, &[n], LamLoc::NONE)
                } else if effect {
                    a.prim_raw(P::PinitMod, &[n], LamLoc::NONE)
                } else {
                    n
                }
            })
            .collect();
        let actions = a.add_list(&actions);
        let keys: Vec<_> = (0..count).map(|i| format!("case{i}")).collect();
        let info = a.add_str_switch(keys.iter().map(String::as_str), default);
        let root = a.string_switch_raw(x, actions, info);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn string_forms_in_all_continuations() {
        for count in 0..=5 {
            for default in [false, true] {
                for shared in [false, true] {
                    for effect in [false, true] {
                        for throwing in [false, true] {
                            string_case(count, default, shared, effect, throwing, false);
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn string_scrutinee_precedes_value_temporary_and_declaration_fold() {
        for count in [0, 1, 2, 3] {
            for default in [false, true] {
                string_case(count, default, false, false, false, true);
            }
        }
    }

    #[test]
    fn frames_and_facts_are_small() {
        assert_eq!(std::mem::size_of::<Switch>(), 4);
        assert_eq!(std::mem::size_of::<Facts>(), 16);
        assert_eq!(std::mem::size_of::<Plan>(), 192);
    }
    #[test]
    fn ten_thousand_cases_have_linear_comparison_counts() {
        for pairs in [false, true] {
            let mut a = LamArena::new();
            let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
            let actions: Vec<_> = (0..10_000)
                .map(|i| {
                    a.const_(C::Int {
                        i: if pairs { i / 2 } else { i },
                        comment: None,
                    })
                })
                .collect();
            let actions = a.add_list(&actions);
            let info = a.add_switch(
                true,
                (0..10_000).map(SwitchKey::Int),
                false,
                std::iter::empty(),
                false,
                SwitchDispatch::Direct,
            );
            let root = a.switch_raw(x, actions, info);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let out = state.probe(Cx::returning(), root).unwrap();
            assert_eq!(state.switch_visits, 10_000);
            assert_eq!(state.switch_comparisons, if pairs { 5_000 } else { 0 });
            assert_eq!(state.switch_compared, if pairs { 5_000 } else { 0 });
            assert_eq!(state.source_steps, if pairs { 5_002 } else { 10_002 });
            let result = state.complete(Cx::returning(), out);
            result
                .program
                .arena
                .validate(Some(result.program.root), false)
                .unwrap();
        }
    }

    #[test]
    fn ten_thousand_nested_switches_use_the_explicit_traversal() {
        for context in 0..5 {
            let mut a = LamArena::new();
            let mut body = a.const_(C::Int {
                i: 42,
                comment: None,
            });
            let info = a.add_switch(
                true,
                [SwitchKey::Int(0)],
                false,
                std::iter::empty(),
                false,
                SwitchDispatch::Direct,
            );
            for _ in 0..10_000 {
                let scrutinee = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
                let actions = a.add_list(&[body]);
                body = a.switch_raw(scrutinee, actions, info);
            }
            let mut input = crate::bir::bridge::import_lambda(&a, body).unwrap();
            let var = input.arena.new_var_id(crate::name::Name::new("result"), 11);
            input
                .idents
                .push(Ident::new("result", 11, crate::ident::IdentFlags::NONE));
            let cx = match context {
                0 => Cx::value(),
                1 => Cx::declare(LetKind::Strict, var),
                2 => Cx::assign(var),
                3 => Cx::effect(),
                _ => Cx::returning(),
            };
            let root = input.root;
            let mut state = State::new(input);
            let out = state.probe(cx, root).unwrap();
            assert_eq!(state.source_steps, 20_001);
            assert_eq!(state.switch_visits, 10_000);
            assert_eq!(state.switch_comparisons, 0);
            let result = state.complete(cx, out);
            result
                .program
                .arena
                .validate(Some(result.program.root), false)
                .unwrap();
        }
    }

    #[test]
    fn scrutinee_statements_follow_the_declaration() {
        let mut a = LamArena::new();
        let arg = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
        let effect = a.prim_raw(P::PinitMod, &[arg], LamLoc::NONE);
        let scrutinee = a.seq_raw(effect, arg);
        let body = a.const_(C::Int {
            i: 42,
            comment: None,
        });
        let actions = a.add_list(&[body]);
        let info = a.add_switch(
            true,
            [SwitchKey::Int(0)],
            false,
            std::iter::empty(),
            false,
            SwitchDispatch::Direct,
        );
        let root = a.switch_raw(scrutinee, actions, info);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn value_matches_legacy() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            false,
            &[0],
        );
    }
    #[test]
    fn declaration_matches_legacy() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            false,
            &[2],
        );
    }
    #[test]
    fn assignment_matches_legacy() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            false,
            &[3],
        );
    }
    #[test]
    fn effect_matches_legacy() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            true,
            false,
            &[1],
        );
    }
    #[test]
    fn return_matches_legacy() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            false,
            &[4],
        );
    }
    #[test]
    fn step1_drops_equal_default() {
        check(
            &[0, 1, 2],
            &[40, 20, 40],
            Some(40),
            false,
            true,
            false,
            &[0, 1, 2, 3, 4],
        );
    }
    #[test]
    fn step2_two_interleaved_groups() {
        check(
            &[0, 1, 2, 3],
            &[10, 20, 10, 20],
            Some(40),
            false,
            true,
            false,
            &[0, 1, 2, 3, 4],
        );
    }
    #[test]
    fn step3_direct_integer_small_forms_remain_switches() {
        for count in 0..=2 {
            let keys: Vec<_> = (0..count).collect();
            let values: Vec<_> = (10..10 + count).collect();
            check(
                &keys,
                &values,
                Some(40),
                false,
                false,
                false,
                &[0, 1, 2, 3, 4],
            );
            check(&keys, &values, None, true, false, false, &[0, 1, 2, 3, 4]);
        }
    }
    #[test]
    fn step4_finished_clauses_do_not_break() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            true,
            &[0, 1, 2, 3, 4],
        );
    }
    #[test]
    fn step5_empty_effect_switch_is_scrutinee() {
        check(
            &[0, 1, 2],
            &[10, 20, 30],
            Some(40),
            false,
            false,
            false,
            &[1],
        );
    }
}
