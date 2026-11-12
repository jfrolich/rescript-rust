//! V: compile_untagged_switch / emit_untagged_tree / emit_untagged_clause.
//! The existing untagged_dispatch planner is unchanged. Its tree becomes an
//! explicit emission program which pauses only to lower a source body once.
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, ClauseMeta};
use crate::lambda::untagged_dispatch::{self as dispatch, Clause, Test, TestId, Tree, TreeId};
use crate::lambda::{SwitchCaseTag, SwitchDispatch, SwitchKey};
use crate::types::{VariantBlockType, VariantConstructorCase as Case, VariantInstance};

#[derive(Clone, Copy)]
pub(super) struct Untagged(pub u32);

#[derive(Clone, Copy)]
enum Op {
    Begin,
    Run(u32),
    Cached(u32),
    Empty,
    If(TestId),
    Block,
    Switch(TreeId),
}
#[derive(Clone, Copy)]
enum Work {
    Visit(TreeId, u32),
    Clause(TreeId, u32),
    Emit(Op),
}
struct Action {
    source: NodeId,
    depth: u32,
    uses: u32,
    fallback: bool,
}
#[derive(Clone, Copy)]
struct Output {
    run: Span,
    action: u32,
    finished: Finished,
}
const NONE: u32 = u32::MAX;

pub(super) struct Plan {
    source: NodeId,
    operands: crate::bir::ListId,
    start: Span,
    cont: Cont,
    target: Option<VarId>,
    scrutinee: Option<NodeId>,
    payload_only: bool,
    dispatch: dispatch::Plan<u32>,
    program: Vec<Op>,
    pc: usize,
    actions: Vec<Action>,
    cached: Vec<Option<NodeId>>,
    finished: Vec<Finished>,
    remaining: Vec<u32>,
    marks: Vec<Span>,
    outputs: Vec<Output>,
}

impl State {
    /// V: compile_untagged_switch. O(planner work + its emitted plan + new
    /// fingerprint nodes). The planner's equality callback rejects differing
    /// fingerprints before confirming source nodes; no legacy lowering runs.
    pub(super) fn untagged_switch(
        &mut self,
        cx: Cx,
        source: NodeId,
        operands: crate::bir::ListId,
        header: crate::bir::SwitchId,
    ) -> Result<Untagged, Unsupported> {
        let h = self.arena.switch(header);
        let n = h.constants as usize;
        let full = (h.consts_full, h.blocks_full);
        let payload_only = h.consts_full && n == 0;
        let fallback = h.has_default.then_some(h.keys.len() as u32);
        let SwitchDispatch::Variant(facts) = &h.dispatch else {
            unreachable!("untagged dispatch")
        };
        let facts = facts.clone();
        let mut literal_arms = Vec::with_capacity(n);
        let mut payload_arms = Vec::with_capacity(h.keys.len() - n);
        for (i, key) in h.keys.iter().enumerate() {
            match key {
                CaseKey::Lambda(SwitchKey::Constructor(Case::Constant(tag))) => {
                    literal_arms.push((tag.literal.clone(), i as u32))
                }
                CaseKey::Lambda(SwitchKey::Constructor(Case::Block(block))) => payload_arms.push((
                    block.block_type().expect("untagged payload").clone(),
                    i as u32,
                )),
                _ => unreachable!("untagged constructor key"),
            }
        }
        let sources = self.source.lists.get(operands).to_vec();
        self.prepare_switch_hashes();
        for &source in &sources {
            self.switch_facts(source);
        }
        let state = std::cell::RefCell::new(&mut *self);
        let dispatch = dispatch::plan(
            |a: &u32, b: &u32| {
                state
                    .borrow_mut()
                    .same_switch_body(sources[*a as usize], sources[*b as usize])
            },
            dispatch::Input {
                facts: &facts,
                literal_arms,
                payload_arms,
                literals_complete: full.0,
                payloads_complete: full.1,
                fallback,
            },
        );
        let (program, actions) =
            Self::untagged_program(&dispatch, &sources, fallback, cx.switch_depth);
        let start = self.statements.mark();
        let binding = match cx.cont {
            Cont::Value(_) => Some((LetKind::Strict, self.fresh_variable("tmp"))),
            Cont::Declare(kind, var) => Some((kind, var)),
            _ => None,
        };
        if let Some((kind, var)) = binding {
            let declaration = plain::node(
                &mut self.arena,
                View::SDecl { var, value: None },
                kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
            );
            self.statements.push(declaration);
        }
        let frame = Untagged(self.untagged.len() as u32);
        let remaining = actions.iter().map(|a| a.uses).collect();
        let cached = vec![None; actions.len()];
        let finished = vec![Finished::False; actions.len()];
        self.untagged.push(Some(Plan {
            source,
            operands,
            start,
            cont: cx.cont,
            target: binding.map(|(_, v)| v),
            scrutinee: None,
            payload_only,
            dispatch,
            program,
            pc: 0,
            actions,
            cached,
            finished,
            remaining,
            marks: Vec::new(),
            outputs: Vec::new(),
        }));
        Ok(frame)
    }

    /// V: emit_untagged_tree's order, including default before switch clauses.
    /// O(plan occurrences + clauses), using an explicit stack. Source actions
    /// are cached by dense arm index and the two in-switch states.
    fn untagged_program(
        plan: &dispatch::Plan<u32>,
        sources: &[NodeId],
        fallback: Option<u32>,
        depth: u32,
    ) -> (Vec<Op>, Vec<Action>) {
        let mut program = Vec::new();
        let mut actions: Vec<Action> = Vec::new();
        let mut cache = vec![[NONE; 2]; sources.len()];
        let mut work = vec![Work::Visit(plan.root(), depth)];
        while let Some(task) = work.pop() {
            match task {
                Work::Emit(op) => program.push(op),
                Work::Clause(tree, depth) => work.push(Work::Visit(tree, depth)),
                Work::Visit(tree, depth) => match plan.tree(tree) {
                    Tree::Run(_) | Tree::Fallback => {
                        let arm = match plan.tree(tree) {
                            Tree::Run(arm) => *arm,
                            _ => fallback.unwrap(),
                        };
                        let slot = &mut cache[arm as usize][usize::from(depth > 0)];
                        if *slot == NONE {
                            *slot = actions.len() as u32;
                            actions.push(Action {
                                source: sources[arm as usize],
                                depth,
                                uses: 1,
                                fallback: matches!(plan.tree(tree), Tree::Fallback),
                            });
                            program.push(Op::Run(*slot));
                        } else {
                            actions[*slot as usize].uses += 1;
                            program.push(Op::Cached(*slot));
                        }
                    }
                    Tree::Skip => program.push(Op::Empty),
                    Tree::If(test, yes, no) => {
                        program.push(Op::Begin);
                        work.push(Work::Emit(Op::If(*test)));
                        work.push(Work::Visit(*no, depth));
                        work.push(Work::Visit(*yes, depth));
                    }
                    Tree::Block(inner) => {
                        program.push(Op::Begin);
                        work.push(Work::Emit(Op::Block));
                        work.push(Work::Visit(*inner, depth));
                    }
                    Tree::SwitchValue(clauses, default) => {
                        program.push(Op::Begin);
                        work.push(Work::Emit(Op::Switch(tree)));
                        for (_, clause) in plan.value_clauses(*clauses).iter().rev() {
                            work.push(match clause {
                                Clause::FallsThrough(_) => Work::Emit(Op::Empty),
                                Clause::Body(body) => Work::Clause(*body, depth + 1),
                            });
                        }
                        work.push(Work::Visit(*default, depth + 1));
                    }
                    Tree::SwitchTypeof(clauses, default) => {
                        let cases = plan.typeof_clauses(*clauses);
                        let small = cases.len() == 1 && matches!(cases[0].1, Clause::Body(_));
                        program.push(Op::Begin);
                        work.push(Work::Emit(Op::Switch(tree)));
                        if small {
                            work.push(Work::Visit(*default, depth));
                            let Clause::Body(body) = cases[0].1 else {
                                unreachable!()
                            };
                            work.push(Work::Clause(body, depth));
                        } else {
                            for (_, clause) in cases.iter().rev() {
                                work.push(match clause {
                                    Clause::FallsThrough(_) => Work::Emit(Op::Empty),
                                    Clause::Body(body) => Work::Clause(*body, depth + 1),
                                });
                            }
                            work.push(Work::Visit(*default, depth + 1));
                        }
                    }
                },
            }
        }
        (program, actions)
    }

    /// Schedule the scrutinee, then each first body occurrence. O(actions).
    pub(super) fn untagged_children(&self, cx: Cx, frame: Untagged, into: &mut Vec<(Cx, NodeId)>) {
        let p = self.untagged[frame.0 as usize].as_ref().unwrap();
        into.push((
            Cx {
                cont: Cont::Value(Tail::No),
                ..cx
            },
            p.source,
        ));
        let cont = p.target.map_or(cx.cont, Cont::Assign);
        into.extend(p.actions.iter().map(|a| {
            (
                Cx {
                    cont,
                    switch_depth: a.depth,
                    ..cx
                },
                a.source,
            )
        }));
    }

    /// V: untagged_output_block. O(statements), copied into cache storage only
    /// if the plan emits the action more than once; single-use runs stay put.
    pub(super) fn untagged_child(
        &mut self,
        cx: Cx,
        frame: Untagged,
        index: usize,
        child: Probed,
    ) -> Probed {
        let mut p = self.untagged[frame.0 as usize].take().unwrap();
        let mut out = self.realize(cx, child);
        if index == 0 {
            let mut value = out.value.unwrap();
            if !p.payload_only && !matches!(self.arena.view(value), View::Var { .. }) {
                let var = self.fresh_variable("tmp");
                let declaration =
                    crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, value);
                self.statements.push(declaration);
                value = self.pure_expression(View::Var { var }, 0);
            }
            p.scrutinee = Some(value);
        } else {
            let Op::Run(action) = p.program[p.pc] else {
                unreachable!("paused for source action")
            };
            assert_eq!(action as usize, index - 1);
            p.pc += 1;
            if let Some(value) = out.value.take() {
                self.drop_pure_effect(value);
            }
            self.unnest(out.stmts.start);
            out.stmts = self.statements.since(Span {
                start: out.stmts.start,
                len: 0,
            });
            self.locate_switch_run(p.actions[action as usize].source, out.stmts);
            p.finished[action as usize] = out.finished;
            if p.actions[action as usize].uses > 1 {
                let list = self.statements.take_list(&mut self.arena, out.stmts);
                p.cached[action as usize] = Some(self.arena.block_from_list(list));
                self.emit_cached_action(&mut p, action);
            } else {
                p.remaining[action as usize] -= 1;
                p.outputs.push(Output {
                    run: out.stmts,
                    action,
                    finished: out.finished,
                });
            }
        }
        self.advance_untagged(&mut p);
        self.untagged[frame.0 as usize] = Some(p);
        Probed::Out(Out {
            stmts: self.statements.mark(),
            value: None,
            finished: Finished::False,
        })
    }

    /// Copy a multiply-emitted J output, never relower its source. O(emitted
    /// nodes), including binder remapping by the arena's existing copier.
    fn copy_dispatch_output(&mut self, root: NodeId) -> NodeId {
        let mut vars = Vec::new();
        let mut labels = Vec::new();
        let copied = self
            .arena
            .copy_subtree_recording(root, &[], &mut vars, &mut labels);
        for (new, old) in vars {
            assert_eq!(new.index(), self.idents.len());
            self.idents.push(self.idents[old.index()]);
            self.arena.vars.order[new.index()] = self.arena.vars.order(old);
        }
        copied
    }

    /// V: untagged_fallback_block, generalized to all shared plan actions.
    /// O(output size) for repeated occurrences; the last takes the original.
    fn emit_cached_action(&mut self, p: &mut Plan, action: u32) {
        let i = action as usize;
        p.remaining[i] -= 1;
        let root = if p.remaining[i] == 0 {
            p.cached[i].take().unwrap()
        } else {
            self.copy_dispatch_output(p.cached[i].unwrap())
        };
        let start = self.statements.mark();
        let View::SBlock { statements } = self.arena.view(root) else {
            unreachable!("cached run")
        };
        for &statement in statements {
            self.statements.push(statement);
        }
        for statement in self.statements.statements(self.statements.since(start)) {
            self.arena.detach(statement);
        }
        self.arena.release(root);
        p.outputs.push(Output {
            run: self.statements.since(start),
            action,
            finished: p.finished[i],
        });
    }

    /// A scrutinee occurrence. O(1) for variables (the normal bound case),
    /// otherwise O(emitted expression) for the legacy payload-only form.
    fn untagged_scrutinee(&mut self, p: &Plan) -> NodeId {
        let value = p.scrutinee.unwrap();
        if let View::Var { var } = self.arena.view(value) {
            self.pure_expression(View::Var { var }, 0)
        } else {
            self.copy_dispatch_output(value)
        }
    }

    /// V: emit_untagged_tree. O(emitted program steps + J-rule costs), with
    /// all control stacks explicit and all kept statement runs left in place.
    fn advance_untagged(&mut self, p: &mut Plan) {
        while let Some(&op) = p.program.get(p.pc) {
            if matches!(op, Op::Run(_)) {
                break;
            }
            p.pc += 1;
            match op {
                Op::Run(_) => unreachable!(),
                Op::Begin => {
                    let start = self.statements.mark();
                    self.statements.reserve();
                    p.marks.push(start);
                }
                Op::Empty => p.outputs.push(Output {
                    run: self.statements.mark(),
                    action: NONE,
                    finished: Finished::False,
                }),
                Op::Cached(action) => self.emit_cached_action(p, action),
                Op::If(test) => {
                    let no = p.outputs.pop().unwrap();
                    let yes = p.outputs.pop().unwrap();
                    let test = self.untagged_test(p, test);
                    self.untagged_if(p, test, yes.run, no.run);
                }
                Op::Block => {
                    let out = p.outputs.pop().unwrap();
                    let start = p.marks.pop().unwrap();
                    let body: Vec<_> = self.statements.statements(out.run).collect();
                    self.statements.copied += body.len();
                    self.statements.kill(out.run);
                    let block = norm::js2_block(&mut self.arena, body);
                    self.place(start.start, block);
                    p.outputs.push(Output {
                        run: self.statements.since(start),
                        action: NONE,
                        finished: Finished::False,
                    });
                }
                Op::Switch(tree) => self.untagged_switch_statement(p, tree),
            }
        }
    }

    /// V: untagged_if / normalized_if_block. O(statements consumed by J-S3).
    fn untagged_if(&mut self, p: &mut Plan, test: NodeId, yes: Span, no: Span) {
        let start = p.marks.pop().unwrap();
        let statement = self.if_statement(test, yes, no);
        self.place(start.start, statement);
        if matches!(p.cont, Cont::Effect(Tail::Return(_))) {
            self.unnest(start.start);
        }
        p.outputs.push(Output {
            run: self.statements.since(start),
            action: NONE,
            finished: Finished::False,
        });
    }

    /// V: emit_untagged_clause. O(1) control/exit facts, plus one list transfer.
    fn untagged_clause(&mut self, p: &Plan, out: Output) -> (NodeId, ClauseMeta) {
        let should_break = if out.action == NONE {
            false
        } else if p.actions[out.action as usize].fallback {
            !self.statements.last(out.run).is_some_and(|s| {
                matches!(
                    self.arena.view(s),
                    View::SReturn { .. }
                        | View::SThrow { .. }
                        | View::SContinue { .. }
                        | View::SBreak { .. }
                )
            })
        } else {
            out.finished != Finished::True
                && (!matches!(p.cont, Cont::Effect(Tail::Return(_)))
                    || self.switch_has_exit(p.actions[out.action as usize].source))
        };
        let loc = if out.action != NONE && !p.actions[out.action as usize].fallback {
            self.switch_location(p.actions[out.action as usize].source)
        } else {
            None
        };
        let list = self.statements.take_list(&mut self.arena, out.run);
        (
            self.arena.block_from_list(list),
            ClauseMeta {
                should_break,
                comment: None,
                loc,
            },
        )
    }

    /// V: emit_untagged_tree's value/typeof switch arms. O(clauses + statements
    /// transferred), with default-first source order and case-first output.
    fn untagged_switch_statement(&mut self, p: &mut Plan, tree: TreeId) {
        let (keys, typeof_, value_switch) = match p.dispatch.tree(tree) {
            Tree::SwitchValue(clauses, _) => (
                p.dispatch
                    .value_clauses(*clauses)
                    .iter()
                    .map(|(l, _)| CaseKey::JavaScript(Self::literal_tag(l)))
                    .collect::<Vec<_>>(),
                false,
                true,
            ),
            Tree::SwitchTypeof(clauses, _) => {
                let cases = p.dispatch.typeof_clauses(*clauses);
                if cases.len() == 1 && matches!(cases[0].1, Clause::Body(_)) {
                    let no = p.outputs.pop().unwrap();
                    let yes = p.outputs.pop().unwrap();
                    let value = self.untagged_scrutinee(p);
                    let test = self.untagged_typeof(value, &cases[0].0);
                    self.untagged_if(p, test, yes.run, no.run);
                    return;
                }
                (
                    cases
                        .iter()
                        .map(|(k, _)| {
                            CaseKey::JavaScript(SwitchCaseTag::String(
                                k.typeof_name().unwrap().into(),
                            ))
                        })
                        .collect(),
                    true,
                    false,
                )
            }
            _ => unreachable!("switch operation"),
        };
        let start = p.marks.pop().unwrap();
        let base = p.outputs.len() - keys.len() - 1;
        let default = p.outputs[base];
        let has_default = !value_switch || self.statements.has_statements(default.run);
        let mut actions = Vec::with_capacity(keys.len() + usize::from(has_default));
        let mut clauses = Vec::with_capacity(actions.capacity());
        for i in 0..keys.len() {
            let (body, mut meta) = self.untagged_clause(p, p.outputs[base + 1 + i]);
            let clause = match p.dispatch.tree(tree) {
                Tree::SwitchValue(c, _) => &p.dispatch.value_clauses(*c)[i].1,
                Tree::SwitchTypeof(c, _) => &p.dispatch.typeof_clauses(*c)[i].1,
                _ => unreachable!(),
            };
            if let Clause::FallsThrough(Some(arm)) = clause {
                meta.loc = self.switch_location(self.source.lists.get(p.operands)[*arm as usize]);
            }
            actions.push(body);
            clauses.push(meta);
        }
        if has_default {
            let list = self.statements.take_list(&mut self.arena, default.run);
            actions.push(self.arena.block_from_list(list));
            clauses.push(ClauseMeta {
                should_break: false,
                comment: None,
                loc: None,
            });
        } else {
            self.statements.kill(default.run);
        }
        p.outputs.truncate(base);
        let mut scrutinee = self.untagged_scrutinee(p);
        if typeof_ {
            scrutinee = plain::node(&mut self.arena, View::JTypeof { value: scrutinee }, 0);
        }
        let header = self.arena.switch_header(crate::bir::SwitchHeader {
            constants: keys.len() as u32,
            keys,
            clauses,
            consts_full: false,
            blocks_full: false,
            has_default,
            dispatch: SwitchDispatch::Direct,
        });
        let statement = plain::node(
            &mut self.arena,
            View::SSwitch {
                scrutinee,
                actions: &actions,
                header,
            },
            1,
        );
        self.statements.fill(start.start, statement);
        p.outputs.push(Output {
            run: self.statements.since(start),
            action: NONE,
            finished: Finished::False,
        });
    }

    /// V: untagged_typeof_expr. O(1), retaining raw typeof rather than folding.
    fn untagged_typeof(&mut self, value: NodeId, kind: &VariantBlockType) -> NodeId {
        let value = plain::node(&mut self.arena, View::JTypeof { value }, 0);
        let text = plain::string(&mut self.arena, kind.typeof_name().expect("typeof kind"));
        norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, value, text)
    }

    /// V: untagged_test_expr. O(test occurrences + emitted scrutinee copies),
    /// using explicit stacks instead of recursion on the planner's tests.
    fn untagged_test(&mut self, p: &Plan, test: TestId) -> NodeId {
        let mut work = vec![(test, false)];
        let mut values = Vec::new();
        while let Some((id, done)) = work.pop() {
            let test = p.dispatch.test(id);
            if !done {
                work.push((id, true));
                match test {
                    Test::Not(a) => work.push((*a, false)),
                    Test::And(a, b) | Test::Or(a, b) => {
                        work.push((*b, false));
                        work.push((*a, false));
                    }
                    _ => {}
                }
                continue;
            }
            let value = match test {
                Test::Equals(tag) => {
                    let left = self.untagged_scrutinee(p);
                    let right =
                        self.switch_key_expression(&CaseKey::JavaScript(Self::literal_tag(tag)));
                    norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, left, right)
                }
                Test::Typeof(kind) => {
                    let value = self.untagged_scrutinee(p);
                    self.untagged_typeof(value, kind)
                }
                Test::Instance(instance) => {
                    let value = self.untagged_scrutinee(p);
                    self.untagged_instance(value, instance)
                }
                Test::NotNull => {
                    let value = self.untagged_scrutinee(p);
                    let null = plain::node(&mut self.arena, View::JNull, 0);
                    let eq =
                        norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, value, null);
                    norm::je8_not(&mut self.arena, eq)
                }
                Test::Not(_) => norm::je8_not(&mut self.arena, values.pop().unwrap()),
                Test::And(..) | Test::Or(..) => {
                    let r = values.pop().unwrap();
                    let l = values.pop().unwrap();
                    norm::je4_bin(
                        &mut self.arena,
                        if matches!(test, Test::And(..)) {
                            crate::js_ir::BinOp::And
                        } else {
                            crate::js_ir::BinOp::Or
                        },
                        l,
                        r,
                    )
                }
            };
            values.push(value);
        }
        values.pop().unwrap()
    }

    /// V: class_constructor / is_instance_of. O(class path bytes); array tests
    /// use the same ordinary CallInfo as the legacy constructor.
    fn untagged_instance(&mut self, value: NodeId, instance: &VariantInstance) -> NodeId {
        let name = match instance {
            VariantInstance::Array(_) => "Array",
            VariantInstance::Class { name, .. } => name,
        };
        let mut parts = name.split('.');
        let first = parts.next().unwrap();
        let var = self.arena.new_var_id(crate::name::Name::new(first), 0);
        self.idents.push(Ident::create_persistent(first));
        self.arena.vars.flags[var.index()].0 |=
            crate::bir::VarFlags::JS_GLOBAL | crate::bir::VarFlags::JS_IDENT;
        let mut class = self.pure_expression(View::Var { var }, 0);
        for property in parts {
            let property = self.arena.intern_text(property);
            class = plain::node(
                &mut self.arena,
                View::JDot {
                    object: class,
                    property,
                    position: crate::js_ir::arena::FieldPos::NONE,
                },
                0,
            );
        }
        if matches!(instance, VariantInstance::Array(_)) {
            let property = self.arena.intern_text("isArray");
            let callee = plain::node(
                &mut self.arena,
                View::JDot {
                    object: class,
                    property,
                    position: crate::js_ir::arena::FieldPos::NONE,
                },
                0,
            );
            let info = self.arena.js_info(crate::bir::JsPayload::Call(
                crate::js_ir::CallInfo::default(),
            ));
            plain::node(
                &mut self.arena,
                View::JCall {
                    callee,
                    args: &[value],
                    info,
                },
                0,
            )
        } else {
            norm::je4_bin(
                &mut self.arena,
                crate::js_ir::BinOp::InstanceOf,
                value,
                class,
            )
        }
    }

    /// V: compile_untagged_switch result. O(trailing empty block shells),
    /// amortized by their removal; the scrutinee template is released once.
    pub(super) fn finish_untagged(&mut self, cx: Cx, frame: Untagged) -> Probed {
        let p = self.untagged[frame.0 as usize].take().unwrap();
        while self.untagged.last().is_some_and(Option::is_none) {
            self.untagged.pop();
        }
        assert_eq!(p.pc, p.program.len());
        assert_eq!(p.outputs.len(), 1);
        self.arena.release(p.scrutinee.unwrap());
        if matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
            self.unnest(p.start.start);
        }
        let value = match cx.cont {
            Cont::Value(_) => Some(self.pure_expression(
                View::Var {
                    var: p.target.unwrap(),
                },
                0,
            )),
            Cont::Effect(Tail::No) => Some(plain::node(&mut self.arena, View::JUndefined, 0)),
            _ => None,
        };
        Probed::Out(Out {
            stmts: self.statements.since(p.start),
            value,
            finished: Finished::False,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{
        arena::LamArena, lam_constant::Constant as C, lam_primitive::Primitive as LambdaPrimitive,
    };
    use crate::types::{
        ShapeAllocation, VariantBlock, VariantLiteralTag as Literal, VariantMatchingFacts,
        VariantTag,
    };

    #[test]
    fn untagged_forms_match_legacy() {
        let array =
            VariantBlockType::Instance(VariantInstance::Array(ShapeAllocation::TUPLE_ARRAY));
        let class = VariantBlockType::Instance(VariantInstance::Class {
            name: "Intl.Locale".into(),
            ancestors: vec![],
            blocks: crate::types::ClassBlocks::fresh(0),
        });
        let forms = [
            vec![],
            vec![VariantBlockType::Number],
            vec![VariantBlockType::String, VariantBlockType::Number],
            vec![VariantBlockType::Object, array.clone()],
            vec![VariantBlockType::Object, array.clone(), class.clone()],
            vec![
                VariantBlockType::Number,
                VariantBlockType::String,
                VariantBlockType::Bigint,
                VariantBlockType::Boolean,
                VariantBlockType::Symbol,
                VariantBlockType::Function,
                VariantBlockType::Object,
                array,
                class,
            ],
            vec![VariantBlockType::Unknown],
        ];
        for kinds in forms {
            for literals in [
                vec![],
                vec![
                    Literal::Null,
                    Literal::Undefined,
                    Literal::String("none".into()),
                    Literal::Bool(true),
                    Literal::Int(1),
                    Literal::Float("1.5".into()),
                    Literal::BigInt("2".into()),
                ],
            ] {
                for full in [[false, false], [true, false], [false, true], [true, true]] {
                    for fallback in [false, true] {
                        for effects in [false, true] {
                            let mut a = LamArena::new();
                            let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
                            let x = if effects {
                                a.prim_raw(
                                    LambdaPrimitive::PinitMod,
                                    &[x],
                                    crate::lambda::LamLoc::NONE,
                                )
                            } else {
                                x
                            };
                            let constants: Vec<_> = literals
                                .iter()
                                .enumerate()
                                .map(|(i, literal)| {
                                    SwitchKey::Constructor(Case::Constant(VariantTag {
                                        name: crate::name::Name::new(&format!("C{i}")),
                                        literal: literal.clone(),
                                    }))
                                })
                                .collect();
                            let blocks: Vec<_> = kinds
                                .iter()
                                .enumerate()
                                .map(|(i, kind)| {
                                    SwitchKey::Constructor(Case::Block(VariantBlock::Untagged {
                                        tag: VariantTag {
                                            name: crate::name::Name::new(&format!("B{i}")),
                                            literal: Literal::String(format!("B{i}")),
                                        },
                                        block_type: kind.clone(),
                                    }))
                                })
                                .collect();
                            let mut actions = Vec::new();
                            for i in 0..constants.len() + blocks.len() + usize::from(fallback) {
                                let value = a.const_(C::Int {
                                    i: (i / 2) as i32,
                                    comment: None,
                                });
                                let body = if effects {
                                    a.prim_raw(
                                        LambdaPrimitive::PinitMod,
                                        &[value],
                                        crate::lambda::LamLoc::NONE,
                                    )
                                } else {
                                    value
                                };
                                actions.push(body);
                            }
                            let info = a.add_switch(
                                full[0],
                                constants,
                                full[1],
                                blocks,
                                fallback,
                                SwitchDispatch::Variant(VariantMatchingFacts {
                                    tag_name: None,
                                    literal_tags: literals.clone(),
                                    block_types: kinds.clone(),
                                }),
                            );
                            let actions = a.add_list(&actions);
                            let root = a.switch_raw(x, actions, info);
                            oracle_tests::compare(a, root);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn a_clause_without_statements_follows_a_clause_that_was_taken() {
        // A clause that is an exit to a catch whose handler follows its body
        // lowers to no statement, so the run of the clause before it is the
        // top of the stack when that clause is taken.
        let kinds = [VariantBlockType::Object];
        // Three literal cases and one block case; `mask` says which exit.
        // The smallest that needs it is the third literal alone (mask 4).
        for mask in 1..16u32 {
            let literals: Vec<_> = (0..3).map(|i| Literal::String(format!("l{i}"))).collect();
            let exits: Vec<_> = (0..4).map(|i| mask >> i & 1 == 1).collect();
            let mut a = LamArena::new();
            let constants: Vec<_> = literals
                .iter()
                .enumerate()
                .map(|(i, literal)| {
                    SwitchKey::Constructor(Case::Constant(VariantTag {
                        name: crate::name::Name::new(&format!("C{i}")),
                        literal: literal.clone(),
                    }))
                })
                .collect();
            let block = SwitchKey::Constructor(Case::Block(VariantBlock::Untagged {
                tag: VariantTag {
                    name: crate::name::Name::new("B"),
                    literal: Literal::String("B".into()),
                },
                block_type: kinds[0].clone(),
            }));
            let effect = |a: &mut LamArena, i: i32| {
                let value = a.const_(C::Int { i, comment: None });
                a.prim_raw(LambdaPrimitive::PinitMod, &[value], crate::lambda::LamLoc::NONE)
            };
            let actions: Vec<_> = exits
                .iter()
                .enumerate()
                .map(|(i, &exit)| if exit { a.static_raise(1, &[]) } else { effect(&mut a, i as i32) })
                .collect();
            let info = a.add_switch(
                true,
                constants,
                true,
                [block],
                false,
                SwitchDispatch::Variant(VariantMatchingFacts {
                    tag_name: None,
                    literal_tags: literals.to_vec(),
                    block_types: kinds.to_vec(),
                }),
            );
            let actions = a.add_list(&actions);
            let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
            let body = a.switch_raw(x, actions, info);
            let handler = effect(&mut a, 9);
            let root = a.static_catch(body, 1, &[], handler);
            oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_nested_payload_dispatches_are_linear() {
        let mut a = LamArena::new();
        let kind = VariantBlockType::Unknown;
        let tag = VariantTag {
            name: crate::name::Name::new("Payload"),
            literal: Literal::String("Payload".into()),
        };
        let info = a.add_switch(
            true,
            [],
            true,
            [SwitchKey::Constructor(Case::Block(
                VariantBlock::Untagged {
                    tag,
                    block_type: kind.clone(),
                },
            ))],
            false,
            SwitchDispatch::Variant(VariantMatchingFacts {
                tag_name: None,
                literal_tags: vec![],
                block_types: vec![kind],
            }),
        );
        let mut root = a.const_(C::Int {
            i: 42,
            comment: None,
        });
        for _ in 0..10_000 {
            let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
            let actions = a.add_list(&[root]);
            root = a.switch_raw(x, actions, info);
        }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let out = state.probe(Cx::returning(), root).unwrap();
        assert_eq!(state.source_steps, 20_001);
        assert_eq!(state.switch_visits, 10_000);
        assert_eq!(state.switch_comparisons, 0);
        state.complete(Cx::returning(), out);
    }

    #[test]
    fn program_element_sizes() {
        assert_eq!(std::mem::size_of::<Plan>(), 336);
        assert_eq!(std::mem::size_of::<Untagged>(), 4);
        assert_eq!(std::mem::size_of::<Op>(), 8);
        assert_eq!(std::mem::size_of::<Work>(), 12);
        assert_eq!(std::mem::size_of::<Action>(), 16);
        assert_eq!(std::mem::size_of::<Output>(), 16);
    }
}
