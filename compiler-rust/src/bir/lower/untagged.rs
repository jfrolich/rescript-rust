//! V: compile_untagged_switch / emit_untagged_tree / emit_untagged_clause.
//! The existing untagged_dispatch planner is unchanged. Its tree becomes an
//! explicit emission program which pauses only to lower a source body once.
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, ClauseMeta};
use crate::lambda::untagged_dispatch::{self as dispatch, Clause, Test, TestId, Tree, TreeId};
use crate::lambda::{SwitchCaseTag, SwitchDispatch, SwitchKey};
use crate::types::VariantConstructorCase as Case;

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
#[derive(Clone, Copy)]
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

/// A typed run of a pool, including a bound for its local stack operations.
#[derive(Clone, Copy)]
struct Run<T> {
    start: u32,
    len: u32,
    limit: u32,
    marker: std::marker::PhantomData<T>,
}
impl<T> Run<T> {
    /// O(1): form a checked pool run.
    fn new(start: usize, len: usize, limit: usize) -> Self {
        u32::try_from(start.checked_add(limit).unwrap()).expect("untagged pool capacity");
        assert!(len <= limit);
        Self {
            start: u32::try_from(start).unwrap(),
            len: u32::try_from(len).unwrap(),
            limit: u32::try_from(limit).unwrap(),
            marker: std::marker::PhantomData,
        }
    }
    /// O(1): current initialized range.
    fn range(&self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}
struct Pool<T> {
    values: Vec<T>,
}
impl<T> Default for Pool<T> {
    fn default() -> Self {
        Self { values: Vec::new() }
    }
}
impl<T: Copy> Pool<T> {
    /// O(count): reserve a disjoint stack region; never shared with a child plan.
    fn stack(&mut self, count: usize, empty: T) -> Run<T> {
        let run = Run::new(self.values.len(), 0, count);
        self.values.resize(self.values.len() + count, empty);
        run
    }
    /// O(1), with no pool growth: write a slot reserved when the plan was made.
    fn push(&mut self, run: &mut Run<T>, value: T) {
        assert!(run.len < run.limit);
        self.values[(run.start + run.len) as usize] = value;
        run.len += 1;
    }
    /// O(1): consume the most recent local stack slot.
    fn pop(&self, run: &mut Run<T>) -> T {
        assert!(run.len > 0);
        run.len -= 1;
        self.values[(run.start + run.len) as usize]
    }
    /// O(1): read a live slot.
    fn get(&self, run: &Run<T>, index: usize) -> T {
        assert!(index < run.len as usize);
        self.values[run.start as usize + index]
    }
    /// O(1): update a live slot.
    fn get_mut(&mut self, run: &Run<T>, index: usize) -> &mut T {
        assert!(index < run.len as usize);
        &mut self.values[run.start as usize + index]
    }
}
#[derive(Clone, Copy)]
struct ActionState {
    cached: Option<NodeId>,
    remaining: u32,
    finished: Finished,
}
#[derive(Default)]
pub(super) struct Storage {
    program: Pool<Op>,
    actions: Pool<Action>,
    states: Pool<ActionState>,
    marks: Pool<Span>,
    outputs: Pool<Output>,
    work: Vec<Work>,
    cache: Vec<[u32; 2]>,
    test_work: Vec<(TestId, bool)>,
    test_values: Vec<NodeId>,
    copy_scratch: crate::bir::edit::CopyScratch,
    copied_vars: Vec<(VarId, VarId)>,
    copied_labels: Vec<(u32, u32)>,
    program_steps: usize,
    copied_outputs: usize,
    imported: Vec<Option<ImportedPlan>>,
    literals: Vec<LiteralEmission>,
    aliases: Vec<Option<u32>>,
}

struct ImportedPlan {
    facts: dispatch::Facts,
    literals: Vec<(dispatch::LiteralId, u32)>,
    payloads: Vec<(dispatch::Kind, u32)>,
}
#[derive(Clone, Copy)]
enum LiteralValue {
    String(crate::bir::StrId),
    Number(crate::bir::ConstId),
    Bool(bool),
    Null,
    Undefined,
}
struct LiteralEmission {
    key: CaseKey,
    value: LiteralValue,
}

/// Metadata-only import: no grouping, planning or simplification runs here.
pub(super) fn prepare(arena: &mut Bir) -> (Storage, dispatch::Plan<u32>) {
    let mut storage = Storage::default();
    let mut graph = dispatch::Plan::default();
    for i in 0..arena.pools.switches.len() {
        let h = arena.switch(crate::bir::SwitchId(i as u32));
        let SwitchDispatch::Variant(facts) = h.dispatch else {
            storage.imported.push(None);
            continue;
        };
        let facts = graph.metadata.import_facts(facts);
        let mut literals = Vec::new();
        let mut payloads = Vec::new();
        for (i, key) in h.keys.iter().enumerate() {
            match key {
                CaseKey::Lambda(SwitchKey::Constructor(Case::Constant(tag))) => {
                    literals.push((graph.metadata.import_literal(&tag.literal), i as u32))
                }
                CaseKey::Lambda(SwitchKey::Constructor(Case::Block(block))) => {
                    if let Some(kind) = block.block_type() {
                        payloads.push((graph.metadata.import_kind(kind), i as u32));
                    }
                }
                _ => {}
            }
        }
        storage.imported.push(Some(ImportedPlan {
            facts,
            literals,
            payloads,
        }));
    }
    for i in 0..graph.metadata.literal_count() {
        use dispatch::Literal as L;
        let (key, value) = match graph.metadata.literal(dispatch::LiteralId(i as u32)) {
            L::String(s) => {
                let text = arena.intern_text(graph.metadata.text(s));
                (CaseKey::String(text), LiteralValue::String(text))
            }
            L::Float(s) => {
                let spelling = graph.metadata.text(s);
                let text = arena.intern_text(spelling);
                let value = arena.intern_float(spelling).expect("valid literal float");
                (CaseKey::Float(text), LiteralValue::Number(value))
            }
            L::BigInt(s) => {
                let spelling = graph.metadata.text(s);
                let text = arena.intern_text(spelling);
                let (positive, digits) = crate::types::typecore::parse_bigint_literal(spelling);
                let canonical =
                    arena.intern_text(&format!("{}{digits}", if positive { '+' } else { '-' }));
                let value = arena.intern_const(crate::bir::Constant::BigInt(canonical));
                (CaseKey::BigInt(text), LiteralValue::Number(value))
            }
            L::Int(i) => {
                let value = arena.intern_const(crate::bir::Constant::Int(i64::from(i as i32)));
                (
                    CaseKey::JavaScript(SwitchCaseTag::Int(i64::from(i as i32))),
                    LiteralValue::Number(value),
                )
            }
            L::Bool(b) => (
                CaseKey::JavaScript(SwitchCaseTag::Bool(b)),
                LiteralValue::Bool(b),
            ),
            L::Null => (CaseKey::JavaScript(SwitchCaseTag::Null), LiteralValue::Null),
            L::Undefined => (
                CaseKey::JavaScript(SwitchCaseTag::Undefined),
                LiteralValue::Undefined,
            ),
        };
        storage.literals.push(LiteralEmission { key, value });
    }
    (storage, graph)
}

pub(super) struct Plan {
    source: NodeId,
    operands: crate::bir::ListId,
    start: Span,
    cont: Cont,
    target: Option<VarId>,
    scrutinee: Option<NodeId>,
    payload_only: bool,
    program: Run<Op>,
    pc: usize,
    actions: Run<Action>,
    states: Run<ActionState>,
    marks: Run<Span>,
    outputs: Run<Output>,
}

impl State {
    /// V: compile_untagged_switch. O(planner work + its emitted plan + new
    /// fingerprint nodes). Stable source groups provide dense equality aliases;
    /// planner comparisons read those aliases without borrowing mutable state.
    /// Dispatch graph pools survive every construct; metadata is borrowed during planning.
    pub(super) fn untagged_switch(
        &mut self,
        cx: Cx,
        source: NodeId,
        operands: crate::bir::ListId,
        header: crate::bir::SwitchId,
    ) -> Result<Untagged, Unsupported> {
        self.prepare_switch_hashes();
        let source_count = self.source.lists.get(operands).len();
        let groups = self.group_switch_cases(operands, source_count, None);
        let mut aliases = std::mem::take(&mut self.untagged_storage.aliases);
        aliases.resize(source_count, None);
        aliases.fill(None);
        for group in 0..groups.heads.len {
            let mut case = self.group_indices[(groups.heads.start + group) as usize];
            loop {
                let source = self.source.lists.get(operands)[case];
                if self.switch_facts[source.index()].comparable() {
                    aliases[case] = Some(group);
                }
                case = self.group_indices[groups.next.start as usize + case];
                if case == super::switch::NONE {
                    break;
                }
            }
        }
        let mut dispatch = std::mem::take(&mut self.untagged_dispatch);
        let h = self.arena.switch(header);
        let n = h.constants as usize;
        let full = (h.consts_full, h.blocks_full);
        let payload_only = h.consts_full && n == 0;
        let fallback = h.has_default.then_some(h.keys.len() as u32);
        let imported = self.untagged_storage.imported[header.index()]
            .as_ref()
            .expect("imported dispatch");
        dispatch::append_bucketed(
            &mut dispatch,
            |a: &u32, b: &u32| {
                aliases[*a as usize].is_some() && aliases[*a as usize] == aliases[*b as usize]
            },
            |body: &u32| {
                aliases[*body as usize]
                    .map_or(source_count + *body as usize, |alias| alias as usize)
            },
            dispatch::BorrowedInput {
                facts: &imported.facts,
                literal_arms: &imported.literals,
                payload_arms: &imported.payloads,
                literals_complete: full.0,
                payloads_complete: full.1,
                fallback,
            },
        );
        let (program, actions) =
            self.untagged_program(&dispatch, operands, fallback, cx.switch_depth);
        aliases.clear();
        self.untagged_storage.aliases = aliases;
        self.untagged_dispatch = dispatch;
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
        let states = Run::new(
            self.untagged_storage.states.values.len(),
            actions.len as usize,
            actions.len as usize,
        );
        for action in &self.untagged_storage.actions.values[actions.range()] {
            self.untagged_storage.states.values.push(ActionState {
                cached: None,
                remaining: action.uses,
                finished: Finished::False,
            });
        }
        let marks = self
            .untagged_storage
            .marks
            .stack(program.len as usize, Span { start: 0, len: 0 });
        let outputs = self.untagged_storage.outputs.stack(
            program.len as usize,
            Output {
                run: Span { start: 0, len: 0 },
                action: NONE,
                finished: Finished::False,
            },
        );
        self.untagged.push(Some(Plan {
            source,
            operands,
            start,
            cont: cx.cont,
            target: binding.map(|(_, v)| v),
            scrutinee: None,
            payload_only,
            program,
            pc: 0,
            actions,
            states,
            marks,
            outputs,
        }));
        Ok(frame)
    }

    /// V: emit_untagged_tree's order, including default before switch clauses.
    /// O(plan occurrences + clauses), using an explicit stack. Source actions
    /// are cached by dense arm index and the two in-switch states.
    fn untagged_program(
        &mut self,
        plan: &dispatch::Plan<u32>,
        sources: crate::bir::ListId,
        fallback: Option<u32>,
        depth: u32,
    ) -> (Run<Op>, Run<Action>) {
        let sources = self.source.lists.get(sources);
        let storage = &mut self.untagged_storage;
        let program_start = storage.program.values.len();
        let action_start = storage.actions.values.len();
        let program = &mut storage.program.values;
        let actions = &mut storage.actions.values;
        let cache = &mut storage.cache;
        cache.resize(sources.len(), [NONE; 2]);
        cache.fill([NONE; 2]);
        let work = &mut storage.work;
        work.push(Work::Visit(plan.root(), depth));
        while let Some(task) = work.pop() {
            storage.program_steps += 1;
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
                            *slot = (actions.len() - action_start) as u32;
                            actions.push(Action {
                                source: sources[arm as usize],
                                depth,
                                uses: 1,
                                fallback: matches!(plan.tree(tree), Tree::Fallback),
                            });
                            program.push(Op::Run(*slot));
                        } else {
                            actions[action_start + *slot as usize].uses += 1;
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
        (
            Run::new(
                program_start,
                program.len() - program_start,
                program.len() - program_start,
            ),
            Run::new(
                action_start,
                actions.len() - action_start,
                actions.len() - action_start,
            ),
        )
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
        into.extend(
            self.untagged_storage.actions.values[p.actions.range()]
                .iter()
                .map(|a| {
                    (
                        Cx {
                            cont,
                            switch_depth: a.depth,
                            ..cx
                        },
                        a.source,
                    )
                }),
        );
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
            let Op::Run(action) = self.untagged_storage.program.get(&p.program, p.pc) else {
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
            self.locate_switch_run(
                self.untagged_storage
                    .actions
                    .get(&p.actions, action as usize)
                    .source,
                out.stmts,
            );
            self.untagged_storage
                .states
                .get_mut(&p.states, action as usize)
                .finished = out.finished;
            if self
                .untagged_storage
                .actions
                .get(&p.actions, action as usize)
                .uses
                > 1
            {
                let list = self.statements.take_list(&mut self.arena, out.stmts);
                self.untagged_storage
                    .states
                    .get_mut(&p.states, action as usize)
                    .cached = Some(self.arena.block_from_list(list));
                self.emit_cached_action(&mut p, action);
            } else {
                self.untagged_storage
                    .states
                    .get_mut(&p.states, action as usize)
                    .remaining -= 1;
                self.untagged_storage.outputs.push(
                    &mut p.outputs,
                    Output {
                        run: out.stmts,
                        action,
                        finished: out.finished,
                    },
                );
            }
        }
        let dispatch = std::mem::take(&mut self.untagged_dispatch);
        self.advance_untagged(&mut p, &dispatch);
        self.untagged_dispatch = dispatch;
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
        self.untagged_storage.copied_outputs += 1;
        let mut vars = std::mem::take(&mut self.untagged_storage.copied_vars);
        let mut labels = std::mem::take(&mut self.untagged_storage.copied_labels);
        let copied = self.arena.copy_subtree_with_scratch(
            root,
            &[],
            &mut vars,
            &mut labels,
            &mut self.untagged_storage.copy_scratch,
        );
        for (new, old) in vars.drain(..) {
            assert_eq!(new.index(), self.idents.len());
            self.idents.push(self.idents[old.index()]);
            self.arena.vars.order[new.index()] = self.arena.vars.order(old);
        }
        labels.clear();
        self.untagged_storage.copied_vars = vars;
        self.untagged_storage.copied_labels = labels;
        copied
    }

    /// V: untagged_fallback_block, generalized to all shared plan actions.
    /// O(output size) for repeated occurrences; the last takes the original.
    fn emit_cached_action(&mut self, p: &mut Plan, action: u32) {
        let i = action as usize;
        self.untagged_storage.states.get_mut(&p.states, i).remaining -= 1;
        let root = if self.untagged_storage.states.get(&p.states, i).remaining == 0 {
            self.untagged_storage
                .states
                .get_mut(&p.states, i)
                .cached
                .take()
                .unwrap()
        } else {
            self.copy_dispatch_output(
                self.untagged_storage
                    .states
                    .get(&p.states, i)
                    .cached
                    .unwrap(),
            )
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
        self.untagged_storage.outputs.push(
            &mut p.outputs,
            Output {
                run: self.statements.since(start),
                action,
                finished: self.untagged_storage.states.get(&p.states, i).finished,
            },
        );
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
    fn advance_untagged(&mut self, p: &mut Plan, dispatch: &dispatch::Plan<u32>) {
        while p.pc < p.program.len as usize {
            let op = self.untagged_storage.program.get(&p.program, p.pc);
            if matches!(op, Op::Run(_)) {
                break;
            }
            p.pc += 1;
            match op {
                Op::Run(_) => unreachable!(),
                Op::Begin => {
                    let start = self.statements.mark();
                    self.statements.reserve();
                    self.untagged_storage.marks.push(&mut p.marks, start);
                }
                Op::Empty => self.untagged_storage.outputs.push(
                    &mut p.outputs,
                    Output {
                        run: self.statements.mark(),
                        action: NONE,
                        finished: Finished::False,
                    },
                ),
                Op::Cached(action) => self.emit_cached_action(p, action),
                Op::If(test) => {
                    let no = self.untagged_storage.outputs.pop(&mut p.outputs);
                    let yes = self.untagged_storage.outputs.pop(&mut p.outputs);
                    let test = self.untagged_test(p, dispatch, test);
                    self.untagged_if(p, test, yes.run, no.run);
                }
                Op::Block => {
                    let out = self.untagged_storage.outputs.pop(&mut p.outputs);
                    let start = self.untagged_storage.marks.pop(&mut p.marks);
                    let only = self.unnest(out.run.start);
                    let run = self.statements.since(Span {
                        start: out.run.start,
                        len: 0,
                    });
                    let block = if let Some((_, statement)) = only {
                        self.statements.kill(run);
                        statement
                    } else {
                        let list = self.statements.take_list(&mut self.arena, run);
                        self.arena.explicit_block_from_list(list)
                    };
                    self.place(start.start, block);
                    self.untagged_storage.outputs.push(
                        &mut p.outputs,
                        Output {
                            run: self.statements.since(start),
                            action: NONE,
                            finished: Finished::False,
                        },
                    );
                }
                Op::Switch(tree) => self.untagged_switch_statement(p, dispatch, tree),
            }
        }
    }

    /// V: untagged_if / normalized_if_block. O(statements consumed by J-S3).
    fn untagged_if(&mut self, p: &mut Plan, test: NodeId, yes: Span, no: Span) {
        let start = self.untagged_storage.marks.pop(&mut p.marks);
        let statement = self.if_statement(test, yes, no);
        self.place(start.start, statement);
        if matches!(p.cont, Cont::Effect(Tail::Return(_))) {
            self.unnest(start.start);
        }
        self.untagged_storage.outputs.push(
            &mut p.outputs,
            Output {
                run: self.statements.since(start),
                action: NONE,
                finished: Finished::False,
            },
        );
    }

    /// V: emit_untagged_clause. O(1) control/exit facts, plus one list transfer.
    fn untagged_clause(&mut self, p: &Plan, out: Output) -> (NodeId, ClauseMeta) {
        let should_break = if out.action == NONE {
            false
        } else if self
            .untagged_storage
            .actions
            .get(&p.actions, out.action as usize)
            .fallback
        {
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
                    || self.switch_has_exit(
                        self.untagged_storage
                            .actions
                            .get(&p.actions, out.action as usize)
                            .source,
                    ))
        };
        let loc = if out.action != NONE
            && !self
                .untagged_storage
                .actions
                .get(&p.actions, out.action as usize)
                .fallback
        {
            self.switch_location(
                self.untagged_storage
                    .actions
                    .get(&p.actions, out.action as usize)
                    .source,
            )
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
    fn untagged_switch_statement(
        &mut self,
        p: &mut Plan,
        dispatch: &dispatch::Plan<u32>,
        tree: TreeId,
    ) {
        let (cases, typeof_, value_switch) = match dispatch.tree(tree) {
            Tree::SwitchValue(clauses, _) => (*clauses, false, true),
            Tree::SwitchTypeof(clauses, _) => {
                let cases = dispatch.typeof_clauses(*clauses);
                if cases.len() == 1 && matches!(cases[0].1, Clause::Body(_)) {
                    let no = self.untagged_storage.outputs.pop(&mut p.outputs);
                    let yes = self.untagged_storage.outputs.pop(&mut p.outputs);
                    let value = self.untagged_scrutinee(p);
                    let test = self.untagged_typeof(value, &cases[0].0);
                    self.untagged_if(p, test, yes.run, no.run);
                    return;
                }
                (*clauses, true, false)
            }
            _ => unreachable!("switch operation"),
        };
        let count = cases.len();
        let keys = crate::bir::KeySpan {
            start: self.arena.pools.switch_keys.len() as u32,
            len: count as u32,
        };
        let start = self.untagged_storage.marks.pop(&mut p.marks);
        let base = p.outputs.len as usize - count - 1;
        let default = self.untagged_storage.outputs.get(&p.outputs, base);
        let has_default = !value_switch || self.statements.has_statements(default.run);
        let action_count = count + usize::from(has_default);
        let actions = self.arena.lists.push_iter(
            action_count,
            std::iter::repeat_n(NodeId(u32::MAX), action_count),
        );
        let clauses = crate::bir::ClauseSpan {
            start: self.arena.pools.switch_clauses.len() as u32,
            len: action_count as u32,
        };
        for i in 0..count {
            let key = if value_switch {
                self.untagged_storage.literals[dispatch.value_clauses(cases)[i].0.0 as usize]
                    .key
                    .clone()
            } else {
                CaseKey::String(
                    self.arena
                        .intern_text(dispatch.typeof_clauses(cases)[i].0.typeof_name().unwrap()),
                )
            };
            self.arena.pools.switch_keys.push(key);
            let (body, mut meta) = self.untagged_clause(
                p,
                self.untagged_storage.outputs.get(&p.outputs, base + 1 + i),
            );
            let clause = match dispatch.tree(tree) {
                Tree::SwitchValue(c, _) => &dispatch.value_clauses(*c)[i].1,
                Tree::SwitchTypeof(c, _) => &dispatch.typeof_clauses(*c)[i].1,
                _ => unreachable!(),
            };
            if let Clause::FallsThrough(Some(arm)) = clause {
                meta.loc = self.switch_location(self.source.lists.get(p.operands)[*arm as usize]);
            }
            self.arena.lists.set(actions, i, body);
            self.arena.pools.switch_clauses.push(meta);
        }
        if has_default {
            let list = self.statements.take_list(&mut self.arena, default.run);
            let body = self.arena.block_from_list(list);
            self.arena.lists.set(actions, count, body);
            self.arena.pools.switch_clauses.push(ClauseMeta {
                should_break: false,
                comment: None,
                loc: None,
            });
        } else {
            self.statements.kill(default.run);
        }
        p.outputs.len = base as u32;
        let mut scrutinee = self.untagged_scrutinee(p);
        if typeof_ {
            scrutinee = plain::node(&mut self.arena, View::JTypeof { value: scrutinee }, 0);
        }
        let header = self.arena.switch_record(crate::bir::SwitchRecord {
            constants: count as u32,
            keys,
            clauses,
            consts_full: false,
            blocks_full: false,
            has_default,
            dispatch: SwitchDispatch::Direct,
        });
        let statement = self.arena.switch_from_list(scrutinee, actions, header, 1);
        self.statements.fill(start.start, statement);
        self.untagged_storage.outputs.push(
            &mut p.outputs,
            Output {
                run: self.statements.since(start),
                action: NONE,
                finished: Finished::False,
            },
        );
    }

    /// V: untagged_typeof_expr. O(1), retaining raw typeof rather than folding.
    fn untagged_typeof(&mut self, value: NodeId, kind: &dispatch::Kind) -> NodeId {
        let value = plain::node(&mut self.arena, View::JTypeof { value }, 0);
        let text = plain::string(&mut self.arena, kind.typeof_name().expect("typeof kind"));
        norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, value, text)
    }

    /// V: untagged_test_expr. O(test occurrences + emitted scrutinee copies),
    /// using explicit stacks instead of recursion on the planner's tests.
    fn untagged_test(&mut self, p: &Plan, dispatch: &dispatch::Plan<u32>, test: TestId) -> NodeId {
        let mut work = std::mem::take(&mut self.untagged_storage.test_work);
        let mut values = std::mem::take(&mut self.untagged_storage.test_values);
        work.push((test, false));
        while let Some((id, done)) = work.pop() {
            let test = dispatch.test(id);
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
                    let right = match self.untagged_storage.literals[tag.0 as usize].value {
                        LiteralValue::String(text) => {
                            plain::node(&mut self.arena, View::JStr { text }, 0)
                        }
                        LiteralValue::Number(value) => {
                            plain::node(&mut self.arena, View::JNumber { value }, 0)
                        }
                        LiteralValue::Bool(b) => plain::boolean(&mut self.arena, b),
                        LiteralValue::Null => plain::node(&mut self.arena, View::JNull, 0),
                        LiteralValue::Undefined => {
                            plain::node(&mut self.arena, View::JUndefined, 0)
                        }
                    };
                    norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::EqEqEq, left, right)
                }
                Test::Typeof(kind) => {
                    let value = self.untagged_scrutinee(p);
                    self.untagged_typeof(value, kind)
                }
                Test::Instance(instance) => {
                    let value = self.untagged_scrutinee(p);
                    self.untagged_instance(value, &dispatch.metadata, *instance)
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
        let value = values.pop().unwrap();
        self.untagged_storage.test_work = work;
        self.untagged_storage.test_values = values;
        value
    }

    /// V: class_constructor / is_instance_of. O(class path bytes); array tests
    /// use the same ordinary CallInfo as the legacy constructor.
    fn untagged_instance(
        &mut self,
        value: NodeId,
        metadata: &dispatch::Metadata,
        instance: dispatch::InstanceId,
    ) -> NodeId {
        let name = metadata.instance_name(instance);
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
        if !metadata.is_class(instance) {
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
        assert_eq!(p.pc, p.program.len as usize);
        assert_eq!(p.outputs.len as usize, 1);
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
        ShapeAllocation, VariantBlock, VariantBlockType, VariantInstance,
        VariantLiteralTag as Literal, VariantMatchingFacts, VariantTag,
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
                vec![Literal::String("single".into())],
                vec![Literal::Float("1.5".into())],
                vec![Literal::BigInt("2".into())],
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
                a.prim_raw(
                    LambdaPrimitive::PinitMod,
                    &[value],
                    crate::lambda::LamLoc::NONE,
                )
            };
            let actions: Vec<_> = exits
                .iter()
                .enumerate()
                .map(|(i, &exit)| {
                    if exit {
                        a.static_raise(1, &[])
                    } else {
                        effect(&mut a, i as i32)
                    }
                })
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
        assert_eq!(state.untagged_storage.program_steps, 10_000);
        state.complete(Cx::returning(), out);
    }

    #[test]
    fn ten_thousand_nested_payload_dispatches_lower_without_allocations() {
        let mut a = LamArena::new();
        let info = a.add_switch(
            true,
            [],
            true,
            [SwitchKey::Constructor(Case::Block(
                VariantBlock::Untagged {
                    tag: VariantTag {
                        name: crate::name::Name::new("Payload"),
                        literal: Literal::String("Payload".into()),
                    },
                    block_type: VariantBlockType::Unknown,
                },
            ))],
            false,
            SwitchDispatch::Variant(VariantMatchingFacts {
                tag_name: None,
                literal_tags: vec![],
                block_types: vec![VariantBlockType::Unknown],
            }),
        );
        let mut root = a.var(Ident::new("result", 101, crate::ident::IdentFlags::NONE));
        for _ in 0..10_000 {
            let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
            let actions = a.add_list(&[root]);
            root = a.switch_raw(x, actions, info);
        }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let output = s.probe(Cx::returning(), root).unwrap();
            let output = s.realize(Cx::returning(), output);
            for node in s.statements.statements(output.stmts) {
                s.arena.release(node);
            }
            if let Some(value) = output.value {
                s.arena.release(value);
            }
            s.statements.kill(output.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        run(&mut state);
        state
            .arena
            .lists
            .reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.free.reserve_repeat();
        state.untagged_dispatch.reserve_repeat();
        state.group_indices.reserve(state.group_indices.len());
        state.group_nodes.reserve(state.group_nodes.len());
        let storage = &mut state.untagged_storage;
        storage.program.values.reserve(storage.program.values.len());
        storage.actions.values.reserve(storage.actions.values.len());
        storage.states.values.reserve(storage.states.values.len());
        storage.marks.values.reserve(storage.marks.values.len());
        storage.outputs.values.reserve(storage.outputs.values.len());
        let capacities = |s: &State| {
            let d = &s.untagged_storage;
            [
                s.arena.nodes.capacity(),
                s.arena.parents.capacity(),
                s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(),
                s.arena.lists.storage_shape().1,
                s.traversal.work.capacity(),
                s.traversal.values.capacity(),
                s.traversal.children.capacity(),
                s.group_indices.capacity(),
                s.group_nodes.capacity(),
                s.group_table.capacity(),
                s.group_heads.capacity(),
                s.group_order.capacity(),
                s.untagged.capacity(),
                d.program.values.capacity(),
                d.actions.values.capacity(),
                d.states.values.capacity(),
                d.marks.values.capacity(),
                d.outputs.values.capacity(),
                d.work.capacity(),
                d.cache.capacity(),
                d.imported.capacity(),
                d.literals.capacity(),
                d.aliases.capacity(),
            ]
        };
        let before = capacities(&state);
        let free_before = state.free.capacities();
        let graph_before = state.untagged_dispatch.capacities();
        let visits = state.source_steps;
        let programs = state.untagged_storage.program_steps;
        let grouping = state.switch_group_steps;
        let allocations = allocation_counter::measure(|| run(&mut state));
        println!("whole nested untagged payloads: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.untagged_dispatch.capacities(), graph_before);
        assert_eq!(state.source_steps - visits, 20_001);
        assert_eq!(state.untagged_storage.program_steps - programs, 10_000);
        assert_eq!(state.switch_group_steps - grouping, 20_000);
    }

    #[test]
    fn ten_thousand_mixed_cases_lower_without_allocations() {
        let mut a = LamArena::new();
        let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
        let mut literals: Vec<_> = (0..9_998)
            .map(|i| Literal::String(format!("tag{i}")))
            .collect();
        let keys: Vec<_> = literals
            .iter()
            .enumerate()
            .map(|(i, literal)| {
                SwitchKey::Constructor(Case::Constant(VariantTag {
                    name: crate::name::Name::new(&format!("C{i}")),
                    literal: literal.clone(),
                }))
            })
            .collect();
        // This unnamed numeric literal must go to fallback, not the Number
        // payload. The fallback also occurs in the payload dispatch, forcing
        // cached-output copying rather than merely sharing grouped case labels.
        literals.push(Literal::Int(42));
        let kinds = vec![VariantBlockType::Number, VariantBlockType::Object];
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
        let bodies: Vec<_> = (0..10_001)
            .map(|i| a.const_(C::String(format!("body{i}"))))
            .collect();
        let actions = a.add_list(&bodies);
        let header = a.add_switch(
            false,
            keys,
            false,
            blocks,
            true,
            SwitchDispatch::Variant(VariantMatchingFacts {
                tag_name: None,
                literal_tags: literals,
                block_types: kinds,
            }),
        );
        let root = a.switch_raw(x, actions, header);
        assert_mixed_allocation_free(a, root, Some((10_003, 20_002, 20_008, 10_003, 1)));
    }

    #[test]
    fn small_equals_literals_lower_without_allocations() {
        for literal in [
            Literal::String("value".into()),
            Literal::Float("1.50".into()),
            Literal::BigInt("+002".into()),
        ] {
            let mut a = LamArena::new();
            let x = a.var(Ident::new("x", 100, crate::ident::IdentFlags::NONE));
            let kinds = vec![VariantBlockType::Number, VariantBlockType::Object];
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
            let body: Vec<_> = (0..4)
                .map(|i| a.const_(C::String(format!("body{i}"))))
                .collect();
            let actions = a.add_list(&body);
            let key = SwitchKey::Constructor(Case::Constant(VariantTag {
                name: crate::name::Name::new("C"),
                literal: literal.clone(),
            }));
            let header = a.add_switch(
                false,
                [key],
                false,
                blocks,
                true,
                SwitchDispatch::Variant(VariantMatchingFacts {
                    tag_name: None,
                    literal_tags: vec![literal, Literal::Int(42)],
                    block_types: kinds,
                }),
            );
            let root = a.switch_raw(x, actions, header);
            assert_mixed_allocation_free(a, root, Some((6, 8, 14, 4, 1)));
        }
    }

    fn assert_mixed_allocation_free(
        a: LamArena,
        root: crate::lambda::arena::Lam,
        expected: Option<(usize, usize, usize, usize, usize)>,
    ) {
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let out = s.probe(Cx::returning(), root).unwrap();
            let out = s.realize(Cx::returning(), out);
            for node in s.statements.statements(out.stmts) {
                s.arena.release(node);
            }
            if let Some(value) = out.value {
                s.arena.release(value);
            }
            s.statements.kill(out.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        let keys = state.arena.pools.switch_keys.len();
        run(&mut state);
        state
            .arena
            .lists
            .reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state
            .arena
            .pools
            .switch_keys
            .reserve(state.arena.pools.switch_keys.len() - keys);
        state
            .arena
            .pools
            .switch_clauses
            .reserve(state.arena.pools.switch_clauses.len());
        state
            .arena
            .pools
            .switches
            .reserve(state.arena.pools.switches.len());
        state.free.reserve_repeat();
        state.untagged_dispatch.reserve_repeat();
        state.group_indices.reserve(state.group_indices.len());
        state.group_nodes.reserve(state.group_nodes.len());
        let d = &mut state.untagged_storage;
        d.program.values.reserve(d.program.values.len());
        d.actions.values.reserve(d.actions.values.len());
        d.states.values.reserve(d.states.values.len());
        d.marks.values.reserve(d.marks.values.len());
        d.outputs.values.reserve(d.outputs.values.len());
        let capacities = |s: &State| {
            let d = &s.untagged_storage;
            [
                s.arena.nodes.capacity(),
                s.arena.parents.capacity(),
                s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(),
                s.arena.lists.storage_shape().1,
                s.arena.pools.switch_keys.capacity(),
                s.arena.pools.switch_clauses.capacity(),
                s.arena.pools.switches.capacity(),
                s.traversal.work.capacity(),
                s.traversal.values.capacity(),
                s.traversal.children.capacity(),
                s.group_indices.capacity(),
                s.group_nodes.capacity(),
                s.group_table.capacity(),
                s.group_heads.capacity(),
                s.group_order.capacity(),
                s.untagged.capacity(),
                d.program.values.capacity(),
                d.actions.values.capacity(),
                d.states.values.capacity(),
                d.marks.values.capacity(),
                d.outputs.values.capacity(),
                d.work.capacity(),
                d.cache.capacity(),
                d.aliases.capacity(),
                d.test_work.capacity(),
                d.test_values.capacity(),
                d.copied_vars.capacity(),
                d.copied_labels.capacity(),
                s.arena.j_equal_work.borrow().capacity(),
            ]
        };
        let before = capacities(&state);
        let statements_before = state.statements.capacities();
        let graph_before = state.untagged_dispatch.capacities();
        let free_before = state.free.capacities();
        let metadata_before = state.untagged_dispatch.metadata.capacities();
        let copy_before = state.untagged_storage.copy_scratch.capacities();
        let counts = (
            state.source_steps,
            state.switch_group_steps,
            state.untagged_storage.program_steps,
            state.untagged_dispatch.grouping_steps(),
            state.untagged_storage.copied_outputs,
        );
        let allocations = allocation_counter::measure(|| run(&mut state));
        println!(
            "mixed whole Lambda: {allocations:?}; source={}, grouping={}, program={}, planner grouping={}, copies={}",
            state.source_steps - counts.0,
            state.switch_group_steps - counts.1,
            state.untagged_storage.program_steps - counts.2,
            state.untagged_dispatch.grouping_steps() - counts.3,
            state.untagged_storage.copied_outputs - counts.4
        );
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.statements.capacities(), statements_before);
        assert_eq!(state.untagged_dispatch.capacities(), graph_before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(
            state.untagged_dispatch.metadata.capacities(),
            metadata_before
        );
        assert_eq!(
            state.untagged_storage.copy_scratch.capacities(),
            copy_before
        );
        if let Some(expected) = expected {
            assert_eq!(
                (
                    state.source_steps - counts.0,
                    state.switch_group_steps - counts.1,
                    state.untagged_storage.program_steps - counts.2,
                    state.untagged_dispatch.grouping_steps() - counts.3,
                    state.untagged_storage.copied_outputs - counts.4
                ),
                expected
            );
        }
        assert!(state.untagged_storage.copied_outputs > counts.4);
    }

    #[test]
    fn ten_thousand_reserved_plan_slots_do_not_allocate() {
        let mut outputs = Pool::default();
        let empty = Output {
            run: Span::default(),
            action: NONE,
            finished: Finished::False,
        };
        let mut parent = outputs.stack(10_000, empty);
        let mut child = outputs.stack(10_000, empty);
        let exercise =
            |outputs: &mut Pool<Output>, parent: &mut Run<Output>, child: &mut Run<Output>| {
                for i in 0..10_000 {
                    outputs.push(parent, Output { action: i, ..empty });
                    outputs.push(
                        child,
                        Output {
                            action: i + 10_000,
                            ..empty
                        },
                    );
                }
                for i in (0..10_000).rev() {
                    assert_eq!(outputs.pop(child).action, i + 10_000);
                    assert_eq!(outputs.pop(parent).action, i);
                }
            };
        exercise(&mut outputs, &mut parent, &mut child);
        let capacity = outputs.values.capacity();
        let allocations =
            allocation_counter::measure(|| exercise(&mut outputs, &mut parent, &mut child));
        assert_eq!(allocations.count_total, 0);
        assert_eq!(outputs.values.capacity(), capacity);
    }

    #[test]
    fn program_element_sizes() {
        assert_eq!(std::mem::size_of::<Plan>(), 120);
        assert_eq!(std::mem::size_of::<Run<Op>>(), 12);
        assert_eq!(std::mem::size_of::<Run<Action>>(), 12);
        assert_eq!(std::mem::size_of::<ActionState>(), 16);
        assert_eq!(std::mem::size_of::<Untagged>(), 4);
        assert_eq!(std::mem::size_of::<Op>(), 8);
        assert_eq!(std::mem::size_of::<Work>(), 12);
        assert_eq!(std::mem::size_of::<Action>(), 16);
        assert_eq!(std::mem::size_of::<Output>(), 16);
    }
}
