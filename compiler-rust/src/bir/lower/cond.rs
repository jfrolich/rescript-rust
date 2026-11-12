//! Conditionals and short circuits (BACKEND_LOWERING sections 3.6 and 3.7).
//!
//! A branch that needs statements stays where it was lowered, as a run of the
//! statement stack. A rule that keeps one branch as the statements following
//! a guard leaves that run in place and puts the guard in a slot reserved
//! before both branches, so no statement is moved once per enclosing
//! conditional. A run becomes a child list exactly once.
use super::*;
use crate::bir::j::norm;
use crate::bir::{ListId, NodeFlags};

/// The construct a `Conditional` frame lowers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    /// `If(c, t, e)`.
    If,
    /// `l && r`: `If(l, r, false)` in a return continuation.
    And,
    /// `l || r`: `If(l, true, r)` in a return continuation.
    Or,
}

/// The variable the branches of a conditional assign.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    /// Rows R4 and R5, and a short circuit that is not declared or assigned.
    None,
    /// Row R1: the result the conditional creates.
    Result(VarId),
    /// Rows R2 and R3: the variable of the continuation.
    Given(VarId),
}

/// The operands of a conditional or short circuit, saved while its children
/// are lowered. One per frame of the source traversal.
pub(super) struct Conditional {
    condition: NodeId,
    then_: NodeId,
    /// The right operand again for a short circuit, whose other branch is a
    /// constant.
    else_: NodeId,
    target: Target,
    kind: Kind,
    /// Row R5 step 0 applies: only the test is lowered.
    unit: bool,
    /// A slot for a declaration is reserved before the head slot.
    declares: bool,
}

/// Where the output of a conditional starts and where its head slot is. The
/// declaration slot, when there is one, is the slot before the head.
#[derive(Clone, Copy)]
struct Parts {
    start: u32,
    head: u32,
}

const EMPTY: Span = Span { start: 0, len: 0 };

impl State {
    /// K1: C:1812, rows R1 to R6 and section 3.7, on entering the node. One
    /// call is constant, except in a return continuation of a function that
    /// returns unit: there it reads the Let/Seq spine of both branches (row
    /// R5 step 0), and a spine node belongs to one conditional.
    pub(super) fn conditional(
        &mut self,
        cx: Cx,
        kind: Kind,
        condition: NodeId,
        then_: NodeId,
        else_: NodeId,
    ) -> Result<Conditional, Unsupported> {
        if matches!(
            cx.cont,
            Cont::Effect(Tail::Return(Ret::Named { loop_: Some(_), .. }))
                | Cont::Value(Tail::Return(Ret::Named { loop_: Some(_), .. }))
        ) {
            // R6 needs the tail-loop record owned by the let-rec slice.
            return Err(Unsupported("let rec"));
        }
        let returns = matches!(cx.cont, Cont::Effect(Tail::Return(_)));
        // R5 step 0, C:3691 compile_if_unit_return_tail_block: decided before
        // the branches are lowered, so nothing is lowered and discarded.
        let unit = returns
            && cx.return_unit
            && kind == Kind::If
            && self.trivial_unit(then_)
            && self.trivial_unit(else_);
        let (target, declares) = match (kind, cx.cont) {
            // 3.8: the result precedes the identifiers of the branches.
            (Kind::If, Cont::Value(_)) => (Target::Result(self.fresh_variable("tmp")), true),
            (_, Cont::Declare(_, target)) => (Target::Given(target), true),
            (_, Cont::Assign(target)) => (Target::Given(target), false),
            (Kind::If, Cont::Effect(_)) => (Target::None, false),
            // 3.7: the result of a short circuit is created after its operands.
            (Kind::And | Kind::Or, Cont::Value(_) | Cont::Effect(_)) => (Target::None, !returns),
        };
        Ok(Conditional {
            condition,
            then_,
            else_,
            target,
            kind,
            unit,
            declares,
        })
    }

    /// The continuation the branches are probed in (3.6, "The new lowering";
    /// 3.7 for the right operand of a short circuit). Constant.
    fn branch_cx(cx: Cx, conditional: &Conditional) -> Cx {
        let cont = match (conditional.kind, conditional.target, cx.cont) {
            (_, _, Cont::Effect(Tail::Return(_))) => cx.cont,
            (Kind::If, Target::Result(target) | Target::Given(target), _) => Cont::Assign(target),
            (Kind::If, Target::None, _) => Cont::Effect(Tail::No),
            (Kind::And | Kind::Or, _, _) => Cont::Value(Tail::No),
        };
        Cx {
            cont,
            probing: true,
            ..cx
        }
    }

    /// K1: C:1812. The test, then the branches unless row R5 step 0 applies.
    /// Constant.
    pub(super) fn conditional_children(
        &self,
        cx: Cx,
        conditional: &Conditional,
        into: &mut Vec<(Cx, NodeId)>,
    ) {
        into.push((
            Cx {
                cont: Cont::Value(Tail::No),
                ..cx
            },
            conditional.condition,
        ));
        if conditional.unit {
            return;
        }
        let branch = Self::branch_cx(cx, conditional);
        into.push((branch, conditional.then_));
        if conditional.kind == Kind::If {
            into.push((branch, conditional.else_));
        }
    }

    /// K1: C:1812, as each child completes; `cx` is the child's. The test is
    /// realized and the slots are reserved; a branch that needs statements
    /// gets the effect of its value (C:4875 compiled_to_effect_block, row R4)
    /// and is trimmed. One call costs the statements it pushes and the holes
    /// it pops.
    pub(super) fn conditional_child(
        &mut self,
        cx: Cx,
        conditional: &Conditional,
        index: usize,
        child: Probed,
    ) -> Probed {
        if index == 0 {
            let mut out = self.realize(cx, child);
            if let Target::Result(target) = conditional.target {
                // 3.8: the result is named after the identifiers of the test.
                self.arena.vars.order[target.index()] = self.next_order;
                self.next_order += 1;
            }
            if !conditional.unit {
                if conditional.declares {
                    self.statements.reserve();
                }
                self.statements.reserve();
            }
            out.stmts = self.statements.since(Span {
                start: out.stmts.start,
                len: 0,
            });
            return Probed::Out(out);
        }
        let Probed::Out(mut out) = child else {
            return child;
        };
        match cx.cont {
            // 3.7: the value of the right operand is assigned by the rule.
            Cont::Value(_) => {}
            Cont::Effect(Tail::No) => {
                if let Some(value) = out.value.take() {
                    if out.finished == Finished::True {
                        self.arena.release(value);
                    } else {
                        self.drop_pure_effect(value);
                    }
                }
            }
            Cont::Effect(Tail::Return(_)) | Cont::Assign(_) | Cont::Declare(..) => {
                if let Some(value) = out.value.take() {
                    self.arena.release(value);
                }
            }
        }
        out.stmts = self.statements.trim(Span {
            start: out.stmts.start,
            len: 0,
        });
        Probed::Out(out)
    }

    /// K1: C:1812, after the children: the row of `cx`. The cost is that
    /// row's; none of them reads a statement of a branch that stays in place.
    pub(super) fn finish_conditional(
        &mut self,
        cx: Cx,
        conditional: Conditional,
        mut children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let Some(Probed::Out(test)) = children.next() else {
            unreachable!("the test was realized")
        };
        let start = test.stmts.start;
        let end = start + test.stmts.len;
        let test = test.value.expect("test value");
        if conditional.unit {
            // R5 step 0, C:3691: the test alone, kept only for its effects.
            self.push_s_if_empty(test);
            return Probed::Out(self.output(start, None, Finished::True));
        }
        let parts = Parts {
            start,
            head: end - 1,
        };
        let yes = children.next().expect("first branch");
        if conditional.kind == Kind::If {
            let no = children.next().expect("second branch");
            return self.finish_if(cx, conditional.target, parts, test, yes, no);
        }
        let and = conditional.kind == Kind::And;
        if !matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
            return self.short_circuit(cx, and, parts, test, yes);
        }
        // 3.7, C:3187 compile_short_circuit_return_output: the If rule with
        // a constant branch; no L node is built.
        let constant = self.pure_expression(View::JBool, u16::from(!and));
        let constant = Probed::Free(self.free.push(Free::Leaf(constant)));
        if and {
            self.finish_if(cx, Target::None, parts, test, yes, constant)
        } else {
            self.finish_if(cx, Target::None, parts, test, constant, yes)
        }
    }

    /// Rows R1 to R5 on the probed branches. Both free costs one deferred
    /// record, or one realization when the test has statements.
    fn finish_if(
        &mut self,
        cx: Cx,
        target: Target,
        parts: Parts,
        test: NodeId,
        yes: Probed,
        no: Probed,
    ) -> Probed {
        let (yes, no) = match (yes, no) {
            (Probed::Free(then_), Probed::Free(else_)) => {
                // Nothing follows the reserved slots: drop them.
                self.statements.trim(Self::from(parts.start));
                if self.statements.since(Self::from(parts.start)).len == 0 {
                    return Probed::Free(self.free.push(Free::Cond { test, then_, else_ }));
                }
                if matches!(cx.cont, Cont::Effect(Tail::No)) {
                    // C:7612 compiled_from_effect_block reads the whole block.
                    let then_ = self.free_value(cx, then_);
                    let else_ = self.free_value(cx, else_);
                    self.free_effect(test, then_, else_);
                    return self.effect_output(parts.start);
                }
                let free = self.free.push(Free::Cond { test, then_, else_ });
                let out = self.realize(cx, Probed::Free(free));
                return Probed::Out(self.output(parts.start, out.value, out.finished));
            }
            branches => branches,
        };
        match (cx.cont, target) {
            (Cont::Effect(Tail::No), _) => self.effect_conditional(cx, parts, test, yes, no),
            (Cont::Effect(Tail::Return(_)), _) => self.return_conditional(cx, parts, test, yes, no),
            (_, Target::Result(target) | Target::Given(target)) => {
                let assign = Cx {
                    cont: Cont::Assign(target),
                    ..cx
                };
                let yes = self.run(assign, yes);
                let no = self.run(assign, no);
                self.assigning_conditional(cx.cont, parts, test, target, yes, no)
            }
            (_, Target::None) => {
                unreachable!("a value, declared or assigned conditional has a target")
            }
        }
    }

    /// The empty run at a stack position.
    fn from(start: u32) -> Span {
        Span { start, len: 0 }
    }

    /// The output from `start` to the top of the stack.
    fn output(&self, start: u32, value: Option<NodeId>, finished: Finished) -> Out {
        Out {
            stmts: self.statements.since(Self::from(start)),
            value,
            finished,
        }
    }

    /// The value of a free branch: one realization, no statement.
    fn free_value(&mut self, cx: Cx, free: FreeId) -> NodeId {
        let cx = Cx {
            cont: Cont::Value(Tail::No),
            ..cx
        };
        let out = self.realize(cx, Probed::Free(free));
        debug_assert!(!self.statements.has_statements(out.stmts));
        out.value.expect("free value")
    }

    /// The run of a branch in `cx`: a free branch is converted (1.4), which
    /// pushes its one statement at the top of the stack.
    fn run(&mut self, cx: Cx, branch: Probed) -> Span {
        match branch {
            Probed::Free(_) => self.realize(cx, branch).stmts,
            Probed::Out(out) => out.stmts,
        }
    }

    /// Fill a reserved slot; an explicit empty block is recorded for the
    /// `if_` of an enclosing conditional. Constant.
    fn place(&mut self, slot: u32, statement: NodeId) {
        self.statements.fill(slot, statement);
        if matches!(self.arena.view(statement), View::SBlock { statements } if statements.is_empty())
        {
            self.statements.note_empty_block(slot, statement);
        }
    }

    /// B:1225 block of no statement: an explicit empty block.
    fn empty_block(&mut self) -> NodeId {
        self.arena.new_node(View::SBlock { statements: &[] }, 1)
    }

    /// Forget two consumed runs, the upper one first so that both are popped
    /// when they are the top of the stack.
    fn kill(&mut self, first: Span, second: Span) {
        let (lower, upper) = if first.start <= second.start {
            (first, second)
        } else {
            (second, first)
        };
        self.statements.kill(upper);
        self.statements.kill(lower);
    }

    /// Release the statements of a discarded run: one step per statement.
    fn release_run(&mut self, run: Span) {
        for statement in self.statements.statements(run) {
            self.arena.release(statement);
        }
        self.statements.kill(run);
    }

    /// `[return value]`: the statement and the returned value. Constant on a
    /// trimmed run.
    fn single_return(&mut self, run: Span) -> Option<(NodeId, NodeId)> {
        let (_, statement) = self.statements.only(run)?;
        match self.arena.view(statement) {
            View::SReturn { value } => Some((statement, value)),
            _ => None,
        }
    }

    /// C:5187 take_single_result_assignment: `[target = value]`, the
    /// statement and the value. Constant on a trimmed run.
    fn single_assignment(&mut self, run: Span, target: VarId) -> Option<(NodeId, NodeId)> {
        let (_, statement) = self.statements.only(run)?;
        let View::SExp { value } = self.arena.view(statement) else {
            return None;
        };
        let View::JBin { left, right } = self.arena.view(value) else {
            return None;
        };
        (self.arena.node(value).aux() == crate::js_ir::BinOp::Eq as u16
            && matches!(self.arena.view(left), View::Var { var } if var == target))
        .then_some((statement, right))
    }

    /// js_stmt_make.ml:186 block_last_is_return_throw_or_continue, on the
    /// literal last statement.
    fn terminal(&self, statement: NodeId) -> bool {
        matches!(
            self.arena.view(statement),
            View::SReturn { .. }
                | View::SThrow { .. }
                | View::SBreak { .. }
                | View::SContinue { .. }
        )
    }

    /// The test without its negation, when it has one. Constant.
    fn positive(&mut self, test: NodeId) -> Option<NodeId> {
        let View::JNot { value } = self.arena.view(test) else {
            return None;
        };
        self.arena.detach(value);
        self.arena.release(test);
        Some(value)
    }

    /// `if (test) yes else no` with both lists as given: no rule of J-S3.
    fn raw_if(&mut self, test: NodeId, yes: ListId, no: ListId) -> NodeId {
        let then_ = self.arena.block_from_list(yes);
        let else_ = self.arena.block_from_list(no);
        self.arena.new_node(
            View::SIf {
                condition: test,
                then_,
                else_: Some(else_),
            },
            0,
        )
    }

    /// J-S3 (B:1575 simplify_if) gives exactly `raw_if` for these operands.
    /// Reads the test, and the first and last statement of each run: constant
    /// on trimmed runs.
    fn plain_if(&mut self, test: NodeId, yes: Span, no: Span) -> bool {
        if matches!(self.arena.view(test), View::JBool) {
            return false;
        }
        let Some(last) = self.statements.last(yes) else {
            return false;
        };
        let terminal = self.terminal(last);
        let nested = |state: &Self, only: Option<(u32, NodeId)>| {
            only.is_some_and(|(_, s)| matches!(state.arena.view(s), View::SIf { .. }))
        };
        let only_yes = self.statements.only(yes);
        if self.statements.first(no).is_none() {
            // Rule 6 with nothing after the guard; else rule 9 on a nested if.
            return terminal || !nested(self, only_yes);
        }
        if matches!(self.arena.view(test), View::JNot { .. }) || terminal {
            return false;
        }
        let only_no = self.statements.only(no);
        let is = |state: &Self, only: Option<(u32, NodeId)>, effect: bool| {
            only.is_some_and(|(_, s)| match state.arena.view(s) {
                View::SExp { .. } => effect,
                View::SReturn { .. } => !effect,
                _ => false,
            })
        };
        !is(self, only_no, false)
            && !(is(self, only_yes, true) && is(self, only_no, true))
            && !nested(self, only_yes)
            && !nested(self, only_no)
    }

    /// B:1575 simplify_if as one statement, consuming both runs. One step per
    /// statement of the runs (each is copied to its list once). The rules
    /// that rewrite the operands are `norm::js3_simplify_if`'s; it takes
    /// owned vectors, and is called only when `plain_if` says a rule applies.
    fn if_statement(&mut self, test: NodeId, yes: Span, no: Span) -> NodeId {
        self.statements.drop_empty_blocks(&mut self.arena, yes);
        self.statements.drop_empty_blocks(&mut self.arena, no);
        if self.plain_if(test, yes, no) {
            let (yes, no) = if yes.start >= no.start {
                let yes = self.statements.take_list(&mut self.arena, yes);
                (yes, self.statements.take_list(&mut self.arena, no))
            } else {
                let no = self.statements.take_list(&mut self.arena, no);
                (self.statements.take_list(&mut self.arena, yes), no)
            };
            return self.raw_if(test, yes, no);
        }
        let then_: Vec<NodeId> = self.statements.statements(yes).collect();
        let else_: Vec<NodeId> = self.statements.statements(no).collect();
        self.statements.copied += then_.len() + else_.len();
        self.kill(yes, no);
        norm::js3_simplify_if(&mut self.arena, test, then_, else_)
    }

    /// B:1575 simplify_if without the block around its result: the head
    /// statement goes to the `head` slot and a branch the rules keep as the
    /// following statements stays where it is. Constant, plus the statements
    /// of a run that becomes a list or is discarded; the kept run is not read.
    fn if_in_place(&mut self, head: u32, mut test: NodeId, mut yes: Span, mut no: Span) {
        self.statements.drop_empty_blocks(&mut self.arena, yes);
        self.statements.drop_empty_blocks(&mut self.arena, no);
        loop {
            if matches!(self.arena.view(test), View::JBool) {
                // Rule 0: block of the branch taken.
                let taken = self.arena.node(test).aux() != 0;
                self.arena.release(test);
                let (kept, dropped) = if taken { (yes, no) } else { (no, yes) };
                self.release_run(dropped);
                if self.statements.first(kept).is_none() {
                    let block = self.empty_block();
                    self.place(head, block);
                }
                return;
            }
            let no_empty = self.statements.first(no).is_none();
            if !no_empty && let Some(value) = self.positive(test) {
                // Rule 1.
                test = value;
                std::mem::swap(&mut yes, &mut no);
                continue;
            }
            let Some(last) = self.statements.last(yes) else {
                if no_empty {
                    // Rule 2: the test alone.
                    let statement = if self.arena.node(test).flags().contains(NodeFlags::PURE) {
                        self.arena.release(test);
                        self.empty_block()
                    } else {
                        norm::js1_exp(&mut self.arena, test)
                    };
                    self.place(head, statement);
                    return;
                }
                // Rule 3.
                test = norm::je8_not(&mut self.arena, test);
                std::mem::swap(&mut yes, &mut no);
                continue;
            };
            if let Some((statement, value)) = self.single_return(no) {
                self.arena.detach(value);
                self.arena.release(statement);
                self.statements.kill(no);
                let statement = if let Some((statement, then_)) = self.single_return(yes) {
                    // Rule 4: one return of a conditional expression.
                    self.arena.detach(then_);
                    self.arena.release(statement);
                    self.statements.kill(yes);
                    let value = norm::je7_cond(&mut self.arena, test, then_, value);
                    self.arena.new_node(View::SReturn { value }, 0)
                } else {
                    // Rule 5: `if (!test) return value`, then `yes` in place.
                    let test = norm::je8_not(&mut self.arena, test);
                    let statement = self.arena.new_node(View::SReturn { value }, 0);
                    let then_ = self.arena.lists.push(&[statement]);
                    let else_ = self.arena.lists.push(&[]);
                    self.raw_if(test, then_, else_)
                };
                self.place(head, statement);
                return;
            }
            if self.terminal(last) {
                // Rule 6: `if (test) yes`, then `no` in place.
                let then_ = self.statements.take_list(&mut self.arena, yes);
                let else_ = self.arena.lists.push(&[]);
                let statement = self.raw_if(test, then_, else_);
                self.place(head, statement);
                return;
            }
            // Rules 7 to 10, or the plain statement.
            let statement = self.if_statement(test, yes, no);
            self.place(head, statement);
            return;
        }
    }

    /// B:1225 block over the statements from `head`: more than one becomes
    /// one explicit block. One step per statement wrapped, each wrapped once.
    fn block_statement(&mut self, head: u32) {
        let run = self.statements.trim(Self::from(head));
        if self.statements.only(run).is_some() {
            return;
        }
        let list = self.statements.take_list(&mut self.arena, run);
        let block = self.arena.explicit_block_from_list(list);
        self.statements.push(block);
        if self.arena.lists.get(list).is_empty() {
            self.statements.note_empty_block(head, block);
        }
    }

    /// B:1565 unnest_block over the output from `start`: a block that is its
    /// only statement is replaced by its statements. Constant when it is not;
    /// else one step per statement of the block.
    fn unnest(&mut self, start: u32) -> Option<(u32, NodeId)> {
        loop {
            let run = self.statements.trim(Self::from(start));
            let only = self.statements.only(run)?;
            let (slot, block) = only;
            let View::SBlock { statements } = self.arena.view(block) else {
                return Some(only);
            };
            self.statements.clear(slot);
            let mark = self.statements.mark();
            for &statement in statements {
                self.statements.push(statement);
            }
            for statement in self.statements.statements(self.statements.since(mark)) {
                self.arena.detach(statement);
            }
            self.arena.release(block);
        }
    }

    /// C:7612 compiled_from_effect_block over the output from `start`: a
    /// lone expression statement becomes the value. Constant, plus `unnest`.
    fn effect_output(&mut self, start: u32) -> Probed {
        let value = match self.unnest(start) {
            Some((slot, statement)) if matches!(self.arena.view(statement), View::SExp { .. }) => {
                let View::SExp { value } = self.arena.view(statement) else {
                    unreachable!()
                };
                self.arena.detach(value);
                self.arena.release(statement);
                self.statements.clear(slot);
                self.statements.trim(Self::from(start));
                value
            }
            _ => self.pure_expression(View::JUndefined, 0),
        };
        Probed::Out(self.output(start, Some(value), Finished::False))
    }

    /// O:359 push_s_if_empty: the test as a statement when it has effects.
    fn push_s_if_empty(&mut self, test: NodeId) {
        let mut statements = std::mem::take(&mut self.scratch);
        norm::jm14_push_s_if_empty(&mut self.arena, test, &mut statements);
        for statement in statements.drain(..) {
            self.statements.push(statement);
        }
        self.scratch = statements;
    }

    /// Rows R1 to R3 on the two runs that assign `target`. Costs
    /// `if_statement`, or is constant when both branches are one assignment.
    fn assigning_conditional(
        &mut self,
        cont: Cont,
        parts: Parts,
        test: NodeId,
        target: VarId,
        yes: Span,
        no: Span,
    ) -> Probed {
        let used = (crate::js_ir::op::UsedStats::Used as u16) << 2;
        if let Cont::Value(_) = cont {
            // R1, C:1812 compile_expr: `let tmp`, `if_(c, T, E)`, value `tmp`.
            let statement = self.if_statement(test, yes, no);
            self.place(parts.head, statement);
            let declaration = self.arena.new_node(
                View::SDecl {
                    var: target,
                    value: None,
                },
                LetKind::Strict as u16 | used,
            );
            self.statements.fill(parts.head - 1, declaration);
            let value = self.pure_expression(View::Var { var: target }, 0);
            return Probed::Out(self.output(parts.start, Some(value), Finished::False));
        }
        let merged = self.merge_assignments(test, target, yes, no);
        match (cont, merged) {
            // R2, C:5049 compile_declared_if_block.
            (Cont::Declare(kind, _), Ok(value)) => {
                let statement = crate::bir::j::declare(&mut self.arena, kind, target, value);
                self.statements.fill(parts.head - 1, statement);
                self.statements.trim(Self::from(parts.head));
            }
            (Cont::Declare(kind, _), Err((test, yes, no))) => {
                let statement = self.if_statement(test, yes, no);
                self.place(parts.head, statement);
                let declaration = self.arena.new_node(
                    View::SDecl {
                        var: target,
                        value: None,
                    },
                    kind as u16 | used,
                );
                self.statements.fill(parts.head - 1, declaration);
            }
            // R3, C:5018 compile_test_assignment_block.
            (_, merged) => {
                let statement = self.assignment_statement(target, merged);
                self.place(parts.head, statement);
            }
        }
        Probed::Out(self.output(parts.start, None, Finished::False))
    }

    /// Rows R2 and R3 before their result: the swap of C:6741
    /// normalize_if_assignment_merge_order, then the conditional expression
    /// when each run is the one statement `target = x` (the runs are
    /// consumed), else the operands after the swap. Constant on trimmed runs.
    fn merge_assignments(
        &mut self,
        mut test: NodeId,
        target: VarId,
        mut yes: Span,
        mut no: Span,
    ) -> Result<NodeId, (NodeId, Span, Span)> {
        if self.statements.first(no).is_some()
            && let Some(value) = self.positive(test)
        {
            test = value;
            std::mem::swap(&mut yes, &mut no);
        }
        let (Some((then_, yes_value)), Some((else_, no_value))) = (
            self.single_assignment(yes, target),
            self.single_assignment(no, target),
        ) else {
            return Err((test, yes, no));
        };
        self.arena.detach(yes_value);
        self.arena.detach(no_value);
        self.arena.release(then_);
        self.arena.release(else_);
        self.kill(yes, no);
        Ok(norm::je7_cond(&mut self.arena, test, yes_value, no_value))
    }

    /// Row R3 as one statement: `target = cond(...)` or `if_(c, T, E)`.
    fn assignment_statement(
        &mut self,
        target: VarId,
        merged: Result<NodeId, (NodeId, Span, Span)>,
    ) -> NodeId {
        match merged {
            Ok(value) => crate::bir::j::assign(&mut self.arena, target, value),
            Err((test, yes, no)) => self.if_statement(test, yes, no),
        }
    }

    /// R4 steps 2 to 4, C:4884 compile_if_effect_block, then C:7612
    /// compiled_from_effect_block. Costs one `if_statement` over the branch
    /// that becomes the guarded list; the other branch is not read.
    fn effect_conditional(
        &mut self,
        cx: Cx,
        parts: Parts,
        test: NodeId,
        yes: Probed,
        no: Probed,
    ) -> Probed {
        let yes = self.effect_run(cx, yes);
        let no = self.effect_run(cx, no);
        let statement = match (yes, no) {
            // Step 2: a free then branch without effects.
            (None, Some(no)) => {
                let test = norm::je8_not(&mut self.arena, test);
                self.if_statement(test, no, EMPTY)
            }
            // Step 3: a free else branch without effects.
            (Some(yes), None) => self.if_statement(test, yes, EMPTY),
            (Some(yes), Some(no)) => {
                let last = self.statements.last(yes);
                if self.single_return(no).is_some() {
                    // Step 4, first form: the then branch follows in place.
                    let test = norm::je8_not(&mut self.arena, test);
                    self.if_statement(test, no, EMPTY)
                } else if last.is_some_and(|last| self.terminal(last)) {
                    // Step 4, second form: the else branch follows in place.
                    self.if_statement(test, yes, EMPTY)
                } else {
                    self.if_statement(test, yes, no)
                }
            }
            (None, None) => unreachable!("two free branches are row R4 step 1"),
        };
        self.place(parts.head, statement);
        self.effect_output(parts.start)
    }

    /// `E(branch)` as a run (C:4875 compiled_to_effect_block), or nothing for
    /// a free branch whose value has no effect (E:15). Constant.
    fn effect_run(&mut self, cx: Cx, branch: Probed) -> Option<Span> {
        match branch {
            // B:1565 unnest_block has nothing to do here: no producer of an
            // effect output leaves one block as its only statement.
            Probed::Out(out) => Some(out.stmts),
            Probed::Free(free) => {
                let value = self.free_value(cx, free);
                if self.arena.node(value).flags().contains(NodeFlags::STRICT) {
                    self.arena.release(value);
                    return None;
                }
                let mark = self.statements.mark();
                self.drop_pure_effect(value);
                Some(self.statements.since(mark))
            }
        }
    }

    /// R4 step 1 on the values of two free branches: pushes the statements.
    /// Constant, plus J-M0 over the comma spine of each value.
    fn free_effect(&mut self, test: NodeId, yes: NodeId, no: NodeId) {
        let yes = norm::jm0_remove_pure_subexpression(&mut self.arena, yes);
        let no = norm::jm0_remove_pure_subexpression(&mut self.arena, no);
        let (test, value) = match (yes, no) {
            (None, None) => return self.push_s_if_empty(test),
            (Some(yes), Some(no)) => {
                let value = norm::je7_cond(&mut self.arena, test, yes, no);
                return self.drop_pure_effect(value);
            }
            (Some(value), None) => (test, value),
            (None, Some(value)) => (norm::je8_not(&mut self.arena, test), value),
        };
        let mark = self.statements.mark();
        let statement = norm::js1_exp(&mut self.arena, value);
        self.statements.push(statement);
        let run = self.statements.since(mark);
        let statement = self.if_statement(test, run, EMPTY);
        let slot = self.statements.mark().start;
        self.statements.push(statement);
        if matches!(self.arena.view(statement), View::SBlock { statements } if statements.is_empty())
        {
            self.statements.note_empty_block(slot, statement);
        }
    }

    /// R5 steps 1 and 3, C:5267 compile_if_return_output, then the
    /// unnest_block of C:3179 compile_return_output. Step 1 reads the
    /// expression statements that lead each branch and stops at the first
    /// other statement; step 3 is `if_in_place`. A branch kept as the
    /// statements after a guard is not read, moved or copied.
    fn return_conditional(
        &mut self,
        cx: Cx,
        parts: Parts,
        test: NodeId,
        yes: Probed,
        no: Probed,
    ) -> Probed {
        let yes = self.run(cx, yes);
        let no = self.run(cx, no);
        // Step 1, C:5241 try_fold_effect_only_return_tail. The legacy gate
        // lambda_contains_statement_value_form (C:5139) holds for every unit
        // this lowering accepts: each such form is still Unsupported.
        if self.returns_after_effects(yes) && self.returns_after_effects(no) {
            let then_ = self.fold_return_tail(yes);
            let else_ = self.fold_return_tail(no);
            self.kill(yes, no);
            let value = norm::je7_cond(&mut self.arena, test, then_, else_);
            let statement = crate::bir::j::return_value(&mut self.arena, value);
            self.statements.fill(parts.head, statement);
            return Probed::Out(self.output(parts.start, None, Finished::True));
        }
        // Step 3, C:5368 compile_test_return_block_with_fallback.
        if self.single_return(yes).is_none() && self.single_return(no).is_some() {
            // One block of `if (!c) E` and `T`; `T` stays in place.
            let test = norm::je8_not(&mut self.arena, test);
            let statement = self.if_statement(test, no, EMPTY);
            self.place(parts.head, statement);
        } else {
            self.if_in_place(parts.head, test, yes, no);
        }
        let prelude = Span {
            start: parts.start,
            len: parts.head - parts.start,
        };
        if self.statements.first(prelude).is_some() {
            // The block is one of several statements and stays a block.
            self.block_statement(parts.head);
        } else {
            self.unnest(parts.start);
        }
        Probed::Out(self.output(parts.start, None, Finished::False))
    }

    /// C:5241: the run is expression statements followed by one `return`.
    /// One step per leading expression statement, counted in `scanned`.
    fn returns_after_effects(&mut self, run: Span) -> bool {
        let Some(last) = self.statements.last(run) else {
            return false;
        };
        if !matches!(self.arena.view(last), View::SReturn { .. }) {
            return false;
        }
        let mut steps = 0;
        let mut folds = true;
        for statement in self.statements.statements(run) {
            steps += 1;
            if statement == last {
                break;
            }
            if !matches!(self.arena.view(statement), View::SExp { .. }) {
                folds = false;
                break;
            }
        }
        self.statements.scanned += steps;
        folds
    }

    /// C:5241: `(e1, (e2, ..., value))` from `e1; e2; ...; return value`.
    /// One step per statement of the run, which is consumed.
    fn fold_return_tail(&mut self, run: Span) -> NodeId {
        let mut result = None;
        for statement in self.statements.statements_rev(run) {
            let (View::SReturn { value } | View::SExp { value }) = self.arena.view(statement)
            else {
                unreachable!("checked by returns_after_effects")
            };
            self.arena.detach(value);
            self.arena.release(statement);
            result = Some(match result {
                None => value,
                Some(result) => norm::jm1_js_seq(&mut self.arena, value, result),
            });
        }
        result.expect("a return statement")
    }

    /// C:3662 lambda_is_trivial_unit_undefined on the forms this lowering
    /// accepts. One step per Let/Seq node of the spine, counted in
    /// `spine_steps`; purity is the node's cached flag.
    fn trivial_unit(&mut self, mut node: NodeId) -> bool {
        let pure =
            |state: &Self, node: NodeId| state.source.node(node).flags().contains(NodeFlags::PURE);
        loop {
            self.spine_steps += 1;
            match self.source.view(node) {
                View::Const { value } => {
                    return matches!(
                        self.arena.constant(value),
                        crate::bir::Constant::Undefined(true)
                    );
                }
                View::Seq { first, second } if pure(self, first) => node = second,
                View::Let {
                    value: Some(value),
                    body,
                    ..
                } if pure(self, value) => node = body,
                _ => return false,
            }
        }
    }

    /// Section 3.7 outside a return continuation: C:2918
    /// compile_short_circuit_js, C:2971 compile_short_circuit_binding_block,
    /// C:5415 for an assignment. The right operand was lowered once, as a
    /// value. Constant when it is free; else `if_statement` over its run.
    fn short_circuit(
        &mut self,
        cx: Cx,
        and: bool,
        parts: Parts,
        left: NodeId,
        right: Probed,
    ) -> Probed {
        let right = match right {
            Probed::Free(free) => {
                let right = self.free_value(cx, free);
                let value = if and {
                    norm::je5_js_and(&mut self.arena, left, right)
                } else {
                    norm::je6_js_or(&mut self.arena, left, right)
                };
                self.statements.trim(Self::from(parts.start));
                if self.statements.since(Self::from(parts.start)).len == 0 {
                    return self.probe_leaf(cx, value);
                }
                let out = self.leaf(cx, value);
                return Probed::Out(self.output(parts.start, out.value, out.finished));
            }
            Probed::Out(right) => right,
        };
        let target = match cx.cont {
            Cont::Assign(target) | Cont::Declare(_, target) => target,
            Cont::Value(_) | Cont::Effect(_) => self.fresh_variable("tmp"),
        };
        if let Some(value) = right.value {
            if right.finished == Finished::True {
                self.arena.release(value);
            } else {
                let statement = crate::bir::j::assign(&mut self.arena, target, value);
                self.statements.push(statement);
            }
        }
        let yes = self.statements.since(Self::from(right.stmts.start));
        let default = self.pure_expression(View::JBool, u16::from(!and));
        let no = match cx.cont {
            Cont::Assign(_) => {
                let mark = self.statements.mark();
                let statement = crate::bir::j::assign(&mut self.arena, target, default);
                self.statements.push(statement);
                self.statements.since(mark)
            }
            Cont::Declare(..) | Cont::Value(_) | Cont::Effect(_) => {
                // lam_compile.ml:1128-1135: a declared target is `Variable`.
                let kind = if matches!(cx.cont, Cont::Declare(..)) {
                    LetKind::Variable
                } else {
                    LetKind::Strict
                };
                let statement = crate::bir::j::declare(&mut self.arena, kind, target, default);
                self.statements.fill(parts.head - 1, statement);
                EMPTY
            }
        };
        let test = if and {
            left
        } else {
            norm::je8_not(&mut self.arena, left)
        };
        let statement = self.if_statement(test, yes, no);
        self.place(parts.head, statement);
        let value = match cx.cont {
            Cont::Value(_) | Cont::Effect(_) => {
                Some(self.pure_expression(View::Var { var: target }, 0))
            }
            Cont::Declare(..) | Cont::Assign(_) => None,
        };
        Probed::Out(self.output(parts.start, value, Finished::False))
    }

    /// `realize(Free::Cond, k)` of section 3.6: on the values of the two
    /// branches, or in **A** on their assignments. Constant.
    pub(super) fn realize_conditional(&mut self, cx: Cx, test: NodeId, yes: Out, no: Out) -> Out {
        match cx.cont {
            Cont::Effect(Tail::No) => {
                let start = self.statements.mark().start;
                let yes = yes.value.expect("free value");
                let no = no.value.expect("free value");
                self.free_effect(test, yes, no);
                let Probed::Out(out) = self.effect_output(start) else {
                    unreachable!()
                };
                out
            }
            Cont::Assign(target) => {
                // R3, C:4996: the branches were realized for `A(target)`.
                let start = yes.stmts.start;
                let merged = self.merge_assignments(test, target, yes.stmts, no.stmts);
                let statement = self.assignment_statement(target, merged);
                self.statements.trim(Self::from(start));
                self.statements.push(statement);
                self.output(start, None, Finished::False)
            }
            Cont::Value(_) | Cont::Declare(..) | Cont::Effect(Tail::Return(_)) => {
                let yes = yes.value.expect("free value");
                let no = no.value.expect("free value");
                let value = norm::je7_cond(&mut self.arena, test, yes, no);
                self.leaf(cx, value)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::oracle_tests::compare;
    use super::*;
    use crate::bir::{bridge, bridge_j};
    use crate::ident::IdentFlags;
    use crate::js_ir::BinOp;
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_constant::Constant;
    use crate::lambda::lam_primitive::Primitive;
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc};

    // Level-L shapes. Every oracle test lowers its shape in the five
    // continuations, probed and direct, against the legacy functions.
    fn var(a: &mut LamArena, name: &str, stamp: i32) -> Lam {
        a.var(Ident::new(name, stamp, IdentFlags::NONE))
    }
    fn int(a: &mut LamArena, i: i32) -> Lam {
        a.const_(Constant::Int { i, comment: None })
    }
    fn unit(a: &mut LamArena) -> Lam {
        a.const_(Constant::JsUndefined { is_unit: true })
    }
    /// A call: a value with an effect and no statement.
    fn effect(a: &mut LamArena, stamp: i32) -> Lam {
        let callee = var(a, "effect", stamp);
        let info = ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::InferFull,
        };
        a.apply_raw(callee, &[], info)
    }
    /// `let binding = null; body`: a form that needs a statement.
    fn bound(a: &mut LamArena, stamp: i32, body: Lam) -> Lam {
        let value = a.const_(Constant::JsNull);
        a.let_(
            LetKind::Strict,
            Ident::new("binding", stamp, IdentFlags::NONE),
            value,
            body,
        )
    }
    fn if_(a: &mut LamArena, stamp: i32, yes: Lam, no: Lam) -> Lam {
        let condition = var(a, "condition", stamp);
        a.if_raw(condition, yes, no)
    }
    fn short(a: &mut LamArena, and: bool, left: Lam, right: Lam) -> Lam {
        let op = if and {
            Primitive::Psequand
        } else {
            Primitive::Psequor
        };
        a.prim_raw(op, &[left, right], LamLoc::NONE)
    }
    fn check(build: impl FnOnce(&mut LamArena) -> Lam) {
        let mut a = LamArena::new();
        let root = build(&mut a);
        compare(a, root);
    }

    #[test]
    fn r1_r2_r3_both_free() {
        check(|a| {
            let (yes, no) = (int(a, 1), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r1_r2_r3_statement_in_then() {
        check(|a| {
            let yes = int(a, 1);
            let (yes, no) = (bound(a, 2, yes), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r1_r2_r3_statement_in_else() {
        check(|a| {
            let no = int(a, 2);
            let (yes, no) = (int(a, 1), bound(a, 2, no));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r1_r2_r3_statements_in_both() {
        check(|a| {
            let (yes, no) = (int(a, 1), int(a, 2));
            let (yes, no) = (bound(a, 2, yes), bound(a, 3, no));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r1_r2_free_sequence_is_a_comma_and_r3_assigns_in_statements() {
        check(|a| {
            let (head, one) = (effect(a, 2), int(a, 1));
            let (yes, no) = (a.seq_raw(head, one), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r1_r2_r3_test_with_statements() {
        check(|a| {
            let test = var(a, "condition", 1);
            let test = bound(a, 2, test);
            let (yes, no) = (int(a, 1), int(a, 2));
            a.if_raw(test, yes, no)
        });
        check(|a| {
            let test = var(a, "condition", 1);
            let test = bound(a, 2, test);
            let yes = int(a, 1);
            let (yes, no) = (bound(a, 3, yes), int(a, 2));
            a.if_raw(test, yes, no)
        });
    }
    #[test]
    fn nested_conditionals_free_and_not() {
        for statement in [false, true] {
            for then_position in [false, true] {
                check(|a| {
                    let mut inner = int(a, 3);
                    if statement {
                        inner = bound(a, 9, inner);
                    }
                    let two = int(a, 2);
                    let inner = if_(a, 2, two, inner);
                    let one = int(a, 1);
                    if then_position {
                        if_(a, 1, inner, one)
                    } else {
                        if_(a, 1, one, inner)
                    }
                });
            }
        }
    }
    #[test]
    fn three_deep_chains_with_statements_at_each_level() {
        for then_position in [false, true] {
            check(|a| {
                let mut root = int(a, 0);
                root = bound(a, 10, root);
                for level in 1..4 {
                    let other = int(a, level);
                    let other = bound(a, 10 + level, other);
                    root = if then_position {
                        if_(a, level, root, other)
                    } else {
                        if_(a, level, other, root)
                    };
                }
                root
            });
        }
    }
    #[test]
    fn conditional_as_binding_argument_and_sequence_head() {
        check(|a| {
            let yes = int(a, 1);
            let (yes, no) = (bound(a, 3, yes), int(a, 2));
            let value = if_(a, 1, yes, no);
            let id = Ident::new("x", 4, IdentFlags::NONE);
            let body = a.var(id);
            a.let_(LetKind::Strict, id, value, body)
        });
        check(|a| {
            let (yes, no) = (effect(a, 2), effect(a, 3));
            let head = if_(a, 1, yes, no);
            let tail = int(a, 1);
            a.seq_raw(head, tail)
        });
    }

    #[test]
    fn r4_step1_neither_branch_has_an_effect() {
        check(|a| {
            let (yes, no) = (int(a, 1), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step1_both_branches_have_effects() {
        check(|a| {
            let (yes, no) = (effect(a, 2), effect(a, 3));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step1_only_then_has_an_effect() {
        check(|a| {
            let (yes, no) = (effect(a, 2), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step1_only_else_has_an_effect() {
        check(|a| {
            let (yes, no) = (int(a, 1), effect(a, 3));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step2_then_is_free_without_effects() {
        check(|a| {
            let no = effect(a, 3);
            let (yes, no) = (int(a, 1), bound(a, 4, no));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step3_else_is_free_without_effects() {
        check(|a| {
            let yes = effect(a, 2);
            let (yes, no) = (bound(a, 4, yes), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step4_free_branch_with_an_effect_beside_statements() {
        check(|a| {
            let no = effect(a, 3);
            let (yes, no) = (effect(a, 2), bound(a, 4, no));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r4_step4_both_branches_need_statements() {
        check(|a| {
            let (yes, no) = (effect(a, 2), effect(a, 3));
            let (yes, no) = (bound(a, 4, yes), bound(a, 5, no));
            if_(a, 1, yes, no)
        });
    }

    /// `throw exception`: a branch that ends in a terminal statement.
    fn raise(a: &mut LamArena, stamp: i32) -> Lam {
        let exception = var(a, "exception", stamp);
        a.prim_raw(Primitive::Praise, &[exception], LamLoc::NONE)
    }
    fn not(a: &mut LamArena, value: Lam) -> Lam {
        a.prim_raw(Primitive::Pnot, &[value], LamLoc::NONE)
    }

    #[test]
    fn negated_test_swaps_the_branches_in_every_row() {
        for statement in [false, true] {
            check(|a| {
                let test = var(a, "condition", 1);
                let test = not(a, test);
                let (mut yes, no) = (int(a, 1), int(a, 2));
                if statement {
                    yes = bound(a, 2, yes);
                }
                a.if_raw(test, yes, no)
            });
            check(|a| {
                let test = var(a, "condition", 1);
                let test = not(a, test);
                let (mut yes, mut no) = (effect(a, 2), effect(a, 3));
                if statement {
                    yes = bound(a, 4, yes);
                    no = bound(a, 5, no);
                }
                a.if_raw(test, yes, no)
            });
        }
    }
    #[test]
    fn r4_step4_then_ends_in_throw() {
        check(|a| {
            let (head, yes) = (effect(a, 2), raise(a, 3));
            let yes = a.seq_raw(head, yes);
            let no = effect(a, 4);
            let no = bound(a, 5, no);
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn branches_that_throw_in_every_row() {
        for statement in [false, true] {
            for then_position in [false, true] {
                check(|a| {
                    let thrown = raise(a, 2);
                    let mut other = int(a, 1);
                    if statement {
                        other = bound(a, 3, other);
                    }
                    if then_position {
                        if_(a, 1, thrown, other)
                    } else {
                        if_(a, 1, other, thrown)
                    }
                });
            }
        }
        check(|a| {
            let (yes, no) = (raise(a, 2), raise(a, 3));
            if_(a, 1, yes, no)
        });
    }

    #[test]
    fn r5_step0_trivial_unit_branches_of_a_unit_function() {
        for spine in [false, true] {
            check(|a| {
                let id = Ident::new("condition", 1, IdentFlags::NONE);
                let condition = a.var(id);
                let (mut yes, mut no) = (unit(a), unit(a));
                if spine {
                    let pure = int(a, 1);
                    yes = a.seq_raw(pure, yes);
                    no = bound(a, 2, no);
                }
                let body = a.if_raw(condition, yes, no);
                let attr = FunctionAttribute {
                    return_unit: true,
                    ..Default::default()
                };
                a.function_(1, &[id], body, attr, LamLoc::NONE)
            });
        }
    }
    #[test]
    fn r5_step0_needs_both_branches_trivial() {
        check(|a| {
            let id = Ident::new("condition", 1, IdentFlags::NONE);
            let condition = a.var(id);
            let (head, tail) = (effect(a, 2), unit(a));
            let (yes, no) = (a.seq_raw(head, tail), unit(a));
            let body = a.if_raw(condition, yes, no);
            let attr = FunctionAttribute {
                return_unit: true,
                ..Default::default()
            };
            a.function_(1, &[id], body, attr, LamLoc::NONE)
        });
    }
    #[test]
    fn r5_step1_effects_before_one_return_fold_to_commas() {
        check(|a| {
            let (first, second) = (effect(a, 2), effect(a, 3));
            let (yes, no) = (unit(a), unit(a));
            let (yes, no) = (a.seq_raw(first, yes), a.seq_raw(second, no));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r5_step2_both_free() {
        check(|a| {
            let (yes, no) = (effect(a, 2), int(a, 2));
            if_(a, 1, yes, no)
        });
    }
    #[test]
    fn r5_step3_else_is_one_return() {
        // The block is the whole output and is unnested.
        check(|a| {
            let yes = int(a, 1);
            let (yes, no) = (bound(a, 2, yes), int(a, 2));
            if_(a, 1, yes, no)
        });
        // After the statements of the test it stays one block.
        check(|a| {
            let test = var(a, "condition", 1);
            let test = bound(a, 3, test);
            let yes = int(a, 1);
            let (yes, no) = (bound(a, 2, yes), int(a, 2));
            a.if_raw(test, yes, no)
        });
    }
    #[test]
    fn r5_step3_then_ends_in_return() {
        check(|a| {
            let no = int(a, 2);
            let (yes, no) = (int(a, 1), bound(a, 2, no));
            if_(a, 1, yes, no)
        });
        check(|a| {
            let (yes, no) = (int(a, 1), int(a, 2));
            let (yes, no) = (bound(a, 2, yes), bound(a, 3, no));
            if_(a, 1, yes, no)
        });
        check(|a| {
            let test = var(a, "condition", 1);
            let test = bound(a, 4, test);
            let (yes, no) = (int(a, 1), int(a, 2));
            let (yes, no) = (bound(a, 2, yes), bound(a, 3, no));
            a.if_raw(test, yes, no)
        });
    }
    #[test]
    fn r6_tail_loop_is_unsupported_until_let_rec() {
        let mut a = LamArena::new();
        let (yes, no) = (int(&mut a, 1), int(&mut a, 2));
        let conditional = if_(&mut a, 1, yes, no);
        let (left, right) = (var(&mut a, "left", 2), var(&mut a, "right", 3));
        let circuit = short(&mut a, true, left, right);
        for root in [conditional, circuit] {
            let input = bridge::import_lambda(&a, root).unwrap();
            let node = input.root;
            let mut state = State::new(input);
            let named = Ret::Named {
                loop_: Some(LoopRef(0)),
                in_catch: false,
            };
            for cont in [
                Cont::Effect(Tail::Return(named)),
                Cont::Value(Tail::Return(named)),
            ] {
                assert!(matches!(
                    state.probe(Cx::new(cont), node),
                    Err(Unsupported("let rec"))
                ));
            }
        }
    }

    // Section 3.7: each test covers the rows V, D, A, E and R.
    #[test]
    fn short_circuit_with_a_free_right_operand() {
        for and in [false, true] {
            check(|a| {
                let (left, right) = (var(a, "left", 1), var(a, "right", 2));
                short(a, and, left, right)
            });
            check(|a| {
                let (left, right) = (var(a, "left", 1), effect(a, 2));
                short(a, and, left, right)
            });
        }
    }
    #[test]
    fn short_circuit_whose_right_operand_needs_statements() {
        for and in [false, true] {
            check(|a| {
                let (left, right) = (var(a, "left", 1), var(a, "right", 2));
                let right = bound(a, 3, right);
                short(a, and, left, right)
            });
        }
    }
    #[test]
    fn short_circuit_whose_left_operand_needs_statements() {
        for and in [false, true] {
            for statement in [false, true] {
                check(|a| {
                    let (left, mut right) = (var(a, "left", 1), var(a, "right", 2));
                    let left = bound(a, 3, left);
                    if statement {
                        right = bound(a, 4, right);
                    }
                    short(a, and, left, right)
                });
            }
        }
    }
    #[test]
    fn short_circuits_nest_in_each_other_and_in_conditionals() {
        for and in [false, true] {
            for statement in [false, true] {
                check(|a| {
                    let (first, second) = (var(a, "first", 1), var(a, "second", 2));
                    let mut third = var(a, "third", 3);
                    if statement {
                        third = bound(a, 4, third);
                    }
                    let inner = short(a, !and, second, third);
                    short(a, and, first, inner)
                });
                check(|a| {
                    let (left, mut right) = (var(a, "left", 2), var(a, "right", 3));
                    if statement {
                        right = bound(a, 4, right);
                    }
                    let test = short(a, and, left, right);
                    let (yes, no) = (int(a, 1), int(a, 2));
                    a.if_raw(test, yes, no)
                });
                check(|a| {
                    let (left, mut right) = (var(a, "left", 2), var(a, "right", 3));
                    if statement {
                        right = bound(a, 4, right);
                    }
                    let yes = short(a, and, left, right);
                    let no = a.const_(Constant::JsFalse);
                    if_(a, 1, yes, no)
                });
            }
        }
    }

    #[test]
    fn conditional_branch_temporaries_preserve_legacy_names() {
        check(|a| {
            let callee = var(a, "callee", 2);
            let argument = effect(a, 3);
            let id = Ident::new("tmp", 4, IdentFlags::NONE);
            let value = a.const_(Constant::JsNull);
            let body = a.var(id);
            let binding = a.let_(LetKind::Strict, id, value, body);
            let info = ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::InferFull,
            };
            let yes = a.apply_raw(callee, &[argument, binding], info);
            let no = a.const_(Constant::JsFalse);
            if_(a, 1, yes, no)
        });
    }

    #[test]
    fn q2_conditional_loop_keeps_the_loop_boundary() {
        let mut a = LamArena::new();
        let loop_test = a.const_(Constant::JsTrue);
        let loop_body = unit(&mut a);
        let loop_ = a.while_(loop_test, loop_body);
        let one = int(&mut a, 1);
        let (yes, no) = (a.seq_raw(loop_, one), int(&mut a, 2));
        let root = if_(&mut a, 1, yes, no);
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        assert!(matches!(
            state.probe(Cx::returning(), root),
            Err(Unsupported("loop"))
        ));
    }

    #[test]
    fn q5_nested_rec_keeps_the_let_rec_boundary() {
        let mut a = LamArena::new();
        let id = Ident::new("nested", 2, IdentFlags::NONE);
        let body = a.const_(Constant::JsTrue);
        let function = a.function_(0, &[], body, Default::default(), LamLoc::NONE);
        let yes = a.var(id);
        let yes = a.letrec(&[(id, function)], yes);
        let no = a.const_(Constant::JsFalse);
        let root = if_(&mut a, 1, yes, no);
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        assert!(matches!(
            state.probe(Cx::returning(), root),
            Err(Unsupported("let rec"))
        ));
    }

    // Level-J rule tests. The lowering cannot yet produce a constant test,
    // `break` or `continue`; the rules that read them, and every rule of
    // J-S3 on runs, are tested on statements built by hand, against J-S3 on
    // vectors.
    struct Hand {
        state: State,
        vars: [VarId; 4],
        /// The variable `l` declares in the then list and in the else list.
        declared: [VarId; 2],
        side: usize,
    }
    impl Hand {
        fn new() -> Self {
            let mut a = LamArena::new();
            let root = a.const_(Constant::JsNull);
            let mut state = State::new(bridge::import_lambda(&a, root).unwrap());
            let vars = ["c", "d", "x", "y"].map(|name| state.fresh_variable(name));
            let declared = ["m", "n"].map(|name| state.fresh_variable(name));
            Self {
                state,
                vars,
                declared,
                side: 0,
            }
        }
        fn var(&mut self, index: usize) -> NodeId {
            self.state.pure_expression(
                View::Var {
                    var: self.vars[index],
                },
                0,
            )
        }
        fn assign(&mut self, index: usize) -> NodeId {
            let one = crate::bir::j::plain::int(&mut self.state.arena, 1);
            crate::bir::j::assign(&mut self.state.arena, self.vars[index], one)
        }
        /// 0: `c`; 1: `!c`; 2: `true`; 3: `false`; 4: `x = 1` (an effect).
        fn test(&mut self, kind: u8) -> NodeId {
            match kind {
                0 => self.var(0),
                1 => {
                    let value = self.var(0);
                    self.state.arena.new_node(View::JNot { value }, 0)
                }
                2 | 3 => crate::bir::j::plain::boolean(&mut self.state.arena, kind == 2),
                _ => {
                    let (left, right) = (self.var(2), self.var(3));
                    self.state
                        .arena
                        .new_node(View::JBin { left, right }, BinOp::Eq as u16)
                }
            }
        }
        /// r: `return y`; e: `x = 1`; f: `y = 1`; l: `let m = c`; t: `throw x`;
        /// b: `break`; k: `continue`; o: `{}`; i: `if (d) { x = 1 }`;
        /// j: `if (d) { x = 1 } else { y = 1 }`.
        fn statement(&mut self, kind: char) -> NodeId {
            match kind {
                'r' => {
                    let value = self.var(3);
                    crate::bir::j::return_value(&mut self.state.arena, value)
                }
                'e' => self.assign(2),
                'f' => self.assign(3),
                'l' => {
                    let value = self.var(0);
                    let var = self.declared[self.side];
                    crate::bir::j::declare(&mut self.state.arena, LetKind::Strict, var, value)
                }
                't' => {
                    let value = self.var(2);
                    self.state.arena.new_node(View::SThrow { value }, 0)
                }
                'b' => self.state.arena.new_node(View::SBreak { label: None }, 0),
                'k' => self
                    .state
                    .arena
                    .new_node(View::SContinue { label: None }, 0),
                'o' => self.state.empty_block(),
                'i' | 'j' => {
                    let test = self.var(1);
                    let yes = self.assign(2);
                    let yes = self.state.arena.lists.push(&[yes]);
                    let no = if kind == 'j' {
                        vec![self.assign(3)]
                    } else {
                        vec![]
                    };
                    let no = self.state.arena.lists.push(&no);
                    self.state.raw_if(test, yes, no)
                }
                _ => unreachable!(),
            }
        }
        fn list(&mut self, side: usize, kinds: &str) -> Vec<NodeId> {
            self.side = side;
            kinds.chars().map(|kind| self.statement(kind)).collect()
        }
        fn run(&mut self, side: usize, kinds: &str) -> Span {
            self.side = side;
            let mark = self.state.statements.mark();
            for kind in kinds.chars() {
                let statement = self.statement(kind);
                let slot = self.state.statements.mark().start;
                self.state.statements.push(statement);
                if kind == 'o' {
                    self.state.statements.note_empty_block(slot, statement);
                }
            }
            self.state.statements.since(mark)
        }
        fn text(mut self, value: Option<NodeId>) -> String {
            let value = value.unwrap_or_else(|| self.state.pure_expression(View::JUndefined, 0));
            let out = self.state.output(0, Some(value), Finished::False);
            let lowered = self.state.complete(Cx::effect(), Probed::Out(out));
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root), false)
                .unwrap();
            let program = bridge_j::export_js(&lowered.program).unwrap();
            crate::js_ir::print_deps_program_with_directives_and_options(
                &program,
                None,
                &[],
                false,
                false,
                false,
            )
        }
    }

    const LISTS: [&str; 16] = [
        "", "r", "e", "f", "l", "er", "le", "ef", "et", "eb", "ek", "i", "j", "o", "or", "eo",
    ];

    /// J-S3 on vectors: the statement `norm::js3_simplify_if` builds.
    fn reference(test: u8, yes: &str, no: &str) -> String {
        let mut hand = Hand::new();
        let (yes, no) = (hand.list(0, yes), hand.list(1, no));
        let test = hand.test(test);
        let statement = norm::js3_simplify_if(&mut hand.state.arena, test, yes, no);
        hand.state.statements.push(statement);
        hand.text(None)
    }

    #[test]
    fn if_in_place_then_block_is_simplify_if_for_every_rule() {
        for test in 0..5 {
            for yes in LISTS {
                for no in LISTS {
                    for swapped in [false, true] {
                        let mut hand = Hand::new();
                        let head = hand.state.statements.reserve();
                        // A free branch realized late lies above the other.
                        let (yes_run, no_run) = if swapped {
                            let no_run = hand.run(1, no);
                            (hand.run(0, yes), no_run)
                        } else {
                            let yes_run = hand.run(0, yes);
                            (yes_run, hand.run(1, no))
                        };
                        let condition = hand.test(test);
                        hand.state.if_in_place(head, condition, yes_run, no_run);
                        hand.state.block_statement(head);
                        assert_eq!(
                            hand.text(None),
                            reference(test, yes, no),
                            "test {test}, then {yes:?}, else {no:?}, swapped {swapped}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn if_statement_is_simplify_if_for_every_rule() {
        for test in 0..5 {
            for yes in LISTS {
                for no in LISTS {
                    let mut hand = Hand::new();
                    let (yes_run, no_run) = (hand.run(0, yes), hand.run(1, no));
                    let condition = hand.test(test);
                    let statement = hand.state.if_statement(condition, yes_run, no_run);
                    hand.state.statements.push(statement);
                    assert_eq!(
                        hand.text(None),
                        reference(test, yes, no),
                        "test {test}, then {yes:?}, else {no:?}"
                    );
                }
            }
        }
    }

    /// C:4884 compile_if_effect_block steps 4 on two blocks, written with
    /// J-S3 on vectors: the guard is one statement, the other branch follows.
    fn effect_reference(yes: &str, no: &str) -> String {
        let mut hand = Hand::new();
        let (then_, else_) = (hand.list(0, yes), hand.list(1, no));
        let test = hand.test(0);
        let arena = &mut hand.state.arena;
        let statements = if no == "r" {
            let test = norm::je8_not(arena, test);
            let mut statements = vec![norm::js3_simplify_if(arena, test, else_, vec![])];
            statements.extend(then_);
            statements
        } else if yes.ends_with(['r', 't', 'b', 'k']) {
            let mut statements = vec![norm::js3_simplify_if(arena, test, then_, vec![])];
            statements.extend(else_);
            statements
        } else {
            vec![norm::js3_simplify_if(arena, test, then_, else_)]
        };
        for statement in statements {
            hand.state.statements.push(statement);
        }
        hand.text(None)
    }

    fn effect_rule(yes: &str, no: &str) {
        let mut hand = Hand::new();
        let head = hand.state.statements.reserve();
        let branch = |hand: &mut Hand, side: usize, kinds: &str| {
            Probed::Out(Out {
                stmts: hand.run(side, kinds),
                value: None,
                finished: Finished::False,
            })
        };
        let (then_, else_) = (branch(&mut hand, 0, yes), branch(&mut hand, 1, no));
        let test = hand.test(0);
        let parts = Parts { start: 0, head };
        let Probed::Out(out) =
            hand.state
                .effect_conditional(Cx::effect(), parts, test, then_, else_)
        else {
            unreachable!()
        };
        assert_eq!(
            hand.text(out.value),
            effect_reference(yes, no),
            "then {yes:?}, else {no:?}"
        );
    }

    #[test]
    fn r4_step4_else_is_exactly_one_return() {
        for yes in ["le", "er", "et", "lef"] {
            effect_rule(yes, "r");
        }
    }
    #[test]
    fn r4_step4_then_ends_in_return_throw_break_or_continue() {
        for yes in ["er", "et", "eb", "ek", "ler"] {
            for no in ["le", "ef", "er", "lef"] {
                effect_rule(yes, no);
            }
        }
    }
    #[test]
    fn r4_step4_otherwise_one_conditional_statement() {
        for yes in ["le", "ef", "lef"] {
            for no in ["le", "ef", "er"] {
                effect_rule(yes, no);
            }
        }
    }

    // Step counts (section 7.4): 10,000 nested constructs, each L node read
    // once and each statement written and copied a constant number of times.
    fn steps(
        cont: u8,
        nodes: usize,
        build: impl FnOnce(&mut LamArena) -> Lam,
    ) -> (usize, usize, usize) {
        let mut a = LamArena::new();
        let root = build(&mut a);
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let target = state.fresh_variable("result");
        let cx = match cont {
            0 => Cx::value(),
            1 => Cx::assign(target),
            2 => Cx::declare(LetKind::Strict, target),
            3 => Cx::effect(),
            _ => Cx::returning(),
        };
        let probed = state.probe(cx, root).unwrap();
        let out = state.realize(cx, probed);

        assert_eq!(state.source_steps, nodes, "each L node is read once");
        let counts = (
            state.statements.pushed,
            state.statements.copied,
            state.statements.scanned,
        );
        // The validator walks a nested tree once per level: it checks the
        // small inputs, the step counts check the large ones.
        if nodes <= 5_000 {
            let lowered = state.complete(cx, Probed::Out(out));
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root), false)
                .unwrap();
        }
        counts
    }

    const DEPTH: i32 = 10_000;

    /// `if (c1) t else if (c2) t else ... else { let binding = null; -1 }`,
    /// or the same chain through the then branches.
    fn chain(a: &mut LamArena, depth: i32, then_position: bool, statement_arm: bool) -> Lam {
        let mut root = int(a, -1);
        root = bound(a, 1, root);
        for level in 0..depth {
            let mut arm = int(a, level);
            if statement_arm {
                arm = bound(a, depth + 2 + level, arm);
            }
            root = if then_position {
                if_(a, level + 2, root, arm)
            } else {
                if_(a, level + 2, arm, root)
            };
        }
        root
    }

    #[test]
    fn ten_thousand_nested_conditionals_are_linear_in_every_continuation() {
        for levels in [100, DEPTH] {
            let depth = levels as usize;
            for cont in 0..5 {
                for then_position in [false, true] {
                    for statement_arm in [false, true] {
                        let nodes = 3 * depth + 3 + if statement_arm { 2 * depth } else { 0 };
                        let (pushed, copied, scanned) = steps(cont, nodes, |a| {
                            chain(a, levels, then_position, statement_arm)
                        });
                        assert!(pushed <= 5 * depth + 5, "statements written: {pushed}");
                        assert!(copied <= 5 * depth + 5, "statements copied: {copied}");
                        assert!(scanned <= 8 * depth + 8, "slots skipped: {scanned}");
                    }
                }
            }
        }
    }

    #[test]
    fn the_else_chain_of_the_return_regression_is_linear() {
        // If(c1, 1, If(c2, 2, ... Let(Strict, x, null, -1))): the shape whose
        // return continuation copied 50,035,000 statements at this depth
        // when each level rebuilt the list of the levels below it.
        let depth = DEPTH as usize;
        let counts =
            [0, 1, 4].map(|cont| steps(cont, 3 * depth + 3, |a| chain(a, DEPTH, false, false)));
        let [value, assign, returning] = counts;
        // (written, copied to a list, holes and dead ranges skipped)
        assert_eq!(value, (2 * depth + 3, 2 * depth + 1, 0));
        assert_eq!(assign, (2 * depth + 2, 2 * depth + 1, 0));
        assert_eq!(returning, (2 * depth + 2, depth, 2 * depth));
    }

    #[test]
    fn ten_thousand_nested_short_circuits_are_linear_in_every_continuation() {
        for levels in [100, DEPTH] {
            let depth = levels as usize;
            for cont in 0..5 {
                for and in [false, true] {
                    for statement in [false, true] {
                        let nodes = 2 * depth + 1 + if statement { 2 } else { 0 };
                        let (pushed, copied, scanned) = steps(cont, nodes, |a| {
                            let mut root = var(a, "right", 1);
                            if statement {
                                root = bound(a, 2, root);
                            }
                            for level in 0..levels {
                                let left = var(a, "left", level + 3);
                                root = short(a, and, left, root);
                            }
                            root
                        });
                        assert!(pushed <= 4 * depth + 5, "statements written: {pushed}");
                        assert!(copied <= 4 * depth + 5, "statements copied: {copied}");
                        assert!(scanned <= 8 * depth + 8, "slots skipped: {scanned}");
                    }
                }
            }
        }
    }

    #[test]
    fn r5_step0_reads_each_spine_node_once() {
        // 10,000 conditionals in a unit function, each branch a pure
        // sequence spine of two nodes ending in the unit value.
        let mut a = LamArena::new();
        let mut body = unit(&mut a);
        for level in 0..DEPTH {
            let mut arms = [unit(&mut a), unit(&mut a)];
            for arm in &mut arms {
                let pure = int(&mut a, level);
                *arm = a.seq_raw(pure, *arm);
            }
            let conditional = if_(&mut a, level + 1, arms[0], arms[1]);
            body = a.seq_raw(conditional, body);
        }
        let attr = FunctionAttribute {
            return_unit: true,
            ..Default::default()
        };
        let root = a.function_(0, &[], body, attr.clone(), LamLoc::NONE);
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.spine_steps, 0, "an effect continuation has no step 0");
        let mut a = LamArena::new();
        let mut body = unit(&mut a);
        for level in 0..DEPTH {
            let pure = int(&mut a, level);
            body = a.seq_raw(pure, body);
        }
        let other = unit(&mut a);
        let body = if_(&mut a, 1, body, other);
        let root = a.function_(0, &[], body, attr, LamLoc::NONE);
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.spine_steps, DEPTH as usize + 2);
        // Only the test was lowered: the conditional, its test, the function.
        assert_eq!(state.source_steps, 3);
    }

    #[test]
    fn conditional_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<Kind>(), 1);
        assert_eq!(size_of::<Target>(), 8);
        assert_eq!(size_of::<Conditional>(), 24);
        assert_eq!(size_of::<Parts>(), 8);
        assert_eq!(size_of::<Cx>(), 32);
    }
}
