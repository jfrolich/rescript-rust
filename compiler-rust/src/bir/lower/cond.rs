//! Conditional continuation rules (BACKEND_LOWERING section 3.6).
use super::*;
use crate::bir::j::norm;

#[derive(Debug)]
pub(super) enum Branch {
    Free(FreeId),
    Statements(Vec<NodeId>, Option<NodeId>, Finished),
}

pub(super) struct Conditional {
    condition: NodeId,
    then_: NodeId,
    else_: NodeId,
    branch_cx: Cx,
    target: Option<VarId>,
    value_result: bool,
    start: Span,
    data: std::cell::RefCell<ConditionalData>,
}

#[derive(Default)]
struct ConditionalData {
    test: Option<NodeId>,
    branches: Vec<Branch>,
    branch_order: u32,
}

impl State {
    pub(super) fn conditional(
        &mut self,
        cx: Cx,
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
        let target = match cx.cont {
            Cont::Value(_) => Some(self.fresh_variable("tmp")),
            Cont::Declare(_, target) | Cont::Assign(target) => Some(target),
            Cont::Effect(_) => None,
        };
        let cont = target.map_or(cx.cont, Cont::Assign);
        Ok(Conditional {
            condition,
            then_,
            else_,
            branch_cx: Cx { cont, ..cx },
            target,
            value_result: matches!(cx.cont, Cont::Value(_)),
            start: self.statements.mark(),
            data: Default::default(),
        })
    }

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
        let branch_cx = if self.direct && conditional.target.is_some() {
            Cx {
                cont: Cont::Value(Tail::No),
                ..conditional.branch_cx
            }
        } else {
            conditional.branch_cx
        };
        into.push((branch_cx, conditional.then_));
        into.push((branch_cx, conditional.else_));
    }

    pub(super) fn conditional_child(
        &mut self,
        cx: Cx,
        conditional: &Conditional,
        index: usize,
        child: Probed,
    ) -> Probed {
        let mut data = conditional.data.borrow_mut();
        if index == 0 {
            let out = self.realize(cx, child);
            data.test = out.value;
            if conditional.value_result {
                // Reserve the handle before scheduling, but order its name
                // after all identifiers created while evaluating the test.
                let target = conditional.target.unwrap();
                self.arena.vars.order[target.index()] = self.next_order;
                self.next_order += 1;
            }
            data.branch_order = self.next_order;
        } else {
            data.branches.push(self.save_branch(child));
        }
        Probed::Out(Out {
            stmts: self.statements.mark(),
            value: None,
            finished: Finished::Dummy,
        })
    }

    pub(super) fn finish_conditional(&mut self, cx: Cx, conditional: Conditional) -> Probed {
        let mut data = conditional.data.into_inner();
        let mut no = data.branches.pop().unwrap();
        let mut yes = data.branches.pop().unwrap();
        let test = data.test.unwrap();
        let start = conditional.start;
        if self.direct
            && conditional.target.is_some()
            && !(matches!(yes, Branch::Free(_)) && matches!(no, Branch::Free(_)))
        {
            // P1's bounded direct oracle follows the legacy discarded V pass.
            // Production probing never enters this second-lowering path.
            self.discard_branch(yes);
            self.discard_branch(no);
            self.next_order = data.branch_order;
            let output = self
                .probe(conditional.branch_cx, conditional.then_)
                .expect("already supported branch");
            let output = self.realize(conditional.branch_cx, output);
            yes = self.save_branch(Probed::Out(output));
            let output = self
                .probe(conditional.branch_cx, conditional.else_)
                .expect("already supported branch");
            let output = self.realize(conditional.branch_cx, output);
            no = self.save_branch(Probed::Out(output));
        }
        if cx.return_unit
            && matches!(cx.cont, Cont::Effect(Tail::Return(_)))
            && self.trivial_unit(conditional.then_)
            && self.trivial_unit(conditional.else_)
        {
            for branch in [yes, no] {
                match branch {
                    Branch::Free(id) => {
                        let out = self.realize(Cx::value(), Probed::Free(id));
                        if let Some(value) = out.value {
                            self.arena.release(value);
                        }
                    }
                    Branch::Statements(statements, value, _) => {
                        for statement in statements {
                            self.arena.release(statement);
                        }
                        if let Some(value) = value {
                            self.arena.release(value);
                        }
                    }
                }
            }
            let mut statements = Vec::new();
            norm::jm14_push_s_if_empty(&mut self.arena, test, &mut statements);
            for statement in statements {
                self.statements.push(statement);
            }
            return Probed::Out(Out {
                stmts: self.statements.since(start),
                value: None,
                finished: Finished::True,
            });
        }
        match (yes, no) {
            (Branch::Free(yes), Branch::Free(no)) => {
                let free = self.free.push(Free::Cond {
                    test,
                    then_: yes,
                    else_: no,
                });
                let prefix = self.statements.since(start);
                if self.statements.has_statements(prefix) {
                    let out = self.realize(cx, Probed::Free(free));
                    Probed::Out(Out {
                        stmts: self.statements.since(start),
                        ..out
                    })
                } else {
                    self.statements.remove_empty(prefix);
                    Probed::Free(free)
                }
            }
            (yes, no) => match cx.cont {
                Cont::Value(_) => self.finish_value_conditional(
                    cx,
                    start,
                    test,
                    conditional.target.unwrap(),
                    yes,
                    no,
                ),
                Cont::Declare(..) => self.finish_declaration_conditional(cx, start, test, yes, no),
                Cont::Assign(_) => self.finish_assignment_conditional(cx, start, test, yes, no),
                Cont::Effect(Tail::No) => self.finish_effect_conditional(cx, start, test, yes, no),
                Cont::Effect(Tail::Return(_)) => {
                    self.finish_return_conditional(cx, start, test, yes, no)
                }
            },
        }
    }

    pub(super) fn realize_conditional(&mut self, cx: Cx, test: NodeId, yes: Out, no: Out) -> Out {
        let start = self.statements.mark();
        assert!(!self.statements.has_statements(yes.stmts));
        assert!(!self.statements.has_statements(no.stmts));
        let yes = yes.value.unwrap();
        let no = no.value.unwrap();
        match cx.cont {
            Cont::Effect(Tail::No) => {
                for statement in self.free_effect_conditional(test, yes, no) {
                    self.statements.push(statement);
                }
                let Probed::Out(out) = self.effect_output(start) else {
                    unreachable!()
                };
                out
            }
            Cont::Assign(target) => {
                let yes = crate::bir::j::assign(&mut self.arena, target, yes);
                let no = crate::bir::j::assign(&mut self.arena, target, no);
                let statement = norm::js3_simplify_if(&mut self.arena, test, vec![yes], vec![no]);
                self.statements.push(statement);
                Out {
                    stmts: self.statements.since(start),
                    value: None,
                    finished: Finished::False,
                }
            }
            Cont::Value(_) | Cont::Declare(..) | Cont::Effect(Tail::Return(_)) => {
                let value = norm::je7_cond(&mut self.arena, test, yes, no);
                self.leaf(cx, value)
            }
        }
    }

    /// R1, C:1812 compile_expr: the statement branches were probed for A(tmp)
    /// once. Only their retained output is materialized; no branch is re-lowered.
    fn finish_value_conditional(
        &mut self,
        cx: Cx,
        start: Span,
        test: NodeId,
        result: VarId,
        yes: Branch,
        no: Branch,
    ) -> Probed {
        let declaration = self.arena.new_node(
            View::SDecl {
                var: result,
                value: None,
            },
            LetKind::Strict as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
        );
        self.statements.push(declaration);
        let assign = Cx {
            cont: Cont::Assign(result),
            ..cx
        };
        let yes = self.branch_statements(assign, yes);
        let no = self.branch_statements(assign, no);
        let statement = norm::js3_simplify_if(&mut self.arena, test, yes, no);
        self.statements.push(statement);
        let value = self.pure_expression(View::Var { var: result }, 0);
        Probed::Out(Out {
            stmts: self.statements.since(start),
            value: Some(value),
            finished: Finished::False,
        })
    }

    /// R2, C:2699 compile_if_binding_block / C:4926 compile_declared_if_block.
    /// Probe directly for assignment: free operands need no discarded value pass.
    fn finish_declaration_conditional(
        &mut self,
        cx: Cx,
        start: Span,
        condition: NodeId,
        yes: Branch,
        no: Branch,
    ) -> Probed {
        let Cont::Declare(kind, target) = cx.cont else {
            unreachable!()
        };
        let value_cx = Cx {
            cont: Cont::Value(Tail::No),
            ..cx
        };
        let assign = Cx {
            cont: Cont::Assign(target),
            ..cx
        };
        match (yes, no) {
            (Branch::Free(yes), Branch::Free(no)) => {
                let yes = self.realize(value_cx, Probed::Free(yes)).value.unwrap();
                let no = self.realize(value_cx, Probed::Free(no)).value.unwrap();
                let value = norm::je7_cond(&mut self.arena, condition, yes, no);
                let statement = crate::bir::j::declare(&mut self.arena, kind, target, value);
                self.statements.push(statement);
            }
            (yes, no) => {
                let yes = self.branch_statements(assign, yes);
                let no = self.branch_statements(assign, no);
                let (condition, yes, no) = self.assignment_order(condition, yes, no);
                if let (Some(y), Some(n)) = (
                    self.single_assignment(&yes, target),
                    self.single_assignment(&no, target),
                ) {
                    self.arena.detach(y);
                    self.arena.detach(n);
                    self.arena.release(yes[0]);
                    self.arena.release(no[0]);
                    let value = norm::je7_cond(&mut self.arena, condition, y, n);
                    let statement = crate::bir::j::declare(&mut self.arena, kind, target, value);
                    self.statements.push(statement);
                } else {
                    let declaration = self.arena.new_node(
                        View::SDecl {
                            var: target,
                            value: None,
                        },
                        kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
                    );
                    self.statements.push(declaration);
                    let statement = norm::js3_simplify_if(&mut self.arena, condition, yes, no);
                    self.statements.push(statement);
                }
            }
        }
        Probed::Out(Out {
            stmts: self.statements.since(start),
            value: None,
            finished: Finished::False,
        })
    }

    fn discard_branch(&mut self, branch: Branch) {
        match branch {
            Branch::Free(id) => {
                let out = self.realize(Cx::value(), Probed::Free(id));
                if let Some(value) = out.value {
                    self.arena.release(value);
                }
            }
            Branch::Statements(statements, value, _) => {
                for statement in statements {
                    self.arena.release(statement);
                }
                if let Some(value) = value {
                    self.arena.release(value);
                }
            }
        }
    }

    fn save_branch(&mut self, branch: Probed) -> Branch {
        match branch {
            Probed::Free(id) => Branch::Free(id),
            Probed::Out(out) => {
                let statements = self.conditional_statements(out.stmts);
                if statements.is_empty()
                    && out.finished == Finished::False
                    && let Some(value) = out.value
                {
                    Branch::Free(self.free.push(Free::Leaf(value)))
                } else {
                    Branch::Statements(statements, out.value, out.finished)
                }
            }
        }
    }

    fn branch_statements(&mut self, cx: Cx, branch: Branch) -> Vec<NodeId> {
        match branch {
            Branch::Free(id) => {
                let out = self.realize(cx, Probed::Free(id));
                self.conditional_statements(out.stmts)
            }
            Branch::Statements(statements, value, finished) => {
                if let Some(value) = value {
                    assert_eq!(
                        finished,
                        Finished::True,
                        "branch already converted to its continuation"
                    );
                    self.arena.release(value);
                }
                statements
            }
        }
    }

    /// C:6595 normalize_if_assignment_merge_order, before declaration promotion.
    fn assignment_order(
        &mut self,
        condition: NodeId,
        yes: Vec<NodeId>,
        no: Vec<NodeId>,
    ) -> (NodeId, Vec<NodeId>, Vec<NodeId>) {
        if !no.is_empty()
            && let View::JNot { value } = self.arena.view(condition)
        {
            self.arena.detach(value);
            self.arena.release(condition);
            (value, no, yes)
        } else {
            (condition, yes, no)
        }
    }

    fn single_assignment(&self, statements: &[NodeId], target: VarId) -> Option<NodeId> {
        let [statement] = statements else { return None };
        let View::SExp { value } = self.arena.view(*statement) else {
            return None;
        };
        let View::JBin { left, right } = self.arena.view(value) else {
            return None;
        };
        if self.arena.node(value).aux() == crate::js_ir::BinOp::Eq as u16
            && matches!(self.arena.view(left), View::Var { var } if var == target)
        {
            Some(right)
        } else {
            None
        }
    }

    /// R4, C:4761 compile_if_effect_block, in its specified rule order.
    fn finish_effect_conditional(
        &mut self,
        cx: Cx,
        start: Span,
        condition: NodeId,
        yes: Branch,
        no: Branch,
    ) -> Probed {
        let value_cx = Cx {
            cont: Cont::Value(Tail::No),
            ..cx
        };
        let statements = match (yes, no) {
            // Step 1: J-M0 removes pure subexpressions, not every pure value.
            (Branch::Free(yes), Branch::Free(no)) => {
                let yes = self.realize(value_cx, Probed::Free(yes)).value.unwrap();
                let no = self.realize(value_cx, Probed::Free(no)).value.unwrap();
                self.free_effect_conditional(condition, yes, no)
            }
            (yes, no) => {
                let yes = self.effect_operand(value_cx, yes);
                let no = self.effect_operand(value_cx, no);
                if self.pure_free_effect(&yes) {
                    // Step 2: the free then branch contributes no effect.
                    self.release_effect_operand(yes);
                    let no = self.effect_branch(cx, no);
                    let test = norm::je8_not(&mut self.arena, condition);
                    vec![norm::js3_simplify_if(&mut self.arena, test, no, vec![])]
                } else if self.pure_free_effect(&no) {
                    // Step 3: the free else branch contributes no effect.
                    self.release_effect_operand(no);
                    let yes = self.effect_branch(cx, yes);
                    vec![norm::js3_simplify_if(
                        &mut self.arena,
                        condition,
                        yes,
                        vec![],
                    )]
                } else {
                    let mut yes = self.effect_branch(cx, yes);
                    let no = self.effect_branch(cx, no);
                    // Step 4a: a single return in else precedes then.
                    if self.single_return(&no).is_some() {
                        let test = norm::je8_not(&mut self.arena, condition);
                        let statement = norm::js3_simplify_if(&mut self.arena, test, no, vec![]);
                        yes.insert(0, statement);
                        yes
                    } else if self.ends_terminal(&yes) {
                        // Step 4b: terminal then falls through to else.
                        let statement =
                            norm::js3_simplify_if(&mut self.arena, condition, yes, vec![]);
                        let mut statements = vec![statement];
                        statements.extend(no);
                        statements
                    } else {
                        // Step 4c: retain both branches.
                        vec![norm::js3_simplify_if(&mut self.arena, condition, yes, no)]
                    }
                }
            }
        };
        for statement in statements {
            self.statements.push(statement);
        }
        self.effect_output(start)
    }

    fn free_effect_conditional(
        &mut self,
        condition: NodeId,
        yes: NodeId,
        no: NodeId,
    ) -> Vec<NodeId> {
        let yes = norm::jm0_remove_pure_subexpression(&mut self.arena, yes);
        let no = norm::jm0_remove_pure_subexpression(&mut self.arena, no);
        let mut statements = Vec::new();
        match (yes, no) {
            (None, None) => norm::jm14_push_s_if_empty(&mut self.arena, condition, &mut statements),
            (Some(yes), Some(no)) => {
                let value = norm::je7_cond(&mut self.arena, condition, yes, no);
                norm::jm14_push_effect_expression(&mut self.arena, value, &mut statements);
            }
            (Some(value), None) => {
                let statement = norm::js1_exp(&mut self.arena, value);
                statements.push(norm::js3_simplify_if(
                    &mut self.arena,
                    condition,
                    vec![statement],
                    vec![],
                ));
            }
            (None, Some(value)) => {
                let test = norm::je8_not(&mut self.arena, condition);
                let statement = norm::js1_exp(&mut self.arena, value);
                statements.push(norm::js3_simplify_if(
                    &mut self.arena,
                    test,
                    vec![statement],
                    vec![],
                ));
            }
        }
        statements
    }

    fn effect_operand(&mut self, cx: Cx, branch: Branch) -> Branch {
        match branch {
            Branch::Free(id) => {
                let out = self.realize(cx, Probed::Free(id));
                Branch::Statements(vec![], out.value, Finished::Dummy)
            }
            branch => branch,
        }
    }

    fn pure_free_effect(&self, branch: &Branch) -> bool {
        matches!(branch, Branch::Statements(_, Some(value), Finished::Dummy)
            if self.arena.node(*value).flags().contains(crate::bir::NodeFlags::STRICT))
    }

    fn release_effect_operand(&mut self, branch: Branch) {
        let Branch::Statements(statements, Some(value), Finished::Dummy) = branch else {
            unreachable!()
        };
        assert!(statements.is_empty());
        self.arena.release(value);
    }

    fn effect_branch(&mut self, cx: Cx, branch: Branch) -> Vec<NodeId> {
        let branch = self.effect_operand(cx, branch);
        let Branch::Statements(mut statements, value, finished) = branch else {
            unreachable!()
        };
        if let Some(value) = value {
            if finished == Finished::True {
                self.arena.release(value);
            } else {
                norm::jm14_push_effect_expression(&mut self.arena, value, &mut statements);
            }
        }
        norm::js5_unnest_block(&mut self.arena, statements)
    }

    fn single_return(&self, statements: &[NodeId]) -> Option<NodeId> {
        if let [statement] = statements
            && let View::SReturn { value } = self.arena.view(*statement)
        {
            Some(value)
        } else {
            None
        }
    }

    fn ends_terminal(&self, statements: &[NodeId]) -> bool {
        statements.last().is_some_and(|&statement| {
            matches!(
                self.arena.view(statement),
                View::SReturn { .. }
                    | View::SThrow { .. }
                    | View::SBreak { .. }
                    | View::SContinue { .. }
            )
        })
    }

    /// C:7465 compiled_from_effect_block: recover a lone expression, but do
    /// not flatten a multi-statement block across a conditional boundary.
    fn effect_output(&mut self, start: Span) -> Probed {
        let span = self.statements.since(start);
        let statements = self.conditional_statements(span);
        let statements = norm::js5_unnest_block(&mut self.arena, statements);
        let value = if let [statement] = statements.as_slice()
            && let View::SExp { value } = self.arena.view(*statement)
        {
            self.arena.detach(value);
            self.arena.release(*statement);
            value
        } else {
            for statement in statements {
                self.statements.push(statement);
            }
            self.pure_expression(View::JUndefined, 0)
        };
        Probed::Out(Out {
            stmts: self.statements.since(start),
            value: Some(value),
            finished: Finished::False,
        })
    }

    /// R5, C:5144 compile_if_return_output, including both folding stages.
    fn finish_return_conditional(
        &mut self,
        cx: Cx,
        start: Span,
        test: NodeId,
        yes: Branch,
        no: Branch,
    ) -> Probed {
        let value_cx = Cx {
            cont: Cont::Value(Tail::No),
            ..cx
        };
        let finished = match (yes, no) {
            // Step 2: statement-free values need no return-block fallback.
            (Branch::Free(yes), Branch::Free(no)) => {
                let yes = self.realize(value_cx, Probed::Free(yes)).value.unwrap();
                let no = self.realize(value_cx, Probed::Free(no)).value.unwrap();
                let value = norm::je7_cond(&mut self.arena, test, yes, no);
                let statement = crate::bir::j::return_value(&mut self.arena, value);
                self.statements.push(statement);
                Finished::True
            }
            (yes, no) => {
                let yes = self.branch_statements(cx, yes);
                let no = self.branch_statements(cx, no);
                // Step 1, C:5118 try_fold_effect_only_return_tail: retain the
                // comma shape before J-S3 sees the raw return blocks.
                if self.effect_return_tail(&yes) && self.effect_return_tail(&no) {
                    let yes = self.fold_return_tail(yes);
                    let no = self.fold_return_tail(no);
                    let value = norm::je7_cond(&mut self.arena, test, yes, no);
                    let statement = crate::bir::j::return_value(&mut self.arena, value);
                    self.statements.push(statement);
                    Finished::True
                } else {
                    // Step 3, C:5231 compile_test_return_block_with_fallback.
                    let statement = if self.single_return(&yes).is_some()
                        && self.single_return(&no).is_some()
                    {
                        norm::js3_simplify_if(&mut self.arena, test, yes, no)
                    } else if self.single_return(&no).is_some() {
                        let test = norm::je8_not(&mut self.arena, test);
                        let guard = norm::js3_simplify_if(&mut self.arena, test, no, vec![]);
                        let mut statements = vec![guard];
                        statements.extend(yes);
                        // The wrapper hides the terminal tail from an outer If.
                        norm::js2_block(&mut self.arena, statements)
                    } else {
                        norm::js3_simplify_if(&mut self.arena, test, yes, no)
                    };
                    self.statements.push(statement);
                    Finished::False
                }
            }
        };
        // C:3179 compile_return_output applies output_as_block after the rule.
        let span = self.statements.since(start);
        let statements = self.conditional_statements(span);
        for statement in norm::js5_unnest_block(&mut self.arena, statements) {
            self.statements.push(statement);
        }
        Probed::Out(Out {
            stmts: self.statements.since(start),
            value: None,
            finished,
        })
    }

    fn trivial_unit(&self, mut node: NodeId) -> bool {
        loop {
            match self.source.view(node) {
                View::Const { value } => {
                    return matches!(
                        self.arena.constant(value),
                        crate::bir::Constant::Undefined(true)
                    );
                }
                View::Seq { first, second }
                    if self
                        .source
                        .node(first)
                        .flags()
                        .contains(crate::bir::NodeFlags::PURE) =>
                {
                    node = second
                }
                View::Let {
                    value: Some(value),
                    body,
                    ..
                } if self
                    .source
                    .node(value)
                    .flags()
                    .contains(crate::bir::NodeFlags::PURE) =>
                {
                    node = body
                }
                _ => return false,
            }
        }
    }

    fn effect_return_tail(&self, statements: &[NodeId]) -> bool {
        let Some((last, prefix)) = statements.split_last() else {
            return false;
        };
        matches!(self.arena.view(*last), View::SReturn { .. })
            && prefix
                .iter()
                .all(|&statement| matches!(self.arena.view(statement), View::SExp { .. }))
    }

    fn fold_return_tail(&mut self, mut statements: Vec<NodeId>) -> NodeId {
        let last = statements.pop().unwrap();
        let View::SReturn { value: mut result } = self.arena.view(last) else {
            unreachable!()
        };
        self.arena.detach(result);
        self.arena.release(last);
        for statement in statements.into_iter().rev() {
            let View::SExp { value } = self.arena.view(statement) else {
                unreachable!()
            };
            self.arena.detach(value);
            self.arena.release(statement);
            result = norm::jm1_js_seq(&mut self.arena, value, result);
        }
        result
    }

    /// Section 3.7, C:2794 compile_short_circuit_expr, C:2859
    /// compile_short_circuit_binding_block, C:5415 assignment, C:3075 return.
    pub(super) fn short_circuit(
        &mut self,
        cx: Cx,
        and: bool,
        left: NodeId,
        right: NodeId,
    ) -> Result<Probed, Unsupported> {
        if matches!(
            cx.cont,
            Cont::Effect(Tail::Return(Ret::Named { loop_: Some(_), .. }))
                | Cont::Value(Tail::Return(Ret::Named { loop_: Some(_), .. }))
        ) {
            return Err(Unsupported("let rec"));
        }
        let start = self.statements.mark();
        let value_cx = Cx {
            cont: Cont::Value(Tail::No),
            ..cx
        };
        let left = self.probe(value_cx, left)?;
        let left = self.realize(value_cx, left).value.unwrap();
        if matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
            // Call the If rule with a constant branch; never manufacture L.
            let right = self.probe(cx, right)?;
            let right = self.save_branch(right);
            let value = self.pure_expression(View::JBool, u16::from(!and));
            let default = self.probe_leaf(value_cx, value);
            let default = self.save_branch(default);
            let (yes, no) = if and {
                (right, default)
            } else {
                (default, right)
            };
            return Ok(self.finish_return_conditional(cx, start, left, yes, no));
        }
        let right = self.probe(value_cx, right)?;
        let right = self.realize(value_cx, right);
        let mut statements = self.conditional_statements(right.stmts);
        if statements.is_empty() {
            let right = right.value.unwrap();
            let value = if and {
                norm::je5_js_and(&mut self.arena, left, right)
            } else {
                norm::je6_js_or(&mut self.arena, left, right)
            };
            let span = self.statements.since(start);
            if !self.statements.has_statements(span) {
                self.statements.remove_empty(span);
                return Ok(self.probe_leaf(cx, value));
            }
            let out = self.leaf(cx, value);
            return Ok(Probed::Out(Out {
                stmts: self.statements.since(start),
                ..out
            }));
        }
        let target = match cx.cont {
            Cont::Assign(target) | Cont::Declare(_, target) => target,
            Cont::Value(_) | Cont::Effect(_) => self.fresh_variable("tmp"),
        };
        if right.finished != Finished::True {
            let assignment = crate::bir::j::assign(&mut self.arena, target, right.value.unwrap());
            statements.push(assignment);
        } else if let Some(value) = right.value {
            self.arena.release(value);
        }
        let default = self.pure_expression(View::JBool, u16::from(!and));
        let no = if matches!(cx.cont, Cont::Assign(_)) {
            vec![crate::bir::j::assign(&mut self.arena, target, default)]
        } else {
            let kind = if matches!(cx.cont, Cont::Declare(..)) {
                LetKind::Variable
            } else {
                LetKind::Strict
            };
            let declaration = crate::bir::j::declare(&mut self.arena, kind, target, default);
            self.statements.push(declaration);
            vec![]
        };
        let test = if and {
            left
        } else {
            norm::je8_not(&mut self.arena, left)
        };
        let statement = norm::js3_simplify_if(&mut self.arena, test, statements, no);
        self.statements.push(statement);
        let value = match cx.cont {
            Cont::Value(_) | Cont::Effect(_) => {
                Some(self.pure_expression(View::Var { var: target }, 0))
            }
            Cont::Declare(..) | Cont::Assign(_) => None,
        };
        Ok(Probed::Out(Out {
            stmts: self.statements.since(start),
            value,
            finished: Finished::False,
        }))
    }

    /// R3, C:4873 compile_if_assignment_block and C:4895
    /// compile_test_assignment_block: assignments are lowered once.
    fn finish_assignment_conditional(
        &mut self,
        cx: Cx,
        start: Span,
        condition: NodeId,
        yes: Branch,
        no: Branch,
    ) -> Probed {
        let yes = self.branch_statements(cx, yes);
        let no = self.branch_statements(cx, no);
        // C:6595 normalize_if_assignment_merge_order: J-S3 swaps a negated
        // test before combining two assignments to the same target.
        let statement = norm::js3_simplify_if(&mut self.arena, condition, yes, no);
        self.statements.push(statement);
        Probed::Out(Out {
            stmts: self.statements.since(start),
            value: None,
            finished: Finished::False,
        })
    }

    /// K0, C:119: transfer a completed branch off the shared statement stack.
    fn conditional_statements(&mut self, span: Span) -> Vec<NodeId> {
        let list = self.statements.take_list(&mut self.arena, span);
        self.arena.lists.get(list).to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{bridge, bridge_j};
    use crate::ident::IdentFlags;
    use crate::js_ir::arena::{JsDepsProgram, JsProgram, StmtKind};
    use crate::lambda::{arena::LamArena, lam_compile::LambdaCompiler, lam_constant::Constant};

    fn compare_context(statement_branch: bool, context: u8) {
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let mut yes = source.const_(Constant::JsTrue);
        if statement_branch {
            let value = source.const_(Constant::JsNull);
            yes = source.let_(
                LetKind::Strict,
                Ident::new("binding", 2, IdentFlags::NONE),
                value,
                yes,
            );
        }
        let no = source.const_(Constant::JsFalse);
        let root = source.if_raw(condition, yes, no);
        compare_given(source, root, context);
    }

    fn compare_given(mut source: LamArena, root: crate::lambda::arena::Lam, context: u8) {
        let input = bridge::import_lambda(&source, root).unwrap();
        let node = input.root;
        let mut state = State::new(input);
        let target = state.fresh_variable("result");
        let target_id = state.idents[target.index()];
        let cx = match context {
            0 => Cx::value(),
            1 => Cx::assign(target),
            2 => Cx::declare(LetKind::Strict, target),
            3 => Cx::effect(),
            4 => Cx::returning(),
            _ => unreachable!(),
        };
        let output = state.probe(cx, node).unwrap();
        let lowered = state.complete(cx, output);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root), false)
            .unwrap();
        let actual = bridge_j::export_js(&lowered.program).unwrap();
        let mut legacy = LambdaCompiler::new();
        let output = legacy.bir_lower_oracle(&mut source, root, cx.cont, target_id);
        let mut block = output.prelude;
        block.push(legacy.j.stmt(StmtKind::Exp(output.expr)));
        let expected = JsDepsProgram {
            program: JsProgram::new_in(block, vec![], legacy.j),
            modules: vec![],
            side_effect: None,
        };
        let print = |program: &JsDepsProgram| {
            crate::js_ir::print_deps_program_with_directives_and_options(
                program,
                None,
                &[],
                false,
                false,
                false,
            )
        };
        assert_eq!(print(&actual), print(&expected));
    }

    fn effect_case(yes_shape: u8, no_shape: u8) {
        fn branch(source: &mut LamArena, shape: u8, stamp: i32) -> crate::lambda::arena::Lam {
            let mut body = if shape & 1 == 0 {
                source.const_(Constant::JsNull)
            } else {
                let callee = source.var(Ident::new("effect", stamp, IdentFlags::NONE));
                source.apply_raw(
                    callee,
                    &[],
                    crate::lambda::ApInfo {
                        loc: crate::lambda::LamLoc::NONE,
                        status: crate::lambda::ApplyStatus::InferFull,
                    },
                )
            };
            if shape & 2 != 0 {
                let value = source.const_(Constant::JsNull);
                body = source.let_(
                    LetKind::Strict,
                    Ident::new("binding", stamp + 1, IdentFlags::NONE),
                    value,
                    body,
                );
            }
            body
        }
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let yes = branch(&mut source, yes_shape, 10);
        let no = branch(&mut source, no_shape, 20);
        let root = source.if_raw(condition, yes, no);
        compare_given(source, root, 3);
    }

    #[test]
    fn r4_step1_neither_effect() {
        effect_case(0, 0);
    }
    #[test]
    fn r4_step1_both_effects() {
        effect_case(1, 1);
    }
    #[test]
    fn r4_step1_then_effect() {
        effect_case(1, 0);
    }
    #[test]
    fn r4_step1_else_effect() {
        effect_case(0, 1);
    }
    #[test]
    fn r4_step2_free_pure_then() {
        effect_case(0, 3);
    }
    #[test]
    fn r4_step3_free_pure_else() {
        effect_case(3, 0);
    }
    #[test]
    fn r4_step4_nonterminal_branches() {
        effect_case(3, 3);
    }

    fn short_circuit_case(context: u8) {
        for and in [false, true] {
            for statement in [false, true] {
                let mut source = LamArena::new();
                let left = source.var(Ident::new("left", 1, IdentFlags::NONE));
                let mut right = source.var(Ident::new("right", 2, IdentFlags::NONE));
                if statement {
                    let value = source.const_(Constant::JsNull);
                    right = source.let_(
                        LetKind::Strict,
                        Ident::new("binding", 3, IdentFlags::NONE),
                        value,
                        right,
                    );
                }
                let op = if and {
                    crate::lambda::lam_primitive::Primitive::Psequand
                } else {
                    crate::lambda::lam_primitive::Primitive::Psequor
                };
                let root = source.prim_raw(op, &[left, right], crate::lambda::LamLoc::NONE);
                compare_given(source, root, context);
            }
        }
    }

    #[test]
    fn ten_thousand_else_nested_conditionals_have_linear_work() {
        for depth in [100, 10_000] {
            for context in [0, 1, 4] {
                let mut source = LamArena::new();
                let value = source.const_(Constant::JsNull);
                let body = source.const_(Constant::Int {
                    i: -1,
                    comment: None,
                });
                let mut root = source.let_(
                    LetKind::Strict,
                    Ident::new("binding", 1, IdentFlags::NONE),
                    value,
                    body,
                );
                for i in 0..depth {
                    let condition = source.var(Ident::new("condition", i + 2, IdentFlags::NONE));
                    let yes = source.const_(Constant::Int { i, comment: None });
                    root = source.if_raw(condition, yes, root);
                }
                let input = bridge::import_lambda(&source, root).unwrap();
                let root = input.root;
                let mut state = State::new(input);
                let target = state.fresh_variable("result");
                let cx = match context {
                    0 => Cx::value(),
                    1 => Cx::assign(target),
                    4 => Cx::returning(),
                    _ => unreachable!(),
                };
                let probed = state.probe(cx, root).unwrap();
                let out = state.realize(cx, probed);
                eprintln!(
                    "context={context} source={} pushed={} copied={}",
                    state.source_steps, state.statements.pushed, state.statements.copied
                );
                assert_eq!(state.source_steps, (3 * depth + 3) as usize);
                assert!(
                    state.statements.copied <= 20 * state.source_steps,
                    "statement copying must be linear"
                );
                let lowered = state.complete(cx, Probed::Out(out));
                lowered
                    .program
                    .arena
                    .validate(Some(lowered.program.root), false)
                    .unwrap();
            }
        }
    }

    #[test]
    fn nested_conditionals_in_all_oracle_contexts() {
        let mut source = LamArena::new();
        let a = source.var(Ident::new("a", 1, IdentFlags::NONE));
        let b = source.var(Ident::new("b", 2, IdentFlags::NONE));
        let one = source.const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let two = source.const_(Constant::Int {
            i: 2,
            comment: None,
        });
        let three = source.const_(Constant::Int {
            i: 3,
            comment: None,
        });
        let inner = source.if_raw(b, two, three);
        let root = source.if_raw(a, one, inner);
        super::super::oracle_tests::compare(source, root);
    }

    #[test]
    fn conditional_branch_temporaries_preserve_legacy_names() {
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let callee = source.var(Ident::new("callee", 2, IdentFlags::NONE));
        let effect = source.var(Ident::new("effect", 3, IdentFlags::NONE));
        let call_info = crate::lambda::ApInfo {
            loc: crate::lambda::LamLoc::NONE,
            status: crate::lambda::ApplyStatus::InferFull,
        };
        let effect = source.apply_raw(effect, &[], call_info.clone());
        let binding = Ident::new("tmp", 4, IdentFlags::NONE);
        let value = source.const_(Constant::JsNull);
        let use_binding = source.var(binding);
        let binding = source.let_(LetKind::Strict, binding, value, use_binding);
        let yes = source.apply_raw(callee, &[effect, binding], call_info);
        let no = source.const_(Constant::JsFalse);
        let root = source.if_raw(condition, yes, no);
        super::super::oracle_tests::compare(source, root);
    }

    #[test]
    fn q2_conditional_loop_keeps_the_loop_boundary() {
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let loop_test = source.const_(Constant::JsTrue);
        let loop_body = source.const_(Constant::JsUndefined { is_unit: true });
        let loop_ = source.while_(loop_test, loop_body);
        let one = source.const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let yes = source.seq_raw(loop_, one);
        let no = source.const_(Constant::Int {
            i: 2,
            comment: None,
        });
        let root = source.if_raw(condition, yes, no);
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        assert!(matches!(
            state.probe(Cx::returning(), root),
            Err(Unsupported("loop"))
        ));
    }

    #[test]
    fn q5_nested_rec_keeps_the_let_rec_boundary() {
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let id = Ident::new("nested", 2, IdentFlags::NONE);
        let body = source.const_(Constant::JsTrue);
        let function = source.function_(
            0,
            &[],
            body,
            Default::default(),
            crate::lambda::LamLoc::NONE,
        );
        let yes = source.var(id);
        let yes = source.letrec(&[(id, function)], yes);
        let no = source.const_(Constant::JsFalse);
        let root = source.if_raw(condition, yes, no);
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        assert!(matches!(
            state.probe(Cx::returning(), root),
            Err(Unsupported("let rec"))
        ));
    }

    #[test]
    fn short_circuit_value() {
        short_circuit_case(0);
    }
    #[test]
    fn short_circuit_assignment() {
        short_circuit_case(1);
    }
    #[test]
    fn short_circuit_declaration() {
        short_circuit_case(2);
    }
    #[test]
    fn short_circuit_effect() {
        short_circuit_case(3);
    }
    #[test]
    fn short_circuit_return() {
        short_circuit_case(4);
    }

    #[test]
    fn r5_step1_effect_return_tails() {
        let mut source = LamArena::new();
        let condition = source.var(Ident::new("condition", 1, IdentFlags::NONE));
        let mut branches = Vec::new();
        for stamp in [10, 20] {
            let callee = source.var(Ident::new("effect", stamp, IdentFlags::NONE));
            let call = source.apply_raw(
                callee,
                &[],
                crate::lambda::ApInfo {
                    loc: crate::lambda::LamLoc::NONE,
                    status: crate::lambda::ApplyStatus::InferFull,
                },
            );
            let value = source.const_(Constant::JsUndefined { is_unit: true });
            branches.push(source.seq_raw(call, value));
        }
        let root = source.if_raw(condition, branches[0], branches[1]);
        compare_given(source, root, 4);
    }

    #[test]
    fn r5_step0_unit_function() {
        let mut source = LamArena::new();
        let id = Ident::new("condition", 1, IdentFlags::NONE);
        let condition = source.var(id);
        let yes = source.const_(Constant::JsUndefined { is_unit: true });
        let no = source.const_(Constant::JsUndefined { is_unit: true });
        let body = source.if_raw(condition, yes, no);
        let root = source.function_(
            1,
            &[id],
            body,
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            crate::lambda::LamLoc::NONE,
        );
        compare_given(source, root, 0);
    }

    #[test]
    fn r6_tail_loop_remains_explicitly_unsupported() {
        let mut source = LamArena::new();
        let condition = source.const_(Constant::JsTrue);
        let yes = source.const_(Constant::JsTrue);
        let no = source.const_(Constant::JsFalse);
        let root = source.if_raw(condition, yes, no);
        let input = bridge::import_lambda(&source, root).unwrap();
        let node = input.root;
        let mut state = State::new(input);
        let cx = Cx::new(Cont::Effect(Tail::Return(Ret::Named {
            loop_: Some(LoopRef(0)),
            in_catch: false,
        })));
        assert!(matches!(state.probe(cx, node), Err(Unsupported("let rec"))));
    }

    #[test]
    fn r5_returns_match_legacy() {
        compare_context(false, 4);
        compare_context(true, 4);
    }

    #[test]
    fn r4_effects_match_legacy() {
        compare_context(false, 3);
        compare_context(true, 3);
    }

    #[test]
    fn r2_declarations_match_legacy() {
        compare_context(false, 2);
        compare_context(true, 2);
    }

    #[test]
    fn r3_assignments_match_legacy() {
        compare_context(false, 1);
        compare_context(true, 1);
    }

    #[test]
    fn r1_free_branches_match_legacy() {
        compare_context(false, 0);
    }

    #[test]
    fn r1_statement_branch_matches_legacy() {
        compare_context(true, 0);
    }
}
