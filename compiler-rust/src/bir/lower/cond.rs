//! Conditional continuation rules (BACKEND_LOWERING section 3.6).
use super::*;
use crate::bir::j::norm;

enum Branch {
    Free(FreeId),
    Statements(Vec<NodeId>, Option<NodeId>, Finished),
}

impl State {
    /// R1, C:1812 compile_expr: expression branches use J-E7; statement
    /// branches assign a Strict result temporary through J-S3.
    pub(super) fn conditional_value(
        &mut self, cx: Cx, condition: NodeId, then_: NodeId, else_: NodeId,
    ) -> Result<Probed, Unsupported> {
        let start = self.statements.mark();
        let value_cx = Cx { cont: Cont::Value(Tail::No), ..cx };
        let condition = self.probe(value_cx, condition)?;
        let condition = self.realize(value_cx, condition).value.expect("condition value");
        let order = self.next_order;
        let yes = self.probe(value_cx, then_)?;
        let yes = self.realize(value_cx, yes);
        let yes_stmts = self.conditional_statements(yes.stmts);
        let no = self.probe(value_cx, else_)?;
        let no = self.realize(value_cx, no);
        let no_stmts = self.conditional_statements(no.stmts);
        let value = if yes_stmts.is_empty() && no_stmts.is_empty() {
            norm::je7_cond(&mut self.arena, condition, yes.value.expect("then value"), no.value.expect("else value"))
        } else {
            for statement in yes_stmts.into_iter().chain(no_stmts) { self.arena.release(statement); }
            if let Some(value) = yes.value { self.arena.release(value); }
            if let Some(value) = no.value { self.arena.release(value); }
            // Only the retained pass contributes to fresh-identifier order.
            self.next_order = order;
            let result = self.fresh_variable("tmp");
            let declaration = self.arena.new_node(View::SDecl { var: result, value: None },
                LetKind::Strict as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2));
            self.statements.push(declaration);
            let assign = Cx { cont: Cont::Assign(result), ..cx };
            let yes = self.probe(assign, then_)?;
            let yes = self.realize(assign, yes);
            let yes = self.conditional_statements(yes.stmts);
            let no = self.probe(assign, else_)?;
            let no = self.realize(assign, no);
            let no = self.conditional_statements(no.stmts);
            let statement = norm::js3_simplify_if(&mut self.arena, condition, yes, no);
            self.statements.push(statement);
            self.pure_expression(View::Var { var: result }, 0)
        };
        let stmts = self.statements.since(start);
        if !self.statements.has_statements(stmts) {
            self.statements.remove_empty(stmts);
            Ok(self.probe_leaf(cx, value))
        } else {
            Ok(Probed::Out(Out { stmts, value: Some(value), finished: Finished::False }))
        }
    }

    /// R2, C:2699 compile_if_binding_block / C:4926 compile_declared_if_block.
    /// Probe directly for assignment: free operands need no discarded value pass.
    pub(super) fn conditional_declaration(
        &mut self, cx: Cx, condition: NodeId, then_: NodeId, else_: NodeId,
    ) -> Result<Probed, Unsupported> {
        let Cont::Declare(kind, target) = cx.cont else { unreachable!() };
        let start = self.statements.mark();
        let value_cx = Cx { cont: Cont::Value(Tail::No), ..cx };
        let condition = self.probe(value_cx, condition)?;
        let condition = self.realize(value_cx, condition).value.expect("condition value");
        let assign = Cx { cont: Cont::Assign(target), ..cx };
        let yes = self.probe(assign, then_)?;
        let yes = self.save_branch(yes);
        let no = self.probe(assign, else_)?;
        let no = self.save_branch(no);
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
                if let (Some(y), Some(n)) = (self.single_assignment(&yes, target), self.single_assignment(&no, target)) {
                    self.arena.detach(y);
                    self.arena.detach(n);
                    self.arena.release(yes[0]);
                    self.arena.release(no[0]);
                    let value = norm::je7_cond(&mut self.arena, condition, y, n);
                    let statement = crate::bir::j::declare(&mut self.arena, kind, target, value);
                    self.statements.push(statement);
                } else {
                    let declaration = self.arena.new_node(View::SDecl { var: target, value: None },
                        kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2));
                    self.statements.push(declaration);
                    let statement = norm::js3_simplify_if(&mut self.arena, condition, yes, no);
                    self.statements.push(statement);
                }
            }
        }
        Ok(Probed::Out(Out { stmts: self.statements.since(start), value: None, finished: Finished::False }))
    }

    fn save_branch(&mut self, branch: Probed) -> Branch {
        match branch {
            Probed::Free(id) => Branch::Free(id),
            Probed::Out(out) => Branch::Statements(self.conditional_statements(out.stmts), out.value, out.finished),
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
                    assert_eq!(finished, Finished::True, "branch already converted to its continuation");
                    self.arena.release(value);
                }
                statements
            }
        }
    }

    /// C:6595 normalize_if_assignment_merge_order, before declaration promotion.
    fn assignment_order(&mut self, condition: NodeId, yes: Vec<NodeId>, no: Vec<NodeId>) -> (NodeId, Vec<NodeId>, Vec<NodeId>) {
        if !no.is_empty() && let View::JNot { value } = self.arena.view(condition) {
            self.arena.detach(value);
            self.arena.release(condition);
            (value, no, yes)
        } else { (condition, yes, no) }
    }

    fn single_assignment(&self, statements: &[NodeId], target: VarId) -> Option<NodeId> {
        let [statement] = statements else { return None };
        let View::SExp { value } = self.arena.view(*statement) else { return None };
        let View::JBin { left, right } = self.arena.view(value) else { return None };
        if self.arena.node(value).aux() == crate::js_ir::BinOp::Eq as u16
            && matches!(self.arena.view(left), View::Var { var } if var == target) { Some(right) } else { None }
    }

    /// R3, C:4873 compile_if_assignment_block and C:4895
    /// compile_test_assignment_block: assignments are lowered once.
    pub(super) fn conditional_assignment(
        &mut self, cx: Cx, condition: NodeId, then_: NodeId, else_: NodeId,
    ) -> Result<Probed, Unsupported> {
        let start = self.statements.mark();
        let value_cx = Cx { cont: Cont::Value(Tail::No), ..cx };
        let condition = self.probe(value_cx, condition)?;
        let condition = self.realize(value_cx, condition).value.expect("condition value");
        let yes = self.probe(cx, then_)?;
        let yes = self.realize(cx, yes);
        let yes = self.conditional_statements(yes.stmts);
        let no = self.probe(cx, else_)?;
        let no = self.realize(cx, no);
        let no = self.conditional_statements(no.stmts);
        // C:6595 normalize_if_assignment_merge_order: J-S3 swaps a negated
        // test before combining two assignments to the same target.
        let statement = norm::js3_simplify_if(&mut self.arena, condition, yes, no);
        self.statements.push(statement);
        Ok(Probed::Out(Out { stmts: self.statements.since(start), value: None, finished: Finished::False }))
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
            yes = source.let_(LetKind::Strict, Ident::new("binding", 2, IdentFlags::NONE), value, yes);
        }
        let no = source.const_(Constant::JsFalse);
        let root = source.if_raw(condition, yes, no);
        let input = bridge::import_lambda(&source, root).unwrap();
        let node = input.root;
        let mut state = State::new(input);
        let target = state.fresh_variable("result");
        let target_id = state.idents[target.index()];
        let cx = match context { 0 => Cx::value(), 1 => Cx::assign(target), 2 => Cx::declare(LetKind::Strict, target), _ => unreachable!() };
        let output = state.probe(cx, node).unwrap();
        let lowered = state.complete(cx, output);
        lowered.program.arena.validate(Some(lowered.program.root), false).unwrap();
        let actual = bridge_j::export_js(&lowered.program).unwrap();
        let mut legacy = LambdaCompiler::new();
        let output = legacy.bir_lower_oracle(&mut source, root, cx.cont, target_id);
        let mut block = output.prelude;
        block.push(legacy.j.stmt(StmtKind::Exp(output.expr)));
        let expected = JsDepsProgram { program: JsProgram::new_in(block, vec![], legacy.j), modules: vec![], side_effect: None };
        let print = |program: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(
            program, None, &[], false, false, false);
        assert_eq!(print(&actual), print(&expected));
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
    fn r1_free_branches_match_legacy() { compare_context(false, 0); }

    #[test]
    fn r1_statement_branch_matches_legacy() { compare_context(true, 0); }
}
