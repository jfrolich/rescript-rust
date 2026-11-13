//! Variant and switch compilation.
//!
//! Port of `js_of_lam_variant.ml` + variant/switch compilation logic.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{ocaml_typeof_expr, raw_typeof_comparison};
use super::lam_coercion::push_s_if_empty;
use super::lam_compile::{
    Compiled, LambdaCompiler, OutputFinished, StrSw, Sw, TailLoopState, return_case_needs_break,
};
use crate::ident::Ident;
use crate::js_ir::arena::{
    Block, Clause, Expr, ExprKind, JsArena, Stmt, StmtKind, StringClauseInfo, VarDecl,
};
use crate::js_ir::build::{exp as JE, expression_has_no_side_effects, stmt as JS};
use crate::js_ir::op::{IdentInfo, Number};
use crate::js_ir::{BinOp, CallInfo};
use crate::lambda::arena::{Lam, LamArena, SwitchPayload, View};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::untagged_dispatch::{
    Clause as UntaggedClause, Plan, Test as UntaggedTest, TestId, Tree, TreeId,
};
use crate::lambda::{SwitchCaseTag, SwitchDispatch, SwitchKey};

#[derive(Clone, Copy)]
pub(crate) enum UntaggedMode<'r> {
    Assign(&'r Ident),
    Return,
    TailLoopReturn,
    Effect,
}
pub(crate) struct UntaggedEmit<'m, 'e> {
    mode: UntaggedMode<'m>,
    scrut: Expr,
    fallback: Option<Lam>,
    plan: &'e Plan<Lam>,
    fallback_blocks: Vec<(bool, Block)>,
}
type TailLoop<'t> = Option<&'t mut TailLoopState>;

fn block_last_is_return_throw_or_continue(j: &JsArena, block: &[Stmt]) -> bool {
    matches!(
        block.last().map(|stmt| j.sk(*stmt)),
        Some(StmtKind::Return(_) | StmtKind::Throw(_) | StmtKind::Continue(_) | StmtKind::Break(_))
    )
}

pub(crate) fn empty_switch_case_clause() -> Clause {
    Clause {
        source_loc: None,
        body: crate::js_ir::arena::StmtList::EMPTY,
        should_break: false,
        comment: None,
    }
}

fn named_payload_switch(
    payload: &SwitchPayload,
    const_keys: &[SwitchKey],
    block_keys: &[SwitchKey],
) -> bool {
    matches!(payload.dispatch, SwitchDispatch::Variant(_))
        && !untagged_switch(
            &payload.dispatch,
            payload.consts_full,
            const_keys.iter(),
            payload.blocks_full,
            block_keys.iter(),
        )
}

/// lambda.ml `untagged_plan`'s precondition: a switch on an untagged
/// variant (one with payload kinds) whose dispatch is not on literals
/// only, with literal constants and untagged payload cases.
fn untagged_switch<'k>(
    dispatch: &SwitchDispatch,
    consts_full: bool,
    mut const_keys: impl ExactSizeIterator<Item = &'k SwitchKey>,
    blocks_full: bool,
    mut block_keys: impl ExactSizeIterator<Item = &'k SwitchKey>,
) -> bool {
    let SwitchDispatch::Variant(facts) = dispatch else {
        return false;
    };
    !facts.block_types.is_empty()
        && ((consts_full && const_keys.len() == 0) || !(blocks_full && block_keys.len() == 0))
        && const_keys.all(|key| {
            matches!(
                key,
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(_))
            )
        })
        && block_keys.all(|key| {
            matches!(
                key,
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Untagged { .. }
                ))
            )
        })
}

/// A switch node decoded for compilation: its keys paired with their
/// actions. Owned, so the arena can be borrowed mutably while cases compile.
pub(crate) struct LamSwitch {
    pub(crate) sw_consts_full: bool,
    pub(crate) sw_consts: Vec<(SwitchKey, Lam)>,
    pub(crate) sw_blocks_full: bool,
    pub(crate) sw_blocks: Vec<(SwitchKey, Lam)>,
    pub(crate) sw_failaction: Option<Lam>,
    pub(crate) sw_dispatch: SwitchDispatch,
}

impl LamSwitch {
    fn is_named(&self) -> bool {
        matches!(self.sw_dispatch, SwitchDispatch::Variant(_))
            && !untagged_switch(
                &self.sw_dispatch,
                self.sw_consts_full,
                self.sw_consts.iter().map(|(key, _)| key),
                self.sw_blocks_full,
                self.sw_blocks.iter().map(|(key, _)| key),
            )
    }
}

impl Sw {
    pub(crate) fn decode(self, a: &LamArena) -> LamSwitch {
        let p = self.payload(a);
        LamSwitch {
            sw_consts_full: p.consts_full,
            sw_consts: self.consts(a),
            sw_blocks_full: p.blocks_full,
            sw_blocks: self.blocks(a),
            sw_failaction: self.fail(a),
            sw_dispatch: p.dispatch.clone(),
        }
    }
}

/// Whether a named-variant switch reuses its scrutinee across const and
/// block dispatch, so it must be bound to a temporary first.
fn named_variant_keys_need_bound_scrutinee<'k>(
    mut consts: impl ExactSizeIterator<Item = &'k SwitchKey>,
    mut blocks: impl ExactSizeIterator<Item = &'k SwitchKey>,
    consts_full: bool,
    blocks_full: bool,
) -> bool {
    // Same as `named_const_cases`/`named_block_cases` being `Some` and
    // non-empty, without building the case vectors.
    let has_const_cases = consts.len() != 0
        && consts.all(|key| {
            matches!(
                key,
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(_))
            )
        });
    let has_block_cases = blocks.len() != 0
        && blocks.all(|key| {
            matches!(
                key,
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(_))
            )
        });

    match (has_const_cases, has_block_cases) {
        // OCaml only forces a temp here when the backend needs to reuse the
        // scrutinee across both const and payload dispatch.
        (true, true) => true,
        // OCaml `compiler/core/lam_compile.ml:715-765` only bypasses the
        // const/block dispatch when the corresponding switch side is
        // saturated (`sw_*_full`) and empty. A missing failaction still
        // goes through `is_a_literal_case`, which reuses the scrutinee.
        (true, false) => !blocks_full,
        (false, true) => !consts_full,
        (false, false) => false,
    }
}

pub(crate) fn stable_group_switch_cases<T, F>(
    a: &LamArena,
    filtered: Vec<(T, Lam)>,
    merge_cases: F,
) -> Vec<(T, Lam, bool)>
where
    F: Fn(&T, &T) -> bool,
{
    let mut groups: Vec<Vec<(T, Lam)>> = Vec::new();

    // OCaml's Ext_list.stable_group walks from the tail and inserts each case
    // into the first matching group so equal bodies can be coalesced even when
    // they are separated by a different branch.
    for (tag, lam) in filtered.into_iter().rev() {
        // Groups are built in reverse; `last()` is the group's head.
        let matching = groups.iter_mut().find(|group| {
            group.last().is_some_and(|(head_tag, head_lam)| {
                merge_cases(&tag, head_tag) && a.eq_approx(lam, *head_lam)
            })
        });
        match matching {
            Some(group) => group.push((tag, lam)),
            None => groups.push(vec![(tag, lam)]),
        }
    }

    groups.reverse();

    let mut grouped = Vec::with_capacity(groups.iter().map(Vec::len).sum());
    for group in groups {
        let last_idx = group.len().saturating_sub(1);
        for (idx, (tag, lam)) in group.into_iter().rev().enumerate() {
            grouped.push((tag, lam, idx == last_idx));
        }
    }

    grouped
}

impl LambdaCompiler {
    fn class_constructor(&mut self, name: &str) -> Expr {
        let mut parts = name.split('.');
        let global = parts.next().expect("class path has global");
        let mut expr = JE::var(Ident::create_persistent(global), &mut self.j);
        for property in parts {
            expr = self.static_index(expr, property);
        }
        expr
    }

    fn is_instance_of(&mut self, instance: &crate::types::VariantInstance, expr: Expr) -> Expr {
        match instance {
            crate::types::VariantInstance::Array(_) => {
                let array = JE::var(Ident::create_persistent("Array"), &mut self.j);
                let callee = self.static_index(array, "isArray");
                JE::call(callee, &[expr], CallInfo::default(), &mut self.j)
            }
            crate::types::VariantInstance::Class { name, .. } => {
                let class = self.class_constructor(name);
                JE::bin(BinOp::InstanceOf, expr, class, &mut self.j)
            }
        }
    }

    fn is_int_tag(&mut self, literal_tags: &[crate::types::VariantLiteralTag], expr: Expr) -> Expr {
        use crate::types::VariantLiteralTag as L;
        let has_null = literal_tags.iter().any(|tag| matches!(tag, L::Null));
        let has_undefined = literal_tags.iter().any(|tag| matches!(tag, L::Undefined));
        let has_other = literal_tags
            .iter()
            .any(|tag| !matches!(tag, L::Null | L::Undefined));
        let is_null = |j: &mut JsArena| {
            let null = JE::null(j);
            JE::bin(BinOp::EqEqEq, expr, null, j)
        };
        let is_undefined = |j: &mut JsArena| {
            let undef = JE::undefined(false, j);
            JE::bin(BinOp::EqEqEq, expr, undef, j)
        };
        let not_object = |j: &mut JsArena| raw_typeof_comparison(expr, BinOp::NotEqEq, "object", j);
        match (has_null, has_undefined, has_other) {
            (true, false, false) => is_null(&mut self.j),
            (true, true, false) => {
                let l = is_null(&mut self.j);
                let r = is_undefined(&mut self.j);
                JE::bin(BinOp::Or, l, r, &mut self.j)
            }
            (false, true, false) => is_undefined(&mut self.j),
            (true, _, true) => {
                let l = is_null(&mut self.j);
                let r = not_object(&mut self.j);
                JE::bin(BinOp::Or, l, r, &mut self.j)
            }
            (false, _, _) => not_object(&mut self.j),
        }
    }

    fn untagged_typeof_expr(
        &mut self,
        scrut: Expr,
        block_type: &crate::types::VariantBlockType,
    ) -> Expr {
        raw_typeof_comparison(
            scrut,
            BinOp::EqEqEq,
            block_type.typeof_name().expect("typeof test kind"),
            &mut self.j,
        )
    }

    fn untagged_test_expr(&mut self, plan: &Plan<Lam>, scrut: Expr, test: TestId) -> Expr {
        match plan.test(test) {
            UntaggedTest::Equals(literal) => {
                let value = self.switch_case_expr(&Self::literal_tag_value(&plan.metadata.owned_literal(*literal)));
                JE::bin(BinOp::EqEqEq, scrut, value, &mut self.j)
            }
            UntaggedTest::Typeof(kind) => self.untagged_typeof_expr(scrut, &kind.block_type()),
            UntaggedTest::Instance(instance) => self.is_instance_of(&plan.metadata.owned_instance(*instance), scrut),
            UntaggedTest::NotNull => {
                let test = self.is_null_expr(scrut);
                JE::not(test, &mut self.j)
            }
            UntaggedTest::Not(test) => {
                let test = self.untagged_test_expr(plan, scrut, *test);
                JE::not(test, &mut self.j)
            }
            UntaggedTest::And(l, r) | UntaggedTest::Or(l, r) => {
                let op = if matches!(plan.test(test), UntaggedTest::And(..)) {
                    BinOp::And
                } else {
                    BinOp::Or
                };
                let l = self.untagged_test_expr(plan, scrut, *l);
                let r = self.untagged_test_expr(plan, scrut, *r);
                JE::bin(op, l, r, &mut self.j)
            }
        }
    }

    fn untagged_if(
        &mut self,
        mode: UntaggedMode<'_>,
        cond: Expr,
        then_: Block,
        else_: Block,
    ) -> Block {
        match mode {
            UntaggedMode::Return | UntaggedMode::TailLoopReturn => {
                self.normalized_if_block(cond, then_, else_)
            }
            UntaggedMode::Assign(_) | UntaggedMode::Effect => {
                vec![JS::if_(cond, &then_, &else_, &mut self.j)]
            }
        }
    }

    fn emit_untagged_tree(
        &mut self,
        a: &mut LamArena,
        emit: &mut UntaggedEmit<'_, '_>,
        tail_loop: &mut TailLoop<'_>,
        tree: TreeId,
    ) -> Block {
        let plan = emit.plan;
        match plan.tree(tree) {
            Tree::Run(lam) => self.untagged_output_block(a, emit.mode, tail_loop, *lam),
            Tree::Fallback => self.untagged_fallback_block(a, emit, tail_loop),
            Tree::Skip => vec![],
            Tree::If(test, then_, else_) => {
                let then_ = self.emit_untagged_tree(a, emit, tail_loop, *then_);
                let else_ = self.emit_untagged_tree(a, emit, tail_loop, *else_);
                let cond = self.untagged_test_expr(plan, emit.scrut, *test);
                self.untagged_if(emit.mode, cond, then_, else_)
            }
            Tree::Block(inner) => {
                let block = self.emit_untagged_tree(a, emit, tail_loop, *inner);
                vec![JS::block(&block, &mut self.j)]
            }
            Tree::SwitchValue(clauses, default) => self.with_switch_depth(|this| {
                let default = this.emit_untagged_tree(a, emit, tail_loop, *default);
                let default = (!default.is_empty()).then(|| this.j.stmt_list(&default));
                let clauses = plan
                    .value_clauses(*clauses)
                    .iter()
                    .map(|(literal, clause)| StringClauseInfo {
                        tag_type: Self::literal_tag_value(&plan.metadata.owned_literal(*literal)),
                        clause: this.emit_untagged_clause(a, emit, tail_loop, clause),
                    })
                    .collect();
                vec![JS::string_switch(emit.scrut, clauses, default, &mut this.j)]
            }),
            Tree::SwitchTypeof(clauses, default)
                if clauses.len() == 1
                    && matches!(plan.typeof_clauses(*clauses)[0].1, UntaggedClause::Body(_)) =>
            {
                let (kind, clause) = &plan.typeof_clauses(*clauses)[0];
                let clause = self.emit_untagged_clause(a, emit, tail_loop, clause);
                let default = self.emit_untagged_tree(a, emit, tail_loop, *default);
                let cond = self.untagged_typeof_expr(emit.scrut, &kind.block_type());
                self.untagged_if(emit.mode, cond, self.j.block_vec(clause.body), default)
            }
            Tree::SwitchTypeof(clauses, default) => self.with_switch_depth(|this| {
                let default = this.emit_untagged_tree(a, emit, tail_loop, *default);
                let clauses = plan
                    .typeof_clauses(*clauses)
                    .iter()
                    .map(|(kind, clause)| StringClauseInfo {
                        tag_type: SwitchCaseTag::String(
                            kind.typeof_name().expect("typeof switch kind").to_string(),
                        ),
                        clause: this.emit_untagged_clause(a, emit, tail_loop, clause),
                    })
                    .collect();
                let expr = ocaml_typeof_expr(emit.scrut, &mut this.j);
                let default = this.j.stmt_list(&default);
                vec![JS::string_switch(expr, clauses, Some(default), &mut this.j)]
            }),
        }
    }

    fn emit_untagged_clause(
        &mut self,
        a: &mut LamArena,
        emit: &mut UntaggedEmit<'_, '_>,
        tail_loop: &mut TailLoop<'_>,
        clause: &UntaggedClause<Lam>,
    ) -> Clause {
        let body = match clause {
            UntaggedClause::FallsThrough(lam) => {
                return Clause {
                    source_loc: lam.and_then(|lam| self.source_loc_of_lam(a, lam)),
                    ..empty_switch_case_clause()
                };
            }
            UntaggedClause::Body(body) => emit.plan.tree(*body),
        };
        match body {
            Tree::Run(lam) => {
                let lam = *lam;
                let (body, should_break) = match emit.mode {
                    UntaggedMode::Assign(result) => {
                        let output = self.compile_assign_to_target_output(a, result, lam);
                        (output.block, output.finished != OutputFinished::True)
                    }
                    UntaggedMode::Return => {
                        let output = self.compile_return_output(a, lam);
                        (
                            output.block,
                            return_case_needs_break(a, lam, output.finished),
                        )
                    }
                    UntaggedMode::TailLoopReturn => {
                        let output = self.compile_tail_loop_return_output(
                            a,
                            lam,
                            tail_loop.as_deref_mut().expect("tail loop"),
                        );
                        (
                            output.block,
                            return_case_needs_break(a, lam, output.finished),
                        )
                    }
                    UntaggedMode::Effect => {
                        let output = self.compile_effect_block_output(a, lam);
                        (output.block, output.finished != OutputFinished::True)
                    }
                };
                let body = self.with_block_source_loc(a, lam, body);
                Clause {
                    source_loc: self.source_loc_of_lam(a, lam),
                    body: self.j.stmt_list(&body),
                    should_break,
                    comment: None,
                }
            }
            Tree::Fallback => {
                let block = self.untagged_fallback_block(a, emit, tail_loop);
                Clause {
                    should_break: !block_last_is_return_throw_or_continue(&self.j, &block),
                    body: self.j.stmt_list(&block),
                    source_loc: None,
                    comment: None,
                }
            }
            _ => unreachable!("clause body is Run or Fallback"),
        }
    }

    pub(crate) fn compile_switch(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Compiled {
        // Named dispatch enters the switch context only in its general
        // switch arm, not the small conditional arms (compiler/core/lam_compile.ml:793).
        // An untagged plan enters the switch context only for the bodies of
        // its `switch` statements (lam_compile.ml `compile_untagged_plan`).
        if let Some(plan) = sw.untagged_plan(a) {
            // lam_compile.ml: the `NeedValue` temp is made before the
            // scrutinee is compiled.
            let tmp = self.fresh_tmp_ident();
            let mut prelude = vec![JS::define(tmp, None, LetKind::Strict, &mut self.j)];
            prelude.extend(self.compile_untagged_switch(
                a,
                UntaggedMode::Assign(&tmp),
                None,
                scrut,
                sw,
                &plan,
            ));
            return Compiled {
                prelude,
                expr: JE::var(tmp, &mut self.j),
                finished: OutputFinished::False,
            };
        }
        let switch = &sw.decode(a);
        if switch.is_named() {
            self.compile_switch_inner(a, scrut, switch)
        } else {
            self.with_switch_depth(|this| this.compile_switch_inner(a, scrut, switch))
        }
    }

    fn untagged_fallback_block(
        &mut self,
        a: &mut LamArena,
        emit: &mut UntaggedEmit<'_, '_>,
        tail_loop: &mut TailLoop<'_>,
    ) -> Block {
        let in_switch = self.switch_depth > 0;
        if let Some((_, block)) = emit
            .fallback_blocks
            .iter()
            .find(|(key, _)| *key == in_switch)
        {
            return block.clone();
        }
        let lam = emit
            .fallback
            .expect("a plan reaches the fallback only when the switch has one");
        let block = self.untagged_output_block(a, emit.mode, tail_loop, lam);
        emit.fallback_blocks.push((in_switch, block.clone()));
        block
    }

    /// `compile_lambda cxt lam |> Js_output.output_as_block |>
    /// with_block_source_loc lam` in the continuation of `mode`.
    fn untagged_output_block(
        &mut self,
        a: &mut LamArena,
        mode: UntaggedMode<'_>,
        tail_loop: &mut TailLoop<'_>,
        lam: Lam,
    ) -> Block {
        let block = match mode {
            UntaggedMode::Assign(result) => self.compile_assign_to_target_block(a, result, lam),
            UntaggedMode::Return => self.compile_return_block(a, lam),
            UntaggedMode::TailLoopReturn => self.compile_tail_loop_return_block(
                a,
                lam,
                tail_loop.as_deref_mut().expect("a tail loop"),
            ),
            UntaggedMode::Effect => self.compile_effect_block(a, lam),
        };
        self.with_block_source_loc(a, lam, block)
    }

    /// lam_compile.ml `compile_untagged_plan`: prints the plan, each node one
    /// statement. A body in a `switch` statement is compiled in a `switch`
    /// context, a body of an `if` is not.
    pub(crate) fn compile_untagged_plan(
        &mut self,
        a: &mut LamArena,
        mode: UntaggedMode<'_>,
        tail_loop: &mut TailLoop<'_>,
        scrut: Expr,
        fallback: Option<Lam>,
        plan: &Plan<Lam>,
    ) -> Block {
        // The default action is compiled once and shared by every path to it,
        // per whether it is printed inside a `switch`.
        let mut emit = UntaggedEmit {
            mode,
            scrut,
            fallback,
            plan,
            fallback_blocks: Vec::new(),
        };
        self.emit_untagged_tree(a, &mut emit, tail_loop, plan.root())
    }

    /// lam_compile.ml `compile_switch`, the `Lambda.untagged_plan sw =
    /// Some plan` branch: compile the scrutinee in the outer context, bind it
    /// to a variable unless only payloads are dispatched, and print the plan.
    pub(crate) fn compile_untagged_switch(
        &mut self,
        a: &mut LamArena,
        mode: UntaggedMode<'_>,
        mut tail_loop: TailLoop<'_>,
        scrut: Lam,
        sw: Sw,
        plan: &Plan<Lam>,
    ) -> Block {
        let payload = sw.payload(a);
        let payload_only = payload.consts_full && payload.n_consts() == 0;
        let fallback = sw.fail(a);
        let scrut_compiled = self.compile_expr(a, scrut);
        let (mut block, scrut_expr) = if payload_only {
            (scrut_compiled.prelude, scrut_compiled.expr)
        } else {
            self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
        };
        block.extend(self.compile_untagged_plan(
            a,
            mode,
            &mut tail_loop,
            scrut_expr,
            fallback,
            plan,
        ));
        block
    }

    fn switch_literal_tags<'a>(
        &self,
        switch: &'a LamSwitch,
    ) -> &'a [crate::types::VariantLiteralTag] {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => &facts.literal_tags,
            SwitchDispatch::Direct => &[],
        }
    }

    fn compile_switch_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        switch: &LamSwitch,
    ) -> Compiled {
        // OCaml reference: compiler/core/lam_compile.ml:775-786 creates the
        // NeedValue result temp before `compile_whole`, and `compile_whole`
        // compiles the switch scrutinee at lam_compile.ml:707-713. Keep the
        // allocation order and statement order identical so any scrutinee temps
        // get later names and the result declaration precedes scrutinee prelude.
        let tmp = self.fresh_tmp_ident();
        let tmp_declaration = |j: &mut JsArena| JS::define(tmp, None, LetKind::Strict, j);

        if switch.is_named() {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (scrut_prelude, scrut_expr) = if Self::decoded_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let mut prelude = vec![tmp_declaration(&mut self.j)];
            prelude.extend(scrut_prelude);
            prelude.extend(
                self.compile_named_variant_switch_assignment_statements(
                    a, &tmp, scrut_expr, switch,
                ),
            );

            return Compiled {
                prelude,
                expr: JE::var(tmp, &mut self.j),
                finished: OutputFinished::False,
            };
        }

        let scrut_compiled = self.compile_expr(a, scrut);
        let mut prelude = vec![tmp_declaration(&mut self.j)];
        prelude.extend(scrut_compiled.prelude);

        let cases: Vec<_> = self
            .grouped_switch_cases(a, &switch.sw_consts, switch.sw_failaction, |_, _| true)
            .into_iter()
            .map(|(key, body, is_last)| {
                (
                    match key {
                        SwitchKey::Int(value) => value,
                        SwitchKey::Constructor(_) => {
                            unreachable!("constructor with direct dispatch")
                        }
                    },
                    if is_last {
                        crate::js_ir::arena::Clause {
                            source_loc: self.source_loc_of_lam(a, body),
                            body: {
                                let body = {
                                    let value_block =
                                        self.compile_switch_value_block(a, &tmp, body);
                                    self.with_block_source_loc(a, body, value_block)
                                };
                                JS::list(&body, &mut self.j)
                            },
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        self.empty_switch_case_clause_for(a, body)
                    },
                )
            })
            .collect();

        // OCaml `compile_general_cases` only calls `Js_output.to_break_block`
        // for grouped cases (compiler/core/lam_compile.ml:610-624). The
        // switch default is `Js_output.output_as_block`
        // (compiler/core/lam_compile.ml:595-605), so it must not get the
        // case-only trailing `break`.
        let default_block = switch.sw_failaction.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, &tmp, fallback);
            self.with_block_source_loc(a, fallback, block)
        });

        prelude.push(JS::int_switch(
            scrut_compiled.expr,
            cases,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));

        Compiled {
            prelude,
            expr: JE::var(tmp, &mut self.j),
            finished: OutputFinished::False,
        }
    }

    pub(crate) fn compile_string_switch(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
    ) -> Compiled {
        let cases = sw.cases(a);
        let default = sw.default(a);
        self.with_switch_depth(|this| this.compile_string_switch_inner(a, scrut, &cases, default))
    }

    fn compile_string_switch_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        cases: &[(String, Lam)],
        default: Option<Lam>,
    ) -> Compiled {
        let scrut_compiled = self.compile_expr(a, scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_tmp_ident();
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), *body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_assignment(
            a,
            &tmp,
            scrut_compiled.expr,
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            // OCaml's `Lam_pass_exits.simplify_exits` inlines one-use static
            // catches before JS lowering (compiler/core/lam_pass_exits.ml:159-169).
            // The resulting small string switch reaches `Js_stmt_make.if_`,
            // which folds same-target branch assignments into one conditional
            // assignment (compiler/core/js_stmt_make.ml:251-286). When that is
            // the whole body, print the fresh NeedValue temp as `let tmp = ...`
            // instead of `let tmp; tmp = ...`.
            match self.take_single_result_assignment(&tmp, small) {
                Ok(expr) => prelude.push(JS::variable(
                    VarDecl {
                        ident: tmp,
                        value: Some(expr),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )),
                Err(block) => {
                    prelude.push(JS::variable(
                        VarDecl {
                            ident: tmp,
                            value: None,
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    ));
                    prelude.extend(block);
                }
            }
            return Compiled {
                prelude,
                expr: JE::var(tmp, &mut self.j),
                finished: OutputFinished::False,
            };
        }

        prelude.push(JS::variable(
            VarDecl {
                ident: tmp,
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));

        // compiler/core/lam_compile.ml:794-799 lowers the default first.
        // OCaml `compile_general_cases` only calls `Js_output.to_break_block`
        // for grouped cases (compiler/core/lam_compile.ml:610-624). The
        // switch default is `Js_output.output_as_block`
        // (compiler/core/lam_compile.ml:595-605), so it must not get the
        // case-only trailing `break`.
        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, &tmp, fallback);
            self.with_block_source_loc(a, fallback, block)
        });

        let clauses: Vec<_> = self
            .grouped_switch_cases(a, cases, default, |_, _| true)
            .into_iter()
            .map(
                |(tag, body, is_last)| crate::js_ir::arena::StringClauseInfo {
                    tag_type: SwitchCaseTag::String(tag),
                    clause: if is_last {
                        crate::js_ir::arena::Clause {
                            source_loc: self.source_loc_of_lam(a, body),
                            body: {
                                let body = {
                                    let value_block =
                                        self.compile_switch_value_block(a, &tmp, body);
                                    self.with_block_source_loc(a, body, value_block)
                                };
                                JS::list(&body, &mut self.j)
                            },
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        self.empty_switch_case_clause_for(a, body)
                    },
                },
            )
            .collect();

        prelude.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));

        Compiled {
            prelude,
            expr: JE::var(tmp, &mut self.j),
            finished: OutputFinished::False,
        }
    }

    pub(crate) fn uses_named_variant_switch(&self, a: &LamArena, sw: Sw) -> bool {
        named_payload_switch(
            sw.payload(a),
            a.switch_const_keys(sw.info),
            a.switch_block_keys(sw.info),
        )
    }

    fn literal_tag_value(tag: &crate::types::VariantLiteralTag) -> SwitchCaseTag {
        match tag {
            crate::types::VariantLiteralTag::String(value) => SwitchCaseTag::String(value.clone()),
            crate::types::VariantLiteralTag::Int(value) => {
                SwitchCaseTag::Int(i64::from(*value as i32))
            }
            crate::types::VariantLiteralTag::Float(value) => SwitchCaseTag::Float(value.clone()),
            crate::types::VariantLiteralTag::BigInt(value) => SwitchCaseTag::BigInt(value.clone()),
            crate::types::VariantLiteralTag::Bool(value) => SwitchCaseTag::Bool(*value),
            crate::types::VariantLiteralTag::Null => SwitchCaseTag::Null,
            crate::types::VariantLiteralTag::Undefined => SwitchCaseTag::Undefined,
        }
    }

    fn switch_tag_value(tag: &crate::types::VariantTag) -> SwitchCaseTag {
        Self::literal_tag_value(&tag.literal)
    }

    fn named_const_cases(&self, switch: &LamSwitch) -> Option<Vec<(SwitchCaseTag, Lam)>> {
        switch
            .sw_consts
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(tag)) => {
                    Some((Self::switch_tag_value(tag), *body))
                }
                SwitchKey::Int(_) | SwitchKey::Constructor(_) => None,
            })
            .collect()
    }

    fn named_block_cases(&self, switch: &LamSwitch) -> Option<Vec<(SwitchCaseTag, Lam)>> {
        switch
            .sw_blocks
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(block)) => {
                    Some((Self::switch_tag_value(block.tag()), *body))
                }
                SwitchKey::Int(_) | SwitchKey::Constructor(_) => None,
            })
            .collect()
    }

    fn const_switch_default(&self, switch: &LamSwitch) -> Option<Lam> {
        if switch.sw_consts_full {
            None
        } else {
            switch.sw_failaction
        }
    }

    fn const_switch_complete(&self, switch: &LamSwitch) -> bool {
        switch.sw_consts_full || switch.sw_failaction.is_none()
    }

    fn block_switch_default(&self, switch: &LamSwitch) -> Option<Lam> {
        if switch.sw_blocks_full {
            None
        } else {
            switch.sw_failaction
        }
    }

    fn block_switch_complete(&self, switch: &LamSwitch) -> bool {
        switch.sw_blocks_full || switch.sw_failaction.is_none()
    }

    fn variant_tag_name(&self, switch: &LamSwitch) -> String {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => facts.tag_name.clone(),
            SwitchDispatch::Direct => None,
        }
        .unwrap_or_else(|| "TAG".to_string())
    }

    pub(crate) fn bind_switch_scrutinee_once(
        &mut self,
        mut prelude: Block,
        expr: Expr,
    ) -> (Block, Expr) {
        if matches!(self.j.ek(expr), ExprKind::Var(_)) {
            return (prelude, expr);
        }

        let ident = self.fresh_tmp_ident();
        prelude.push(JS::variable(
            VarDecl {
                ident,
                value: Some(expr),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));
        (prelude, JE::var(ident, &mut self.j))
    }

    pub(crate) fn named_variant_switch_needs_bound_scrutinee(&self, a: &LamArena, sw: Sw) -> bool {
        let p = sw.payload(a);
        named_variant_keys_need_bound_scrutinee(
            a.switch_const_keys(sw.info).iter(),
            a.switch_block_keys(sw.info).iter(),
            p.consts_full,
            p.blocks_full,
        )
    }

    fn decoded_switch_needs_bound_scrutinee(switch: &LamSwitch) -> bool {
        named_variant_keys_need_bound_scrutinee(
            switch.sw_consts.iter().map(|(key, _)| key),
            switch.sw_blocks.iter().map(|(key, _)| key),
            switch.sw_consts_full,
            switch.sw_blocks_full,
        )
    }

    /// lam_compile.ml `compile_switch`: `S.if_ (E.is_int_tag ~literal_tags
    /// e) consts ~else_:blocks`, with `S.if_`'s empty-branch rules.
    fn dispatch_named_variant_branches(
        &mut self,
        switch: &LamSwitch,
        scrut_expr: Expr,
        const_branch: Block,
        block_branch: Block,
    ) -> Block {
        let is_int_tag = self.is_int_tag(self.switch_literal_tags(switch), scrut_expr);
        if const_branch.is_empty() {
            let test = JE::not(is_int_tag, &mut self.j);
            vec![JS::if_(test, &block_branch, &[], &mut self.j)]
        } else if block_branch.is_empty() {
            vec![JS::if_(is_int_tag, &const_branch, &[], &mut self.j)]
        } else {
            vec![JS::if_(
                is_int_tag,
                &const_branch,
                &block_branch,
                &mut self.j,
            )]
        }
    }

    fn variant_tag_expr(&mut self, expr: Expr, field_name: &str) -> Expr {
        JE::new(
            ExprKind::StaticIndex(
                expr,
                JE::str_id(field_name, &mut self.j),
                crate::js_ir::arena::FieldPos::new(None),
            ),
            &mut self.j,
        )
    }

    pub(crate) fn switch_case_expr(&mut self, tag: &SwitchCaseTag) -> Expr {
        match tag {
            SwitchCaseTag::String(value) => {
                JE::new(ExprKind::Str(JE::str_id(value, &mut self.j)), &mut self.j)
            }
            SwitchCaseTag::Int(value) => match i32::try_from(*value) {
                Ok(value) => JE::number(Number::int(value), &mut self.j),
                Err(_) => JE::number(Number::float(value.to_string()), &mut self.j),
            },
            SwitchCaseTag::Float(value) => JE::number(Number::float(value.clone()), &mut self.j),
            // js_exp_make.ml `literal_tag`: `Bigint_utils.parse_bigint`.
            SwitchCaseTag::BigInt(value) => {
                let (positive, digits) = crate::types::typecore::parse_bigint_literal(value);
                JE::number(Number::bigint(positive, digits), &mut self.j)
            }
            SwitchCaseTag::Bool(value) => JE::bool(*value, &mut self.j),
            SwitchCaseTag::Null => JE::null(&mut self.j),
            SwitchCaseTag::Undefined => JE::undefined(false, &mut self.j),
        }
    }

    fn switch_case_test(&mut self, test: Expr, tag: &SwitchCaseTag) -> Expr {
        JE::bin(BinOp::EqEqEq, test, self.switch_case_expr(tag), &mut self.j)
    }

    pub(crate) fn compile_small_string_switch_assignment(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(a, result, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_assign_to_target_block(a, result, *body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(a, result, *body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(a, result, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default();
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(a, result, *then_body);
                let else_block = self.compile_assign_to_target_block(a, result, *else_body);
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_small_string_switch_return(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(a, fallback))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_return_block(a, *body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(a, *body);
                let else_block = default
                    .map(|fallback| self.compile_return_block(a, fallback))
                    .unwrap_or_default();
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(a, *then_body);
                let else_block = self.compile_return_block(a, *else_body);
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_effect_if(
        &mut self,
        cond: Expr,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        if then_block.is_empty() {
            if else_block.is_empty() {
                // OCaml's `S.if_ cond [] []` keeps only a condition with side
                // effects (js_stmt_make.ml `if_`), so a switch where every
                // dispatched arm falls through to the same continuation
                // leaves no bare comparison like `tmp === null;`.
                let mut block = vec![];
                push_s_if_empty(&mut self.j, &mut block, cond);
                block
            } else {
                vec![JS::if_(
                    JE::not(cond, &mut self.j),
                    &else_block,
                    &[],
                    &mut self.j,
                )]
            }
        } else if else_block.is_empty() {
            vec![JS::if_(cond, &then_block, &[], &mut self.j)]
        } else {
            vec![JS::if_(cond, &then_block, &else_block, &mut self.j)]
        }
    }

    fn normalized_if_block(&mut self, cond: Expr, then_block: Block, else_block: Block) -> Block {
        let stmt = JS::if_(cond, &then_block, &else_block, &mut self.j);
        match self.j.sk(stmt) {
            StmtKind::Block(block) => self.j.block_vec(block),
            kind => vec![JS::new(kind, &mut self.j)],
        }
    }

    pub(crate) fn compile_small_string_switch_effect(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_effect_block(a, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_effect_block(a, *body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(a, *body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_effect_block(a, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default();
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(a, *then_body);
                let else_block = self.compile_effect_block(a, *else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    /// The general `switch` arm of `compile_general_cases` for a named string
    /// switch assigning to `result`, without trying the small-switch arms.
    fn compile_named_string_switch_assignment_general(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
    ) -> Block {
        // compiler/core/lam_compile.ml:793: only actual JS switch arms
        // enter the switch context; small conditional dispatch does not.
        self.with_switch_depth(|this| {
            let filtered_cases = this.filtered_switch_case_refs(a, cases, default);
            let clauses = stable_group_switch_cases(a, filtered_cases, |_, _| true)
                .into_iter()
                .map(|(tag, body, is_last)| StringClauseInfo {
                    tag_type: tag,
                    clause: if is_last {
                        Clause {
                            source_loc: this.source_loc_of_lam(a, body),
                            body: {
                                let body = {
                                    let value_block = this.compile_switch_value_block(a, result, body);
                                    this.with_block_source_loc(a, body, value_block)
                                };
                                JS::list(&body, &mut this.j)
                            },
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        this.empty_switch_case_clause_for(a, body)
                    },
                })
                .collect();

            let default_block = default.map(|fallback| {
                let block = this.compile_assign_to_target_block(a, result, fallback);
                this.with_block_source_loc(a, fallback, block)
            });
            vec![JS::string_switch(
                test,
                clauses,
                default_block.map(|b| JS::list(&b, &mut this.j)),
                &mut this.j,
            )]
        })
    }

    pub(crate) fn compile_named_string_switch_assignment(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Block {
        // OCaml's `compile_general_cases` (lam_compile.ml:540-566) pattern-
        // matches the UNFILTERED cases list against `[(id, lam)], Default x`
        // etc. Cases that equal the default are only filtered out in the
        // `_, _` switch arm (lam_compile.ml:587-592), AFTER the small-arm
        // selection. Pre-filtering would let `[("Pow", 1), ("Sum", -1)]`
        // with `Default(-1)` collapse to `[(Pow, 1)] + Default(-1)` and
        // hit the 1-case-Default S.if_ arm, where OCaml stays in the
        // switch arm and emits `switch { case "Pow": 1; default: -1 }`.
        match self.compile_small_string_switch_assignment(a, result, test, cases, default, complete)
        {
            Some(block) => block,
            None => {
                self.compile_named_string_switch_assignment_general(a, result, test, cases, default)
            }
        }
    }

    fn compile_named_string_switch_return_with_strategy(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if complete
            && default.is_none()
            && expression_has_no_side_effects(&self.j, test)
            && cases.split_first().is_some_and(|((_, first_body), rest)| {
                rest.iter().all(|(_, body)| a.eq_approx(*first_body, *body))
            })
        {
            let body = self.compile_return_block(a, cases[0].1);
            if !body.is_empty() {
                // OCaml's two-case Complete arm (lam_compile.ml:560-568)
                // emits `S.if_ (test === id1) then else`. When every case is
                // `Lstaticraise X` and Rust's `compile_return_block` resolved
                // it via `with_static_handler` -> `resolve_static_raise`
                // inline, the inlined handler body fills both branches.
                // OCaml's pseudo-jump staticcatch path leaves those raises as
                // fallthrough -> empty and emits the handler body once after
                // the dispatch (lam_compile.ml:980-1008), so `S.if_ test []
                // []` collapses to `S.exp test` (js_stmt_make.ml:242) and the
                // bare comparison (`tmp === null;`) survives in front of the
                // handler. Do not do this for the explicit-jump path:
                // `compile_staticraise` assigns `exit_id = order_id`
                // (lam_compile.ml:936-950), and `compile_staticcatch` emits
                // that path for `Assign _` / non-pseudo continuations
                // (lam_compile.ml:1010-1063). In that case both branches are
                // real assignments, not empty fallthrough branches.
                if cases.len() >= 2
                    && cases.iter().all(|(_, body)| match a.view(*body) {
                        View::StaticRaise(label, args) => {
                            self.static_handlers.iter().any(|handler| {
                                handler.label == label && handler.bindings.len() == args.len()
                            }) && !self.static_jump_handlers.iter().any(|handler| {
                                handler.label == label && handler.bindings.len() == args.len()
                            })
                        }
                        _ => false,
                    })
                {
                    let test_expr = self.switch_case_test(test, &cases[0].0);
                    let mut prefix = vec![];
                    push_s_if_empty(&mut self.j, &mut prefix, test_expr);
                    prefix.extend(body);
                    return prefix;
                }
                // OCaml returns the body directly only for the one-case
                // Complete arm (compiler/core/lam_compile.ml:543). The
                // two-case Complete arm stays on the `S.if_` path
                // (compiler/core/lam_compile.ml:558-566), so it must fall
                // through to `compile_small_string_switch_return` to preserve
                // the observable statement shape. For 3+ cases OCaml takes
                // the `_, _` arm (compiler/core/lam_compile.ml:567+) which
                // keeps the switch form even when all bodies are identical.
                if allow_small && cases.len() == 1 {
                    return body;
                }
            }
            // Body compiles to empty (e.g. all dispatched cases are
            // fallthrough static raises). Fall through to the regular
            // dispatch path so OCaml's `S.if_ cond [] []` -> `S.exp cond`
            // rule (js_stmt_make.ml:242 + 45-53) preserves bare comparisons
            // like `tmp === null;`.
        }

        if allow_small {
            if let Some(block) =
                self.compile_small_string_switch_return(a, test, cases, default, complete)
            {
                return block;
            }
        }

        // compiler/core/lam_compile.ml:793: only actual JS switch arms
        // enter the switch context; small conditional dispatch does not.
        self.with_switch_depth(|this| {
            let filtered_cases = this.filtered_switch_case_refs(a, cases, default);
            let grouped_cases = stable_group_switch_cases(a, filtered_cases, |_, _| true);
            let mut shared_tail = None;
            let clauses = if default.is_none() && this.active_fallthrough_return_handler().is_none() {
                let mut clauses = Vec::with_capacity(grouped_cases.len());
                let mut group_start = 0;
                while group_start < grouped_cases.len() {
                    let mut group_end = group_start;
                    while !grouped_cases[group_end].2 {
                        group_end += 1;
                    }

                    let (_, body, _) = &grouped_cases[group_end];
                    let compiled_output = this.compile_hoisted_named_string_return_tail(a, *body);
                    let compiled_finished = compiled_output.finished;
                    let compiled_body = compiled_output.block;
                    let hoist_shared_tail = group_start != group_end
                        && group_end + 1 == grouped_cases.len()
                        && this.should_hoist_grouped_named_string_return_tail(a, *body)
                        && !compiled_body.is_empty()
                        && compiled_finished == OutputFinished::True;

                    for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                        clauses.push(StringClauseInfo {
                            tag_type: tag.clone(),
                            clause: this.empty_switch_case_clause_for(a, *case_lam),
                        });
                    }
                    clauses.push(StringClauseInfo {
                        tag_type: grouped_cases[group_end].0.clone(),
                        clause: if hoist_shared_tail {
                            shared_tail = Some(compiled_body);
                            Clause {
                                source_loc: None,
                                body: crate::js_ir::arena::StmtList::EMPTY,
                                should_break: true,
                                comment: None,
                            }
                        } else {
                            // Mirror `grouped_return_string_clauses`'s break
                            // calculation from `compile_general_cases`
                            // (compiler/core/lam_compile.ml:610-624) and
                            // `Js_output.to_break_block`
                            // (compiler/core/js_output.ml:88-100).
                            let should_break = return_case_needs_break(a, *body, compiled_finished);
                            Clause {
                                source_loc: this.source_loc_of_lam(a, *body),
                                body: {
                                    let body = this.with_block_source_loc(a, *body, compiled_body);
                                    JS::list(&body, &mut this.j)
                                },
                                should_break,
                                comment: None,
                            }
                        },
                    });

                    group_start = group_end + 1;
                }
                clauses
            } else {
                this.grouped_return_string_clauses(a, grouped_cases, |tag| tag)
            };

            let default_block = default
                .map(|fallback| this.compile_return_block(a, fallback))
                .filter(|body| !body.is_empty());
            let mut block = vec![JS::string_switch(
                test,
                clauses,
                default_block.map(|b| JS::list(&b, &mut this.j)),
                &mut this.j,
            )];
            if let Some(tail) = shared_tail {
                block.extend(tail);
            }
            block
        })
    }

    pub(crate) fn compile_named_string_switch_return(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_return_with_strategy(
            a, test, cases, default, complete, true,
        )
    }

    pub(crate) fn compile_small_string_switch_tail_loop_return(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
        tail_loop: &mut TailLoopState,
    ) -> Option<Block> {
        // OCaml compiler/core/lam_compile.ml:535-567 handles the same small
        // switch cases before falling back to `switch`: one non-complete case
        // becomes `S.if_`, and two complete cases become `S.if_ ... ~else_`.
        // This tail-loop-specific helper keeps those statement shapes while
        // still lowering self tail calls to assignment + `continue`.
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_tail_loop_return_block(a, *body, tail_loop))
            }
            [(tag, body)] => Some(vec![JS::if_(
                self.switch_case_test(test, tag),
                &self.compile_tail_loop_return_block(a, *body, tail_loop),
                &default
                    .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
                    .unwrap_or_default(),
                &mut self.j,
            )]),
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                Some(vec![JS::if_(
                    self.switch_case_test(test, tag),
                    &self.compile_tail_loop_return_block(a, *then_body, tail_loop),
                    &self.compile_tail_loop_return_block(a, *else_body, tail_loop),
                    &mut self.j,
                )])
            }
            _ => None,
        }
    }

    pub(crate) fn grouped_tail_loop_return_string_clauses<T: Clone>(
        &mut self,
        a: &mut LamArena,
        grouped_cases: Vec<(T, Lam, bool)>,
        mut to_tag: impl FnMut(T) -> SwitchCaseTag,
        tail_loop: &mut TailLoopState,
    ) -> Vec<StringClauseInfo> {
        let mut clauses = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_output = self.compile_tail_loop_return_output(a, *body, tail_loop);
            let compiled_finished = compiled_output.finished;
            let compiled_body = compiled_output.block;
            let group_falls_through = compiled_body.is_empty();
            // Mirror `compile_general_cases` + `Js_output.to_break_block`
            // (compiler/core/lam_compile.ml:610-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = return_case_needs_break(a, *body, compiled_finished);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                clauses.push((
                    to_tag(tag.clone()),
                    self.empty_switch_case_clause_for(a, *case_lam),
                    group_falls_through,
                ));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                Clause {
                    source_loc: self.source_loc_of_lam(a, *body),
                    body: {
                        let body = self.with_block_source_loc(a, *body, compiled_body);
                        JS::list(&body, &mut self.j)
                    },
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }

        self.reorder_fallthrough_return_clauses(clauses, |(_, _, falls_through)| *falls_through)
            .into_iter()
            .map(|(tag_type, clause, _)| StringClauseInfo { tag_type, clause })
            .collect()
    }

    pub(crate) fn compile_named_string_switch_tail_loop_return(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // OCaml's `compile_general_cases` (lam_compile.ml:540-566) selects the
        // small `S.if_` arms against the UNFILTERED cases list. Filtering
        // happens only inside the `_, _` switch arm (lam_compile.ml:587-592).
        // Pass the original cases here so a 2-cases-with-Default that filters
        // down to 1 still emits a `switch` (matching OCaml), instead of
        // collapsing to `if/else`.
        if let Some(block) = self.compile_small_string_switch_tail_loop_return(
            a, test, cases, default, complete, tail_loop,
        ) {
            return block;
        }

        // compiler/core/lam_compile.ml:793: only actual JS switch arms
        // enter the switch context; small conditional dispatch does not.
        self.with_switch_depth(|this| {
            let filtered_cases = this.filtered_switch_case_refs(a, cases, default);
            let clauses = this.grouped_tail_loop_return_string_clauses(
                a,
                stable_group_switch_cases(a, filtered_cases, |_, _| true),
                |tag| tag,
                tail_loop,
            );

            let default_block = default
                .map(|fallback| this.compile_tail_loop_return_block(a, fallback, tail_loop))
                .filter(|body| !body.is_empty());

            vec![JS::string_switch(
                test,
                clauses,
                default_block.map(|b| JS::list(&b, &mut this.j)),
                &mut this.j,
            )]
        })
    }

    pub(crate) fn compile_named_string_switch_effect_with_strategy(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if allow_small {
            // OCaml's `compile_general_cases` (lam_compile.ml:540-566) selects
            // the small `S.if_` arms against the UNFILTERED cases list.
            // Filtering happens only inside the `_, _` switch arm
            // (lam_compile.ml:587-592). Pass `cases` here, not the filtered
            // list, so `[(case, body)] + Default(eq body)` shapes derived from
            // a >1-case input keep emitting a switch.
            if let Some(block) =
                self.compile_small_string_switch_effect(a, test, cases, default, complete)
            {
                return block;
            }
        }

        // compiler/core/lam_compile.ml:793: only actual JS switch arms
        // enter the switch context; small conditional dispatch does not.
        self.with_switch_depth(|this| {
            let filtered_cases = this.filtered_switch_case_refs(a, cases, default);
            let clauses: Vec<_> = stable_group_switch_cases(a, filtered_cases, |_, _| true)
                .into_iter()
                .map(|(tag, body, is_last)| {
                    let clause = if is_last {
                        let source_loc = this.source_loc_of_lam(a, body);
                        // `Js_output.to_break_block` (js_output.ml:88-100).
                        let body_output = this.compile_effect_block_output(a, body);
                        let should_break = body_output.finished != OutputFinished::True;
                        let body = this.with_block_source_loc(a, body, body_output.block);
                        Clause {
                            source_loc,
                            should_break,
                            body: JS::list(&body, &mut this.j),
                            comment: None,
                        }
                    } else {
                        this.empty_switch_case_clause_for(a, body)
                    };
                    StringClauseInfo {
                        tag_type: tag,
                        clause,
                    }
                })
                .collect();

            let default_block = default
                .map(|fallback| {
                    let block = this.compile_effect_block(a, fallback);
                    this.with_block_source_loc(a, fallback, block)
                })
                .filter(|body| !body.is_empty());
            vec![JS::string_switch(
                test,
                clauses,
                default_block.map(|b| JS::list(&b, &mut this.j)),
                &mut this.j,
            )]
        })
    }

    pub(crate) fn compile_named_string_switch_effect(
        &mut self,
        a: &mut LamArena,
        test: Expr,
        cases: &[(SwitchCaseTag, Lam)],
        default: Option<Lam>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_effect_with_strategy(
            a, test, cases, default, complete, true,
        )
    }

    pub(crate) fn compile_named_variant_switch_assignment_statements(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(a, result, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(a, result, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                a,
                result,
                scrut_expr,
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(a, result, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default()
        } else {
            let tag_expr = self.variant_tag_expr(scrut_expr, &tag_name);
            self.compile_named_string_switch_assignment(
                a,
                result,
                tag_expr,
                &block_cases,
                block_default,
                block_complete,
            )
        };

        // OCaml `compiler/core/lam_compile.ml:715-765` skips the mixed
        // const/block dispatch only for saturated empty sides. `Complete`
        // caused by `sw_failaction = None` still routes through
        // `is_a_literal_case`, preserving the object guard around TAG access.
        if const_cases.is_empty() && switch.sw_consts_full {
            block_branch
        } else if block_cases.is_empty() && switch.sw_blocks_full {
            const_branch
        } else {
            self.dispatch_named_variant_branches(switch, scrut_expr, const_branch, block_branch)
        }
    }

    pub(crate) fn compile_named_variant_switch_return_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_return_block(a, fallback))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_return_block(a, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                a,
                scrut_expr,
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_return_block(a, fallback))
                .unwrap_or_default()
        } else {
            let tag_expr = self.variant_tag_expr(scrut_expr, &tag_name);
            self.compile_named_string_switch_return(
                a,
                tag_expr,
                &block_cases,
                block_default,
                block_complete,
            )
        };

        // OCaml `compiler/core/lam_compile.ml:715-765` skips the mixed
        // const/block dispatch only for saturated empty sides. `Complete`
        // caused by `sw_failaction = None` still routes through
        // `is_a_literal_case`, preserving the object guard around TAG access.
        if const_cases.is_empty() && switch.sw_consts_full {
            block_branch
        } else if block_cases.is_empty() && switch.sw_blocks_full {
            const_branch
        } else {
            self.dispatch_named_variant_branches(switch, scrut_expr, const_branch, block_branch)
        }
    }

    pub(crate) fn compile_named_variant_switch_tail_loop_return_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_tail_loop_return(
                a,
                scrut_expr,
                &const_cases,
                const_default,
                const_complete,
                tail_loop,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
                .unwrap_or_default()
        } else {
            let tag_expr = self.variant_tag_expr(scrut_expr, &tag_name);
            self.compile_named_string_switch_tail_loop_return(
                a,
                tag_expr,
                &block_cases,
                block_default,
                block_complete,
                tail_loop,
            )
        };

        // OCaml `compiler/core/lam_compile.ml:715-765` skips the mixed
        // const/block dispatch only for saturated empty sides. `Complete`
        // caused by `sw_failaction = None` still routes through
        // `is_a_literal_case`, preserving the object guard around TAG access.
        if const_cases.is_empty() && switch.sw_consts_full {
            block_branch
        } else if block_cases.is_empty() && switch.sw_blocks_full {
            const_branch
        } else {
            self.dispatch_named_variant_branches(switch, scrut_expr, const_branch, block_branch)
        }
    }

    pub(crate) fn compile_named_variant_switch_effect_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| {
                    let block = self.compile_effect_block(a, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| {
                    let block = self.compile_effect_block(a, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                a,
                scrut_expr,
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| {
                    let block = self.compile_effect_block(a, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default()
        } else {
            let tag_expr = self.variant_tag_expr(scrut_expr, &tag_name);
            self.compile_named_string_switch_effect(
                a,
                tag_expr,
                &block_cases,
                block_default,
                block_complete,
            )
        };

        // OCaml `compiler/core/lam_compile.ml:715-765` skips the mixed
        // const/block dispatch only for saturated empty sides. `Complete`
        // caused by `sw_failaction = None` still routes through
        // `is_a_literal_case`, preserving the object guard around TAG access.
        if const_cases.is_empty() && switch.sw_consts_full {
            block_branch
        } else if block_cases.is_empty() && switch.sw_blocks_full {
            const_branch
        } else {
            let test = self.is_int_tag(self.switch_literal_tags(switch), scrut_expr);
            self.compile_effect_if(test, const_branch, block_branch)
        }
    }
}
