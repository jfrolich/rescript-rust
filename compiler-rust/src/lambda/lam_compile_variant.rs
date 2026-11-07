//! Variant and switch compilation.
//!
//! Port of `js_of_lam_variant.ml` + variant/switch compilation logic.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{ocaml_typeof_expr, raw_typeof_comparison};
use super::js_stmt_make::block_terminates;
use super::lam_coercion::push_s_if_empty;
use super::lam_compile::{
    Compiled, LambdaCompiler, TailLoopState,
};
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, Number};
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Expression, ExpressionDesc, Statement, StatementDesc,
    StringClause, VariableDeclaration, expression_has_no_side_effects,
};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{Lambda, LambdaSwitch, SwitchCaseTag, SwitchDispatch, SwitchKey};
use crate::lambda::untagged_dispatch::{
    Clause as UntaggedClause, Plan, Test as UntaggedTest, TestId, Tree, TreeId,
};

/// The continuation an untagged plan is printed in: OCaml's `Assign`,
/// return and effect `Lam_compile_context.continuation`s.
#[derive(Clone, Copy)]
pub(crate) enum UntaggedMode<'r> {
    Assign(&'r Ident),
    Return,
    /// A return in a self-recursive function compiled as a loop, whose
    /// self calls are jumps (the `TailLoopState` passed alongside).
    TailLoopReturn,
    Effect,
}

/// What printing one plan shares across its nodes: lam_compile.ml
/// `compile_untagged_plan`'s closure over the scrutinee, the default action
/// and the blocks compiled for it.
pub(crate) struct UntaggedEmit<'m, 'e, 'p> {
    mode: UntaggedMode<'m>,
    scrut: &'e Expression,
    fallback: Option<&'p Lambda>,
    plan: &'e Plan<&'p Lambda>,
    fallback_blocks: Vec<(bool, Block)>,
}

/// The loop state of [`UntaggedMode::TailLoopReturn`].
type TailLoop<'t> = Option<&'t mut TailLoopState>;

/// js_stmt_make.ml `block_last_is_return_throw_or_continue`: only the last
/// statement itself, not the branches of a statement.
fn block_last_is_return_throw_or_continue(block: &Block) -> bool {
    matches!(
        block.last().map(|stmt| &stmt.desc),
        Some(
            StatementDesc::Return(_)
                | StatementDesc::Throw(_)
                | StatementDesc::Continue(_)
                | StatementDesc::Break(_)
        )
    )
}

pub(crate) fn empty_switch_case_clause() -> CaseClause {
    CaseClause {
        source_loc: None,
        body: vec![],
        should_break: false,
        comment: None,
    }
}

pub(crate) fn stable_group_switch_cases<'a, T, F>(
    filtered: Vec<(T, &'a Lambda)>,
    merge_cases: F,
) -> Vec<(T, &'a Lambda, bool)>
where
    F: Fn(&T, &T) -> bool,
{
    let mut groups: Vec<Vec<(T, &'a Lambda)>> = Vec::new();

    // OCaml's Ext_list.stable_group walks from the tail and inserts each case
    // into the first matching group so equal bodies can be coalesced even when
    // they are separated by a different branch.
    for (tag, lam) in filtered.into_iter().rev() {
        // Groups are built in reverse; `last()` is the group's head.
        let matching = groups.iter_mut().find(|group| {
            group.last().is_some_and(|(head_tag, head_lam)| {
                merge_cases(&tag, head_tag) && super::lambda_eq_approx(lam, head_lam)
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
    pub(crate) fn compile_switch(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Compiled {
        // OCaml's `compile_switch` builds `switch_cxt = enter_switch cxt`
        // and threads it into every case body and the default branch
        // (compiler/core/lam_compile.ml). Wrap the whole switch with
        // `with_switch_depth` so any nested `Lbreak`/`Lcontinue` knows it
        // must use a labeled JS break/continue to escape the loop.
        //
        // An untagged plan enters the switch context only for the bodies of
        // its `switch` statements (lam_compile.ml `compile_untagged_plan`).
        if let Some(plan) = super::untagged_plan(switch) {
            // lam_compile.ml: the `NeedValue` temp is made before the
            // scrutinee is compiled.
            let tmp = self.fresh_tmp_ident();
            let mut prelude = vec![Statement::variable(VariableDeclaration {
                ident: tmp,
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })];
            prelude.extend(self.compile_untagged_switch(
                UntaggedMode::Assign(&tmp),
                None,
                scrut,
                switch,
                &plan,
            ));
            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }
        self.with_switch_depth(|this| this.compile_switch_inner(scrut, switch))
    }

    fn compile_switch_inner(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Compiled {
        // OCaml reference: compiler/core/lam_compile.ml:775-786 creates the
        // NeedValue result temp before `compile_whole`, and `compile_whole`
        // compiles the switch scrutinee at lam_compile.ml:707-713. Keep the
        // allocation order and statement order identical so any scrutinee temps
        // get later names and the result declaration precedes scrutinee prelude.
        let tmp = self.fresh_tmp_ident();
        let tmp_declaration = || {
            Statement::variable(VariableDeclaration {
                ident: tmp,
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })
        };

        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (scrut_prelude, scrut_expr) =
                if self.named_variant_switch_needs_bound_scrutinee(switch) {
                    self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
                } else {
                    (scrut_compiled.prelude, scrut_compiled.expr)
                };
            let mut prelude = vec![tmp_declaration()];
            prelude.extend(scrut_prelude);
            prelude.extend(
                self.compile_named_variant_switch_assignment_statements(&tmp, scrut_expr, switch),
            );

            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = vec![tmp_declaration()];
        prelude.extend(scrut_compiled.prelude);

        let cases: Vec<_> = self
            .grouped_switch_cases(
                &switch.sw_consts,
                switch.sw_failaction.as_deref(),
                |_, _| true,
            )
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
                        crate::js_ir::CaseClause {
                            source_loc: self.source_loc_of_lam(body),
                            body: {
                                let value_block = self.compile_switch_value_block(&tmp, body);
                                self.with_block_source_loc(body, value_block)
                            },
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        self.empty_switch_case_clause_for(body)
                    },
                )
            })
            .collect();

        // OCaml `compile_general_cases` only calls `Js_output.to_break_block`
        // for grouped cases (compiler/core/lam_compile.ml:610-624). The
        // switch default is `Js_output.output_as_block`
        // (compiler/core/lam_compile.ml:595-605), so it must not get the
        // case-only trailing `break`.
        let default_block = switch.sw_failaction.as_ref().map(|fallback| {
            let block = self.compile_assign_to_target_block(&tmp, fallback);
            self.with_block_source_loc(fallback, block)
        });

        prelude.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    pub(crate) fn compile_string_switch(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Compiled {
        self.with_switch_depth(|this| this.compile_string_switch_inner(scrut, cases, default))
    }

    fn compile_string_switch_inner(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Compiled {
        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_tmp_ident();
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_assignment(
            &tmp,
            scrut_compiled.expr.clone(),
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
                Ok(expr) => prelude.push(Statement::variable(VariableDeclaration {
                    ident: tmp,
                    value: Some(expr),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })),
                Err(block) => {
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: tmp,
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                    prelude.extend(block);
                }
            }
            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp,
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let clauses: Vec<_> = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| crate::js_ir::StringClause {
                tag_type: SwitchCaseTag::String(tag),
                clause: if is_last {
                    crate::js_ir::CaseClause {
                        source_loc: self.source_loc_of_lam(body),
                        body: {
                            let value_block = self.compile_switch_value_block(&tmp, body);
                            self.with_block_source_loc(body, value_block)
                        },
                        should_break: false,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                },
            })
            .collect();

        // OCaml `compile_general_cases` only calls `Js_output.to_break_block`
        // for grouped cases (compiler/core/lam_compile.ml:610-624). The
        // switch default is `Js_output.output_as_block`
        // (compiler/core/lam_compile.ml:595-605), so it must not get the
        // case-only trailing `break`.
        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(&tmp, fallback);
            self.with_block_source_loc(fallback, block)
        });

        prelude.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    /// lambda.ml `untagged_plan`'s precondition: a switch on an untagged
    /// variant (one with payload kinds) whose dispatch is not on literals
    /// only, with literal constants and untagged payload cases.
    pub(crate) fn uses_untagged_variant_switch(&self, switch: &LambdaSwitch) -> bool {
        let SwitchDispatch::Variant(facts) = &switch.sw_dispatch else {
            return false;
        };
        !facts.block_types.is_empty()
            && ((switch.sw_consts_full && switch.sw_consts.is_empty())
                || !(switch.sw_blocks_full && switch.sw_blocks.is_empty()))
            && switch.sw_consts.iter().all(|(key, _)| {
                matches!(
                    key,
                    SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(_))
                )
            })
            && switch.sw_blocks.iter().all(|(key, _)| {
                matches!(
                    key,
                    SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                        crate::types::VariantBlock::Untagged { .. }
                    ))
                )
            })
    }

    pub(crate) fn uses_named_variant_switch(&self, switch: &LambdaSwitch) -> bool {
        matches!(switch.sw_dispatch, SwitchDispatch::Variant(_))
            && !self.uses_untagged_variant_switch(switch)
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

    fn named_const_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(SwitchCaseTag, &'a Lambda)>> {
        switch
            .sw_consts
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(tag)) => {
                    Some((Self::switch_tag_value(tag), body))
                }
                SwitchKey::Int(_) | SwitchKey::Constructor(_) => None,
            })
            .collect()
    }

    fn named_block_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(SwitchCaseTag, &'a Lambda)>> {
        switch
            .sw_blocks
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(block)) => {
                    Some((Self::switch_tag_value(block.tag()), body))
                }
                SwitchKey::Int(_) | SwitchKey::Constructor(_) => None,
            })
            .collect()
    }

    fn const_switch_default<'a>(&self, switch: &'a LambdaSwitch) -> Option<&'a Lambda> {
        if switch.sw_consts_full {
            None
        } else {
            switch.sw_failaction.as_deref()
        }
    }

    fn const_switch_complete(&self, switch: &LambdaSwitch) -> bool {
        switch.sw_consts_full || switch.sw_failaction.is_none()
    }

    fn block_switch_default<'a>(&self, switch: &'a LambdaSwitch) -> Option<&'a Lambda> {
        if switch.sw_blocks_full {
            None
        } else {
            switch.sw_failaction.as_deref()
        }
    }

    fn block_switch_complete(&self, switch: &LambdaSwitch) -> bool {
        switch.sw_blocks_full || switch.sw_failaction.is_none()
    }

    fn variant_tag_name(&self, switch: &LambdaSwitch) -> String {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => facts.tag_name.clone(),
            SwitchDispatch::Direct => None,
        }
        .unwrap_or_else(|| "TAG".to_string())
    }

    /// js_exp_make.ml `class_constructor`: the constructor of a class at a
    /// global path such as `Intl.Locale`, a global with properties.
    fn class_constructor(&self, name: &str) -> Expression {
        let mut parts = name.split('.');
        let global = parts.next().expect("a class path has a global");
        parts.fold(
            Expression::var(Ident::create_persistent(global)),
            |expr, property| self.static_index(expr, property),
        )
    }

    /// js_exp_make.ml `is_instance_of`: `Array.isArray(e)` or
    /// `e instanceof C`.
    fn is_instance_of(&self, instance: &crate::types::VariantInstance, expr: Expression) -> Expression {
        match instance {
            crate::types::VariantInstance::Array => Expression::call(
                self.static_index(
                    Expression::var(Ident::create_persistent("Array")),
                    "isArray",
                ),
                vec![expr],
                CallInfo::default(),
            ),
            crate::types::VariantInstance::Class { name, .. } => {
                Expression::bin(BinOp::InstanceOf, expr, self.class_constructor(name))
            }
        }
    }

    /// js_exp_make.ml `is_int_tag ~literal_tags`: whether a value of a
    /// tagged variant is a constant rather than a block, given the literals
    /// of its constants.
    fn is_int_tag(&self, literal_tags: &[crate::types::VariantLiteralTag], expr: Expression) -> Expression {
        use crate::types::VariantLiteralTag as L;
        let has_null = literal_tags.iter().any(|tag| matches!(tag, L::Null));
        let has_undefined = literal_tags.iter().any(|tag| matches!(tag, L::Undefined));
        let has_other = literal_tags
            .iter()
            .any(|tag| !matches!(tag, L::Null | L::Undefined));
        let is_null = || Expression::bin(BinOp::EqEqEq, expr.clone(), Expression::null());
        let is_undefined =
            || Expression::bin(BinOp::EqEqEq, expr.clone(), Expression::undefined(false));
        let not_an_object = || raw_typeof_comparison(expr.clone(), BinOp::NotEqEq, "object");
        match (has_null, has_undefined, has_other) {
            (true, false, false) => is_null(),
            (true, true, false) => Expression::bin(BinOp::Or, is_null(), is_undefined()),
            (false, true, false) => is_undefined(),
            (true, _, true) => Expression::bin(BinOp::Or, is_null(), not_an_object()),
            (false, _, _) => not_an_object(),
        }
    }

    fn switch_literal_tags<'a>(&self, switch: &'a LambdaSwitch) -> &'a [crate::types::VariantLiteralTag] {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => &facts.literal_tags,
            SwitchDispatch::Direct => &[],
        }
    }

    /// lam_compile.ml `compile_switch`, the `Lambda.untagged_plan sw =
    /// Some plan` branch: compile the scrutinee in the outer context, bind it
    /// to a variable unless only payloads are dispatched, and print the plan.
    pub(crate) fn compile_untagged_switch(
        &mut self,
        mode: UntaggedMode<'_>,
        mut tail_loop: TailLoop<'_>,
        scrut: &Lambda,
        switch: &LambdaSwitch,
        plan: &Plan<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let payload_only = switch.sw_consts_full && switch.sw_consts.is_empty();
        let (mut block, scrut_expr) = if payload_only {
            (scrut_compiled.prelude, scrut_compiled.expr)
        } else {
            self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
        };
        block.extend(self.compile_untagged_plan(
            mode,
            &mut tail_loop,
            &scrut_expr,
            switch.sw_failaction.as_deref(),
            plan,
        ));
        block
    }

    #[cfg(test)]
    pub(crate) fn compile_untagged_variant_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let plan = super::untagged_plan(switch).expect("an untagged switch");
        let fallback = switch.sw_failaction.as_deref();
        self.compile_untagged_plan(UntaggedMode::Assign(result), &mut None, &scrut_expr, fallback, &plan)
    }

    #[cfg(test)]
    pub(crate) fn compile_untagged_variant_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let plan = super::untagged_plan(switch).expect("an untagged switch");
        let fallback = switch.sw_failaction.as_deref();
        self.compile_untagged_plan(UntaggedMode::Return, &mut None, &scrut_expr, fallback, &plan)
    }

    #[cfg(test)]
    pub(crate) fn compile_untagged_variant_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let plan = super::untagged_plan(switch).expect("an untagged switch");
        let fallback = switch.sw_failaction.as_deref();
        self.compile_untagged_plan(UntaggedMode::Effect, &mut None, &scrut_expr, fallback, &plan)
    }

    /// lam_compile.ml `compile_untagged_plan`: prints the plan, each node one
    /// statement. A body in a `switch` statement is compiled in a `switch`
    /// context, a body of an `if` is not.
    pub(crate) fn compile_untagged_plan(
        &mut self,
        mode: UntaggedMode<'_>,
        tail_loop: &mut TailLoop<'_>,
        scrut: &Expression,
        fallback: Option<&Lambda>,
        plan: &Plan<&Lambda>,
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
        self.emit_untagged_tree(&mut emit, tail_loop, plan.root())
    }

    fn untagged_typeof_expr(scrut: &Expression, block_type: &crate::types::VariantBlockType) -> Expression {
        raw_typeof_comparison(
            scrut.clone(),
            BinOp::EqEqEq,
            block_type
                .typeof_name()
                .expect("a typeof test is on a kind with a typeof name"),
        )
    }

    fn untagged_test_expr(&self, plan: &Plan<&Lambda>, scrut: &Expression, test: TestId) -> Expression {
        match plan.test(test) {
            UntaggedTest::Equals(literal) => Expression::bin(
                BinOp::EqEqEq,
                scrut.clone(),
                Self::switch_case_expr(&Self::literal_tag_value(literal)),
            ),
            UntaggedTest::Typeof(block_type) => Self::untagged_typeof_expr(scrut, block_type),
            UntaggedTest::Instance(instance) => self.is_instance_of(instance, scrut.clone()),
            UntaggedTest::NotNull => Expression::not(self.is_null_expr(scrut.clone())),
            UntaggedTest::Not(test) => {
                Expression::not(self.untagged_test_expr(plan, scrut, *test))
            }
            UntaggedTest::And(test1, test2) => Expression::bin(
                BinOp::And,
                self.untagged_test_expr(plan, scrut, *test1),
                self.untagged_test_expr(plan, scrut, *test2),
            ),
            UntaggedTest::Or(test1, test2) => Expression::bin(
                BinOp::Or,
                self.untagged_test_expr(plan, scrut, *test1),
                self.untagged_test_expr(plan, scrut, *test2),
            ),
        }
    }

    /// `compile_lambda cxt lam |> Js_output.output_as_block |>
    /// with_block_source_loc lam` in the continuation of `mode`.
    fn untagged_output_block(
        &mut self,
        mode: UntaggedMode<'_>,
        tail_loop: &mut TailLoop<'_>,
        lam: &Lambda,
    ) -> Block {
        let block = match mode {
            UntaggedMode::Assign(result) => self.compile_assign_to_target_block(result, lam),
            UntaggedMode::Return => self.compile_return_block(lam),
            UntaggedMode::TailLoopReturn => self.compile_tail_loop_return_block(
                lam,
                tail_loop.as_deref_mut().expect("a tail loop"),
            ),
            UntaggedMode::Effect => self.compile_effect_block(lam),
        };
        self.with_block_source_loc(lam, block)
    }

    fn untagged_fallback_block(
        &mut self,
        emit: &mut UntaggedEmit<'_, '_, '_>,
        tail_loop: &mut TailLoop<'_>,
    ) -> Block {
        let in_switch = self.switch_depth > 0;
        if let Some((_, block)) = emit.fallback_blocks.iter().find(|(key, _)| *key == in_switch) {
            return block.clone();
        }
        let lam = emit
            .fallback
            .expect("a plan reaches the fallback only when the switch has one");
        let block = self.untagged_output_block(emit.mode, tail_loop, lam);
        emit.fallback_blocks.push((in_switch, block.clone()));
        block
    }

    fn untagged_if(mode: UntaggedMode<'_>, cond: Expression, then_: Block, else_: Block) -> Block {
        match mode {
            UntaggedMode::Return | UntaggedMode::TailLoopReturn => {
                Self::normalized_if_block(cond, then_, else_)
            }
            UntaggedMode::Assign(_) | UntaggedMode::Effect => {
                vec![Statement::if_(cond, then_, else_)]
            }
        }
    }

    fn emit_untagged_tree(
        &mut self,
        emit: &mut UntaggedEmit<'_, '_, '_>,
        tail_loop: &mut TailLoop<'_>,
        tree: TreeId,
    ) -> Block {
        let plan = emit.plan;
        match plan.tree(tree) {
            Tree::Run(lam) => self.untagged_output_block(emit.mode, tail_loop, lam),
            Tree::Fallback => self.untagged_fallback_block(emit, tail_loop),
            Tree::Skip => vec![],
            Tree::If(test, then_, else_) => {
                // Bodies are compiled in the order they are printed, which
                // numbers loop labels top to bottom.
                let then_ = self.emit_untagged_tree(emit, tail_loop, *then_);
                let else_ = self.emit_untagged_tree(emit, tail_loop, *else_);
                let cond = self.untagged_test_expr(plan, emit.scrut, *test);
                Self::untagged_if(emit.mode, cond, then_, else_)
            }
            Tree::Block(inner) => {
                let block = self.emit_untagged_tree(emit, tail_loop, *inner);
                vec![Statement::block(block)]
            }
            Tree::SwitchValue(clauses, default) => self.with_switch_depth(|this| {
                let default = this.emit_untagged_tree(emit, tail_loop, *default);
                let default = (!default.is_empty()).then_some(default);
                let clauses = plan
                    .value_clauses(*clauses)
                    .iter()
                    .map(|(literal, clause)| StringClause {
                        tag_type: Self::literal_tag_value(literal),
                        clause: this.emit_untagged_clause(emit, tail_loop, clause),
                    })
                    .collect();
                vec![Statement::new(StatementDesc::StringSwitch(
                    emit.scrut.clone(),
                    clauses,
                    default,
                ))]
            }),
            Tree::SwitchTypeof(clauses, default)
                if clauses.len() == 1
                    && matches!(plan.typeof_clauses(*clauses)[0].1, UntaggedClause::Body(_)) =>
            {
                // One kind is an `if`, so its bodies are not in a `switch`.
                let (block_type, clause) = &plan.typeof_clauses(*clauses)[0];
                let clause = self.emit_untagged_clause(emit, tail_loop, clause);
                let default = self.emit_untagged_tree(emit, tail_loop, *default);
                let cond = Self::untagged_typeof_expr(emit.scrut, block_type);
                Self::untagged_if(emit.mode, cond, clause.body, default)
            }
            Tree::SwitchTypeof(clauses, default) => self.with_switch_depth(|this| {
                let default = this.emit_untagged_tree(emit, tail_loop, *default);
                let clauses = plan
                    .typeof_clauses(*clauses)
                    .iter()
                    .map(|(block_type, clause)| StringClause {
                        tag_type: SwitchCaseTag::String(
                            block_type
                                .typeof_name()
                                .expect("a typeof switch is on kinds with a typeof name")
                                .to_string(),
                        ),
                        clause: this.emit_untagged_clause(emit, tail_loop, clause),
                    })
                    .collect();
                vec![Statement::new(StatementDesc::StringSwitch(
                    ocaml_typeof_expr(emit.scrut.clone()),
                    clauses,
                    Some(default),
                ))]
            }),
        }
    }

    fn emit_untagged_clause(
        &mut self,
        emit: &mut UntaggedEmit<'_, '_, '_>,
        tail_loop: &mut TailLoop<'_>,
        clause: &UntaggedClause<&Lambda>,
    ) -> CaseClause {
        let body = match clause {
            UntaggedClause::FallsThrough(lam) => {
                return CaseClause {
                    source_loc: lam.and_then(|lam| self.source_loc_of_lam(lam)),
                    ..empty_switch_case_clause()
                };
            }
            UntaggedClause::Body(body) => emit.plan.tree(*body),
        };
        match body {
            Tree::Run(lam) => {
                let lam: &Lambda = lam;
                let (body, should_break) = match emit.mode {
                    // `Js_output.to_break_block`: the assignment needs a
                    // `break` unless it finishes; an `if` drops the flag.
                    UntaggedMode::Assign(result) => {
                        let body = self.compile_assign_to_target_block(result, lam);
                        let should_break = !block_terminates(&body);
                        (body, should_break)
                    }
                    UntaggedMode::Return => {
                        let body = self.compile_return_block(lam);
                        let should_break = self.return_case_needs_break_like_ocaml(lam, &body);
                        (body, should_break)
                    }
                    UntaggedMode::TailLoopReturn => {
                        let body = self.compile_tail_loop_return_block(
                            lam,
                            tail_loop.as_deref_mut().expect("a tail loop"),
                        );
                        let should_break = self.return_case_needs_break_like_ocaml(lam, &body);
                        (body, should_break)
                    }
                    UntaggedMode::Effect => {
                        let body = self.compile_effect_block(lam);
                        let should_break = !block_terminates(&body);
                        (body, should_break)
                    }
                };
                CaseClause {
                    source_loc: self.source_loc_of_lam(lam),
                    body: self.with_block_source_loc(lam, body),
                    should_break,
                    comment: None,
                }
            }
            Tree::Fallback => {
                let block = self.untagged_fallback_block(emit, tail_loop);
                CaseClause {
                    should_break: !block_last_is_return_throw_or_continue(&block),
                    body: block,
                    source_loc: None,
                    comment: None,
                }
            }
            _ => unreachable!("a clause body is a Run or the Fallback"),
        }
    }

    pub(crate) fn bind_switch_scrutinee_once(
        &mut self,
        mut prelude: Block,
        expr: Expression,
    ) -> (Block, Expression) {
        if matches!(expr.desc, ExpressionDesc::Var(_)) {
            return (prelude, expr);
        }

        let ident = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident,
            value: Some(expr),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));
        (prelude, Expression::var(ident))
    }

    pub(crate) fn named_variant_switch_needs_bound_scrutinee(&self, switch: &LambdaSwitch) -> bool {
        // Same as `named_const_cases`/`named_block_cases` being `Some` and
        // non-empty, without building the case vectors.
        let has_const_cases = !switch.sw_consts.is_empty()
            && switch.sw_consts.iter().all(|(key, _)| {
                matches!(
                    key,
                    SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(_))
                )
            });
        let has_block_cases = !switch.sw_blocks.is_empty()
            && switch.sw_blocks.iter().all(|(key, _)| {
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
            (true, false) => !switch.sw_blocks_full,
            (false, true) => !switch.sw_consts_full,
            (false, false) => false,
        }
    }

    /// lam_compile.ml `compile_switch`: `S.if_ (E.is_int_tag ~literal_tags
    /// e) consts ~else_:blocks`, with `S.if_`'s empty-branch rules.
    fn dispatch_named_variant_branches(
        &self,
        switch: &LambdaSwitch,
        scrut_expr: Expression,
        const_branch: Block,
        block_branch: Block,
    ) -> Block {
        let is_int_tag = self.is_int_tag(self.switch_literal_tags(switch), scrut_expr);
        if const_branch.is_empty() {
            vec![Statement::if_(Expression::not(is_int_tag), block_branch, vec![])]
        } else if block_branch.is_empty() {
            vec![Statement::if_(is_int_tag, const_branch, vec![])]
        } else {
            vec![Statement::if_(is_int_tag, const_branch, block_branch)]
        }
    }

    fn variant_tag_expr(&self, expr: Expression, field_name: &str) -> Expression {
        Expression::new(ExpressionDesc::StaticIndex(
            Box::new(expr),
            field_name.to_string(),
            None,
        ))
    }

    pub(crate) fn switch_case_expr(tag: &SwitchCaseTag) -> Expression {
        match tag {
            SwitchCaseTag::String(value) => Expression::new(ExpressionDesc::Str(value.clone())),
            SwitchCaseTag::Int(value) => match i32::try_from(*value) {
                Ok(value) => Expression::number(Number::int(value)),
                Err(_) => Expression::number(Number::float(value.to_string())),
            },
            SwitchCaseTag::Float(value) => Expression::number(Number::float(value.clone())),
            // js_exp_make.ml `literal_tag`: `Bigint_utils.parse_bigint`.
            SwitchCaseTag::BigInt(value) => {
                let (positive, digits) = crate::types::typecore::parse_bigint_literal(value);
                Expression::number(Number::bigint(positive, digits))
            }
            SwitchCaseTag::Bool(value) => Expression::bool(*value),
            SwitchCaseTag::Null => Expression::null(),
            SwitchCaseTag::Undefined => Expression::undefined(false),
        }
    }

    fn switch_case_test(&self, test: Expression, tag: &SwitchCaseTag) -> Expression {
        Expression::bin(BinOp::EqEqEq, test, Self::switch_case_expr(tag))
    }

    pub(crate) fn compile_small_string_switch_assignment(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(result, fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_assign_to_target_block(result, body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(result, body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(result, fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default();
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(result, then_body);
                let else_block = self.compile_assign_to_target_block(result, else_body);
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_small_string_switch_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_return_block(body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(body);
                let else_block = default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default();
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(then_body);
                let else_block = self.compile_return_block(else_body);
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_effect_if(
        &self,
        cond: Expression,
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
                push_s_if_empty(&mut block, cond);
                block
            } else {
                vec![Statement::if_(Expression::not(cond), else_block, vec![])]
            }
        } else if else_block.is_empty() {
            vec![Statement::if_(cond, then_block, vec![])]
        } else {
            vec![Statement::if_(cond, then_block, else_block)]
        }
    }

    fn normalized_if_block(cond: Expression, then_block: Block, else_block: Block) -> Block {
        match Statement::if_(cond, then_block, else_block).desc {
            StatementDesc::Block(block) => block,
            desc => vec![Statement::new(desc)],
        }
    }

    pub(crate) fn compile_small_string_switch_effect(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_effect_block(fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_effect_block(body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_effect_block(fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default();
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(then_body);
                let else_block = self.compile_effect_block(else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_named_string_switch_assignment_with_strategy(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if allow_small {
            // OCaml's `compile_general_cases` (lam_compile.ml:540-566) pattern-
            // matches the UNFILTERED cases list against `[(id, lam)], Default x`
            // etc. Cases that equal the default are only filtered out in the
            // `_, _` switch arm (lam_compile.ml:587-592), AFTER the small-arm
            // selection. Pre-filtering would let `[("Pow", 1), ("Sum", -1)]`
            // with `Default(-1)` collapse to `[(Pow, 1)] + Default(-1)` and
            // hit the 1-case-Default S.if_ arm, where OCaml stays in the
            // switch arm and emits `switch { case "Pow": 1; default: -1 }`.
            if let Some(block) = self.compile_small_string_switch_assignment(
                result,
                test.clone(),
                cases,
                default,
                complete,
            ) {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses = stable_group_switch_cases(filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| StringClause {
                tag_type: tag,
                clause: if is_last {
                    CaseClause {
                        source_loc: self.source_loc_of_lam(body),
                        body: {
                            let value_block = self.compile_switch_value_block(result, body);
                            self.with_block_source_loc(body, value_block)
                        },
                        should_break: false,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                },
            })
            .collect();

        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(result, fallback);
            self.with_block_source_loc(fallback, block)
        });
        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    pub(crate) fn compile_named_string_switch_assignment(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_assignment_with_strategy(
            result, test, cases, default, complete, true,
        )
    }

    fn compile_named_string_switch_return_with_strategy(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if complete
            && default.is_none()
            && expression_has_no_side_effects(&test)
            && cases.split_first().is_some_and(|((_, first_body), rest)| {
                rest.iter()
                    .all(|(_, body)| super::lambda_eq_approx(first_body, body))
            })
        {
            let body = self.compile_return_block(cases[0].1);
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
                    && cases.iter().all(|(_, body)| match body {
                        Lambda::LstaticRaise(label, args) => {
                            self.static_handlers.iter().any(|handler| {
                                handler.label == *label && handler.bindings.len() == args.len()
                            }) && !self.static_jump_handlers.iter().any(|handler| {
                                handler.label == *label && handler.bindings.len() == args.len()
                            })
                        }
                        _ => false,
                    })
                {
                    let test_expr = self.switch_case_test(test, &cases[0].0);
                    let mut prefix = vec![];
                    push_s_if_empty(&mut prefix, test_expr);
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
            // dispatch path, which applies OCaml's `S.if_ cond [] []` rule
            // (js_stmt_make.ml `if_`).
        }

        if allow_small {
            if let Some(block) =
                self.compile_small_string_switch_return(test.clone(), cases, default, complete)
            {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let grouped_cases = stable_group_switch_cases(filtered_cases, |_, _| true);
        let mut shared_tail = None;
        let clauses = if default.is_none() && self.active_fallthrough_return_handler().is_none() {
            let mut clauses = Vec::with_capacity(grouped_cases.len());
            let mut group_start = 0;
            while group_start < grouped_cases.len() {
                let mut group_end = group_start;
                while !grouped_cases[group_end].2 {
                    group_end += 1;
                }

                let (_, body, _) = &grouped_cases[group_end];
                let compiled_body = self.compile_hoisted_named_string_return_tail(body);
                let hoist_shared_tail = group_start != group_end
                    && group_end + 1 == grouped_cases.len()
                    && self.should_hoist_grouped_named_string_return_tail(body)
                    && !compiled_body.is_empty()
                    && block_terminates(&compiled_body);

                for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                    clauses.push(StringClause {
                        tag_type: tag.clone(),
                        clause: self.empty_switch_case_clause_for(case_lam),
                    });
                }
                clauses.push(StringClause {
                    tag_type: grouped_cases[group_end].0.clone(),
                    clause: if hoist_shared_tail {
                        shared_tail = Some(compiled_body);
                        CaseClause {
                            source_loc: None,
                            body: vec![],
                            should_break: true,
                            comment: None,
                        }
                    } else {
                        // Mirror `grouped_return_string_clauses`'s break
                        // calculation from `compile_general_cases`
                        // (compiler/core/lam_compile.ml:610-624) and
                        // `Js_output.to_break_block`
                        // (compiler/core/js_output.ml:88-100).
                        let should_break =
                            self.return_case_needs_break_like_ocaml(body, &compiled_body);
                        CaseClause {
                            source_loc: self.source_loc_of_lam(body),
                            body: self.with_block_source_loc(body, compiled_body),
                            should_break,
                            comment: None,
                        }
                    },
                });

                group_start = group_end + 1;
            }
            clauses
        } else {
            self.grouped_return_string_clauses(grouped_cases, |tag| tag)
        };

        let default_block = default
            .map(|fallback| self.compile_return_block(fallback))
            .filter(|body| !body.is_empty());
        let mut block = vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))];
        if let Some(tail) = shared_tail {
            block.extend(tail);
        }
        block
    }

    pub(crate) fn compile_named_string_switch_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_return_with_strategy(test, cases, default, complete, true)
    }

    pub(crate) fn compile_small_string_switch_tail_loop_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
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
                    .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_tail_loop_return_block(body, tail_loop))
            }
            [(tag, body)] => Some(vec![Statement::if_(
                self.switch_case_test(test, tag),
                self.compile_tail_loop_return_block(body, tail_loop),
                default
                    .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                    .unwrap_or_default(),
            )]),
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                Some(vec![Statement::if_(
                    self.switch_case_test(test, tag),
                    self.compile_tail_loop_return_block(then_body, tail_loop),
                    self.compile_tail_loop_return_block(else_body, tail_loop),
                )])
            }
            _ => None,
        }
    }

    pub(crate) fn grouped_tail_loop_return_string_clauses<T: Clone>(
        &mut self,
        grouped_cases: Vec<(T, &Lambda, bool)>,
        mut to_tag: impl FnMut(T) -> SwitchCaseTag,
        tail_loop: &mut TailLoopState,
    ) -> Vec<StringClause> {
        let mut clauses = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_body = self.compile_tail_loop_return_block(body, tail_loop);
            let group_falls_through = compiled_body.is_empty();
            // Mirror `compile_general_cases` + `Js_output.to_break_block`
            // (compiler/core/lam_compile.ml:610-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = self.return_case_needs_break_like_ocaml(body, &compiled_body);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                clauses.push((
                    to_tag(tag.clone()),
                    self.empty_switch_case_clause_for(case_lam),
                    group_falls_through,
                ));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                CaseClause {
                    source_loc: self.source_loc_of_lam(body),
                    body: self.with_block_source_loc(body, compiled_body),
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }

        self.reorder_fallthrough_return_clauses(clauses, |(_, _, falls_through)| *falls_through)
            .into_iter()
            .map(|(tag_type, clause, _)| StringClause { tag_type, clause })
            .collect()
    }

    pub(crate) fn compile_named_string_switch_tail_loop_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
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
            test.clone(),
            cases,
            default,
            complete,
            tail_loop,
        ) {
            return block;
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses = self.grouped_tail_loop_return_string_clauses(
            stable_group_switch_cases(filtered_cases, |_, _| true),
            |tag| tag,
            tail_loop,
        );

        let default_block = default
            .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
            .filter(|body| !body.is_empty());

        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    pub(crate) fn compile_named_string_switch_effect_with_strategy(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
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
                self.compile_small_string_switch_effect(test.clone(), cases, default, complete)
            {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses: Vec<_> = stable_group_switch_cases(filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let source_loc = self.source_loc_of_lam(body);
                    let body_block = self.compile_effect_block(body);
                    let body = self.with_block_source_loc(body, body_block);
                    CaseClause {
                        source_loc,
                        should_break: !block_terminates(&body),
                        body,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                };
                StringClause {
                    tag_type: tag,
                    clause,
                }
            })
            .collect();

        let default_block = default
            .map(|fallback| {
                let block = self.compile_effect_block(fallback);
                self.with_block_source_loc(fallback, block)
            })
            .filter(|body| !body.is_empty());
        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    pub(crate) fn compile_named_string_switch_effect(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_effect_with_strategy(test, cases, default, complete, true)
    }

    pub(crate) fn compile_named_variant_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
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
                    let block = self.compile_assign_to_target_block(result, fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(result, fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(result, fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
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
        scrut_expr: Expression,
        switch: &LambdaSwitch,
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
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
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
        scrut_expr: Expression,
        switch: &LambdaSwitch,
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
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_tail_loop_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
                tail_loop,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_tail_loop_return(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
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
        scrut_expr: Expression,
        switch: &LambdaSwitch,
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
                    let block = self.compile_effect_block(fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| {
                    let block = self.compile_effect_block(fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| {
                    let block = self.compile_effect_block(fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
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
            let is_int_tag = self.is_int_tag(self.switch_literal_tags(switch), scrut_expr);
            self.compile_effect_if(is_int_tag, const_branch, block_branch)
        }
    }
}
