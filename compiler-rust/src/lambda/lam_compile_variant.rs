//! Variant and switch compilation.
//!
//! Port of `js_of_lam_variant.ml` + variant/switch compilation logic.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{ocaml_typeof_expr, raw_typeof_comparison};
use super::js_stmt_make::{block_terminates, strict_single_return_expr};
use super::lam_coercion::push_s_exp;
use super::lam_compile::{
    Compiled, GroupedSwitchDefault, LambdaCompiler, StrSw, Sw, TailLoopState,
    trailing_return_expression,
};
use crate::ident::Ident;
use crate::js_ir::arena::{
    Block, Clause, Expr, ExprKind, JsArena, Stmt, StmtKind, StringClauseInfo, VarDecl,
};
use crate::js_ir::build::{
    exp as JE, expression_has_no_side_effects, ocaml_eq_expression, stmt as JS,
};
use crate::js_ir::op::{IdentInfo, Number};
use crate::js_ir::{BinOp, CallInfo};
use crate::lambda::arena::{Lam, LamArena, SwitchPayload, View};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{SwitchCaseTag, SwitchDispatch, SwitchKey};
use crate::types::VariantBlockType;

pub(crate) fn empty_switch_case_clause() -> Clause {
    Clause {
        source_loc: None,
        body: crate::js_ir::arena::StmtList::EMPTY,
        should_break: false,
        comment: None,
    }
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

fn untagged_dispatch(dispatch: &SwitchDispatch) -> bool {
    matches!(dispatch, SwitchDispatch::Variant(facts) if !facts.block_types.is_empty())
}

fn named_dispatch(dispatch: &SwitchDispatch) -> bool {
    matches!(dispatch, SwitchDispatch::Variant(_)) && !untagged_dispatch(dispatch)
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
    pub(crate) fn compile_switch(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Compiled {
        let switch = &sw.decode(a);
        // OCaml's `compile_switch` builds `switch_cxt = enter_switch cxt`
        // and threads it into every case body and the default branch
        // (compiler/core/lam_compile.ml). Wrap the whole switch with
        // `with_switch_depth` so any nested `Lbreak`/`Lcontinue` knows it
        // must use a labeled JS break/continue to escape the loop.
        self.with_switch_depth(|this| this.compile_switch_inner(a, scrut, switch))
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

        if untagged_dispatch(&switch.sw_dispatch) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (scrut_prelude, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let mut prelude = vec![tmp_declaration(&mut self.j)];
            prelude.extend(scrut_prelude);
            prelude.extend(self.compile_untagged_variant_switch_assignment_statements(
                a, &tmp, scrut_expr, switch,
            ));
            return Compiled {
                prelude,
                expr: JE::var(tmp, &mut self.j),
            };
        }

        if named_dispatch(&switch.sw_dispatch) {
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

        // OCaml `compile_general_cases` only calls `Js_output.to_break_block`
        // for grouped cases (compiler/core/lam_compile.ml:610-624). The
        // switch default is `Js_output.output_as_block`
        // (compiler/core/lam_compile.ml:595-605), so it must not get the
        // case-only trailing `break`.
        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, &tmp, fallback);
            self.with_block_source_loc(a, fallback, block)
        });

        prelude.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));

        Compiled {
            prelude,
            expr: JE::var(tmp, &mut self.j),
        }
    }

    pub(crate) fn uses_untagged_variant_dispatch(&self, payload: &SwitchPayload) -> bool {
        untagged_dispatch(&payload.dispatch)
    }

    pub(crate) fn uses_named_variant_dispatch(&self, payload: &SwitchPayload) -> bool {
        named_dispatch(&payload.dispatch)
    }

    pub(crate) fn uses_untagged_variant_switch(&self, a: &LamArena, sw: Sw) -> bool {
        untagged_dispatch(&sw.payload(a).dispatch)
    }

    pub(crate) fn uses_named_variant_switch(&self, a: &LamArena, sw: Sw) -> bool {
        named_dispatch(&sw.payload(a).dispatch)
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
        tag.literal
            .as_ref()
            .map(Self::literal_tag_value)
            .unwrap_or_else(|| SwitchCaseTag::String(tag.name.to_string()))
    }

    fn literal_cases(&self, switch: &LamSwitch) -> Option<Vec<SwitchCaseTag>> {
        let SwitchDispatch::Variant(facts) = &switch.sw_dispatch else {
            return None;
        };
        Some(
            facts
                .literal_tags
                .iter()
                .map(Self::literal_tag_value)
                .collect(),
        )
    }

    /// Whether the variant has a `@as(null)` literal constructor.
    fn has_null_literal(&self, switch: &LamSwitch) -> bool {
        matches!(&switch.sw_dispatch, SwitchDispatch::Variant(facts)
            if facts.literal_tags.iter().any(|tag| matches!(tag, crate::types::VariantLiteralTag::Null)))
    }

    fn untagged_block_types<'a>(&self, switch: &'a LamSwitch) -> &'a [VariantBlockType] {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => &facts.block_types,
            SwitchDispatch::Direct => &[],
        }
    }

    fn block_type_switch_tag(block_type: &VariantBlockType) -> Option<SwitchCaseTag> {
        match block_type {
            VariantBlockType::String => Some(SwitchCaseTag::String("string".to_string())),
            VariantBlockType::Int | VariantBlockType::Float => {
                Some(SwitchCaseTag::String("number".to_string()))
            }
            VariantBlockType::Bigint => Some(SwitchCaseTag::String("bigint".to_string())),
            VariantBlockType::Boolean => Some(SwitchCaseTag::String("boolean".to_string())),
            VariantBlockType::Function => Some(SwitchCaseTag::String("function".to_string())),
            VariantBlockType::Object => Some(SwitchCaseTag::String("object".to_string())),
            VariantBlockType::Instance(_) | VariantBlockType::Unknown => None,
        }
    }

    fn literal_case_dispatch_test(&mut self, expr: Expr, switch: &LamSwitch) -> Option<Expr> {
        let literal_cases = self.literal_cases(switch)?;
        let block_cases = self.untagged_block_types(switch);
        if literal_cases.is_empty() || block_cases.is_empty() {
            return None;
        }

        fn bin(
            c: &mut LambdaCompiler,
            op: BinOp,
            lhs: (Expr, usize),
            rhs: (Expr, usize),
        ) -> (Expr, usize) {
            (JE::bin(op, lhs.0, rhs.0, &mut c.j), 1 + lhs.1 + rhs.1)
        }

        fn ocaml_literal_case_or(
            compiler: &mut LambdaCompiler,
            expr: Expr,
            cases: &[&SwitchCaseTag],
        ) -> (Expr, usize) {
            let mut reversed = cases.iter().rev().copied();
            let current_case = reversed.next().expect("literal cases are non-empty");
            let rest: Vec<_> = reversed.collect();
            let current = (compiler.switch_case_test(expr, current_case), 3usize);
            if rest.is_empty() {
                current
            } else {
                let rest = ocaml_literal_case_or(compiler, expr, &rest);
                bin(compiler, BinOp::Or, current, rest)
            }
        }

        fn ocaml_literal_fold_right_or(
            compiler: &mut LambdaCompiler,
            expr: Expr,
            cases: &[SwitchCaseTag],
        ) -> (Expr, usize) {
            let (first, others) = cases.split_first().expect("literal cases are non-empty");
            let mut acc = (compiler.switch_case_test(expr, first), 3usize);
            for literal in others.iter().rev() {
                let test = (compiler.switch_case_test(expr, literal), 3usize);
                acc = bin(compiler, BinOp::Or, test, acc);
            }
            acc
        }

        let literals_overlap_with_string = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::String(_)));
        let literals_overlap_with_number = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Int(_) | SwitchCaseTag::Float(_)));
        let literals_overlap_with_bigint = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::BigInt(_)));
        let literals_overlap_with_boolean = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Bool(_)));
        let literals_overlap_with_object = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Null));

        let with_literal_cases = {
            let literal_cases: Vec<_> = literal_cases.iter().collect();
            ocaml_literal_case_or(self, expr, &literal_cases)
        };
        let typeof_neq = |c: &mut LambdaCompiler, type_name: &str| {
            (
                raw_typeof_comparison(expr, BinOp::NotEqEq, type_name, &mut c.j),
                4usize,
            )
        };

        let is_not_block_case = |c: &mut LambdaCompiler,
                                 block_type: &VariantBlockType|
         -> (Expr, usize) {
            match block_type {
                VariantBlockType::String if !literals_overlap_with_string => {
                    typeof_neq(c, "string")
                }
                VariantBlockType::Int | VariantBlockType::Float
                    if !literals_overlap_with_number =>
                {
                    typeof_neq(c, "number")
                }
                VariantBlockType::Bigint if !literals_overlap_with_bigint => {
                    typeof_neq(c, "bigint")
                }
                VariantBlockType::Boolean if !literals_overlap_with_boolean => {
                    typeof_neq(c, "boolean")
                }
                VariantBlockType::Function => typeof_neq(c, "function"),
                VariantBlockType::Instance(name) => {
                    let instance_test = c.builtin_untagged_instance_test(expr, *name);
                    (JE::not(instance_test, &mut c.j), 3usize)
                }
                VariantBlockType::Object if !literals_overlap_with_object => {
                    typeof_neq(c, "object")
                }
                VariantBlockType::Object => {
                    let null_case = (c.switch_case_test(expr, &SwitchCaseTag::Null), 3usize);
                    let object = typeof_neq(c, "object");
                    bin(c, BinOp::Or, null_case, object)
                }
                VariantBlockType::String
                | VariantBlockType::Int
                | VariantBlockType::Float
                | VariantBlockType::Bigint
                | VariantBlockType::Boolean
                | VariantBlockType::Unknown => ocaml_literal_fold_right_or(c, expr, &literal_cases),
            }
        };

        let without_literal_cases = {
            let (last, rest) = block_cases.split_last().expect("block cases are non-empty");
            let mut acc = is_not_block_case(self, last);
            for block_case in rest.iter().rev() {
                let case = is_not_block_case(self, block_case);
                acc = bin(self, BinOp::And, case, acc);
            }
            acc
        };

        Some(if with_literal_cases.1 <= without_literal_cases.1 {
            with_literal_cases.0
        } else {
            without_literal_cases.0
        })
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

    fn untagged_block_cases<'a>(
        &self,
        switch: &'a LamSwitch,
    ) -> Option<Vec<(&'a crate::types::VariantBlock, Lam)>> {
        switch
            .sw_blocks
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(block)) => {
                    Some((block, *body))
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

    fn untagged_literal_and_block_defaults_match(&self, a: &LamArena, switch: &LamSwitch) -> bool {
        let failaction = switch.sw_failaction;
        let const_default = self.grouped_switch_default(switch.sw_consts_full, failaction);
        let block_default = self.grouped_switch_default(switch.sw_blocks_full, failaction);
        match (const_default, block_default) {
            (GroupedSwitchDefault::Complete, GroupedSwitchDefault::Complete)
            | (GroupedSwitchDefault::NonComplete, GroupedSwitchDefault::NonComplete) => true,
            (GroupedSwitchDefault::Default(lhs), GroupedSwitchDefault::Default(rhs)) => {
                a.eq_approx(lhs, rhs)
            }
            _ => false,
        }
    }

    fn variant_tag_name(&self, switch: &LamSwitch) -> String {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => facts.tag_name.clone(),
            SwitchDispatch::Direct => None,
        }
        .unwrap_or_else(|| "TAG".to_string())
    }

    fn builtin_untagged_typeof_test(&mut self, expr: Expr, type_name: &str) -> Expr {
        raw_typeof_comparison(expr, BinOp::EqEqEq, type_name, &mut self.j)
    }

    fn builtin_untagged_instance_test(
        &mut self,
        expr: Expr,
        instance: crate::types::VariantInstance,
    ) -> Expr {
        match instance {
            crate::types::VariantInstance::Array => {
                let array = JE::var(Ident::create_persistent("Array"), &mut self.j);
                let is_array = self.static_index(array, "isArray");
                JE::call(is_array, &[expr], CallInfo::default(), &mut self.j)
            }
            _ => JE::bin(
                BinOp::InstanceOf,
                expr,
                JE::var(Ident::create_persistent(instance.as_str()), &mut self.j),
                &mut self.j,
            ),
        }
    }

    fn builtin_untagged_block_test(
        &mut self,
        expr: Expr,
        case: &crate::types::VariantBlock,
        all_block_types: &[VariantBlockType],
        has_null_case: bool,
    ) -> Option<Expr> {
        let test = match case.block_type()? {
            VariantBlockType::String => self.builtin_untagged_typeof_test(expr, "string"),
            VariantBlockType::Int | VariantBlockType::Float => {
                self.builtin_untagged_typeof_test(expr, "number")
            }
            VariantBlockType::Bigint => self.builtin_untagged_typeof_test(expr, "bigint"),
            VariantBlockType::Boolean => self.builtin_untagged_typeof_test(expr, "boolean"),
            VariantBlockType::Function => self.builtin_untagged_typeof_test(expr, "function"),
            VariantBlockType::Instance(name) => self.builtin_untagged_instance_test(expr, *name),
            VariantBlockType::Object => {
                let mut test = self.builtin_untagged_typeof_test(expr, "object");
                if has_null_case {
                    test = JE::bin(
                        BinOp::And,
                        test,
                        JE::bin(BinOp::NotEqEq, expr, JE::null(&mut self.j), &mut self.j),
                        &mut self.j,
                    );
                }
                for other in all_block_types {
                    let VariantBlockType::Instance(name) = other else {
                        continue;
                    };
                    let instance_test = self.builtin_untagged_instance_test(expr, *name);
                    test = JE::bin(
                        BinOp::And,
                        test,
                        JE::not(instance_test, &mut self.j),
                        &mut self.j,
                    );
                }
                test
            }
            VariantBlockType::Unknown => return None,
        };
        Some(test)
    }

    /// Compute the null/array guard expression for an untagged-variant typeof
    /// switch (mirrors OCaml `lam_compile.ml` switch helper after upstream
    /// PRs ebed19abd / fbe7a7391 / ccdec51fc — #8251).
    ///
    /// When a typeof switch has an `"object"` case (because some variant arm
    /// is `VariantBlockType::Object`), null and arrays would otherwise match
    /// that case too (`typeof null === typeof [] === "object"`). Returns a
    /// guard expression that should be wrapped around the typeof switch to
    /// route null / array values to the default body instead.
    fn untagged_typeof_object_guard(
        &mut self,
        scrut: Expr,
        typeof_cases: &[(SwitchCaseTag, Lam)],
        runtime_test_cases: &[(&crate::types::VariantBlock, Lam)],
        all_block_types: &[VariantBlockType],
        has_null_case: bool,
    ) -> Option<Expr> {
        let has_object_typeof = typeof_cases
            .iter()
            .any(|(tag, _)| matches!(tag, SwitchCaseTag::String(s) if s == "object"));
        if !has_object_typeof {
            return None;
        }
        let clauses_have_array_case = runtime_test_cases.iter().any(|(case, _)| {
            matches!(
                case.block_type(),
                Some(VariantBlockType::Instance(
                    crate::types::VariantInstance::Array
                ))
            )
        });
        let type_has_array_case = all_block_types.iter().any(|t| {
            matches!(
                t,
                VariantBlockType::Instance(crate::types::VariantInstance::Array)
            )
        });
        let needs_null_guard = has_null_case;
        let needs_array_guard = type_has_array_case && !clauses_have_array_case;

        let null_check = |c: &mut LambdaCompiler| c.is_null_expr(scrut);
        let array_check = |c: &mut LambdaCompiler| {
            c.builtin_untagged_instance_test(scrut, crate::types::VariantInstance::Array)
        };

        match (needs_null_guard, needs_array_guard) {
            (true, true) => {
                let null = null_check(self);
                let array = array_check(self);
                Some(JE::bin(BinOp::Or, null, array, &mut self.j))
            }
            (true, false) => Some(null_check(self)),
            (false, true) => Some(array_check(self)),
            (false, false) => None,
        }
    }

    fn compile_untagged_block_switch_assignment_statements(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut_expr: Expr,
        switch: &LamSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(a, result, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_assignment(
            a,
            result,
            scrut_expr,
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch);
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_assign_to_target_block(a, result, *body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_assign_to_target_block(a, result, block_cases[0].1);
        }

        let has_unfiltered_runtime_test_cases = block_cases
            .iter()
            .any(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Instance(_))));
        let filtered_block_cases =
            self.filtered_switch_case_refs(a, &block_cases, self.block_switch_default(switch));
        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in filtered_block_cases {
            match case.block_type() {
                Some(VariantBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = !has_unfiltered_runtime_test_cases;

        // OCaml reference: compiler/core/lam_compile.ml:800-887 builds the
        // runtime-instance chain with a `typeof_switch` tail. That tail is
        // still emitted when default filtering leaves zero typeof clauses,
        // because `compile_general_cases` filters cases only after selecting
        // the general switch path (compiler/core/lam_compile.ml:567-630).
        let typeof_scrut = ocaml_typeof_expr(scrut_expr, &mut self.j);
        let typeof_default = self.block_switch_default(switch);
        let typeof_complete = self.block_switch_complete(switch);
        let small_tail = if allow_small_typeof_tail && !typeof_cases.is_empty() {
            self.compile_small_string_switch_assignment(
                a,
                result,
                typeof_scrut,
                &typeof_cases,
                typeof_default,
                typeof_complete,
            )
        } else {
            None
        };
        let mut tail = match small_tail {
            Some(block) => block,
            None => self.compile_named_string_switch_assignment_general(
                a,
                result,
                typeof_scrut,
                &typeof_cases,
                typeof_default,
            ),
        };

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                all_block_types,
                has_null_case,
            )
        {
            let default_body = self.block_switch_default(switch).map(|fallback| {
                let block = self.compile_assign_to_target_block(a, result, fallback);
                self.with_block_source_loc(a, fallback, block)
            });
            tail = match default_body {
                Some(default_block) => vec![JS::if_(guard, &default_block, &tail, &mut self.j)],
                None => vec![JS::if_(
                    JE::not(guard, &mut self.j),
                    &tail,
                    &Vec::new(),
                    &mut self.j,
                )],
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(scrut_expr, case, all_block_types, has_null_case)
                .expect("instance cases stay supported");
            tail = vec![JS::if_(
                test,
                &self.compile_assign_to_target_block(a, result, body),
                &tail,
                &mut self.j,
            )];
        }

        tail
    }

    fn compile_small_untagged_block_switch_assignment(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut_expr: Expr,
        switch: &LamSwitch,
        block_cases: &[(&crate::types::VariantBlock, Lam)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch);
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(a, result, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_assign_to_target_block(a, result, *body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                Some(vec![JS::if_(
                    cond,
                    &self.compile_assign_to_target_block(a, result, *body),
                    &default
                        .map(|fallback| {
                            let block = self.compile_assign_to_target_block(a, result, fallback);
                            self.with_block_source_loc(a, fallback, block)
                        })
                        .unwrap_or_default(),
                    &mut self.j,
                )])
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                Some(vec![JS::if_(
                    cond,
                    &self.compile_assign_to_target_block(a, result, *then_body),
                    &self.compile_assign_to_target_block(a, result, *else_body),
                    &mut self.j,
                )])
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_return_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| self.compile_return_block(a, fallback))
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_return(
            a,
            scrut_expr,
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch);
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_return_block(a, *body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_return_block(a, block_cases[0].1);
        }

        let has_unfiltered_runtime_test_cases = block_cases
            .iter()
            .any(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Instance(_))));
        let filtered_block_cases =
            self.filtered_switch_case_refs(a, &block_cases, self.block_switch_default(switch));
        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in filtered_block_cases {
            match case.block_type() {
                Some(VariantBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = !has_unfiltered_runtime_test_cases;

        // OCaml reference: compiler/core/lam_compile.ml:800-887 builds the
        // runtime-instance chain with a `typeof_switch` tail. That tail is
        // still emitted when default filtering leaves zero typeof clauses,
        // because `compile_general_cases` filters cases only after selecting
        // the general switch path (compiler/core/lam_compile.ml:567-630).
        let typeof_scrut = ocaml_typeof_expr(scrut_expr, &mut self.j);
        let mut tail = self.compile_named_string_switch_return_with_strategy(
            a,
            typeof_scrut,
            &typeof_cases,
            self.block_switch_default(switch),
            self.block_switch_complete(switch),
            allow_small_typeof_tail && !typeof_cases.is_empty(),
        );

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                all_block_types,
                has_null_case,
            )
        {
            let default_body = self
                .block_switch_default(switch)
                .map(|fallback| self.compile_return_block(a, fallback));
            tail = match default_body {
                Some(default_block)
                    if self.return_unit_stack.last().copied() == Some(true)
                        && (default_block.is_empty()
                            || self.is_unit_undefined_return_block(&default_block)) =>
                {
                    let mut block = vec![JS::new(
                        StmtKind::If(
                            guard,
                            JS::list(
                                &[JS::return_(JE::undefined(true, &mut self.j), &mut self.j)],
                                &mut self.j,
                            ),
                            self.j.empty_block(),
                        ),
                        &mut self.j,
                    )];
                    block.extend(tail);
                    block
                }
                Some(default_block) => self.normalized_if_block(guard, default_block, tail),
                None => {
                    let ret = self.return_unit_block();
                    self.normalized_if_block(guard, ret, tail)
                }
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(scrut_expr, case, all_block_types, has_null_case)
                .expect("instance cases stay supported");
            let body = self.compile_return_block(a, body);
            let body = self.normalize_runtime_test_return_body(body);
            tail = self.normalized_if_block(test, body, tail);
        }

        tail
    }

    fn is_unit_undefined_return_block(&mut self, block: &Block) -> bool {
        let block = self.peel_single_block(block);
        strict_single_return_expr(&self.j, &block)
            .is_some_and(|e| matches!(self.j.ek(e), ExprKind::Undefined { is_unit: true }))
    }

    /// `[return undefined]` for a unit-returning function.
    pub(crate) fn return_unit_block(&mut self) -> Block {
        let undefined = JE::undefined(true, &mut self.j);
        vec![JS::return_(undefined, &mut self.j)]
    }

    fn compile_small_untagged_block_switch_return(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
        block_cases: &[(&crate::types::VariantBlock, Lam)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch);
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(a, fallback))
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_return_block(a, *body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_return_block(a, *body);
                let then_block = self.normalize_runtime_test_return_body(then_block);
                let else_block = default
                    .map(|fallback| self.compile_return_block(a, fallback))
                    .unwrap_or_default();
                Some(self.normalized_if_block(cond, then_block, else_block))
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_return_block(a, *then_body);
                let then_block = self.normalize_runtime_test_return_body(then_block);
                let else_block = self.compile_return_block(a, *else_body);
                Some(self.normalized_if_block(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_effect_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| {
                    let block = self.compile_effect_block(a, fallback);
                    self.with_block_source_loc(a, fallback, block)
                })
                .unwrap_or_default();
        };
        let all_block_types = self.untagged_block_types(switch);
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_effect_block(a, *body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_effect_block(a, block_cases[0].1);
        }
        if let Some(block) = self.compile_small_untagged_block_switch_effect(
            a,
            scrut_expr,
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }

        let has_unfiltered_runtime_test_cases = block_cases
            .iter()
            .any(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Instance(_))));
        let filtered_block_cases =
            self.filtered_switch_case_refs(a, &block_cases, self.block_switch_default(switch));
        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in filtered_block_cases {
            match case.block_type() {
                Some(VariantBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = !has_unfiltered_runtime_test_cases;

        // OCaml reference: compiler/core/lam_compile.ml:800-887 builds the
        // runtime-instance chain with a `typeof_switch` tail. That tail is
        // still emitted when default filtering leaves zero typeof clauses,
        // because `compile_general_cases` filters cases only after selecting
        // the general switch path (compiler/core/lam_compile.ml:567-630).
        let typeof_scrut = ocaml_typeof_expr(scrut_expr, &mut self.j);
        let mut tail = self.compile_named_string_switch_effect_with_strategy(
            a,
            typeof_scrut,
            &typeof_cases,
            self.block_switch_default(switch),
            self.block_switch_complete(switch),
            allow_small_typeof_tail && !typeof_cases.is_empty(),
        );

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                all_block_types,
                has_null_case,
            )
        {
            let default_body = self.block_switch_default(switch).map(|fallback| {
                let block = self.compile_effect_block(a, fallback);
                self.with_block_source_loc(a, fallback, block)
            });
            tail = match default_body {
                Some(default_block) => vec![JS::if_(guard, &default_block, &tail, &mut self.j)],
                None if self.return_unit_stack.last().copied() == Some(true) => {
                    let ret = self.return_unit_block();
                    self.normalized_if_block(guard, ret, tail)
                }
                None => vec![JS::if_(
                    JE::not(guard, &mut self.j),
                    &tail,
                    &Vec::new(),
                    &mut self.j,
                )],
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(scrut_expr, case, all_block_types, has_null_case)
                .expect("instance cases stay supported");
            let body_block = self.compile_effect_block(a, body);
            tail = self.compile_effect_if(test, body_block, tail);
        }

        tail
    }

    fn compile_small_untagged_block_switch_effect(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
        block_cases: &[(&crate::types::VariantBlock, Lam)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch);
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_effect_block(a, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_effect_block(a, *body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(a, *body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_effect_block(a, fallback);
                        self.with_block_source_loc(a, fallback, block)
                    })
                    .unwrap_or_default();
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(a, *then_body);
                let else_block = self.compile_effect_block(a, *else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_untagged_variant_switch_assignment_statements(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(a, switch)
        {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_assignment_statements(
                a,
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_assignment_statements(
                a,
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_assignment(
                a,
                result,
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path (const cases + block cases): null is dispatched by the
        // outer const_branch, so when we fall into block_branch, x cannot be
        // null. Match OCaml's `compile_cases` default `has_null_case = false`
        // in the else branch of lam_compile.ml:755.
        let block_branch = self.compile_untagged_block_switch_assignment_statements(
            a, result, scrut_expr, switch, false,
        );

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr, switch) else {
            return block_branch;
        };

        if const_branch.is_empty() {
            vec![JS::if_(
                JE::not(dispatch_test, &mut self.j),
                &block_branch,
                &[],
                &mut self.j,
            )]
        } else if block_branch.is_empty() {
            vec![JS::if_(dispatch_test, &const_branch, &[], &mut self.j)]
        } else {
            vec![JS::if_(
                dispatch_test,
                &const_branch,
                &block_branch,
                &mut self.j,
            )]
        }
    }

    pub(crate) fn compile_untagged_variant_switch_return_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(a, switch)
        {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_return_statements(
                a,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_return_statements(
                a,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_return(
                a,
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path: null handled by const_branch; block_branch sees non-null x.
        let block_branch =
            self.compile_untagged_block_switch_return_statements(a, scrut_expr, switch, false);

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr, switch) else {
            return block_branch;
        };

        if const_branch.is_empty() {
            if self.return_unit_stack.last().copied() == Some(true) {
                let ret = self.return_unit_block();
                self.normalized_if_block(dispatch_test, ret, block_branch)
            } else {
                vec![JS::if_(
                    JE::not(dispatch_test, &mut self.j),
                    &block_branch,
                    &[],
                    &mut self.j,
                )]
            }
        } else if block_branch.is_empty() {
            vec![JS::if_(dispatch_test, &const_branch, &[], &mut self.j)]
        } else {
            vec![JS::if_(
                dispatch_test,
                &const_branch,
                &block_branch,
                &mut self.j,
            )]
        }
    }

    pub(crate) fn compile_untagged_variant_switch_effect_statements(
        &mut self,
        a: &mut LamArena,
        scrut_expr: Expr,
        switch: &LamSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(a, switch)
        {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_effect_statements(
                a,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self.has_null_literal(switch);
            return self.compile_untagged_block_switch_effect_statements(
                a,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_effect(
                a,
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path: null handled by const_branch; block_branch sees non-null x.
        let block_branch =
            self.compile_untagged_block_switch_effect_statements(a, scrut_expr, switch, false);

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr, switch) else {
            return block_branch;
        };

        // An empty branch still needs the dispatch test around the other one:
        // `S.if_ test const_branch block_branch` (js_stmt_make.ml:248-262)
        // turns `if (test) {} else {b}` into `if (!test) {b}`.
        if const_branch.is_empty() && block_branch.is_empty() {
            Vec::new()
        } else {
            self.compile_effect_if(dispatch_test, const_branch, block_branch)
        }
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

    fn variant_object_test(&mut self, expr: Expr) -> Expr {
        raw_typeof_comparison(expr, BinOp::EqEqEq, "object", &mut self.j)
    }

    fn variant_non_object_test(&mut self, expr: Expr) -> Expr {
        raw_typeof_comparison(expr, BinOp::NotEqEq, "object", &mut self.j)
    }

    fn dispatch_named_variant_branches(
        &mut self,
        scrut_expr: Expr,
        const_branch: Block,
        block_branch: Block,
    ) -> Block {
        if const_branch.is_empty() {
            vec![JS::if_(
                self.variant_object_test(scrut_expr),
                &block_branch,
                &[],
                &mut self.j,
            )]
        } else if block_branch.is_empty() {
            vec![JS::if_(
                self.variant_non_object_test(scrut_expr),
                &const_branch,
                &[],
                &mut self.j,
            )]
        } else {
            vec![JS::if_(
                self.variant_non_object_test(scrut_expr),
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
                // OCaml's `S.if_ cond [] []` collapses to `S.exp cond`
                // (js_stmt_make.ml:242 + 45-53). Preserves bare comparisons
                // like `tmp === null;` that come from a switch where every
                // dispatched arm falls through to the same continuation.
                let mut block = vec![];
                push_s_exp(&mut self.j, &mut block, cond);
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

    fn peel_single_block(&self, block: &[Stmt]) -> Block {
        match block {
            [stmt] => match self.j.sk(*stmt) {
                StmtKind::Block(inner) => self.peel_single_block(self.j.stmts(inner)),
                _ => block.to_vec(),
            },
            _ => block.to_vec(),
        }
    }

    pub(crate) fn normalize_runtime_test_return_body(&mut self, block: Block) -> Block {
        let block = self.peel_single_block(&block);
        self.shared_trailing_return_guard_block(&block)
            .unwrap_or(block)
    }

    fn shared_trailing_return_guard_block(&mut self, block: &Block) -> Option<Block> {
        let (first, rest) = block.split_first()?;
        let StmtKind::If(cond, then_block, else_block) = self.j.sk(*first) else {
            return None;
        };
        if !self.j.stmts(else_block).is_empty() || rest.is_empty() {
            return None;
        }

        let then_block = self.j.block_vec(then_block);
        let then_return = trailing_return_expression(&self.j, &then_block)?;
        let else_return = trailing_return_expression(&self.j, rest)?;
        if !ocaml_eq_expression(&self.j, then_return, else_return) {
            return None;
        }
        if then_block.len() != 2 || rest.len() != 2 {
            return None;
        }

        let then_block = then_block[..then_block.len() - 1].to_vec();
        let else_block = rest[..rest.len() - 1].to_vec();
        if then_block.is_empty() || else_block.is_empty() {
            return None;
        }

        let then_list = JS::list(&then_block, &mut self.j);
        let else_list = JS::list(&else_block, &mut self.j);
        Some(vec![
            JS::new(StmtKind::If(cond, then_list, else_list), &mut self.j),
            JS::return_(then_return, &mut self.j),
        ])
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
        let filtered_cases = self.filtered_switch_case_refs(a, cases, default);
        let clauses = stable_group_switch_cases(a, filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| StringClauseInfo {
                tag_type: tag,
                clause: if is_last {
                    Clause {
                        source_loc: self.source_loc_of_lam(a, body),
                        body: {
                            let body = {
                                let value_block = self.compile_switch_value_block(a, result, body);
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
            })
            .collect();

        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, result, fallback);
            self.with_block_source_loc(a, fallback, block)
        });
        vec![JS::string_switch(
            test,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        )]
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
                    push_s_exp(&mut self.j, &mut prefix, test_expr);
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

        let filtered_cases = self.filtered_switch_case_refs(a, cases, default);
        let grouped_cases = stable_group_switch_cases(a, filtered_cases, |_, _| true);
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
                let compiled_body = self.compile_hoisted_named_string_return_tail(a, *body);
                let hoist_shared_tail = group_start != group_end
                    && group_end + 1 == grouped_cases.len()
                    && self.should_hoist_grouped_named_string_return_tail(a, *body)
                    && !compiled_body.is_empty()
                    && block_terminates(&self.j, &compiled_body);

                for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                    clauses.push(StringClauseInfo {
                        tag_type: tag.clone(),
                        clause: self.empty_switch_case_clause_for(a, *case_lam),
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
                        let should_break =
                            self.return_case_needs_break_like_ocaml(a, *body, &compiled_body);
                        Clause {
                            source_loc: self.source_loc_of_lam(a, *body),
                            body: {
                                let body = self.with_block_source_loc(a, *body, compiled_body);
                                JS::list(&body, &mut self.j)
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
            self.grouped_return_string_clauses(a, grouped_cases, |tag| tag)
        };

        let default_block = default
            .map(|fallback| self.compile_return_block(a, fallback))
            .filter(|body| !body.is_empty());
        let mut block = vec![JS::string_switch(
            test,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        )];
        if let Some(tail) = shared_tail {
            block.extend(tail);
        }
        block
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
            let compiled_body = self.compile_tail_loop_return_block(a, *body, tail_loop);
            let group_falls_through = compiled_body.is_empty();
            // Mirror `compile_general_cases` + `Js_output.to_break_block`
            // (compiler/core/lam_compile.ml:610-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = self.return_case_needs_break_like_ocaml(a, *body, &compiled_body);

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

        let filtered_cases = self.filtered_switch_case_refs(a, cases, default);
        let clauses = self.grouped_tail_loop_return_string_clauses(
            a,
            stable_group_switch_cases(a, filtered_cases, |_, _| true),
            |tag| tag,
            tail_loop,
        );

        let default_block = default
            .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
            .filter(|body| !body.is_empty());

        vec![JS::string_switch(
            test,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        )]
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

        let filtered_cases = self.filtered_switch_case_refs(a, cases, default);
        let clauses: Vec<_> = stable_group_switch_cases(a, filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let source_loc = self.source_loc_of_lam(a, body);
                    let body_block = self.compile_effect_block(a, body);
                    let body = self.with_block_source_loc(a, body, body_block);
                    Clause {
                        source_loc,
                        should_break: !block_terminates(&self.j, &body),
                        body: JS::list(&body, &mut self.j),
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(a, body)
                };
                StringClauseInfo {
                    tag_type: tag,
                    clause,
                }
            })
            .collect();

        let default_block = default
            .map(|fallback| {
                let block = self.compile_effect_block(a, fallback);
                self.with_block_source_loc(a, fallback, block)
            })
            .filter(|body| !body.is_empty());
        vec![JS::string_switch(
            test,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        )]
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            let test = self.variant_non_object_test(scrut_expr);
            self.compile_effect_if(test, const_branch, block_branch)
        }
    }
}
