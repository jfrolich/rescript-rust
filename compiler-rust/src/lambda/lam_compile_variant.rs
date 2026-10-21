//! Variant and switch compilation.
//!
//! Port of `js_of_lam_variant.ml` + variant/switch compilation logic.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{ocaml_typeof_expr, raw_typeof_comparison};
use super::js_stmt_make::{block_terminates, strict_single_return_expr};
use super::lam_coercion::push_s_exp;
use super::lam_compile::{
    Compiled, GroupedSwitchDefault, LambdaCompiler, TailLoopState, trailing_return_expression,
};
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, Number};
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Expression, ExpressionDesc, Statement, StatementDesc,
    StringClause, VariableDeclaration, expression_has_no_side_effects, ocaml_eq_expression,
};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{Lambda, LambdaSwitch, SwitchCaseTag, SwitchDispatch, SwitchKey};
use crate::types::VariantBlockType;

pub(crate) fn empty_switch_case_clause() -> CaseClause {
    CaseClause {
        source_loc: None,
        body: vec![],
        should_break: false,
        comment: None,
    }
}

pub(crate) fn stable_group_switch_cases<'a, T: Clone, F>(
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
        let mut placed = false;
        for group in &mut groups {
            let Some((head_tag, head_lam)) = group.first() else {
                continue;
            };
            if merge_cases(&tag, head_tag) && super::lambda_eq_approx(lam, head_lam) {
                group.insert(0, (tag.clone(), lam));
                placed = true;
                break;
            }
        }
        if !placed {
            groups.push(vec![(tag, lam)]);
        }
    }

    groups.reverse();

    let mut grouped = Vec::with_capacity(groups.iter().map(Vec::len).sum());
    for group in groups {
        let last_idx = group.len().saturating_sub(1);
        for (idx, (tag, lam)) in group.into_iter().enumerate() {
            grouped.push((tag, lam, idx == last_idx));
        }
    }

    grouped
}

pub(crate) fn is_builtin_untagged_switch_name(name: &str) -> bool {
    matches!(
        name,
        "Null"
            | "Undefined"
            | "Boolean"
            | "String"
            | "Number"
            | "BigInt"
            | "Object"
            | "Array"
            | "Function"
            | "ArrayBuffer"
            | "BigInt64Array"
            | "BigUint64Array"
            | "Blob"
            | "DataView"
            | "Date"
            | "File"
            | "Float32Array"
            | "Float64Array"
            | "Int16Array"
            | "Int32Array"
            | "Int8Array"
            | "Promise"
            | "RegExp"
            | "Set"
            | "Map"
            | "Uint16Array"
            | "Uint32Array"
            | "Uint8Array"
            | "Uint8ClampedArray"
            | "WeakSet"
            | "WeakMap"
    )
}

impl LambdaCompiler {
    pub(crate) fn compile_switch(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Compiled {
        // OCaml's `compile_switch` builds `switch_cxt = enter_switch cxt`
        // and threads it into every case body and the default branch
        // (compiler/core/lam_compile.ml). Wrap the whole switch with
        // `with_switch_depth` so any nested `Lbreak`/`Lcontinue` knows it
        // must use a labeled JS break/continue to escape the loop.
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

        if self.uses_untagged_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (scrut_prelude, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let mut prelude = vec![tmp_declaration()];
            prelude.extend(scrut_prelude);
            prelude.extend(
                self.compile_untagged_variant_switch_assignment_statements(
                    &tmp, scrut_expr, switch,
                ),
            );
            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

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

    pub(crate) fn uses_untagged_variant_switch(&self, switch: &LambdaSwitch) -> bool {
        matches!(&switch.sw_dispatch, SwitchDispatch::Variant(facts) if !facts.block_types.is_empty())
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
        tag.literal
            .as_ref()
            .map(Self::literal_tag_value)
            .unwrap_or_else(|| SwitchCaseTag::String(tag.name.clone()))
    }

    fn block_type_value(block: &crate::types::VariantBlockType) -> VariantBlockType {
        block.clone()
    }

    fn literal_cases(&self, switch: &LambdaSwitch) -> Option<Vec<SwitchCaseTag>> {
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

    fn untagged_block_types(&self, switch: &LambdaSwitch) -> Option<Vec<VariantBlockType>> {
        let SwitchDispatch::Variant(facts) = &switch.sw_dispatch else {
            return None;
        };
        Some(
            facts
                .block_types
                .iter()
                .map(Self::block_type_value)
                .collect(),
        )
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

    fn literal_case_dispatch_test(
        &self,
        expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Expression> {
        let literal_cases = self.literal_cases(switch)?;
        let block_cases = self.untagged_block_types(switch)?;
        if literal_cases.is_empty() || block_cases.is_empty() {
            return None;
        }

        fn bin(
            op: BinOp,
            lhs: (Expression, usize),
            rhs: (Expression, usize),
        ) -> (Expression, usize) {
            (Expression::bin(op, lhs.0, rhs.0), 1 + lhs.1 + rhs.1)
        }

        fn ocaml_literal_case_or(
            compiler: &LambdaCompiler,
            expr: &Expression,
            cases: &[&SwitchCaseTag],
        ) -> (Expression, usize) {
            let mut reversed = cases.iter().rev().copied();
            let current_case = reversed.next().expect("literal cases are non-empty");
            let rest: Vec<_> = reversed.collect();
            let current = (
                compiler.switch_case_test(expr.clone(), current_case),
                3usize,
            );
            if rest.is_empty() {
                current
            } else {
                bin(
                    BinOp::Or,
                    current,
                    ocaml_literal_case_or(compiler, expr, &rest),
                )
            }
        }

        fn ocaml_literal_fold_right_or(
            compiler: &LambdaCompiler,
            expr: &Expression,
            cases: &[SwitchCaseTag],
        ) -> (Expression, usize) {
            let (first, others) = cases.split_first().expect("literal cases are non-empty");
            let mut acc = (compiler.switch_case_test(expr.clone(), first), 3usize);
            for literal in others.iter().rev() {
                acc = bin(
                    BinOp::Or,
                    (compiler.switch_case_test(expr.clone(), literal), 3usize),
                    acc,
                );
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

        let literal_case = |tag: &SwitchCaseTag| (self.switch_case_test(expr.clone(), tag), 3usize);
        let with_literal_cases = {
            let literal_cases: Vec<_> = literal_cases.iter().collect();
            ocaml_literal_case_or(self, &expr, &literal_cases)
        };
        let overlap_literal_disjunction =
            || ocaml_literal_fold_right_or(self, &expr, &literal_cases);
        let typeof_neq = |type_name: &str| {
            (
                raw_typeof_comparison(expr.clone(), BinOp::NotEqEq, type_name),
                4usize,
            )
        };

        let is_not_block_case = |block_type: &VariantBlockType| -> (Expression, usize) {
            match block_type {
                VariantBlockType::String if !literals_overlap_with_string => typeof_neq("string"),
                VariantBlockType::Int | VariantBlockType::Float
                    if !literals_overlap_with_number =>
                {
                    typeof_neq("number")
                }
                VariantBlockType::Bigint if !literals_overlap_with_bigint => typeof_neq("bigint"),
                VariantBlockType::Boolean if !literals_overlap_with_boolean => {
                    typeof_neq("boolean")
                }
                VariantBlockType::Function => typeof_neq("function"),
                VariantBlockType::Instance(name) => {
                    let instance_test = self
                        .builtin_untagged_instance_test(expr.clone(), name.as_str())
                        .expect("instance-backed block types stay supported");
                    (Expression::not(instance_test), 3usize)
                }
                VariantBlockType::Object if !literals_overlap_with_object => typeof_neq("object"),
                VariantBlockType::Object => bin(
                    BinOp::Or,
                    literal_case(&SwitchCaseTag::Null),
                    typeof_neq("object"),
                ),
                VariantBlockType::String
                | VariantBlockType::Int
                | VariantBlockType::Float
                | VariantBlockType::Bigint
                | VariantBlockType::Boolean
                | VariantBlockType::Unknown => overlap_literal_disjunction(),
            }
        };

        let without_literal_cases = {
            let (last, rest) = block_cases.split_last().expect("block cases are non-empty");
            let mut acc = is_not_block_case(last);
            for block_case in rest.iter().rev() {
                acc = bin(BinOp::And, is_not_block_case(block_case), acc);
            }
            acc
        };

        Some(if with_literal_cases.1 <= without_literal_cases.1 {
            with_literal_cases.0
        } else {
            without_literal_cases.0
        })
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

    fn untagged_block_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(&'a crate::types::VariantBlock, &'a Lambda)>> {
        switch
            .sw_blocks
            .iter()
            .map(|(key, body)| match key {
                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(block)) => {
                    Some((block, body))
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

    fn untagged_literal_and_block_defaults_match(&self, switch: &LambdaSwitch) -> bool {
        let failaction = switch.sw_failaction.as_deref();
        let const_default = self.grouped_switch_default(switch.sw_consts_full, failaction);
        let block_default = self.grouped_switch_default(switch.sw_blocks_full, failaction);
        match (const_default, block_default) {
            (GroupedSwitchDefault::Complete, GroupedSwitchDefault::Complete)
            | (GroupedSwitchDefault::NonComplete, GroupedSwitchDefault::NonComplete) => true,
            (GroupedSwitchDefault::Default(lhs), GroupedSwitchDefault::Default(rhs)) => {
                super::lambda_eq_approx(lhs, rhs)
            }
            _ => false,
        }
    }

    fn variant_tag_name(&self, switch: &LambdaSwitch) -> String {
        match &switch.sw_dispatch {
            SwitchDispatch::Variant(facts) => facts.tag_name.clone(),
            SwitchDispatch::Direct => None,
        }
        .unwrap_or_else(|| "TAG".to_string())
    }

    fn builtin_untagged_typeof_test(&self, expr: Expression, type_name: &str) -> Expression {
        raw_typeof_comparison(expr, BinOp::EqEqEq, type_name)
    }

    fn builtin_untagged_instance_test(
        &self,
        expr: Expression,
        case_name: &str,
    ) -> Option<Expression> {
        match case_name {
            "Array" => Some(Expression::call(
                self.static_index(
                    Expression::var(Ident::create_persistent("Array")),
                    "isArray",
                ),
                vec![expr],
                CallInfo::default(),
            )),
            "ArrayBuffer" | "BigInt64Array" | "BigUint64Array" | "Blob" | "DataView" | "Date"
            | "File" | "Float32Array" | "Float64Array" | "Int16Array" | "Int32Array"
            | "Int8Array" | "Promise" | "RegExp" | "Set" | "Map" | "Uint16Array"
            | "Uint32Array" | "Uint8Array" | "Uint8ClampedArray" | "WeakSet" | "WeakMap" => {
                Some(Expression::bin(
                    BinOp::InstanceOf,
                    expr,
                    Expression::var(Ident::create_persistent(case_name)),
                ))
            }
            _ => None,
        }
    }

    fn builtin_untagged_block_test(
        &self,
        expr: Expression,
        case: &crate::types::VariantBlock,
        all_block_types: &[VariantBlockType],
        has_null_case: bool,
    ) -> Option<Expression> {
        let test = match case.block_type()? {
            VariantBlockType::String => self.builtin_untagged_typeof_test(expr, "string"),
            VariantBlockType::Int | VariantBlockType::Float => {
                self.builtin_untagged_typeof_test(expr, "number")
            }
            VariantBlockType::Bigint => self.builtin_untagged_typeof_test(expr, "bigint"),
            VariantBlockType::Boolean => self.builtin_untagged_typeof_test(expr, "boolean"),
            VariantBlockType::Function => self.builtin_untagged_typeof_test(expr, "function"),
            VariantBlockType::Instance(name) => {
                self.builtin_untagged_instance_test(expr, name.as_str())?
            }
            VariantBlockType::Object => {
                let mut test = self.builtin_untagged_typeof_test(expr.clone(), "object");
                if has_null_case {
                    test = Expression::bin(
                        BinOp::And,
                        test,
                        Expression::bin(BinOp::NotEqEq, expr.clone(), Expression::null()),
                    );
                }
                for other in all_block_types {
                    let VariantBlockType::Instance(name) = other else {
                        continue;
                    };
                    if let Some(instance_test) =
                        self.builtin_untagged_instance_test(expr.clone(), name.as_str())
                    {
                        test = Expression::bin(BinOp::And, test, Expression::not(instance_test));
                    }
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
        &self,
        scrut: &Expression,
        typeof_cases: &[(SwitchCaseTag, &Lambda)],
        runtime_test_cases: &[(&crate::types::VariantBlock, &Lambda)],
        all_block_types: &[VariantBlockType],
        has_null_case: bool,
    ) -> Option<Expression> {
        let has_object_typeof = typeof_cases
            .iter()
            .any(|(tag, _)| matches!(tag, SwitchCaseTag::String(s) if s == "object"));
        if !has_object_typeof {
            return None;
        }
        let clauses_have_array_case = runtime_test_cases.iter().any(|(case, _)| {
            matches!(case.block_type(), Some(VariantBlockType::Instance(name)) if name.as_str() == "Array")
        });
        let type_has_array_case = all_block_types
            .iter()
            .any(|t| matches!(t, VariantBlockType::Instance(name) if name.as_str() == "Array"));
        let needs_null_guard = has_null_case;
        let needs_array_guard = type_has_array_case && !clauses_have_array_case;

        let null_check = || self.is_null_expr(scrut.clone());
        let array_check = || {
            self.builtin_untagged_instance_test(scrut.clone(), "Array")
                .expect("Array instance test always available")
        };

        match (needs_null_guard, needs_array_guard) {
            (true, true) => Some(Expression::bin(BinOp::Or, null_check(), array_check())),
            (true, false) => Some(null_check()),
            (false, true) => Some(array_check()),
            (false, false) => None,
        }
    }

    fn compile_builtin_untagged_block_chain<F>(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&crate::types::VariantBlock, &Lambda)],
        default_block: Block,
        mut build_body: F,
    ) -> Option<Block>
    where
        F: FnMut(&mut Self, &Lambda) -> Block,
    {
        let const_cases = self.named_const_cases(switch)?;
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if const_cases.is_empty() && block_cases.is_empty() {
            return Some(default_block);
        }

        if const_cases.is_empty()
            && self.block_switch_complete(switch)
            && block_cases.len() == 1
            && default_block.is_empty()
            && matches!(
                block_cases[0].0.block_type(),
                Some(VariantBlockType::Unknown)
            )
        {
            return Some(build_body(self, block_cases[0].1));
        }

        let has_null_case = const_cases
            .iter()
            .any(|(tag, _)| matches!(tag, SwitchCaseTag::Null));
        let mut current_else = default_block;
        for (case, body) in block_cases.iter().rev() {
            let body_block = build_body(self, body);
            if matches!(case.block_type(), Some(VariantBlockType::Unknown)) {
                current_else = body_block;
                continue;
            }
            let test = self.builtin_untagged_block_test(
                scrut_expr.clone(),
                case,
                &all_block_types,
                has_null_case,
            )?;
            current_else = vec![Statement::if_(test, body_block, current_else)];
        }
        for (tag, body) in const_cases.iter().rev() {
            current_else = vec![Statement::if_(
                self.switch_case_test(scrut_expr.clone(), tag),
                build_body(self, body),
                current_else,
            )];
        }
        Some(current_else)
    }

    fn compile_builtin_untagged_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| {
                let block = self.compile_assign_to_target_block(result, fallback);
                self.with_block_source_loc(fallback, block)
            })
            .unwrap_or_default();
        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_assign_to_target_block(result, body),
        )
    }

    fn compile_builtin_untagged_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| self.compile_return_block(fallback))
            .unwrap_or_default();
        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_return_block(body),
        )
    }

    fn compile_builtin_untagged_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| {
                let block = self.compile_effect_block(fallback);
                self.with_block_source_loc(fallback, block)
            })
            .unwrap_or_default();

        let mut has_effectful_case = !default_block.is_empty();
        for (_, body) in &block_cases {
            if !self.compile_effect_block(body).is_empty() {
                has_effectful_case = true;
                break;
            }
        }
        if !has_effectful_case {
            return Some(vec![]);
        }

        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_effect_block(body),
        )
    }

    fn compile_untagged_block_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| {
                    let block = self.compile_assign_to_target_block(result, fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_assignment(
            result,
            scrut_expr.clone(),
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_assign_to_target_block(result, body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_assign_to_target_block(result, block_cases[0].1);
        }

        let has_unfiltered_runtime_test_cases = block_cases
            .iter()
            .any(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Instance(_))));
        let filtered_block_cases =
            self.filtered_switch_case_refs(&block_cases, self.block_switch_default(switch));
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
        let mut tail = self.compile_named_string_switch_assignment_with_strategy(
            result,
            ocaml_typeof_expr(scrut_expr.clone()),
            &typeof_cases,
            self.block_switch_default(switch),
            self.block_switch_complete(switch),
            allow_small_typeof_tail && !typeof_cases.is_empty(),
        );

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                &scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                &all_block_types,
                has_null_case,
            )
        {
            let default_body = self.block_switch_default(switch).map(|fallback| {
                let block = self.compile_assign_to_target_block(result, fallback);
                self.with_block_source_loc(fallback, block)
            });
            tail = match default_body {
                Some(default_block) => vec![Statement::if_(guard, default_block, tail)],
                None => vec![Statement::if_(Expression::not(guard), tail, Vec::new())],
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            tail = vec![Statement::if_(
                test,
                self.compile_assign_to_target_block(result, body),
                tail,
            )];
        }

        tail
    }

    fn compile_small_untagged_block_switch_assignment(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&crate::types::VariantBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_assign_to_target_block(result, fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_assign_to_target_block(result, body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(vec![Statement::if_(
                    cond,
                    self.compile_assign_to_target_block(result, body),
                    default
                        .map(|fallback| {
                            let block = self.compile_assign_to_target_block(result, fallback);
                            self.with_block_source_loc(fallback, block)
                        })
                        .unwrap_or_default(),
                )])
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(vec![Statement::if_(
                    cond,
                    self.compile_assign_to_target_block(result, then_body),
                    self.compile_assign_to_target_block(result, else_body),
                )])
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_return(
            scrut_expr.clone(),
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_return_block(body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_return_block(block_cases[0].1);
        }

        let has_unfiltered_runtime_test_cases = block_cases
            .iter()
            .any(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Instance(_))));
        let filtered_block_cases =
            self.filtered_switch_case_refs(&block_cases, self.block_switch_default(switch));
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
        let mut tail = self.compile_named_string_switch_return_with_strategy(
            ocaml_typeof_expr(scrut_expr.clone()),
            &typeof_cases,
            self.block_switch_default(switch),
            self.block_switch_complete(switch),
            allow_small_typeof_tail && !typeof_cases.is_empty(),
        );

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                &scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                &all_block_types,
                has_null_case,
            )
        {
            let default_body = self
                .block_switch_default(switch)
                .map(|fallback| self.compile_return_block(fallback));
            tail = match default_body {
                Some(default_block)
                    if self.return_unit_stack.last().copied() == Some(true)
                        && (default_block.is_empty()
                            || Self::is_unit_undefined_return_block(&default_block)) =>
                {
                    let mut block = vec![Statement::new(StatementDesc::If(
                        guard,
                        vec![Statement::return_(Expression::undefined(true))],
                        Vec::new(),
                    ))];
                    block.extend(tail);
                    block
                }
                Some(default_block) => Self::normalized_if_block(guard, default_block, tail),
                None => Self::normalized_if_block(
                    guard,
                    vec![Statement::return_(Expression::undefined(true))],
                    tail,
                ),
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            tail = Self::normalized_if_block(
                test,
                Self::normalize_runtime_test_return_body(self.compile_return_block(body)),
                tail,
            );
        }

        tail
    }

    fn is_unit_undefined_return_block(block: &Block) -> bool {
        let block = Self::peel_single_block_statement(block.clone());
        matches!(
            strict_single_return_expr(&block),
            Some(Expression {
                desc: ExpressionDesc::Undefined { is_unit: true },
                ..
            })
        )
    }

    fn compile_small_untagged_block_switch_return(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&crate::types::VariantBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_return_block(body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(Self::normalized_if_block(
                    cond,
                    Self::normalize_runtime_test_return_body(self.compile_return_block(body)),
                    default
                        .map(|fallback| self.compile_return_block(fallback))
                        .unwrap_or_default(),
                ))
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(Self::normalized_if_block(
                    cond,
                    Self::normalize_runtime_test_return_body(self.compile_return_block(then_body)),
                    self.compile_return_block(else_body),
                ))
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| {
                    let block = self.compile_effect_block(fallback);
                    self.with_block_source_loc(fallback, block)
                })
                .unwrap_or_default();
        };
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type(), Some(VariantBlockType::Unknown)))
        {
            return self.compile_effect_block(body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_effect_block(block_cases[0].1);
        }
        if let Some(block) = self.compile_small_untagged_block_switch_effect(
            scrut_expr.clone(),
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
            self.filtered_switch_case_refs(&block_cases, self.block_switch_default(switch));
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
        let mut tail = self.compile_named_string_switch_effect_with_strategy(
            ocaml_typeof_expr(scrut_expr.clone()),
            &typeof_cases,
            self.block_switch_default(switch),
            self.block_switch_complete(switch),
            allow_small_typeof_tail && !typeof_cases.is_empty(),
        );

        // #8251: guard typeof "object" against null / arrays
        if !typeof_cases.is_empty()
            && let Some(guard) = self.untagged_typeof_object_guard(
                &scrut_expr,
                &typeof_cases,
                &runtime_test_cases,
                &all_block_types,
                has_null_case,
            )
        {
            let default_body = self.block_switch_default(switch).map(|fallback| {
                let block = self.compile_effect_block(fallback);
                self.with_block_source_loc(fallback, block)
            });
            tail = match default_body {
                Some(default_block) => vec![Statement::if_(guard, default_block, tail)],
                None if self.return_unit_stack.last().copied() == Some(true) => {
                    Self::normalized_if_block(
                        guard,
                        vec![Statement::return_(Expression::undefined(true))],
                        tail,
                    )
                }
                None => vec![Statement::if_(Expression::not(guard), tail, Vec::new())],
            };
        }

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            let body_block = self.compile_effect_block(body);
            tail = self.compile_effect_if(test, body_block, tail);
        }

        tail
    }

    fn compile_small_untagged_block_switch_effect(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&crate::types::VariantBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| {
                        let block = self.compile_effect_block(fallback);
                        self.with_block_source_loc(fallback, block)
                    })
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_effect_block(body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(body);
                let else_block = default
                    .map(|fallback| {
                        let block = self.compile_effect_block(fallback);
                        self.with_block_source_loc(fallback, block)
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
                    &all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(then_body);
                let else_block = self.compile_effect_block(else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    pub(crate) fn compile_untagged_variant_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_assignment_statements(
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_assignment_statements(
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_assignment(
                result,
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let _ = literal_cases;
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path (const cases + block cases): null is dispatched by the
        // outer const_branch, so when we fall into block_branch, x cannot be
        // null. Match OCaml's `compile_cases` default `has_null_case = false`
        // in the else branch of lam_compile.ml:755.
        let block_branch = self.compile_untagged_block_switch_assignment_statements(
            result,
            scrut_expr.clone(),
            switch,
            false,
        );

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
            return block_branch;
        };

        if const_branch.is_empty() {
            vec![Statement::if_(
                Expression::not(dispatch_test),
                block_branch,
                vec![],
            )]
        } else if block_branch.is_empty() {
            vec![Statement::if_(dispatch_test, const_branch, vec![])]
        } else {
            vec![Statement::if_(dispatch_test, const_branch, block_branch)]
        }
    }

    pub(crate) fn compile_untagged_variant_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_return_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_return_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_return(
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let _ = literal_cases;
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path: null handled by const_branch; block_branch sees non-null x.
        let block_branch =
            self.compile_untagged_block_switch_return_statements(scrut_expr.clone(), switch, false);

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
            return block_branch;
        };

        if const_branch.is_empty() {
            if self.return_unit_stack.last().copied() == Some(true) {
                Self::normalized_if_block(
                    dispatch_test,
                    vec![Statement::return_(Expression::undefined(true))],
                    block_branch,
                )
            } else {
                vec![Statement::if_(
                    Expression::not(dispatch_test),
                    block_branch,
                    vec![],
                )]
            }
        } else if block_branch.is_empty() {
            vec![Statement::if_(dispatch_test, const_branch, vec![])]
        } else {
            vec![Statement::if_(dispatch_test, const_branch, block_branch)]
        }
    }

    pub(crate) fn compile_untagged_variant_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_effect_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_effect_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_effect(
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let _ = literal_cases;
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
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
        // Mixed path: null handled by const_branch; block_branch sees non-null x.
        let block_branch =
            self.compile_untagged_block_switch_effect_statements(scrut_expr.clone(), switch, false);

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
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
        let const_case_count = self
            .named_const_cases(switch)
            .map_or(0, |cases| cases.len());
        let block_case_count = self
            .named_block_cases(switch)
            .map_or(0, |cases| cases.len());

        match (const_case_count > 0, block_case_count > 0) {
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

    fn variant_object_test(&self, expr: Expression) -> Expression {
        raw_typeof_comparison(expr, BinOp::EqEqEq, "object")
    }

    fn variant_non_object_test(&self, expr: Expression) -> Expression {
        raw_typeof_comparison(expr, BinOp::NotEqEq, "object")
    }

    fn dispatch_named_variant_branches(
        &self,
        scrut_expr: Expression,
        const_branch: Block,
        block_branch: Block,
    ) -> Block {
        if const_branch.is_empty() {
            vec![Statement::if_(
                self.variant_object_test(scrut_expr),
                block_branch,
                vec![],
            )]
        } else if block_branch.is_empty() {
            vec![Statement::if_(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                vec![],
            )]
        } else {
            vec![Statement::if_(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                block_branch,
            )]
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
                // OCaml's `S.if_ cond [] []` collapses to `S.exp cond`
                // (js_stmt_make.ml:242 + 45-53). Preserves bare comparisons
                // like `tmp === null;` that come from a switch where every
                // dispatched arm falls through to the same continuation.
                let mut block = vec![];
                push_s_exp(&mut block, cond);
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

    fn peel_single_block_statement(block: Block) -> Block {
        match block.as_slice() {
            [
                Statement {
                    desc: StatementDesc::Block(inner),
                    ..
                },
            ] => Self::peel_single_block_statement(inner.clone()),
            _ => block,
        }
    }

    pub(crate) fn normalize_runtime_test_return_body(block: Block) -> Block {
        let block = Self::peel_single_block_statement(block);
        Self::shared_trailing_return_guard_block(&block).unwrap_or(block)
    }

    fn shared_trailing_return_guard_block(block: &Block) -> Option<Block> {
        let (first, rest) = block.split_first()?;
        let StatementDesc::If(cond, then_block, else_block) = &first.desc else {
            return None;
        };
        if !else_block.is_empty() || rest.is_empty() {
            return None;
        }

        let then_return = trailing_return_expression(then_block)?;
        let else_return = trailing_return_expression(rest)?;
        if !ocaml_eq_expression(then_return, else_return) {
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

        Some(vec![
            Statement::new(StatementDesc::If(cond.clone(), then_block, else_block)),
            Statement::return_(then_return.clone()),
        ])
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
                    && cases
                        .iter()
                        .all(|(_, body)| matches!(body, Lambda::LstaticRaise(_, _)))
                    && cases.iter().all(|(_, body)| match body {
                        Lambda::LstaticRaise(label, args) => {
                            self.static_handlers.iter().any(|handler| {
                                handler.label == *label && handler.bindings.len() == args.len()
                            })
                        }
                        _ => false,
                    })
                    && cases.iter().all(|(_, body)| match body {
                        Lambda::LstaticRaise(label, args) => {
                            !self.static_jump_handlers.iter().any(|handler| {
                                handler.label == *label && handler.bindings.len() == args.len()
                            })
                        }
                        _ => false,
                    })
                {
                    let test_expr = self.switch_case_test(test, &cases[0].0);
                    let mut prefix = vec![];
                    push_s_exp(&mut prefix, test_expr);
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
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
            self.compile_effect_if(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                block_branch,
            )
        }
    }
}
