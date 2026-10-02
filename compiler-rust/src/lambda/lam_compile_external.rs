//! External call and object compilation.
//!
//! Port of `lam_compile_external_call.ml` + `lam_compile_external_obj.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    external_polyvar_int_dispatch, external_polyvar_string_dispatch, int_expr,
    is_nullish_literal, is_optional_block, is_pure_subexpression,
    js_expr_no_side_effects, js_seq, poly_var_tag_access, poly_var_value_access,
    remove_pure_subexpression, runtime_member_for_eta_wrapped_primitive, string_switch_iife,
};
use super::lam_compile::{
    Compiled, ExternalModuleCacheKey, LambdaCompiler, call_info_of_apply_status,
};
use super::lam_compile_input::{FunctionInput, LambdaInput, LambdaInputView};
use crate::ident::Ident;
use crate::js_ir::op::{
    IdentInfo, ImportAttributes as JsImportAttributes, Kind, Number, PropertyName, UsedStats,
};
use crate::js_ir::printer::{convert_ident_name, is_js_keyword_or_global};
use crate::js_ir::{
    BinOp, Block, CallInfo, Delim, Expression, ExpressionDesc, ModuleId, Statement, StatementDesc,
    VIdent, VariableDeclaration, expression_has_no_side_effects,
};
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalFfiKind, ExternalModuleBindName, ExternalModuleName, ExternalObjLabel, ExternalObjSpec,
    ExternalSpec, Mutable, Primitive,
};
use crate::lambda::{ApplyStatus, Lambda, TagInfo};
use crate::location::Location;

pub(crate) fn external_module_import_attributes(
    module_name: &ExternalModuleName,
) -> Option<JsImportAttributes> {
    let entries = module_name.import_attributes.clone()?;
    Some(JsImportAttributes { entries })
}

pub(crate) fn external_module_ident_name(module_name: &ExternalModuleName) -> String {
    match &module_name.module_bind_name {
        ExternalModuleBindName::HintName(hint) => capitalize_ascii_first(hint),
        ExternalModuleBindName::Nothing => js_id_name_of_hint_name(&module_name.bundle),
    }
}

pub(crate) fn capitalize_ascii_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut out = String::new();
            out.push(first.to_ascii_uppercase());
            out.push_str(chars.as_str());
            out
        }
    }
}

pub(crate) fn good_hint_name(module_name: &str, offset: usize) -> bool {
    let bytes = module_name.as_bytes();
    offset < bytes.len()
        && bytes[offset].is_ascii_alphabetic()
        && bytes[offset + 1..]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
}

pub(crate) fn collect_start(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' => {
                buf.push((s[offset] as char).to_ascii_uppercase());
                collect_next(buf, s, offset + 1);
                return;
            }
            b'A'..=b'Z' => {
                buf.push(s[offset] as char);
                collect_next(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

pub(crate) fn collect_next(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' => {
                buf.push(s[offset] as char);
                offset += 1;
            }
            b'.' | b'-' => {
                collect_start(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

pub(crate) fn js_id_name_of_hint_name(module_name: &str) -> String {
    let offset = module_name.rfind('/').map_or(0, |index| index + 1);
    if good_hint_name(module_name, offset) {
        capitalize_ascii_first(&module_name[offset..])
    } else {
        let bytes = module_name.as_bytes();
        let mut buf = String::new();
        collect_start(&mut buf, bytes, offset);
        if buf.is_empty() {
            if offset == 0 {
                module_name.to_string()
            } else {
                capitalize_ascii_first(module_name)
            }
        } else {
            buf
        }
    }
}

impl LambdaCompiler {
    pub(crate) fn external_optional_to_undefined_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::OptionalBlock(inner, _) => *inner,
            _ if expression_has_no_side_effects(&arg) => Expression::cond(
                self.is_not_none_expr(arg.clone()),
                self.val_from_option_expr(arg),
                Expression::undefined(false),
            ),
            // `Js_of_lam_option.get_default_undefined_from_optional`: a
            // non-duplicable option is already represented so that the
            // ordinary option unboxer yields `undefined` for `None`.
            _ => self.runtime_call_expr("Primitive_option", "valFromOption", vec![arg]),
        }
    }

    pub(crate) fn external_option_unwrap_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::OptionalBlock(inner, _) => self.external_polyvar_unwrap_expr(*inner),
            _ => self.runtime_call_expr("Primitive_option", "unwrapPolyVar", vec![arg]),
        }
    }

    pub(crate) fn external_polyvar_string_expr(
        &self,
        arg: Expression,
        dispatches: &[(String, String)],
    ) -> Expression {
        match &arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::Str { txt, .. } => {
                Expression::string(external_polyvar_string_dispatch(dispatches, txt))
            }
            _ => string_switch_iife(
                arg,
                dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), Expression::string(target.clone())))
                    .collect(),
            ),
        }
    }

    pub(crate) fn external_polyvar_event_exprs(
        &self,
        arg: Expression,
        dispatches: Option<&[(String, String)]>,
    ) -> Vec<Expression> {
        match &arg.desc {
            ExpressionDesc::CamlBlock(items, _, tag)
                if matches!(**tag, TagInfo::PolyVar(_))
                    && matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Str { .. },
                            ..
                        },
                        value,
                    ] if expression_has_no_side_effects(value)
                ) =>
            {
                let [
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                    value,
                ] = items.as_slice()
                else {
                    unreachable!();
                };
                let tag = match dispatches {
                    Some(dispatches) => {
                        Expression::string(external_polyvar_string_dispatch(dispatches, txt))
                    }
                    None => Expression::string(txt.clone()),
                };
                vec![tag, value.clone()]
            }
            _ => {
                let tag = match dispatches {
                    Some(dispatches) => {
                        self.external_polyvar_string_expr(poly_var_tag_access(&arg), dispatches)
                    }
                    None => poly_var_tag_access(&arg),
                };
                vec![tag, poly_var_value_access(&arg)]
            }
        }
    }

    pub(crate) fn external_polyvar_int_expr(
        &self,
        arg: Expression,
        dispatches: &[(String, i64)],
    ) -> Expression {
        match &arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::Str { txt, .. } => {
                int_expr(external_polyvar_int_dispatch(dispatches, txt) as i32)
            }
            _ => string_switch_iife(
                arg,
                dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), int_expr(*target as i32)))
                    .collect(),
            ),
        }
    }

    pub(crate) fn external_polyvar_unwrap_expr(&self, arg: Expression) -> Expression {
        match &arg.desc {
            ExpressionDesc::CamlBlock(items, _, _)
                if matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Number(_),
                            ..
                        },
                        _,
                    ]
                ) =>
            {
                items[1].clone()
            }
            _ => poly_var_value_access(&arg),
        }
    }

    pub(crate) fn pure_runtime_call_expr(
        &self,
        module_name: &str,
        member: &str,
        args: Vec<Expression>,
    ) -> Expression {
        Expression::with_comment(
            ExpressionDesc::Call(
                Box::new(self.runtime_member_expr(module_name, member)),
                args,
                Self::builtin_runtime_call_info(),
            ),
            "@__PURE__",
        )
    }

    pub(crate) fn compile_eta_wrapped_runtime_alias(
        &self,
        func: &crate::lambda::LFunction,
    ) -> Option<Expression> {
        self.compile_eta_wrapped_runtime_alias_input(FunctionInput {
            arity: func.arity,
            params: &func.params,
            body: (&func.body).into(),
            attr: &func.attr,
        })
    }

    pub(crate) fn compile_eta_wrapped_runtime_alias_input(
        &self,
        func: FunctionInput<'_>,
    ) -> Option<Expression> {
        if func.attr.one_unit_arg || func.attr.async_ || func.attr.directive.is_some() {
            return None;
        }

        let LambdaInputView::Prim(primitive, args, _) = func.body.view() else {
            return None;
        };
        if func.params.len() != args.len()
            || !func.params.iter().zip(args.iter()).all(|(param, arg)| {
                matches!(arg.view(), LambdaInputView::Var(id) if id.same(param))
            })
        {
            return None;
        }
        let (module_name, member) = runtime_member_for_eta_wrapped_primitive(primitive)?;
        Some(self.runtime_member_expr(module_name, member))
    }

    pub(crate) fn try_compile_identity_module_return_expr(
        &mut self,
        lam: &Lambda,
    ) -> Option<Expression> {
        self.try_compile_identity_module_return_input(lam.into())
    }

    pub(crate) fn try_compile_identity_module_return_input(
        &mut self,
        lam: LambdaInput<'_>,
    ) -> Option<Expression> {
        let mut module_target_var: Option<Ident> = None;
        let mut module_target_global: Option<(Ident, bool)> = None;
        let mut alias_chain = Vec::new();
        let mut cursor = lam;

        let mut note_target = |target: LambdaInput<'_>| -> Option<()> {
            match target.view() {
                LambdaInputView::Var(id) => {
                    if module_target_global.is_some()
                        || module_target_var
                            .as_ref()
                            .is_some_and(|current| !current.same(id))
                    {
                        return None;
                    }
                    module_target_var.get_or_insert_with(|| id.clone());
                    Some(())
                }
                LambdaInputView::GlobalModule(id, dynamic_import) => {
                    if module_target_var.is_some()
                        || module_target_global.as_ref().is_some_and(
                            |(current_id, current_dynamic_import)| {
                                !current_id.same(id) || *current_dynamic_import != dynamic_import
                            },
                        )
                    {
                        return None;
                    }
                    module_target_global.get_or_insert_with(|| (id.clone(), dynamic_import));
                    Some(())
                }
                _ => None,
            }
        };

        loop {
            match cursor.view() {
                LambdaInputView::Let(kind, alias_id, value, body)
                    if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt) =>
                {
                    let LambdaInputView::Prim(primitive, args, _) = value.view() else {
                        return None;
                    };
                    let Primitive::Pfield(index, FieldDbgInfo::Module { name }) = primitive else {
                        return None;
                    };
                    if args.len() != 1 {
                        return None;
                    }
                    let target = args.first()?;
                    note_target(target)?;

                    alias_chain.push((alias_id.clone(), *index, name.clone()));
                    cursor = body;
                }
                LambdaInputView::Prim(primitive, args, _) => {
                    let Primitive::Pmakeblock(TagInfo::Module(fields), Mutable::Immutable) =
                        primitive
                    else {
                        return None;
                    };
                    if alias_chain.len() != fields.len() || args.len() != fields.len() {
                        // The simplifier can inline the alias chain into the final
                        // Pmakeblock args, so only the final runtime field count is exact.
                        if args.len() != fields.len() {
                            return None;
                        }
                    }

                    for (position, arg) in args.iter().enumerate() {
                        let expected_field = &fields[position];
                        match arg.view() {
                            LambdaInputView::Var(arg_id) => {
                                let Some((_, field_index, field_name)) = alias_chain
                                    .iter()
                                    .find(|(alias_id, _, _)| alias_id.same(arg_id))
                                else {
                                    return None;
                                };
                                if *field_index != position as i32 || field_name != expected_field {
                                    return None;
                                }
                            }
                            LambdaInputView::Prim(
                                Primitive::Pfield(
                                    field_index,
                                    FieldDbgInfo::Module { name: field_name },
                                ),
                                args,
                                _,
                            ) => {
                                if *field_index != position as i32 || field_name != expected_field {
                                    return None;
                                }
                                if args.len() != 1 {
                                    return None;
                                }
                                let target = args.first()?;
                                note_target(target)?;
                            }
                            _ => return None,
                        }
                    }

                    return if let Some(id) = module_target_var {
                        Some(Expression::var(id))
                    } else if let Some((id, dynamic_import)) = module_target_global {
                        Some(Expression::qualified(
                            ModuleId {
                                id,
                                kind: Kind::Ml,
                                dynamic_import,
                            },
                            None,
                        ))
                    } else {
                        None
                    };
                }
                _ => return None,
            }
        }
    }

    pub(crate) fn external_module_id(
        &mut self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> ModuleId {
        let key = ExternalModuleCacheKey {
            // OCaml interns external imports by bundle/default, not by the
            // latest hint name, so later aliases reuse the first binding id.
            bundle: module_name.bundle.clone(),
            default,
        };
        let id = self
            .external_module_ids
            .entry(key)
            .or_insert_with(|| self.id_gen.create(&external_module_ident_name(module_name)))
            .clone();

        ModuleId {
            id,
            kind: Kind::External {
                name: module_name.bundle.clone(),
                default,
                import_attributes: external_module_import_attributes(module_name),
            },
            dynamic_import,
        }
    }

    pub(crate) fn external_module_binding(
        &mut self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> Expression {
        Expression::qualified(
            self.external_module_id(module_name, default, dynamic_import),
            None,
        )
    }

    pub(crate) fn translate_scoped_module_value(
        &mut self,
        module_name: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
        dynamic_import: bool,
    ) -> Expression {
        match module_name {
            Some(module_name) => match scopes.split_first() {
                None => {
                    let default = name == "default";
                    Expression::qualified(
                        self.external_module_id(module_name, default, dynamic_import),
                        Some(name.to_string()),
                    )
                }
                Some((first_scope, rest_scopes)) => {
                    let mut expr = Expression::qualified(
                        self.external_module_id(module_name, false, dynamic_import),
                        Some(first_scope.clone()),
                    );
                    for scope in rest_scopes {
                        expr = self.static_index(expr, scope);
                    }
                    self.static_index(expr, name)
                }
            },
            None => self.translate_scoped_global_value(name, scopes),
        }
    }

    pub(crate) fn optional_block(&self, value: Expression, identity: bool) -> Expression {
        Expression::new(ExpressionDesc::OptionalBlock(Box::new(value), identity))
    }

    pub(crate) fn can_inline_null_to_opt(&self, expr: &Expression) -> bool {
        matches!(
            expr.desc,
            ExpressionDesc::Var(_) | ExpressionDesc::Undefined { .. } | ExpressionDesc::Null
        )
    }

    pub(crate) fn null_to_opt_expr(&self, expr: Expression) -> Expression {
        if self.can_inline_null_to_opt(&expr) {
            Expression::cond(
                self.is_null_expr(expr.clone()),
                Expression::undefined(false),
                self.optional_block(expr, false),
            )
        } else {
            self.runtime_call_expr("Primitive_option", "fromNull", vec![expr])
        }
    }

    pub(crate) fn null_undefined_to_opt_expr(&self, expr: Expression) -> Expression {
        if self.can_inline_null_to_opt(&expr) {
            Expression::cond(
                self.is_null_or_undefined_expr(expr.clone()),
                Expression::undefined(false),
                self.optional_block(expr, false),
            )
        } else {
            self.runtime_call_expr("Primitive_option", "fromNullable", vec![expr])
        }
    }

    pub(crate) fn is_null_expr(&self, expr: Expression) -> Expression {
        Expression::bin(BinOp::EqEqEq, expr, Expression::null())
    }

    pub(crate) fn is_undefined_expr(&self, expr: Expression) -> Expression {
        Expression::bin(BinOp::EqEqEq, expr, Expression::undefined(false))
    }

    pub(crate) fn is_null_or_undefined_expr(&self, expr: Expression) -> Expression {
        Expression::is_null_or_undefined(expr)
    }

    pub(crate) fn some_expr(&self, value: Expression) -> Expression {
        let identity = matches!(
            value.desc,
            ExpressionDesc::Null
                | ExpressionDesc::Object(_, _)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::CamlBlock(_, _, _)
                | ExpressionDesc::Array(_, _)
                | ExpressionDesc::Str { .. }
        );
        self.optional_block(value, identity)
    }

    pub(crate) fn val_from_option_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::OptionalBlock(inner, _) => *inner,
            _ => self.runtime_call_expr("Primitive_option", "valFromOption", vec![arg]),
        }
    }

    pub(crate) fn is_not_none_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::bool(false),
            ExpressionDesc::OptionalBlock(_, _) => Expression::bool(true),
            _ => Expression::bin(BinOp::NotEqEq, arg, Expression::undefined(false)),
        }
    }

    pub(crate) fn external_arg_effect(&self, arg: &Expression) -> Option<Expression> {
        if expression_has_no_side_effects(arg) {
            None
        } else {
            Some(arg.clone())
        }
    }

    pub(crate) fn fuse_external_effects(&self, effects: Vec<Expression>) -> Option<Expression> {
        let mut effects = effects.into_iter();
        let first = effects.next()?;
        Some(effects.fold(first, js_seq))
    }

    pub(crate) fn add_external_effect(
        &self,
        effect: Option<Expression>,
        expr: Expression,
    ) -> Expression {
        match effect {
            Some(effect) => js_seq(effect, expr),
            None => expr,
        }
    }

    pub(crate) fn lower_object_external_arg_value_and_effect(
        &self,
        raw_arg: Expression,
        arg_label: ExternalArgLabel,
        arg_type: &ExternalArgAttr,
    ) -> (Expression, Option<Expression>) {
        let (values, effect) =
            self.lower_external_arg_values_and_effect(raw_arg, arg_label, arg_type);
        match values.as_slice() {
            [value] => (value.clone(), effect),
            [] => panic!("object field lowering expected one JS arg for {arg_type:?}"),
            _ => panic!(
                "object field lowering expected one JS arg, got {:?}",
                values
            ),
        }
    }

    pub(crate) fn lower_external_arg_values_and_effect(
        &self,
        raw_arg: Expression,
        arg_label: ExternalArgLabel,
        arg_type: &ExternalArgAttr,
    ) -> (Vec<Expression>, Option<Expression>) {
        // Only `Unwrap` of an optional argument reads the raw argument again.
        let keep_raw = matches!(arg_type, ExternalArgAttr::Unwrap)
            && matches!(arg_label, ExternalArgLabel::Optional);
        let (arg, raw_arg) = match arg_label {
            ExternalArgLabel::Optional => {
                let raw_copy = keep_raw.then(|| raw_arg.clone());
                (self.external_optional_to_undefined_expr(raw_arg), raw_copy)
            }
            ExternalArgLabel::Label | ExternalArgLabel::Empty => (raw_arg, None),
        };

        match arg_type {
            ExternalArgAttr::ArgCst(_) => (Vec::new(), None),
            ExternalArgAttr::ExternUnit => {
                let effect = self.external_arg_effect(&arg);
                let values = if matches!(arg_label, ExternalArgLabel::Empty) {
                    Vec::new()
                } else {
                    vec![Expression::undefined(true)]
                };
                (values, effect)
            }
            ExternalArgAttr::Ignore => (Vec::new(), self.external_arg_effect(&arg)),
            ExternalArgAttr::PolyVarString { descr } => {
                (vec![self.external_polyvar_string_expr(arg, descr)], None)
            }
            ExternalArgAttr::PolyVar { descr } => (
                self.external_polyvar_event_exprs(arg, descr.as_deref()),
                None,
            ),
            ExternalArgAttr::Int(dispatches) => {
                (vec![self.external_polyvar_int_expr(arg, dispatches)], None)
            }
            ExternalArgAttr::Unwrap => {
                let value = match arg_label {
                    ExternalArgLabel::Optional => self.external_option_unwrap_expr(
                        raw_arg.expect("optional unwrap keeps the raw argument"),
                    ),
                    ExternalArgLabel::Label | ExternalArgLabel::Empty => {
                        self.external_polyvar_unwrap_expr(arg)
                    }
                };
                (vec![value], None)
            }
            ExternalArgAttr::Nothing => (vec![arg], None),
        }
    }

    pub(crate) fn assemble_external_args_no_splice(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter();
        let mut assembled = Vec::new();
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                ExternalArgAttr::ArgCst(cst) => {
                    assembled.push(self.compile_external_arg_const(cst));
                }
                _ => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    let (values, effect) = self.lower_external_arg_values_and_effect(
                        arg,
                        arg_spec.arg_label,
                        &arg_spec.arg_type,
                    );
                    if let Some(effect) = effect {
                        effects.push(effect);
                    }
                    assembled.extend(values);
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());
        (
            self.keep_non_undefined_external_args(arg_types, assembled),
            self.fuse_external_effects(effects),
        )
    }

    pub(crate) fn keep_non_undefined_external_args(
        &self,
        arg_types: &[ExternalArgSpec],
        mut args: Vec<Expression>,
    ) -> Vec<Expression> {
        let trailing_optional_undefined_count = arg_types
            .iter()
            .rev()
            .zip(args.iter().rev())
            .take_while(|(arg_spec, arg)| {
                matches!(arg_spec.arg_label, ExternalArgLabel::Optional)
                    && matches!(arg.desc, ExpressionDesc::Undefined { is_unit: false })
            })
            .count();

        if trailing_optional_undefined_count > 0 {
            args.truncate(args.len() - trailing_optional_undefined_count);
        }

        args
    }

    pub(crate) fn assemble_external_args_with_splice(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter().peekable();
        let mut assembled = Vec::new();
        let mut needs_spread = false;
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                ExternalArgAttr::ArgCst(cst) => {
                    assembled.push(self.compile_external_arg_const(cst));
                }
                _ => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    let is_last_runtime_arg = runtime_args.peek().is_none();

                    if is_last_runtime_arg {
                        match arg {
                            Expression {
                                desc: ExpressionDesc::Array(items, _),
                                ..
                            } => {
                                assembled.extend(items);
                            }
                            arg => {
                                needs_spread = true;
                                let (values, effect) = self.lower_external_arg_values_and_effect(
                                    arg,
                                    arg_spec.arg_label,
                                    &arg_spec.arg_type,
                                );
                                if let Some(effect) = effect {
                                    effects.push(effect);
                                }
                                assembled.extend(values);
                            }
                        }
                    } else {
                        let (values, effect) = self.lower_external_arg_values_and_effect(
                            arg,
                            arg_spec.arg_label,
                            &arg_spec.arg_type,
                        );
                        if let Some(effect) = effect {
                            effects.push(effect);
                        }
                        assembled.extend(values);
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        if needs_spread {
            if let Some(last) = assembled.pop() {
                assembled.push(Expression::new(ExpressionDesc::Spread(Box::new(last))));
            }
        }

        (assembled, self.fuse_external_effects(effects))
    }

    pub(crate) fn assemble_external_args(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
        splice: bool,
    ) -> (Vec<Expression>, Option<Expression>) {
        if splice {
            self.assemble_external_args_with_splice(arg_types, args)
        } else {
            self.assemble_external_args_no_splice(arg_types, args)
        }
    }

    pub(crate) fn compile_js_object_create(
        &mut self,
        obj_params: &[ExternalObjSpec],
        args: Vec<Expression>,
        prelude: &mut Block,
    ) -> Expression {
        #[derive(Clone)]
        struct PendingOptionalAssignment {
            name: String,
            arg: Expression,
            arg_type: ExternalArgAttr,
            for_sure_no_nested_option: bool,
        }

        let mut runtime_args = args.into_iter();
        let mut props = Vec::new();
        let mut effects = Vec::new();
        let mut optional_assignments: Vec<PendingOptionalAssignment> = Vec::new();

        for obj_param in obj_params {
            match &obj_param.obj_arg_label {
                ExternalObjLabel::Empty => {
                    if !matches!(obj_param.obj_arg_type, ExternalArgAttr::ArgCst(_)) {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        if let Some(effect) = self.external_arg_effect(&arg) {
                            effects.push(effect);
                        }
                    }
                }
                ExternalObjLabel::Label { name } => match &obj_param.obj_arg_type {
                    ExternalArgAttr::ArgCst(cst) => {
                        props.push((
                            PropertyName::lit(name.clone()),
                            self.compile_external_arg_const(cst),
                        ));
                    }
                    _ => {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        let (value, effect) = self.lower_object_external_arg_value_and_effect(
                            arg,
                            ExternalArgLabel::Label,
                            &obj_param.obj_arg_type,
                        );
                        if let Some(effect) = effect {
                            effects.push(effect);
                        }
                        props.push((PropertyName::lit(name.clone()), value));
                    }
                },
                ExternalObjLabel::Optional {
                    name,
                    for_sure_no_nested_option,
                } => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));

                    match arg.desc {
                        ExpressionDesc::Undefined { .. } => continue,
                        // Match OCaml's Js_of_lam_option.destruct_optional:
                        // statically-known `Some x` goes straight into the
                        // object literal, while unknown option values keep the
                        // temp-object plus conditional assignment path.
                        ExpressionDesc::OptionalBlock(inner, _) => {
                            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                                *inner,
                                ExternalArgLabel::Label,
                                &obj_param.obj_arg_type,
                            );
                            if let Some(effect) = effect {
                                effects.push(effect);
                            }
                            props.push((PropertyName::lit(name.clone()), value));
                        }
                        other => {
                            optional_assignments.push(PendingOptionalAssignment {
                                name: name.clone(),
                                arg: Expression::new(other),
                                arg_type: obj_param.obj_arg_type.clone(),
                                for_sure_no_nested_option: *for_sure_no_nested_option,
                            });
                        }
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        let object = self.add_external_effect(
            self.fuse_external_effects(effects),
            Expression::new(ExpressionDesc::Object(None, props)),
        );

        if optional_assignments.is_empty() {
            return object;
        }

        let obj = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: obj.clone(),
            value: Some(object),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));

        for pending in optional_assignments {
            let prepared = if self.expr_is_simple(&pending.arg) {
                pending.arg
            } else {
                let tmp = self.fresh_tmp_ident();
                prelude.push(Statement::variable(VariableDeclaration {
                    ident: tmp.clone(),
                    value: Some(pending.arg),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }));
                Expression::var(tmp)
            };

            let value_arg = if pending.for_sure_no_nested_option {
                prepared.clone()
            } else {
                self.val_from_option_expr(prepared.clone())
            };
            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                value_arg,
                ExternalArgLabel::Empty,
                &pending.arg_type,
            );
            let cond = Expression::bin(BinOp::NotEqEq, prepared, Expression::undefined(false));
            let assign = Expression::bin(
                BinOp::Eq,
                self.static_index(Expression::var(obj.clone()), &pending.name),
                self.add_external_effect(effect, value),
            );
            prelude.push(Statement::if_(cond, vec![Statement::exp(assign)], vec![]));
        }

        Expression::var(obj)
    }

    pub(crate) fn expr_is_simple(&self, expr: &Expression) -> bool {
        matches!(
            expr.desc,
            ExpressionDesc::Var(_)
                | ExpressionDesc::Undefined { .. }
                | ExpressionDesc::Null
                | ExpressionDesc::Bool(_)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::Str { .. }
        )
    }

    pub(crate) fn compile_js_call(
        &mut self,
        loc: &Location,
        prim_name: &str,
        arg_types: &[ExternalArgSpec],
        ffi: &crate::lambda::lam_primitive::ExternalFfiSpec,
        dynamic_import: bool,
        transformed_jsx: bool,
        args: Vec<Expression>,
        _prelude: &mut Block,
    ) -> Expression {
        let transformed_jsx_call_info = CallInfo {
            call_transformed_jsx: transformed_jsx,
            ..CallInfo::default()
        };

        if ffi.kind == ExternalFfiKind::Normal {
            self.report_diagnostic(
                loc,
                &format!(
                    "\x1b[1;31mError:\x1b[0m internal error, using unrecognized primitive {prim_name}"
                ),
            );
            return Expression::undefined(false);
        }

        match ffi.spec.as_ref() {
            Some(ExternalSpec::JsVar {
                name,
                external_module_name,
                scopes,
            }) => {
                let value = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );
                if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, transformed_jsx_call_info.clone())
                }
            }
            Some(ExternalSpec::JsCall {
                name,
                external_module_name,
                splice,
                scopes,
            }) => {
                let target = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );

                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                self.add_external_effect(
                    effect,
                    Expression::call(target, args, transformed_jsx_call_info.clone()),
                )
            }
            Some(ExternalSpec::JsNew {
                name,
                external_module_name,
                splice,
                scopes,
                ..
            }) => {
                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                let target = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSend {
                name,
                splice,
                js_send_scopes,
                ..
            }) => match args.split_first() {
                Some((receiver, rest)) => {
                    let (rest_args, effect) = self.assemble_external_args(
                        arg_types.get(1..).unwrap_or(&[]),
                        rest.to_vec(),
                        *splice,
                    );
                    self.add_external_effect(
                        effect,
                        Expression::call(
                            self.static_index(
                                self.apply_scoped_access(receiver.clone(), js_send_scopes),
                                name,
                            ),
                            rest_args,
                            transformed_jsx_call_info.clone(),
                        ),
                    )
                }
                None => self.compile_plain_js_call(prim_name, args, transformed_jsx),
            },
            Some(ExternalSpec::JsGet {
                js_get_name,
                js_get_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver] => self.static_index(
                        self.apply_scoped_access(receiver.clone(), js_get_scopes),
                        js_get_name,
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSet {
                js_set_name,
                js_set_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, value] => Expression::bin(
                        BinOp::Eq,
                        self.static_index(
                            self.apply_scoped_access(receiver.clone(), js_set_scopes),
                            js_set_name,
                        ),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsGetIndex {
                js_get_index_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, index] => Expression::new(ExpressionDesc::ArrayIndex(
                        Box::new(self.apply_scoped_access(receiver.clone(), js_get_index_scopes)),
                        Box::new(index.clone()),
                    )),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSetIndex {
                js_set_index_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, index, value] => Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(
                                self.apply_scoped_access(receiver.clone(), js_set_index_scopes),
                            ),
                            Box::new(index.clone()),
                        )),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsVar(module_name)) => {
                let value = self.external_module_binding(module_name, false, dynamic_import);
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, transformed_jsx_call_info.clone())
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsFn {
                external_module_name,
                splice,
            }) => {
                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                let target =
                    self.external_module_binding(external_module_name, false, dynamic_import);
                let expr = Expression::call(target, args, transformed_jsx_call_info.clone());
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsClass(module_name)) => {
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let target = self.external_module_binding(module_name, false, dynamic_import);
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            _ => self.compile_plain_js_call(prim_name, args, transformed_jsx),
        }
    }

    pub(crate) fn compile_plain_js_call(
        &self,
        prim_name: &str,
        args: Vec<Expression>,
        transformed_jsx: bool,
    ) -> Expression {
        Expression::call(
            Expression::var(Ident::create_persistent(prim_name)),
            args,
            CallInfo {
                call_transformed_jsx: transformed_jsx,
                ..CallInfo::default()
            },
        )
    }

    pub(crate) fn compile_import(&mut self, loc: &Location, args: Vec<Expression>) -> Expression {
        let arg = match args.as_slice() {
            [arg] => arg,
            [
                arg,
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                },
            ] => arg,
            _ => {
                self.report_diagnostic(
                    loc,
                    "Invalid argument: Dynamic import must take a single module or module value as its argument.",
                );
                return Expression::undefined(false);
            }
        };

        let Some((module, member)) = self.module_of_expression(arg) else {
            self.report_diagnostic(
                loc,
                "Invalid argument: Dynamic import requires a module or module value that is a file as argument. Passing a value or local module is not allowed.",
            );
            return Expression::undefined(false);
        };

        let path = match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            _ => self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.resolve_module_path(&module)),
        };

        let Some(path) = path else {
            self.report_diagnostic(
                loc,
                "Invalid argument: Dynamic import requires a module or module value that is a file as argument. Passing a value or local module is not allowed.",
            );
            return Expression::undefined(false);
        };

        let import_expr = Expression::call(
            Expression::var(Ident::create_persistent("import")),
            vec![Expression::string(path)],
            CallInfo::default(),
        );

        let member = member.or_else(|| match &module.kind {
            Kind::External { default: true, .. } => Some("default".to_string()),
            _ => None,
        });

        match member {
            Some(member) => {
                let param = self.fresh_ident("m");
                let body = vec![Statement::return_(
                    self.static_index(Expression::var(param.clone()), &member),
                )];
                let callback = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param],
                    body,
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                });
                Expression::call(
                    self.static_index(import_expr, "then"),
                    vec![callback],
                    CallInfo::default(),
                )
            }
            None => import_expr,
        }
    }

    pub(crate) fn module_of_expression(
        &self,
        expr: &Expression,
    ) -> Option<(ModuleId, Option<String>)> {
        match &expr.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                Some(((**module).clone(), member.clone()))
            }
            ExpressionDesc::StaticIndex(target, field, _) => match &target.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, None)) => {
                    Some(((**module).clone(), Some(field.clone())))
                }
                _ => None,
            },
            ExpressionDesc::Call(func, _, _) => match &func.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                    Some(((**module).clone(), member.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn translate_scoped_global_value(
        &self,
        name: &str,
        scopes: &[String],
    ) -> Expression {
        let mut expr = match scopes.split_first() {
            Some((head, rest)) => {
                let mut expr = Expression::var(Ident::create_persistent(head));
                for scope in rest {
                    expr = self.static_index(expr, scope);
                }
                expr
            }
            None => Expression::var(Ident::create_persistent(name)),
        };
        if !scopes.is_empty() {
            expr = self.static_index(expr, name);
        }
        expr
    }

    pub(crate) fn apply_scoped_access(
        &self,
        mut expr: Expression,
        scopes: &[String],
    ) -> Expression {
        for scope in scopes {
            expr = self.static_index(expr, scope);
        }
        expr
    }

    pub(crate) fn static_index(&self, target: Expression, field: &str) -> Expression {
        Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target),
            field.to_string(),
            None,
        ))
    }

    pub(crate) fn fresh_ident(&self, prefix: &str) -> Ident {
        self.id_gen.create(prefix)
    }

    pub(crate) fn fresh_tmp_ident(&self) -> Ident {
        self.fresh_ident("tmp")
    }
}
