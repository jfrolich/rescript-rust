//! External call and object compilation.
//!
//! Port of `lam_compile_external_call.ml` + `lam_compile_external_obj.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    external_polyvar_int_dispatch, external_polyvar_string_dispatch, int_expr, js_seq,
    poly_var_tag_access, poly_var_value_access, runtime_member_for_eta_wrapped_primitive,
    string_switch_iife,
};
use super::lam_compile::{ExternalModuleCacheKey, LambdaCompiler};
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, ImportAttributes as JsImportAttributes, Kind, PropertyName};
use crate::js_ir::printer::js_export_name;
use crate::js_ir::{
    BinOp, Block, CallInfo, Expression, ExpressionDesc, ModuleId, Statement, VariableDeclaration,
    expression_has_no_side_effects,
};
use crate::lambda::arena::{FuncId, Lam, LamArena, View};
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_primitive::{
    Attr, DeclKind, ExternalDecl, ExternalModuleName, ImportSource, Label, LabelNoname,
    ModuleBindName, ModuleSource, Mutable, ObjParam, Param, Primitive,
};
use crate::lambda::LamLoc;
use crate::lambda::TagInfo;

pub(crate) fn external_module_import_attributes(
    module_name: &ExternalModuleName,
) -> Option<JsImportAttributes> {
    let entries = module_name.import_attributes.clone()?;
    Some(JsImportAttributes { entries })
}

pub(crate) fn external_module_ident_name(module_name: &ExternalModuleName) -> String {
    match &module_name.module_bind_name {
        ModuleBindName::PhintName(hint) => capitalize_ascii_first(hint),
        ModuleBindName::PhintNothing => js_id_name_of_hint_name(&module_name.bundle),
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
            ExpressionDesc::Str(txt) => {
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
                                desc: ExpressionDesc::Str(_),
                                ..
                            },
                            value,
                        ] if expression_has_no_side_effects(value)
                    ) =>
            {
                let [
                    Expression {
                        desc: ExpressionDesc::Str(txt),
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
            ExpressionDesc::Str(txt) => {
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
        a: &LamArena,
        info: FuncId,
        body: Lam,
    ) -> Option<Expression> {
        let func = a.func_payload(info);
        if func.attr.one_unit_arg || func.attr.async_ || func.attr.directive.is_some() {
            return None;
        }

        let (primitive, args, _) = a.as_prim(body)?;
        let params = a.params(info);
        if params.len() != args.len()
            || !params
                .iter()
                .zip(args)
                .all(|(param, arg)| a.as_var(*arg).is_some_and(|id| id.same(param)))
        {
            return None;
        }
        let (module_name, member) = runtime_member_for_eta_wrapped_primitive(primitive)?;
        Some(self.runtime_member_expr(module_name, member))
    }

    pub(crate) fn try_compile_identity_module_return_expr(
        &mut self,
        a: &LamArena,
        lam: Lam,
    ) -> Option<Expression> {
        let mut module_target_var: Option<Ident> = None;
        let mut module_target_global: Option<Ident> = None;
        let mut alias_chain = Vec::new();
        let mut cursor = lam;

        let mut note_target = |target: Lam| -> Option<()> {
            match a.view(target) {
                View::Var(id) => {
                    if module_target_global.is_some()
                        || module_target_var
                            .as_ref()
                            .is_some_and(|current| !current.same(&id))
                    {
                        return None;
                    }
                    module_target_var.get_or_insert(id);
                    Some(())
                }
                View::GlobalModule(id) => {
                    if module_target_var.is_some()
                        || module_target_global
                            .as_ref()
                            .is_some_and(|current_id| !current_id.same(&id))
                    {
                        return None;
                    }
                    module_target_global.get_or_insert(id);
                    Some(())
                }
                _ => None,
            }
        };

        loop {
            match a.view(cursor) {
                View::Let(kind, alias_id, value, body)
                    if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt) =>
                {
                    let (primitive, args, _) = a.as_prim(value)?;
                    let Primitive::Pfield(index, FieldDbgInfo::Module { name }) = primitive else {
                        return None;
                    };
                    if args.len() != 1 {
                        return None;
                    }
                    note_target(*args.first()?)?;

                    alias_chain.push((alias_id, *index, name.clone()));
                    cursor = body;
                }
                View::Prim(primitive, args, _) => {
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
                        match a.view(*arg) {
                            View::Var(arg_id) => {
                                let Some((_, field_index, field_name)) = alias_chain
                                    .iter()
                                    .find(|(alias_id, _, _)| alias_id.same(&arg_id))
                                else {
                                    return None;
                                };
                                if *field_index != position as i32 || field_name != expected_field {
                                    return None;
                                }
                            }
                            View::Prim(
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
                                note_target(*args.first()?)?;
                            }
                            _ => return None,
                        }
                    }

                    return if let Some(id) = module_target_var {
                        Some(Expression::var(id))
                    } else {
                        module_target_global.map(|id| {
                            Expression::qualified(
                                ModuleId {
                                    id,
                                    kind: Kind::Ml,
                                    dynamic_import: false,
                                },
                                None,
                            )
                        })
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
        let id = *self
            .external_module_ids
            .entry(key)
            .or_insert_with(|| self.id_gen.create(&external_module_ident_name(module_name)));

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
    ) -> Expression {
        Expression::qualified(self.external_module_id(module_name, default, false), None)
    }

    pub(crate) fn translate_scoped_module_value(
        &mut self,
        module_name: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
    ) -> Expression {
        match module_name {
            Some(module_name) => match scopes.split_first() {
                None => {
                    let default = name == "default";
                    Expression::qualified(
                        self.external_module_id(module_name, default, false),
                        Some(name.to_string()),
                    )
                }
                Some((first_scope, rest_scopes)) => {
                    let mut expr = Expression::qualified(
                        self.external_module_id(module_name, false, false),
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
                | ExpressionDesc::Str(_)
                | ExpressionDesc::TemplateLiteral(_)
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
        arg_label: LabelNoname,
        arg_type: &Attr,
    ) -> (Expression, Option<Expression>) {
        let (values, effect) =
            self.lower_external_arg_values_and_effect(raw_arg, arg_label, arg_type);
        match <[Expression; 1]>::try_from(values) {
            Ok([value]) => (value, effect),
            Err(values) if values.is_empty() => {
                panic!("object field lowering expected one JS arg for {arg_type:?}")
            }
            Err(values) => panic!(
                "object field lowering expected one JS arg, got {:?}",
                values
            ),
        }
    }

    pub(crate) fn lower_external_arg_values_and_effect(
        &self,
        raw_arg: Expression,
        arg_label: LabelNoname,
        arg_type: &Attr,
    ) -> (Vec<Expression>, Option<Expression>) {
        // Only `Unwrap` of an optional argument reads the raw argument again.
        let keep_raw =
            matches!(arg_type, Attr::Unwrap) && matches!(arg_label, LabelNoname::ArgOptional);
        let (arg, raw_arg) = match arg_label {
            LabelNoname::ArgOptional => {
                let raw_copy = keep_raw.then(|| raw_arg.clone());
                (self.external_optional_to_undefined_expr(raw_arg), raw_copy)
            }
            LabelNoname::ArgLabel | LabelNoname::ArgEmpty => (raw_arg, None),
        };

        match arg_type {
            Attr::ArgCst(_) => (Vec::new(), None),
            Attr::ExternUnit => {
                let effect = self.external_arg_effect(&arg);
                let values = if matches!(arg_label, LabelNoname::ArgEmpty) {
                    Vec::new()
                } else {
                    vec![Expression::undefined(true)]
                };
                (values, effect)
            }
            Attr::Ignore => (Vec::new(), self.external_arg_effect(&arg)),
            Attr::PolyVarString { descr } => {
                (vec![self.external_polyvar_string_expr(arg, descr)], None)
            }
            Attr::PolyVar { descr } => (
                self.external_polyvar_event_exprs(arg, descr.as_deref()),
                None,
            ),
            Attr::Int(dispatches) => (vec![self.external_polyvar_int_expr(arg, dispatches)], None),
            Attr::Unwrap => {
                let value = match arg_label {
                    LabelNoname::ArgOptional => self.external_option_unwrap_expr(
                        raw_arg.expect("optional unwrap keeps the raw argument"),
                    ),
                    LabelNoname::ArgLabel | LabelNoname::ArgEmpty => {
                        self.external_polyvar_unwrap_expr(arg)
                    }
                };
                (vec![value], None)
            }
            Attr::Nothing => (vec![arg], None),
        }
    }

    pub(crate) fn assemble_external_args_no_splice(
        &self,
        arg_types: &[Param],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter();
        let mut assembled = Vec::new();
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                Attr::ArgCst(cst) => {
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
        arg_types: &[Param],
        mut args: Vec<Expression>,
    ) -> Vec<Expression> {
        let trailing_optional_undefined_count = arg_types
            .iter()
            .rev()
            .zip(args.iter().rev())
            .take_while(|(arg_spec, arg)| {
                matches!(arg_spec.arg_label, LabelNoname::ArgOptional)
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
        arg_types: &[Param],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter().peekable();
        let mut assembled = Vec::new();
        let mut needs_spread = false;
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                Attr::ArgCst(cst) => {
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
        arg_types: &[Param],
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
        obj_params: &[ObjParam],
        args: Vec<Expression>,
        prelude: &mut Block,
    ) -> Expression {
        #[derive(Clone)]
        struct PendingOptionalAssignment {
            name: String,
            arg: Expression,
            arg_type: Attr,
            for_sure_no_nested_option: bool,
        }

        let mut runtime_args = args.into_iter();
        let mut props = Vec::new();
        let mut effects = Vec::new();
        let mut optional_assignments: Vec<PendingOptionalAssignment> = Vec::new();

        for obj_param in obj_params {
            match &obj_param.obj_arg_label {
                Label::ObjEmpty => {
                    if !matches!(obj_param.obj_arg_type, Attr::ArgCst(_)) {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        if let Some(effect) = self.external_arg_effect(&arg) {
                            effects.push(effect);
                        }
                    }
                }
                Label::ObjLabel { name } => match &obj_param.obj_arg_type {
                    Attr::ArgCst(cst) => {
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
                            LabelNoname::ArgLabel,
                            &obj_param.obj_arg_type,
                        );
                        if let Some(effect) = effect {
                            effects.push(effect);
                        }
                        props.push((PropertyName::lit(name.clone()), value));
                    }
                },
                Label::ObjOptional {
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
                                LabelNoname::ArgLabel,
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
            ident: obj,
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
                    ident: tmp,
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
                LabelNoname::ArgEmpty,
                &pending.arg_type,
            );
            let cond = Expression::bin(BinOp::NotEqEq, prepared, Expression::undefined(false));
            let assign = Expression::bin(
                BinOp::Eq,
                self.static_index(Expression::var(obj), &pending.name),
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
                | ExpressionDesc::Str(_)
        )
    }

    /// `Lam_compile_external_call.translate_ffi`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compile_js_call(
        &mut self,
        prim_name: &str,
        arg_types: &[Param],
        decl: &ExternalDecl,
        transformed_jsx: bool,
        args: Vec<Expression>,
    ) -> Expression {
        let call_info = CallInfo {
            call_transformed_jsx: transformed_jsx,
            ..CallInfo::default()
        };
        let splice = decl.variadic;
        let scopes = &decl.scopes;
        // a bare `@module` binds the module itself under the primitive name
        let module_itself_name = || ExternalModuleName {
            bundle: prim_name.to_string(),
            module_bind_name: ModuleBindName::PhintNothing,
            import_attributes: None,
        };
        let named_module = match &decl.module_ {
            Some(ModuleSource::ModuleNamed(emn)) => Some(emn),
            Some(ModuleSource::ModuleItself) | None => None,
        };
        let module_itself = matches!(decl.module_, Some(ModuleSource::ModuleItself));
        match &decl.kind {
            // the module itself, as a value
            DeclKind::DeclVal { .. } if module_itself && decl.effective_arity == 0 => {
                self.external_module_binding(&module_itself_name(), false)
            }
            // the module itself, called as a function
            DeclKind::DeclVal { .. } if module_itself => {
                let target = self.external_module_binding(&module_itself_name(), false);
                let (args, effect) = self.assemble_external_args(arg_types, args, splice);
                self.add_external_effect(effect, Expression::call(target, args, call_info))
            }
            // the module itself, as a class
            DeclKind::DeclNew { .. } if module_itself => {
                let target = self.external_module_binding(&module_itself_name(), false);
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            _ if module_itself => unreachable!("rejected during digestion"),
            // a global value
            DeclKind::DeclVal { name } if decl.effective_arity == 0 => {
                let value = self.translate_scoped_module_value(named_module, name, scopes);
                if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, call_info)
                }
            }
            // a global (possibly module-scoped) function call
            DeclKind::DeclVal { name } => {
                let target = self.translate_scoped_module_value(named_module, name, scopes);
                let (args, effect) = self.assemble_external_args(arg_types, args, splice);
                self.add_external_effect(effect, Expression::call(target, args, call_info))
            }
            DeclKind::DeclNew { name } => {
                let (args, effect) = self.assemble_external_args(arg_types, args, splice);
                let target = self.translate_scoped_module_value(named_module, name, scopes);
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclSend { name } => {
                let mut args = args.into_iter();
                let Some(receiver) = args.next() else {
                    unreachable!("@send external called without a receiver")
                };
                let (rest_args, effect) = self.assemble_external_args(
                    arg_types.get(1..).unwrap_or(&[]),
                    args.collect(),
                    splice,
                );
                self.add_external_effect(
                    effect,
                    Expression::call(
                        self.static_index(self.apply_scoped_access(receiver, scopes), name),
                        rest_args,
                        call_info,
                    ),
                )
            }
            DeclKind::DeclGet { name } => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expression; 1]>::try_from(assembled) {
                    Ok([receiver]) => {
                        self.static_index(self.apply_scoped_access(receiver, scopes), name)
                    }
                    Err(_) => panic!(
                        "Internal compiler error: @get external called with wrong number of arguments. Expected exactly one object argument."
                    ),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclSet { name } => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expression; 2]>::try_from(assembled) {
                    Ok([receiver, value]) => Expression::bin(
                        BinOp::Eq,
                        self.static_index(self.apply_scoped_access(receiver, scopes), name),
                        value,
                    ),
                    Err(_) => unreachable!("@set external takes an object and a value"),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclGetIndex => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expression; 2]>::try_from(assembled) {
                    Ok([receiver, index]) => Expression::new(ExpressionDesc::ArrayIndex(
                        Box::new(self.apply_scoped_access(receiver, scopes)),
                        Box::new(index),
                    )),
                    Err(_) => unreachable!("@get_index external takes an object and an index"),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclSetIndex => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expression; 3]>::try_from(assembled) {
                    Ok([receiver, index, value]) => Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(self.apply_scoped_access(receiver, scopes)),
                            Box::new(index),
                        )),
                        value,
                    ),
                    Err(_) => {
                        unreachable!("@set_index external takes an object, an index and a value")
                    }
                };
                self.add_external_effect(effect, expr)
            }
        }
    }

    /// `[import(...).then(m => m.<p0>.<p1>...)]`
    /// (`Lam_compile_primitive.wrap_then_path`).
    fn wrap_then_path(&self, import: Expression, path: &[String]) -> Expression {
        let param = self.fresh_ident("m");
        let mut value = Expression::var(param);
        for segment in path {
            value = self.static_index(value, segment);
        }
        let callback = Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![param],
            body: vec![Statement::return_(value)],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        });
        Expression::call(
            self.static_index(import, "then"),
            vec![callback],
            CallInfo::default(),
        )
    }

    fn import_of_path(path: String) -> Expression {
        Expression::call(
            Expression::var(Ident::create_persistent("import")),
            vec![Expression::string(path)],
            CallInfo::default(),
        )
    }

    /// `Lam_compile_primitive.translate` for `Pimport source`: the module is
    /// registered as a dynamic dependency here, the single place that knows
    /// about it, and the emitted form is `import("path")[.then(m => m.<name>)]`.
    pub(crate) fn compile_import(&mut self, loc: &LamLoc, source: &ImportSource) -> Expression {
        let invalid = "Invalid argument: Dynamic import requires a module or module value that is a file as argument. Passing a value or local module is not allowed.";
        match source {
            ImportSource::ImportModule { module_, path } => {
                let oid = ModuleId {
                    id: *module_,
                    kind: Kind::Ml,
                    dynamic_import: true,
                };
                self.dynamic_import_modules.push(oid.clone());
                let Some(import_path) = self
                    .module_path_resolver
                    .as_ref()
                    .and_then(|resolver| resolver.resolve_module_path(&oid))
                else {
                    self.report_diagnostic(loc, invalid);
                    return Expression::undefined(false);
                };
                let import = Self::import_of_path(import_path);
                match path.as_slice() {
                    [] => import,
                    [name] => self.wrap_then_path(import, &[js_export_name(name)]),
                    _ => {
                        // a nested path is importable when the target is a
                        // hoisted root-level export; the cmj knows
                        let hoisted = self.module_path_resolver.as_ref().and_then(|resolver| {
                            resolver.module_cmj_hoisted_export(module_.name(), path)
                        });
                        match hoisted {
                            Some(hoisted_name) => {
                                self.wrap_then_path(import, &[js_export_name(&hoisted_name)])
                            }
                            None => {
                                self.report_diagnostic(loc, invalid);
                                Expression::undefined(false)
                            }
                        }
                    }
                }
            }
            ImportSource::ImportExternal { module_, path } => {
                let default = path.len() == 1 && path[0] == "default";
                let oid = self.external_module_id(module_, default, true);
                self.dynamic_import_modules.push(oid.clone());
                let import = Self::import_of_path(module_.bundle.clone());
                if path.is_empty() {
                    import
                } else {
                    self.wrap_then_path(import, path)
                }
            }
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
