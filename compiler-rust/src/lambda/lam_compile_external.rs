//! External call and object compilation.
//!
//! Port of `lam_compile_external_call.ml` + `lam_compile_external_obj.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    external_polyvar_int_dispatch, external_polyvar_string_dispatch, int_expr,
    js_expr_no_side_effects, js_seq, poly_var_tag_access, poly_var_value_access,
    runtime_member_for_eta_wrapped_primitive, string_switch_iife,
};
use super::lam_compile::{ExternalModuleCacheKey, LambdaCompiler};
use crate::ident::Ident;
use crate::js_ir::arena::{Block, Expr, ExprKind, JsArena, JsxInfo, PropName, VarDecl};
use crate::js_ir::build::{exp as JE, expression_has_no_side_effects, stmt as JS};
use crate::js_ir::op::{IdentInfo, ImportAttributes as JsImportAttributes, Kind, PropertyName};
use crate::js_ir::printer::js_export_name;
use crate::js_ir::{BinOp, CallInfo, ModuleId};
use crate::lambda::LamLoc;
use crate::lambda::TagInfo;
use crate::lambda::arena::{FuncId, Lam, LamArena, View};
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_primitive::{
    Attr, DeclKind, ExternalDecl, ExternalModuleName, ImportSource, JsxElement, Label, LabelNoname,
    ModuleBindName, ModuleSource, Mutable, ObjParam, Param, Primitive,
};

/// The literal tag and payload of a poly-variant block
/// `{NAME: "tag", VAL: value}`.
fn literal_polyvar_block(j: &JsArena, arg: Expr) -> Option<(crate::js_ir::arena::StrId, Expr)> {
    let ExprKind::CamlBlock(items, _, tag) = j.ek(arg) else {
        return None;
    };
    if !matches!(j.tag(tag), TagInfo::PolyVar(_)) {
        return None;
    }
    match j.exprs(items) {
        [key, value] => match j.ek(*key) {
            ExprKind::Str(txt) => Some((txt, *value)),
            _ => None,
        },
        _ => None,
    }
}

/// js_of_lam_variant.ml `eval_in_place`: the `@string` and `@int`
/// dispatches read an argument other than a literal once, inside the
/// function that switches on it. That is the same as reading it in place
/// when the read has no effect and cannot await.
pub(crate) fn polyvar_dispatch_in_place(j: &JsArena, arg: Expr) -> bool {
    js_expr_no_side_effects(j, arg)
}

/// js_of_lam_variant.ml `eval_as_event_in_place`: an event-style argument
/// other than a literal is read twice, for the tag and for the payload. That
/// is the same as reading it once for constants, variables, and fields,
/// array elements and conditionals of them. A JS global (`@val`) or a
/// property read, as from a `@get` external, may run a getter each time.
pub(crate) fn polyvar_event_in_place(j: &JsArena, arg: Expr) -> bool {
    fn duplicable(j: &JsArena, e: Expr) -> bool {
        match j.ek(e) {
            ExprKind::Undefined { .. }
            | ExprKind::Bool(_)
            | ExprKind::Number(_)
            | ExprKind::Str(_)
            | ExprKind::TemplateLiteral(_)
            | ExprKind::Qualified(_) => true,
            // `Ext_ident.is_js`; Rust creates JS globals as persistent idents.
            ExprKind::Var(id) => !super::js_pass_external_shadow::is_js_global(&j.ident(id)),
            ExprKind::StaticIndex(e, _, pos) => pos.get().is_some() && duplicable(j, e),
            ExprKind::ArrayIndex(a, b) => duplicable(j, a) && duplicable(j, b),
            ExprKind::Cond(a, b, c) => duplicable(j, a) && duplicable(j, b) && duplicable(j, c),
            _ => false,
        }
    }
    literal_polyvar_block(j, arg).is_some() || duplicable(j, arg)
}

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
    pub(crate) fn external_optional_to_undefined_expr(&mut self, arg: Expr) -> Expr {
        match self.j.ek(arg) {
            ExprKind::Undefined { .. } => JE::undefined(false, &mut self.j),
            ExprKind::OptionalBlock(inner, _) => inner,
            _ if expression_has_no_side_effects(&self.j, arg) => {
                let test = self.is_not_none_expr(arg);
                let value = self.val_from_option_expr(arg);
                let undefined = JE::undefined(false, &mut self.j);
                JE::cond(test, value, undefined, &mut self.j)
            }
            // `Js_of_lam_option.get_default_undefined_from_optional`: a
            // non-duplicable option is already represented so that the
            // ordinary option unboxer yields `undefined` for `None`.
            _ => self.runtime_call_expr("Primitive_option", "valFromOption", vec![arg]),
        }
    }

    pub(crate) fn external_option_unwrap_expr(&mut self, arg: Expr) -> Expr {
        match self.j.ek(arg) {
            ExprKind::Undefined { .. } => JE::undefined(false, &mut self.j),
            ExprKind::OptionalBlock(inner, _) => self.external_polyvar_unwrap_expr(inner),
            _ => self.runtime_call_expr("Primitive_option", "unwrapPolyVar", vec![arg]),
        }
    }

    /// lam_compile_external_call.ml `hold_arg`: the translation of a
    /// poly-variant argument other than a literal reads it twice, as
    /// `e.NAME` and `e.VAL`, or inside the function a dispatch on its tag
    /// builds, where an `await` is a syntax error. So unless it can read the
    /// argument in place, the argument is bound to a temporary after its
    /// statements, which keeps it in its place among the arguments (see
    /// `sequence_arguments`). Of an optional argument known to be present,
    /// only the payload is bound, so the translation still sees `Some`.
    pub(crate) fn hold_external_arg(
        &mut self,
        arg_label: LabelNoname,
        arg_type: &Attr,
        (mut block, arg): (Block, Expr),
    ) -> (Block, Expr) {
        let needs_temporary = |j: &JsArena, e: Expr| match arg_type {
            Attr::PolyVar { .. } => !polyvar_event_in_place(j, e),
            Attr::PolyVarString { .. } | Attr::Int(_) => !polyvar_dispatch_in_place(j, e),
            Attr::ArgCst(_) | Attr::ExternUnit | Attr::Nothing | Attr::Ignore | Attr::Unwrap => {
                false
            }
        };
        let target = match (arg_label, self.j.ek(arg)) {
            (LabelNoname::ArgOptional, ExprKind::OptionalBlock(x, _)) => x,
            _ => arg,
        };
        if !needs_temporary(&self.j, target) {
            return (block, arg);
        }
        let tmp = self.fresh_tmp_ident();
        block.push(super::lam_compile_arguments::define_strict_variable(
            tmp,
            target,
            &mut self.j,
        ));
        let var = JE::var(tmp, &mut self.j);
        let value = match self.j.ek(arg) {
            ExprKind::OptionalBlock(_, identity) if target != arg => {
                let cold = self.j.expr_cold(arg);
                self.j
                    .expr_with(ExprKind::OptionalBlock(var, identity), cold)
            }
            _ => var,
        };
        (block, value)
    }

    /// lam_compile_external_call.ml `hold_args`: `hold_external_arg` for
    /// the compiled arguments of a call, paired with the specs as in
    /// `assemble_external_args_no_splice`.
    pub(crate) fn hold_external_args(
        &mut self,
        arg_types: &[Param],
        args: Vec<(Block, Expr)>,
    ) -> Vec<(Block, Expr)> {
        let mut args = args.into_iter();
        let mut held = Vec::with_capacity(args.len());
        for spec in arg_types {
            if matches!(spec.arg_type, Attr::ArgCst(_)) {
                continue;
            }
            let Some(arg) = args.next() else { break };
            held.push(self.hold_external_arg(spec.arg_label, &spec.arg_type, arg));
        }
        held.extend(args);
        held
    }

    /// lam_compile_external_obj.ml `hold_obj_args`: `hold_external_arg` for
    /// the compiled arguments of an object-creating external, paired with
    /// the labels as in `compile_js_object_create`.
    pub(crate) fn hold_external_obj_args(
        &mut self,
        obj_params: &[ObjParam],
        args: Vec<(Block, Expr)>,
    ) -> Vec<(Block, Expr)> {
        let mut args = args.into_iter();
        let mut held = Vec::with_capacity(args.len());
        for param in obj_params {
            let arg_label = match &param.obj_arg_label {
                Label::ObjLabel { .. } | Label::ObjEmpty
                    if matches!(param.obj_arg_type, Attr::ArgCst(_)) =>
                {
                    continue;
                }
                Label::ObjEmpty => None,
                Label::ObjLabel { .. } => Some(LabelNoname::ArgLabel),
                Label::ObjOptional { .. } => Some(LabelNoname::ArgOptional),
            };
            let Some(arg) = args.next() else { break };
            held.push(match arg_label {
                Some(label) => self.hold_external_arg(label, &param.obj_arg_type, arg),
                None => arg,
            });
        }
        held.extend(args);
        held
    }

    pub(crate) fn external_polyvar_string_expr(
        &mut self,
        arg: Expr,
        dispatches: &[(String, String)],
    ) -> Expr {
        match self.j.ek(arg) {
            ExprKind::Undefined { .. } => JE::undefined(false, &mut self.j),
            ExprKind::Str(txt) => {
                let txt = self.j.text(txt).to_string();
                JE::string(
                    &external_polyvar_string_dispatch(dispatches, &txt),
                    &mut self.j,
                )
            }
            _ => {
                let cases = dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), JE::string(target, &mut self.j)))
                    .collect();
                string_switch_iife(arg, cases, &mut self.j)
            }
        }
    }

    /// The literal tag and payload of a poly-variant block
    /// `{NAME: "tag", VAL: value}`, which pass in place.
    fn literal_polyvar_block(&self, arg: Expr) -> Option<(crate::js_ir::arena::StrId, Expr)> {
        literal_polyvar_block(&self.j, arg)
    }

    pub(crate) fn external_polyvar_event_exprs(
        &mut self,
        arg: Expr,
        dispatches: Option<&[(String, String)]>,
    ) -> Vec<Expr> {
        if let Some((txt, value)) = self.literal_polyvar_block(arg) {
            let txt = self.j.text(txt).to_string();
            let tag = match dispatches {
                Some(dispatches) => JE::string(
                    &external_polyvar_string_dispatch(dispatches, &txt),
                    &mut self.j,
                ),
                None => JE::string(&txt, &mut self.j),
            };
            return vec![tag, value];
        }
        let tag = match dispatches {
            Some(dispatches) => {
                let tag = poly_var_tag_access(arg, &mut self.j);
                self.external_polyvar_string_expr(tag, dispatches)
            }
            None => poly_var_tag_access(arg, &mut self.j),
        };
        vec![tag, poly_var_value_access(arg, &mut self.j)]
    }

    pub(crate) fn external_polyvar_int_expr(
        &mut self,
        arg: Expr,
        dispatches: &[(String, i64)],
    ) -> Expr {
        match self.j.ek(arg) {
            ExprKind::Undefined { .. } => JE::undefined(false, &mut self.j),
            ExprKind::Str(txt) => {
                let value = external_polyvar_int_dispatch(dispatches, self.j.text(txt));
                int_expr(value as i32, &mut self.j)
            }
            _ => {
                let cases = dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), int_expr(*target as i32, &mut self.j)))
                    .collect();
                string_switch_iife(arg, cases, &mut self.j)
            }
        }
    }

    pub(crate) fn external_polyvar_unwrap_expr(&mut self, arg: Expr) -> Expr {
        if let ExprKind::CamlBlock(items, _, _) = self.j.ek(arg)
            && let [first, second] = self.j.exprs(items)
            && matches!(self.j.ek(*first), ExprKind::Number(_))
        {
            return *second;
        }
        poly_var_value_access(arg, &mut self.j)
    }

    pub(crate) fn pure_runtime_call_expr(
        &mut self,
        module_name: &str,
        member: &str,
        args: Vec<Expr>,
    ) -> Expr {
        let func = self.runtime_member_expr(module_name, member);
        let args = self.j.expr_list(&args);
        let info = self.j.call_id(Self::builtin_runtime_call_info());
        JE::with_comment(ExprKind::Call(func, args, info), "@__PURE__", &mut self.j)
    }

    pub(crate) fn compile_eta_wrapped_runtime_alias(
        &mut self,
        a: &LamArena,
        info: FuncId,
        body: Lam,
    ) -> Option<Expr> {
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
    ) -> Option<Expr> {
        /// The one module every field access in the chain reads from.
        enum ModuleTarget {
            Var(Ident),
            Global(Ident),
        }
        let mut module_target: Option<ModuleTarget> = None;
        let mut alias_chain = Vec::new();
        let mut cursor = lam;

        let mut note_target = |target: Lam| -> Option<()> {
            let next = match a.view(target) {
                View::Var(id) => ModuleTarget::Var(id),
                View::GlobalModule(id) => ModuleTarget::Global(id),
                _ => return None,
            };
            match (&module_target, &next) {
                (None, _) => module_target = Some(next),
                (Some(ModuleTarget::Var(current)), ModuleTarget::Var(id))
                | (Some(ModuleTarget::Global(current)), ModuleTarget::Global(id))
                    if current.same(id) => {}
                _ => return None,
            }
            Some(())
        };

        loop {
            match a.view(cursor) {
                View::Let(
                    LetKind::Alias | LetKind::Strict | LetKind::StrictOpt,
                    alias_id,
                    value,
                    body,
                ) => {
                    let (primitive, args, _) = a.as_prim(value)?;
                    let Primitive::Pfield(index, FieldDbgInfo::Module { name }) = primitive else {
                        return None;
                    };
                    if args.len() != 1 {
                        return None;
                    }
                    note_target(*args.first()?)?;

                    alias_chain.push((alias_id, *index, *name));
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
                                let (_, field_index, field_name) = alias_chain
                                    .iter()
                                    .find(|(alias_id, _, _)| alias_id.same(&arg_id))?;
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

                    return module_target.map(|target| match target {
                        ModuleTarget::Var(id) => JE::var(id, &mut self.j),
                        ModuleTarget::Global(id) => JE::qualified(
                            ModuleId {
                                id,
                                kind: Kind::Ml,
                                dynamic_import: false,
                            },
                            None,
                            &mut self.j,
                        ),
                    });
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
            .or_insert_with(|| self.id_gen.create(external_module_ident_name(module_name)));

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
    ) -> Expr {
        JE::qualified(
            self.external_module_id(module_name, default, false),
            None,
            &mut self.j,
        )
    }

    pub(crate) fn translate_scoped_module_value(
        &mut self,
        module_name: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
    ) -> Expr {
        match module_name {
            Some(module_name) => match scopes.split_first() {
                None => {
                    let default = name == "default";
                    JE::qualified(
                        self.external_module_id(module_name, default, false),
                        Some(name.to_string()),
                        &mut self.j,
                    )
                }
                Some((first_scope, rest_scopes)) => {
                    // A leading "default" scope is the module's default
                    // export: import it as such, like
                    // `external x: t = "default"`.
                    let default = first_scope == "default";
                    let mut expr = JE::qualified(
                        self.external_module_id(module_name, default, false),
                        Some(first_scope.clone()),
                        &mut self.j,
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

    pub(crate) fn optional_block(&mut self, value: Expr, identity: bool) -> Expr {
        JE::new(ExprKind::OptionalBlock(value, identity), &mut self.j)
    }

    pub(crate) fn can_inline_null_to_opt(&self, expr: Expr) -> bool {
        matches!(
            self.j.ek(expr),
            ExprKind::Var(_) | ExprKind::Undefined { .. } | ExprKind::Null
        )
    }

    pub(crate) fn null_to_opt_expr(&mut self, expr: Expr) -> Expr {
        if self.can_inline_null_to_opt(expr) {
            let test = self.is_null_expr(expr);
            let undefined = JE::undefined(false, &mut self.j);
            let some = self.optional_block(expr, false);
            JE::cond(test, undefined, some, &mut self.j)
        } else {
            self.runtime_call_expr("Primitive_option", "fromNull", vec![expr])
        }
    }

    pub(crate) fn null_undefined_to_opt_expr(&mut self, expr: Expr) -> Expr {
        if self.can_inline_null_to_opt(expr) {
            JE::cond(
                self.is_null_or_undefined_expr(expr),
                JE::undefined(false, &mut self.j),
                self.optional_block(expr, false),
                &mut self.j,
            )
        } else {
            self.runtime_call_expr("Primitive_option", "fromNullable", vec![expr])
        }
    }

    pub(crate) fn is_null_expr(&mut self, expr: Expr) -> Expr {
        JE::bin(BinOp::EqEqEq, expr, JE::null(&mut self.j), &mut self.j)
    }

    pub(crate) fn is_undefined_expr(&mut self, expr: Expr) -> Expr {
        JE::bin(
            BinOp::EqEqEq,
            expr,
            JE::undefined(false, &mut self.j),
            &mut self.j,
        )
    }

    pub(crate) fn is_null_or_undefined_expr(&mut self, expr: Expr) -> Expr {
        JE::is_null_or_undefined(expr, &mut self.j)
    }

    pub(crate) fn some_expr(&mut self, value: Expr) -> Expr {
        let identity = matches!(
            self.j.ek(value),
            ExprKind::Null
                | ExprKind::Object(_)
                | ExprKind::Number(_)
                | ExprKind::CamlBlock(_, _, _)
                | ExprKind::Array(_, _)
                | ExprKind::Str(_)
                | ExprKind::TemplateLiteral(_)
        );
        self.optional_block(value, identity)
    }

    pub(crate) fn val_from_option_expr(&mut self, arg: Expr) -> Expr {
        match self.j.ek(arg) {
            ExprKind::OptionalBlock(inner, _) => inner,
            _ => self.runtime_call_expr("Primitive_option", "valFromOption", vec![arg]),
        }
    }

    pub(crate) fn is_not_none_expr(&mut self, arg: Expr) -> Expr {
        match self.j.ek(arg) {
            ExprKind::Undefined { .. } => JE::bool(false, &mut self.j),
            ExprKind::OptionalBlock(_, _) => JE::bool(true, &mut self.j),
            _ => {
                let undefined = JE::undefined(false, &mut self.j);
                JE::bin(BinOp::NotEqEq, arg, undefined, &mut self.j)
            }
        }
    }

    pub(crate) fn external_arg_effect(&self, arg: Expr) -> Option<Expr> {
        if expression_has_no_side_effects(&self.j, arg) {
            None
        } else {
            Some(arg)
        }
    }

    pub(crate) fn fuse_external_effects(&mut self, effects: Vec<Expr>) -> Option<Expr> {
        let mut effects = effects.into_iter();
        let first = effects.next()?;
        Some(effects.fold(first, |acc, e| js_seq(acc, e, &mut self.j)))
    }

    pub(crate) fn add_external_effect(&mut self, effect: Option<Expr>, expr: Expr) -> Expr {
        match effect {
            Some(effect) => js_seq(effect, expr, &mut self.j),
            None => expr,
        }
    }

    pub(crate) fn lower_object_external_arg_value_and_effect(
        &mut self,
        raw_arg: Expr,
        arg_label: LabelNoname,
        arg_type: &Attr,
    ) -> (Expr, Option<Expr>) {
        let (values, effect) =
            self.lower_external_arg_values_and_effect(raw_arg, arg_label, arg_type);
        match <[Expr; 1]>::try_from(values) {
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
        &mut self,
        raw_arg: Expr,
        arg_label: LabelNoname,
        arg_type: &Attr,
    ) -> (Vec<Expr>, Option<Expr>) {
        // Only `Unwrap` of an optional argument reads the raw argument again.
        let keep_raw =
            matches!(arg_type, Attr::Unwrap) && matches!(arg_label, LabelNoname::ArgOptional);
        let (arg, raw_arg) = match arg_label {
            LabelNoname::ArgOptional => {
                let raw_copy = keep_raw.then_some(raw_arg);
                (self.external_optional_to_undefined_expr(raw_arg), raw_copy)
            }
            LabelNoname::ArgLabel | LabelNoname::ArgEmpty => (raw_arg, None),
        };

        match arg_type {
            Attr::ArgCst(_) => (Vec::new(), None),
            Attr::ExternUnit => {
                let effect = self.external_arg_effect(arg);
                let values = if matches!(arg_label, LabelNoname::ArgEmpty) {
                    Vec::new()
                } else {
                    vec![JE::undefined(true, &mut self.j)]
                };
                (values, effect)
            }
            Attr::Ignore => (Vec::new(), self.external_arg_effect(arg)),
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
        &mut self,
        arg_types: &[Param],
        args: Vec<Expr>,
    ) -> (Vec<Expr>, Option<Expr>) {
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
                        .unwrap_or_else(|| JE::undefined(false, &mut self.j));
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
        mut args: Vec<Expr>,
    ) -> Vec<Expr> {
        let trailing_optional_undefined_count = arg_types
            .iter()
            .rev()
            .zip(args.iter().rev())
            .take_while(|(arg_spec, arg)| {
                matches!(arg_spec.arg_label, LabelNoname::ArgOptional)
                    && matches!(self.j.ek(**arg), ExprKind::Undefined { is_unit: false })
            })
            .count();

        if trailing_optional_undefined_count > 0 {
            args.truncate(args.len() - trailing_optional_undefined_count);
        }

        args
    }

    pub(crate) fn assemble_external_args_with_splice(
        &mut self,
        arg_types: &[Param],
        args: Vec<Expr>,
    ) -> (Vec<Expr>, Option<Expr>) {
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
                        .unwrap_or_else(|| JE::undefined(false, &mut self.j));
                    let is_last_runtime_arg = runtime_args.peek().is_none();

                    if is_last_runtime_arg {
                        match self.j.ek(arg) {
                            ExprKind::Array(items, _) => {
                                assembled.extend_from_slice(self.j.exprs(items));
                            }
                            _ => {
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
                assembled.push(JE::new(ExprKind::Spread(last), &mut self.j));
            }
        }

        (assembled, self.fuse_external_effects(effects))
    }

    pub(crate) fn assemble_external_args(
        &mut self,
        arg_types: &[Param],
        args: Vec<Expr>,
        splice: bool,
    ) -> (Vec<Expr>, Option<Expr>) {
        if splice {
            self.assemble_external_args_with_splice(arg_types, args)
        } else {
            self.assemble_external_args_no_splice(arg_types, args)
        }
    }

    pub(crate) fn compile_js_object_create(
        &mut self,
        obj_params: &[ObjParam],
        args: Vec<Expr>,
        prelude: &mut Block,
    ) -> Expr {
        #[derive(Clone)]
        struct PendingOptionalAssignment {
            name: String,
            arg: Expr,
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
                            .unwrap_or_else(|| JE::undefined(false, &mut self.j));
                        if let Some(effect) = self.external_arg_effect(arg) {
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
                            .unwrap_or_else(|| JE::undefined(false, &mut self.j));
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
                        .unwrap_or_else(|| JE::undefined(false, &mut self.j));

                    match self.j.ek(arg) {
                        ExprKind::Undefined { .. } => continue,
                        // Match OCaml's Js_of_lam_option.destruct_optional:
                        // statically-known `Some x` goes straight into the
                        // object literal, while unknown option values keep the
                        // temp-object plus conditional assignment path.
                        ExprKind::OptionalBlock(inner, _) => {
                            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                                inner,
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
                                arg: JE::new(other, &mut self.j),
                                arg_type: obj_param.obj_arg_type.clone(),
                                for_sure_no_nested_option: *for_sure_no_nested_option,
                            });
                        }
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        let effect = self.fuse_external_effects(effects);
        let props: Vec<(crate::js_ir::arena::PropName, Expr)> = props
            .into_iter()
            .map(|(name, value)| (self.prop_name(name), value))
            .collect();
        let props = self.j.prop_list(&props);
        let object = JE::new(ExprKind::Object(props), &mut self.j);
        let object = self.add_external_effect(effect, object);

        if optional_assignments.is_empty() {
            return object;
        }

        let obj = self.fresh_tmp_ident();
        prelude.push(JS::variable(
            VarDecl {
                ident: obj,
                value: Some(object),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));

        for pending in optional_assignments {
            let prepared = if self.expr_is_simple(pending.arg) {
                pending.arg
            } else {
                let tmp = self.fresh_tmp_ident();
                prelude.push(JS::variable(
                    VarDecl {
                        ident: tmp,
                        value: Some(pending.arg),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                ));
                JE::var(tmp, &mut self.j)
            };

            let value_arg = if pending.for_sure_no_nested_option {
                prepared
            } else {
                self.val_from_option_expr(prepared)
            };
            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                value_arg,
                LabelNoname::ArgEmpty,
                &pending.arg_type,
            );
            let cond = JE::bin(
                BinOp::NotEqEq,
                prepared,
                JE::undefined(false, &mut self.j),
                &mut self.j,
            );
            let obj_var = JE::var(obj, &mut self.j);
            let target = self.static_index(obj_var, &pending.name);
            let value = self.add_external_effect(effect, value);
            let assign = JE::bin(BinOp::Eq, target, value, &mut self.j);
            prelude.push(JS::if_(
                cond,
                &[JS::exp(assign, &mut self.j)],
                &[],
                &mut self.j,
            ));
        }

        JE::var(obj, &mut self.j)
    }

    pub(crate) fn expr_is_simple(&self, expr: Expr) -> bool {
        matches!(
            self.j.ek(expr),
            ExprKind::Var(_)
                | ExprKind::Undefined { .. }
                | ExprKind::Null
                | ExprKind::Bool(_)
                | ExprKind::Number(_)
                | ExprKind::Str(_)
        )
    }

    /// `Lam_compile_external_call.jsx_callee`: the function a JSX external
    /// refers to. Translcore only builds `Pjsx` for `Decl_val` externals that
    /// aren't the module itself.
    pub(crate) fn jsx_callee(&mut self, decl: &ExternalDecl) -> Expr {
        match (&decl.kind, &decl.module_) {
            (DeclKind::DeclVal { name }, None) => {
                self.translate_scoped_module_value(None, name, &decl.scopes)
            }
            (DeclKind::DeclVal { name }, Some(ModuleSource::ModuleNamed(emn))) => {
                self.translate_scoped_module_value(Some(emn), name, &decl.scopes)
            }
            _ => unreachable!("Pjsx of an external that isn't a Decl_val"),
        }
    }

    /// `Pjsx` (lam_compile_primitive.ml): the arguments are the tag, the
    /// spread, the props, the children and the key. Optional props that are
    /// statically `undefined` are left out.
    pub(crate) fn compile_jsx(&mut self, jsx: &JsxElement, args: Vec<Expr>) -> Expr {
        let mut args = args.into_iter();
        let tag = args.next().expect("Pjsx without a tag");
        let spread = jsx
            .jsx_spread
            .then(|| args.next().expect("Pjsx without its spread"));
        let props = jsx
            .jsx_props
            .iter()
            .zip(args.by_ref())
            .filter(|((_, optional), value)| {
                !(*optional && matches!(self.j.ek(*value), ExprKind::Undefined { .. }))
            })
            .map(|((name, _), value)| (name.clone(), value))
            .collect::<Vec<_>>();
        let children = jsx
            .jsx_children
            .map(|n| args.by_ref().take(n).collect::<Vec<_>>());
        let key = match (jsx.jsx_key, args.next(), args.next()) {
            (true, Some(key), None) => Some(self.external_optional_to_undefined_expr(key)),
            (false, None, None) => None,
            _ => unreachable!("Pjsx with a wrong number of arguments"),
        };
        let callee = self.jsx_callee(&jsx.jsx_ffi);
        let props: Vec<_> = props
            .into_iter()
            .map(|(name, value)| (PropName::Lit(self.j.str(&name)), value))
            .collect();
        let props = self.j.prop_list(&props);
        let children = children.map(|children| self.j.expr_list(&children));
        let info = self.j.jsx_id(JsxInfo {
            callee,
            tag,
            spread,
            props,
            children,
            key,
            multi: jsx.jsx_multi,
            fragment: jsx.jsx_fragment,
        });
        self.j.expr(ExprKind::Jsx(info))
    }

    /// `Lam_compile_external_call.translate_ffi`.
    pub(crate) fn compile_js_call(
        &mut self,
        prim_name: &str,
        arg_types: &[Param],
        decl: &ExternalDecl,
        args: Vec<Expr>,
    ) -> Expr {
        let call_info = CallInfo::default();
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
                let call = JE::call(target, &args, call_info, &mut self.j);
                self.add_external_effect(effect, call)
            }
            // the module itself, as a class
            DeclKind::DeclNew { .. } if module_itself => {
                let target = self.external_module_binding(&module_itself_name(), false);
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let args = self.j.expr_list(&args);
                let expr = JE::new(ExprKind::New(target, Some(args)), &mut self.j);
                self.add_external_effect(effect, expr)
            }
            _ if module_itself => unreachable!("rejected during digestion"),
            // a global value
            DeclKind::DeclVal { name } if decl.effective_arity == 0 => {
                let value = self.translate_scoped_module_value(named_module, name, scopes);
                if args.is_empty() {
                    value
                } else {
                    JE::call(value, &args, call_info, &mut self.j)
                }
            }
            // a global (possibly module-scoped) function call
            DeclKind::DeclVal { name } => {
                let target = self.translate_scoped_module_value(named_module, name, scopes);
                let (args, effect) = self.assemble_external_args(arg_types, args, splice);
                let call = JE::call(target, &args, call_info, &mut self.j);
                self.add_external_effect(effect, call)
            }
            DeclKind::DeclNew { name } => {
                let (args, effect) = self.assemble_external_args(arg_types, args, splice);
                let target = self.translate_scoped_module_value(named_module, name, scopes);
                let args = self.j.expr_list(&args);
                let expr = JE::new(ExprKind::New(target, Some(args)), &mut self.j);
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
                let receiver = self.apply_scoped_access(receiver, scopes);
                let target = self.static_index(receiver, name);
                let call = JE::call(target, &rest_args, call_info, &mut self.j);
                self.add_external_effect(effect, call)
            }
            DeclKind::DeclGet { name } => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expr; 1]>::try_from(assembled) {
                    Ok([receiver]) => {
                        let receiver = self.apply_scoped_access(receiver, scopes);
                        self.static_index(receiver, name)
                    }
                    Err(_) => panic!(
                        "Internal compiler error: @get external called with wrong number of arguments. Expected exactly one object argument."
                    ),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclSet { name } => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expr; 2]>::try_from(assembled) {
                    Ok([receiver, value]) => {
                        let receiver = self.apply_scoped_access(receiver, scopes);
                        let target = self.static_index(receiver, name);
                        JE::bin(BinOp::Eq, target, value, &mut self.j)
                    }
                    Err(_) => unreachable!("@set external takes an object and a value"),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclGetIndex => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expr; 2]>::try_from(assembled) {
                    Ok([receiver, index]) => JE::new(
                        ExprKind::ArrayIndex(self.apply_scoped_access(receiver, scopes), index),
                        &mut self.j,
                    ),
                    Err(_) => unreachable!("@get_index external takes an object and an index"),
                };
                self.add_external_effect(effect, expr)
            }
            DeclKind::DeclSetIndex => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match <[Expr; 3]>::try_from(assembled) {
                    Ok([receiver, index, value]) => JE::bin(
                        BinOp::Eq,
                        JE::new(
                            ExprKind::ArrayIndex(self.apply_scoped_access(receiver, scopes), index),
                            &mut self.j,
                        ),
                        value,
                        &mut self.j,
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
    fn wrap_then_path(&mut self, import: Expr, path: &[String]) -> Expr {
        let param = self.fresh_ident("m");
        let mut value = JE::var(param, &mut self.j);
        for segment in path {
            value = self.static_index(value, segment);
        }
        let ret = JS::return_(value, &mut self.j);
        let callback = crate::lambda::js_exp_make::fun_expr(
            false,
            &[param],
            &[ret],
            false,
            false,
            &mut self.j,
        );
        let then = self.static_index(import, "then");
        JE::call(then, &[callback], CallInfo::default(), &mut self.j)
    }

    fn import_of_path(path: String, j: &mut JsArena) -> Expr {
        let import = JE::var(Ident::create_persistent("import"), j);
        let path = JE::string(&path, j);
        JE::call(import, &[path], CallInfo::default(), j)
    }

    /// `Lam_compile_primitive.translate` for `Pimport source`: the module is
    /// registered as a dynamic dependency here, the single place that knows
    /// about it, and the emitted form is `import("path")[.then(m => m.<name>)]`.
    pub(crate) fn compile_import(&mut self, loc: &LamLoc, source: &ImportSource) -> Expr {
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
                    return JE::undefined(false, &mut self.j);
                };
                let import = Self::import_of_path(import_path, &mut self.j);
                match path.as_slice() {
                    [] => import,
                    [name] => self.wrap_then_path(import, &[js_export_name(name)]),
                    _ => {
                        // Nested `make` values are importable through their flat export.
                        match crate::lambda::flat_make_name(path) {
                            Some(name) => self.wrap_then_path(import, &[js_export_name(&name)]),
                            None => {
                                self.report_diagnostic(loc, invalid);
                                JE::undefined(false, &mut self.j)
                            }
                        }
                    }
                }
            }
            ImportSource::ImportExternal { module_, path } => {
                let default = path.len() == 1 && path[0] == "default";
                let oid = self.external_module_id(module_, default, true);
                self.dynamic_import_modules.push(oid.clone());
                let import = Self::import_of_path(module_.bundle.clone(), &mut self.j);
                if path.is_empty() {
                    import
                } else {
                    self.wrap_then_path(import, path)
                }
            }
        }
    }

    pub(crate) fn translate_scoped_global_value(&mut self, name: &str, scopes: &[String]) -> Expr {
        let mut expr = match scopes.split_first() {
            Some((head, rest)) => {
                let mut expr = JE::var(Ident::create_persistent(head), &mut self.j);
                for scope in rest {
                    expr = self.static_index(expr, scope);
                }
                expr
            }
            None => JE::var(Ident::create_persistent(name), &mut self.j),
        };
        if !scopes.is_empty() {
            expr = self.static_index(expr, name);
        }
        expr
    }

    pub(crate) fn apply_scoped_access(&mut self, mut expr: Expr, scopes: &[String]) -> Expr {
        for scope in scopes {
            expr = self.static_index(expr, scope);
        }
        expr
    }

    pub(crate) fn static_index(&mut self, target: Expr, field: &str) -> Expr {
        JE::static_index(target, field, None, &mut self.j)
    }

    pub(crate) fn fresh_ident(&self, prefix: &str) -> Ident {
        self.id_gen.create(prefix)
    }

    pub(crate) fn fresh_tmp_ident(&self) -> Ident {
        self.fresh_ident("tmp")
    }
}
