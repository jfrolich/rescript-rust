//! X: external calls, scoped targets, and indexed module references.
use super::*;
use crate::bir::{ImportId, PrimId};
use crate::bir::j::plain;
use crate::lambda::lam_primitive::{DeclKind, ExternalModuleName, JsCall, ModuleBindName, ModuleSource};
use smallvec::SmallVec;

impl State {
    /// P:84 compile_js_object_get. O(receiver field spine), holding only
    /// receivers with a prelude that cannot be safely read in place.
    pub(super) fn hold_external_receiver(&mut self, _cx: Cx, mut arg: Out) -> Out {
        if !self.statements.has_statements(arg.stmts) { return arg; }
        let value = arg.value.expect("receiver value");
        let mut root = value;
        let duplicable = loop {
            match self.arena.view(root) {
                View::JDot { object, .. } => root = object,
                View::Var { .. } | View::JQualified { .. } | View::JBool | View::JStr { .. }
                | View::JTemplate { .. } | View::JNumber { .. } => break true,
                _ => break false,
            }
        };
        if !duplicable {
            let var = self.fresh_variable("tmp");
            let statement = crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, value);
            self.statements.fill_held(arg.stmts.start + arg.stmts.len - 1, &[statement]);
            arg.value = Some(self.pure_expression(View::Var { var }, 0));
        }
        arg
    }

    /// X:762 lower_object_external_arg_value_and_effect. O(conversion work).
    fn lower_object_external_arg_value_and_effect(&mut self, cx: Cx, arg: NodeId, label: crate::lambda::lam_primitive::LabelNoname, attr: &crate::lambda::lam_primitive::Attr) -> (NodeId, Option<NodeId>) {
        let (values, effect) = self.lower_external_arg_values_and_effect(cx, arg, label, attr);
        assert_eq!(values.len(), 1, "object argument must produce exactly one value");
        (values[0], effect)
    }

    /// X:972 compile_js_object_create. O(specs + argument conversion work).
    /// Pending fields retain only their spec index and owned value handle.
    pub(super) fn compile_js_object_create(&mut self, cx: Cx, specs: &[crate::lambda::lam_primitive::ObjParam], args: SmallVec<[NodeId; 4]>) -> NodeId {
        use crate::lambda::lam_primitive::{Attr, Label, LabelNoname};
        let mut args = args.into_iter();
        let mut keys = Vec::new();
        let mut values = Vec::new();
        let mut effects: SmallVec<[NodeId; 4]> = SmallVec::new();
        let mut pending: Vec<(u32, NodeId)> = Vec::new();
        for (i, spec) in specs.iter().enumerate() {
            self.primitive_steps += 1;
            match &spec.obj_arg_label {
                Label::ObjEmpty => {
                    if !matches!(spec.obj_arg_type, Attr::ArgCst(_)) {
                        let arg = args.next().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                        effects.extend(self.external_arg_effect(cx, arg));
                    }
                }
                Label::ObjLabel { name } => {
                    let value = if let Attr::ArgCst(cst) = &spec.obj_arg_type {
                        self.compile_external_arg_const(cx, cst)
                    } else {
                        let arg = args.next().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                        let (value, effect) = self.lower_object_external_arg_value_and_effect(cx, arg, LabelNoname::ArgLabel, &spec.obj_arg_type);
                        effects.extend(effect);
                        value
                    };
                    keys.push(crate::bir::PropertyKey::Literal(self.arena.intern_text(name)));
                    values.push(value);
                }
                Label::ObjOptional { name, .. } => {
                    let arg = args.next().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                    match self.arena.view(arg) {
                        View::JUndefined => self.arena.release(arg),
                        View::JOptional { value } => {
                            self.arena.detach(value); self.arena.release(arg);
                            let (value, effect) = self.lower_object_external_arg_value_and_effect(cx, value, LabelNoname::ArgLabel, &spec.obj_arg_type);
                            effects.extend(effect);
                            keys.push(crate::bir::PropertyKey::Literal(self.arena.intern_text(name)));
                            values.push(value);
                        }
                        _ => pending.push((u32::try_from(i).expect("object spec capacity"), arg)),
                    }
                }
            }
        }
        debug_assert!(args.next().is_none());
        let effect = self.fuse_external_effects(cx, effects);
        let info = self.arena.js_info(crate::bir::JsPayload::Object(keys));
        let object = plain::node(&mut self.arena, View::JObject { values: &values, info }, 0);
        let object = self.add_external_effect(cx, effect, object);
        if pending.is_empty() { return object; }
        let obj = self.fresh_variable("tmp");
        let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Variable, obj, object);
        self.statements.push(declaration);
        for (i, mut arg) in pending {
            self.primitive_steps += 1;
            let spec = &specs[i as usize];
            let Label::ObjOptional { name, for_sure_no_nested_option } = &spec.obj_arg_label else { unreachable!() };
            if !self.optional_duplicable(cx, arg) {
                let tmp = self.fresh_variable("tmp");
                let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Strict, tmp, arg);
                self.statements.push(declaration);
                arg = self.pure_expression(View::Var { var: tmp }, 0);
            }
            let test_arg = self.arena.copy_subtree(arg, &[]);
            let value_arg = if *for_sure_no_nested_option { arg }
                else { self.primitive_runtime("Primitive_option", "valFromOption", &[arg]) };
            let (value, effect) = self.lower_object_external_arg_value_and_effect(cx, value_arg, LabelNoname::ArgEmpty, &spec.obj_arg_type);
            let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
            let test = crate::bir::j::norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::NotEqEq, test_arg, undefined);
            let receiver = self.pure_expression(View::Var { var: obj }, 0);
            let target = self.static_member(receiver, name);
            let value = self.add_external_effect(cx, effect, value);
            let assign = plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, value);
            let statement = crate::bir::j::norm::js1_exp(&mut self.arena, assign);
            let branch = crate::bir::j::norm::js3_simplify_if(&mut self.arena, test, vec![statement], vec![]);
            self.statements.push(branch);
        }
        self.pure_expression(View::Var { var: obj }, 0)
    }

    /// X:581 external_module_id. O(1) for a previously seen primitive; the
    /// first reference interns its bundle and constructs import metadata.
    pub(super) fn external_module_cached(&mut self, _cx: Cx, primitive: PrimId, external: &ExternalModuleName, default: bool, dynamic: bool) -> ImportId {
        if self.external_references.len() <= primitive.index() {
            self.external_references.resize(primitive.index() + 1, None);
        }
        if let Some(module) = self.external_references[primitive.index()] { return module; }
        let module = self.external_module(external, default, dynamic);
        self.external_references[primitive.index()] = Some(module);
        module
    }

    /// X:1434 apply_scoped_access. O(scope segments + spelling bytes).
    fn apply_scoped_access(&mut self, _cx: Cx, mut value: NodeId, scopes: &[String]) -> NodeId {
        for scope in scopes { self.primitive_steps += 1; value = self.static_member(value, scope); }
        value
    }

    /// X:1417 translate_scoped_global_value. O(scope segments + spelling bytes).
    fn translate_scoped_global_value(&mut self, cx: Cx, name: &str, scopes: &[String]) -> NodeId {
        let head = scopes.first().map_or(name, String::as_str);
        let var = self.fresh_variable(head);
        self.arena.mark_js_global(var);
        self.idents[var.index()] = Ident::create_persistent(head);
        let value = self.pure_expression(View::Var { var }, 0);
        if scopes.is_empty() { value } else {
            let value = self.apply_scoped_access(cx, value, &scopes[1..]);
            self.static_member(value, name)
        }
    }

    /// X:621 translate_scoped_module_value. O(scope segments + spelling bytes)
    /// after the first primitive's module binding has been registered.
    fn translate_scoped_module_value(&mut self, cx: Cx, primitive: PrimId, module: Option<&ExternalModuleName>, name: &str, scopes: &[String]) -> NodeId {
        let Some(module) = module else { return self.translate_scoped_global_value(cx, name, scopes); };
        let head = scopes.first().map_or(name, String::as_str);
        let module = self.external_module_cached(cx, primitive, module, head == "default", false);
        let member = Some(self.arena.intern_text(head));
        let value = plain::node(&mut self.arena, View::JQualified { module, member }, 0);
        if scopes.is_empty() { value } else {
            let value = self.apply_scoped_access(cx, value, &scopes[1..]);
            self.static_member(value, name)
        }
    }

    /// X:609 external_module_binding. O(1) after first primitive registration.
    fn external_module_binding(&mut self, cx: Cx, primitive: PrimId, name: &str) -> NodeId {
        let module = if let Some(Some(module)) = self.external_references.get(primitive.index()) { *module } else {
            self.external_module_cached(cx, primitive, &ExternalModuleName {
                bundle: name.to_owned(), module_bind_name: ModuleBindName::PhintNothing, import_attributes: None,
            }, false, false)
        };
        plain::node(&mut self.arena, View::JQualified { module, member: None }, 0)
    }

    /// X:1202 compile_js_call. O(arguments + conversions + scope spelling).
    /// All operands are already held and sequenced; this consumes their roots.
    pub(super) fn compile_js_call(&mut self, cx: Cx, primitive: PrimId, call: &JsCall, args: SmallVec<[NodeId; 4]>) -> NodeId {
        let decl = &call.ffi;
        let specs = &call.arg_types;
        let itself = matches!(decl.module_, Some(ModuleSource::ModuleItself));
        let module = match &decl.module_ { Some(ModuleSource::ModuleNamed(module)) => Some(module), _ => None };
        match &decl.kind {
            DeclKind::DeclVal { .. } if itself && decl.effective_arity == 0 => {
                for value in args { self.arena.release(value); }
                self.external_module_binding(cx, primitive, &call.prim_name)
            }
            DeclKind::DeclVal { .. } if itself => {
                let target = self.external_module_binding(cx, primitive, &call.prim_name);
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let value = self.call_node(target, &args, Default::default());
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclNew { .. } if itself => {
                let target = self.external_module_binding(cx, primitive, &call.prim_name);
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let value = plain::node(&mut self.arena, View::JNew { callee: target, args: &args }, 1);
                self.add_external_effect(cx, effect, value)
            }
            _ if itself => unreachable!("invalid module-itself declaration"),
            DeclKind::DeclVal { name } if decl.effective_arity == 0 => {
                let target = self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                if args.is_empty() { target } else { self.call_node(target, &args, Default::default()) }
            }
            DeclKind::DeclVal { name } => {
                let target = self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let value = self.call_node(target, &args, Default::default());
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclNew { name } => {
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let target = self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                let value = plain::node(&mut self.arena, View::JNew { callee: target, args: &args }, 1);
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclSend { name } => {
                let mut args = args.into_iter();
                let receiver = args.next().expect("send receiver");
                let (args, effect) = self.assemble_external_args(cx, specs.get(1..).unwrap_or(&[]), args.collect(), decl.variadic);
                let receiver = self.apply_scoped_access(cx, receiver, &decl.scopes);
                let target = self.static_member(receiver, name);
                let value = self.call_node(target, &args, Default::default());
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclGet { name } | DeclKind::DeclSet { name } => {
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let receiver = self.apply_scoped_access(cx, args[0], &decl.scopes);
                let target = self.static_member(receiver, name);
                let value = if matches!(decl.kind, DeclKind::DeclSet { .. }) {
                    assert_eq!(args.len(), 2);
                    plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, args[1])
                } else { assert_eq!(args.len(), 1); target };
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclGetIndex | DeclKind::DeclSetIndex => {
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let receiver = self.apply_scoped_access(cx, args[0], &decl.scopes);
                let target = plain::node(&mut self.arena, View::JIndex { object: receiver, index: args[1] }, 0);
                let value = if matches!(decl.kind, DeclKind::DeclSetIndex) {
                    assert_eq!(args.len(), 3);
                    plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, args[2])
                } else { assert_eq!(args.len(), 2); target };
                self.add_external_effect(cx, effect, value)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{arena::LamArena, lam_constant::Constant, lam_primitive::{Primitive, ExternalDecl, Param}, LamLoc};

    #[test]
    fn objects_and_methods_match_legacy_in_all_continuations() {
        use crate::lambda::lam_primitive::{Attr, Label, ObjParam};
        assert_eq!(std::mem::size_of::<(u32, NodeId)>(), 8);
        for shape in 0..4 {
            for nested in [false, true] {
                let mut a = LamArena::new();
                let arg = match shape {
                    0 => a.const_(Constant::JsUndefined { is_unit: false }),
                    1 => {
                        let value = a.const_(Constant::Int { i: 42, comment: None });
                        a.prim_raw(Primitive::Psome, &[value], LamLoc::NONE)
                    }
                    2 => a.var(Ident::new("opt", 10, crate::ident::IdentFlags::NONE)),
                    _ => a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE),
                };
                let later = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
                let root = a.prim_raw(Primitive::PjsObjectCreate(vec![
                    ObjParam { obj_arg_type: Attr::Nothing, obj_arg_label: Label::ObjOptional { name: "optional".into(), for_sure_no_nested_option: nested } },
                    ObjParam { obj_arg_type: Attr::Nothing, obj_arg_label: Label::ObjLabel { name: "required".into() } },
                ]), &[arg, later], LamLoc::NONE);
                oracle_tests::compare(a, root);
            }
        }
        for primitive in [Primitive::PjsObjectGet("field".into()), Primitive::PjsObjectSet("field".into()), Primitive::PjsFnMethod] {
            let mut a = LamArena::new();
            let receiver = a.var(Ident::new("obj", 10, crate::ident::IdentFlags::NONE));
            let args = if matches!(primitive, Primitive::PjsObjectSet(_)) {
                vec![receiver, a.const_(Constant::Int { i: 1, comment: None })]
            } else { vec![receiver] };
            let root = a.prim_raw(primitive, &args, LamLoc::NONE);
            oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn variadic_arguments_match_legacy() {
        use crate::lambda::lam_primitive::{Attr, LabelNoname};
        use crate::types::external_ffi_types::Cst;
        for literal in [false, true] {
            for trailing_constant in [false, true] {
                let mut a = LamArena::new();
                let arg = if literal {
                    let values: Vec<_> = (0..3).map(|i| a.const_(Constant::Int { i, comment: None })).collect();
                    a.prim_raw(Primitive::Pmakearray, &values, LamLoc::NONE)
                } else { a.var(Ident::new("args", 10, crate::ident::IdentFlags::NONE)) };
                let mut specs = vec![Param::dummy()];
                if trailing_constant { specs.push(Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::ArgCst(Cst::ArgIntLit(7)) }); }
                let root = a.prim_raw(Primitive::PjsCall(Box::new(JsCall {
                    prim_name: "invoke".into(), arg_types: specs,
                    ffi: ExternalDecl { kind: DeclKind::DeclVal { name: "invoke".into() }, module_: None,
                        scopes: vec![], variadic: true, effective_arity: 1 },
                })), &[arg], LamLoc::NONE);
                oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn calls_and_access_match_legacy_in_all_continuations() {
        for (kind, count) in [
            (DeclKind::DeclVal { name: "invoke".into() }, 0),
            (DeclKind::DeclVal { name: "invoke".into() }, 2),
            (DeclKind::DeclNew { name: "Class".into() }, 2),
            (DeclKind::DeclSend { name: "method".into() }, 2),
            (DeclKind::DeclGet { name: "field".into() }, 1),
            (DeclKind::DeclSet { name: "field".into() }, 2),
            (DeclKind::DeclGetIndex, 2), (DeclKind::DeclSetIndex, 3),
        ] {
            for scoped in [false, true] {
                let mut a = LamArena::new();
                let args: Vec<_> = (0..count).map(|i| a.const_(Constant::Int { i, comment: None })).collect();
                let root = a.prim_raw(Primitive::PjsCall(Box::new(JsCall {
                    prim_name: "invoke".into(), arg_types: vec![Param::dummy(); count as usize],
                    ffi: ExternalDecl { kind: kind.clone(), module_: None, scopes: if scoped { vec!["scope".into()] } else { vec![] }, variadic: false, effective_arity: i64::from(count) },
                })), &args, LamLoc::NONE);
                oracle_tests::compare(a, root);
            }
        }
        let mut a = LamArena::new();
        let func = a.var(Ident::new("f", 10, crate::ident::IdentFlags::NONE));
        let arg = a.const_(Constant::Int { i: 1, comment: None });
        let root = a.prim_raw(Primitive::PjsApply, &[func, arg], LamLoc::NONE);
        oracle_tests::compare(a, root);
    }
}
