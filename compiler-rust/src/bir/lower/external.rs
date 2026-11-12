//! X: external calls, scoped targets, and indexed module references.
use super::*;
use crate::bir::{ImportId, PrimId};
use crate::bir::j::plain;
use crate::lambda::lam_primitive::{DeclKind, ExternalModuleName, JsCall, ModuleBindName, ModuleSource};
use smallvec::SmallVec;

impl State {
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
