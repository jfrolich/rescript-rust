//! X: external calls, scoped targets, and indexed module references.
use super::*;
use crate::bir::j::plain;
use crate::bir::{ImportId, PrimId};
use crate::lambda::lam_primitive::{
    DeclKind, ExternalModuleName, JsCall, ModuleBindName, ModuleSource,
};

impl State {
    /// P:84 compile_js_object_get. O(receiver field spine), holding only
    /// receivers with a prelude that cannot be safely read in place.
    pub(super) fn hold_external_receiver(&mut self, _cx: Cx, mut arg: Out) -> Out {
        if !self.statements.has_statements(arg.stmts) {
            return arg;
        }
        let value = arg.value.expect("receiver value");
        let mut root = value;
        let duplicable = loop {
            match self.arena.view(root) {
                View::JDot { object, .. } => root = object,
                View::Var { .. }
                | View::JQualified { .. }
                | View::JBool
                | View::JStr { .. }
                | View::JTemplate { .. }
                | View::JNumber { .. } => break true,
                _ => break false,
            }
        };
        if !duplicable {
            let var = self.fresh_variable("tmp");
            let statement = crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, value);
            self.statements
                .fill_held(arg.stmts.start + arg.stmts.len - 1, &[statement]);
            arg.value = Some(self.pure_expression(View::Var { var }, 0));
        }
        arg
    }

    /// X:762 lower_object_external_arg_value_and_effect. O(conversion work).
    fn lower_object_external_arg_value_and_effect(
        &mut self,
        cx: Cx,
        arg: NodeId,
        label: crate::lambda::lam_primitive::LabelNoname,
        attr: &crate::lambda::lam_primitive::Attr,
    ) -> (NodeId, Option<NodeId>) {
        let (values, effect) = self.lower_external_arg_values_and_effect(cx, arg, label, attr);
        let [Some(value), None] = values else {
            panic!("object argument must produce exactly one value")
        };
        (value, effect)
    }

    /// X:972 compile_js_object_create. O(specs + argument conversion work).
    /// Pending fields retain only their spec index and owned value handle.
    pub(super) fn compile_js_object_create(
        &mut self,
        cx: Cx,
        specs: &[crate::lambda::lam_primitive::ObjParam],
        args: crate::bir::ListId,
    ) -> NodeId {
        use crate::lambda::lam_primitive::{Attr, Label, LabelNoname};
        let argc = self.arena.lists.get(args).len();
        let mut at = 0;
        let mut keys = crate::bir::PropertySpan {
            start: u32::try_from(self.arena.pools.property_keys.len())
                .expect("property pool capacity"),
            len: 0,
        };
        self.arena.pools.property_keys.resize(
            keys.start as usize + specs.len(),
            crate::bir::PropertyKey::Symbol,
        );
        let values = self.arena.lists.push_iter(
            specs.len(),
            std::iter::repeat_n(NodeId(u32::MAX), specs.len()),
        );
        let mut effect = None;
        let mut pending = std::mem::take(&mut self.external_pending);
        debug_assert!(pending.is_empty());
        for (i, spec) in specs.iter().enumerate() {
            self.primitive_steps += 1;
            match &spec.obj_arg_label {
                Label::ObjEmpty => {
                    if !matches!(spec.obj_arg_type, Attr::ArgCst(_)) {
                        let arg = if at < argc {
                            let value = self.arena.lists.get(args)[at];
                            at += 1;
                            value
                        } else {
                            plain::node(&mut self.arena, View::JUndefined, 0)
                        };
                        let next = self.external_arg_effect(cx, arg);
                        if let Some(next) = next {
                            effect = Some(self.add_external_effect(cx, effect, next));
                        }
                    }
                }
                Label::ObjLabel { name } => {
                    let value = if let Attr::ArgCst(cst) = &spec.obj_arg_type {
                        self.compile_external_arg_const(cx, cst)
                    } else {
                        let arg = if at < argc {
                            let value = self.arena.lists.get(args)[at];
                            at += 1;
                            value
                        } else {
                            plain::node(&mut self.arena, View::JUndefined, 0)
                        };
                        let (value, next_effect) = self.lower_object_external_arg_value_and_effect(
                            cx,
                            arg,
                            LabelNoname::ArgLabel,
                            &spec.obj_arg_type,
                        );
                        if let Some(next) = next_effect {
                            effect = Some(self.add_external_effect(cx, effect, next));
                        }
                        value
                    };
                    let key = crate::bir::PropertyKey::Literal(self.arena.intern_text(name));
                    self.arena.pools.property_keys[(keys.start + keys.len) as usize] = key;
                    self.arena.lists.set(values, keys.len as usize, value);
                    keys.len += 1;
                }
                Label::ObjOptional { name, .. } => {
                    let arg = if at < argc {
                        let value = self.arena.lists.get(args)[at];
                        at += 1;
                        value
                    } else {
                        plain::node(&mut self.arena, View::JUndefined, 0)
                    };
                    match self.arena.view(arg) {
                        View::JUndefined => self.arena.release(arg),
                        View::JOptional { value } => {
                            self.arena.detach(value);
                            self.arena.release(arg);
                            let (value, next_effect) = self
                                .lower_object_external_arg_value_and_effect(
                                    cx,
                                    value,
                                    LabelNoname::ArgLabel,
                                    &spec.obj_arg_type,
                                );
                            if let Some(next) = next_effect {
                                effect = Some(self.add_external_effect(cx, effect, next));
                            }
                            let key =
                                crate::bir::PropertyKey::Literal(self.arena.intern_text(name));
                            self.arena.pools.property_keys[(keys.start + keys.len) as usize] = key;
                            self.arena.lists.set(values, keys.len as usize, value);
                            keys.len += 1;
                        }
                        _ => pending.push((u32::try_from(i).expect("object spec capacity"), arg)),
                    }
                }
            }
        }
        debug_assert_eq!(at, argc);
        self.arena.lists.truncate(values, keys.len as usize);
        let object = self.arena.object_from_list(values, keys);
        let object = self.add_external_effect(cx, effect, object);
        if pending.is_empty() {
            self.external_pending = pending;
            return object;
        }
        let obj = self.fresh_variable("tmp");
        let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Variable, obj, object);
        self.statements.push(declaration);
        for (i, mut arg) in pending.drain(..) {
            self.primitive_steps += 1;
            let spec = &specs[i as usize];
            let Label::ObjOptional {
                name,
                for_sure_no_nested_option,
            } = &spec.obj_arg_label
            else {
                unreachable!()
            };
            if !self.optional_duplicable(cx, arg) {
                let tmp = self.fresh_variable("tmp");
                let declaration =
                    crate::bir::j::declare(&mut self.arena, LetKind::Strict, tmp, arg);
                self.statements.push(declaration);
                arg = self.pure_expression(View::Var { var: tmp }, 0);
            }
            let test_arg = self.arena.copy_subtree(arg, &[]);
            let value_arg = if *for_sure_no_nested_option {
                arg
            } else {
                self.primitive_runtime("Primitive_option", "valFromOption", &[arg])
            };
            let (value, next_effect) = self.lower_object_external_arg_value_and_effect(
                cx,
                value_arg,
                LabelNoname::ArgEmpty,
                &spec.obj_arg_type,
            );
            let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
            let test = crate::bir::j::norm::je4_bin(
                &mut self.arena,
                crate::js_ir::BinOp::NotEqEq,
                test_arg,
                undefined,
            );
            let receiver = self.pure_expression(View::Var { var: obj }, 0);
            let target = self.static_member(receiver, name);
            let value = self.add_external_effect(cx, next_effect, value);
            let assign = plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, value);
            let statement = crate::bir::j::norm::js1_exp(&mut self.arena, assign);
            let yes = self.arena.lists.push(&[statement]);
            let no = self.arena.lists.push(&[]);
            let branch = crate::bir::j::norm::js3_simplify_if(&mut self.arena, test, yes, no);
            self.statements.push(branch);
        }
        self.external_pending = pending;
        self.pure_expression(View::Var { var: obj }, 0)
    }

    /// X:581 external_module_id. O(1) for a previously seen primitive; the
    /// first reference interns its bundle and constructs import metadata.
    pub(super) fn external_module_cached(
        &mut self,
        _cx: Cx,
        primitive: PrimId,
        external: &ExternalModuleName,
        default: bool,
        dynamic: bool,
    ) -> ImportId {
        if self.external_references.len() <= primitive.index() {
            self.external_references.resize(primitive.index() + 1, None);
        }
        if let Some(module) = self.external_references[primitive.index()] {
            return module;
        }
        let module = self.external_module(external, default, dynamic);
        self.external_references[primitive.index()] = Some(module);
        module
    }

    /// X:1434 apply_scoped_access. O(scope segments + spelling bytes).
    fn apply_scoped_access(&mut self, _cx: Cx, mut value: NodeId, scopes: &[String]) -> NodeId {
        for scope in scopes {
            self.primitive_steps += 1;
            value = self.static_member(value, scope);
        }
        value
    }

    /// X:1417 translate_scoped_global_value. O(scope segments + spelling bytes).
    fn translate_scoped_global_value(&mut self, cx: Cx, name: &str, scopes: &[String]) -> NodeId {
        let head = scopes.first().map_or(name, String::as_str);
        let text = self.arena.intern_text(head);
        if self.external_globals.len() <= text.index() {
            self.external_globals.resize(text.index() + 1, None);
        }
        let var = match self.external_globals[text.index()] {
            Some(var) => var,
            None => {
                let var = self.fresh_variable(head);
                self.arena.mark_js_global(var);
                self.idents[var.index()] = Ident::create_persistent(head);
                self.external_globals[text.index()] = Some(var);
                var
            }
        };
        let value = self.pure_expression(View::Var { var }, 0);
        if scopes.is_empty() {
            value
        } else {
            let value = self.apply_scoped_access(cx, value, &scopes[1..]);
            self.static_member(value, name)
        }
    }

    /// X:621 translate_scoped_module_value. O(scope segments + spelling bytes)
    /// after the first primitive's module binding has been registered.
    fn translate_scoped_module_value(
        &mut self,
        cx: Cx,
        primitive: PrimId,
        module: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
    ) -> NodeId {
        let Some(module) = module else {
            return self.translate_scoped_global_value(cx, name, scopes);
        };
        let head = scopes.first().map_or(name, String::as_str);
        let module = self.external_module_cached(cx, primitive, module, head == "default", false);
        let member = Some(self.arena.intern_text(head));
        let value = plain::node(&mut self.arena, View::JQualified { module, member }, 0);
        if scopes.is_empty() {
            value
        } else {
            let value = self.apply_scoped_access(cx, value, &scopes[1..]);
            self.static_member(value, name)
        }
    }

    /// X:609 external_module_binding. O(1) after first primitive registration.
    fn external_module_binding(&mut self, _cx: Cx, primitive: PrimId, name: &str) -> NodeId {
        let module = if let Some(Some(module)) = self.external_references.get(primitive.index()) {
            *module
        } else {
            let module =
                self.external_module_parts(name, &ModuleBindName::PhintNothing, None, false, false);
            if self.external_references.len() <= primitive.index() {
                self.external_references.resize(primitive.index() + 1, None);
            }
            self.external_references[primitive.index()] = Some(module);
            module
        };
        plain::node(
            &mut self.arena,
            View::JQualified {
                module,
                member: None,
            },
            0,
        )
    }

    /// O(arguments): consume a pooled call argument list without a transient vector.
    fn external_call_from_list(&mut self, callee: NodeId, args: crate::bir::ListId) -> NodeId {
        let info = self
            .arena
            .js_info(crate::bir::JsPayload::Call(Default::default()));
        self.arena.call_from_list(callee, args, Some(info))
    }

    /// X:1202 compile_js_call. O(arguments + conversions + scope spelling).
    /// All operands are already held and sequenced; this consumes their roots.
    pub(super) fn compile_js_call(
        &mut self,
        cx: Cx,
        primitive: PrimId,
        call: &JsCall,
        args: crate::bir::ListId,
    ) -> NodeId {
        let decl = &call.ffi;
        let specs = &call.arg_types;
        let itself = matches!(decl.module_, Some(ModuleSource::ModuleItself));
        let module = match &decl.module_ {
            Some(ModuleSource::ModuleNamed(module)) => Some(module),
            _ => None,
        };
        match &decl.kind {
            DeclKind::DeclVal { .. } if itself && decl.effective_arity == 0 => {
                for i in 0..self.arena.lists.get(args).len() {
                    let value = self.arena.lists.get(args)[i];
                    self.arena.release(value);
                }
                self.external_module_binding(cx, primitive, &call.prim_name)
            }
            DeclKind::DeclVal { .. } if itself => {
                let target = self.external_module_binding(cx, primitive, &call.prim_name);
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let value = self.external_call_from_list(target, args);
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclNew { .. } if itself => {
                let target = self.external_module_binding(cx, primitive, &call.prim_name);
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let value = self.arena.call_from_list(target, args, None);
                self.add_external_effect(cx, effect, value)
            }
            _ if itself => unreachable!("invalid module-itself declaration"),
            DeclKind::DeclVal { name } if decl.effective_arity == 0 => {
                let target =
                    self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                if self.arena.lists.get(args).is_empty() {
                    target
                } else {
                    self.external_call_from_list(target, args)
                }
            }
            DeclKind::DeclVal { name } => {
                let target =
                    self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let value = self.external_call_from_list(target, args);
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclNew { name } => {
                let (args, effect) = self.assemble_external_args(cx, specs, args, decl.variadic);
                let target =
                    self.translate_scoped_module_value(cx, primitive, module, name, &decl.scopes);
                let value = self.arena.call_from_list(target, args, None);
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclSend { name } => {
                let receiver = self.arena.lists.get(args)[0];
                let len = self.arena.lists.get(args).len();
                let args = self.arena.lists.slice(args, 1, len - 1);
                let (args, effect) = self.assemble_external_args(
                    cx,
                    specs.get(1..).unwrap_or(&[]),
                    args,
                    decl.variadic,
                );
                let receiver = self.apply_scoped_access(cx, receiver, &decl.scopes);
                let target = self.static_member(receiver, name);
                let value = self.external_call_from_list(target, args);
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclGet { name } | DeclKind::DeclSet { name } => {
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let receiver = self.arena.lists.get(args)[0];
                let receiver = self.apply_scoped_access(cx, receiver, &decl.scopes);
                let target = self.static_member(receiver, name);
                let value = if matches!(decl.kind, DeclKind::DeclSet { .. }) {
                    assert_eq!(self.arena.lists.get(args).len(), 2);
                    {
                        let value = self.arena.lists.get(args)[1];
                        plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, value)
                    }
                } else {
                    assert_eq!(self.arena.lists.get(args).len(), 1);
                    target
                };
                self.add_external_effect(cx, effect, value)
            }
            DeclKind::DeclGetIndex | DeclKind::DeclSetIndex => {
                let (args, effect) = self.assemble_external_args_no_splice(cx, specs, args);
                let receiver = self.arena.lists.get(args)[0];
                let receiver = self.apply_scoped_access(cx, receiver, &decl.scopes);
                let index = self.arena.lists.get(args)[1];
                let target = plain::node(
                    &mut self.arena,
                    View::JIndex {
                        object: receiver,
                        index,
                    },
                    0,
                );
                let value = if matches!(decl.kind, DeclKind::DeclSetIndex) {
                    assert_eq!(self.arena.lists.get(args).len(), 3);
                    {
                        let value = self.arena.lists.get(args)[2];
                        plain::bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, value)
                    }
                } else {
                    assert_eq!(self.arena.lists.get(args).len(), 2);
                    target
                };
                self.add_external_effect(cx, effect, value)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{
        LamLoc,
        arena::LamArena,
        lam_constant::Constant,
        lam_primitive::{ExternalDecl, Param, Primitive},
    };

    #[test]
    fn pooled_external_payload_sizes() {
        assert_eq!(std::mem::size_of::<crate::bir::PropertySpan>(), 8);
        assert_eq!(std::mem::size_of::<crate::bir::ListId>(), 4);
        assert_eq!(std::mem::size_of::<(u32, NodeId)>(), 8);
        assert_eq!(std::mem::size_of::<crate::bir::JsPayload>(), 40);
    }

    /// Import once, then lower the complete source node twice. The measured
    /// pass includes source traversal, constant lowering, holding, sequencing,
    /// conversion, emission, realization and release of the resulting J tree.
    fn allocation_fixture(object: bool) {
        use crate::lambda::lam_primitive::{Attr, Label, ObjParam};
        let mut source = LamArena::new();
        let count = if object { 1 } else { 10_000 };
        let width = if object { 10_000 } else { 8 };
        let primitive = if object {
            Primitive::PjsObjectCreate(
                (0..width)
                    .map(|i| ObjParam {
                        obj_arg_type: Attr::Nothing,
                        obj_arg_label: Label::ObjLabel {
                            name: format!("field{i}"),
                        },
                    })
                    .collect(),
            )
        } else {
            Primitive::PjsCall(Box::new(JsCall {
                prim_name: "invoke".into(),
                arg_types: vec![Param::dummy(); width],
                ffi: ExternalDecl {
                    kind: DeclKind::DeclVal {
                        name: "invoke".into(),
                    },
                    module_: None,
                    scopes: vec![],
                    variadic: false,
                    effective_arity: width as i64,
                },
            }))
        };
        let mut root = None;
        for _ in 0..count {
            let args: Vec<_> = (0..width)
                .map(|_| source.const_(Constant::JsUndefined { is_unit: false }))
                .collect();
            let call = source.prim_raw(primitive.clone(), &args, LamLoc::NONE);
            root = Some(root.map_or(call, |previous| source.seq(previous, call)));
        }
        let input = crate::bir::bridge::import_lambda(&source, root.unwrap()).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |state: &mut State| {
            let result = state.probe(Cx::value(), root).unwrap();
            let result = state.realize(Cx::value(), result);
            for statement in state.statements.statements(result.stmts) {
                state.arena.release(statement);
            }
            if let Some(value) = result.value {
                state.arena.release(value);
            }
            state.statements.kill(result.stmts);
        };
        let initial_lists = state.arena.lists.storage_shape().0;
        let initial_js = state.arena.pools.js.len();
        run(&mut state);
        // Append-only output pools retain the warm pass. Reserve the measured
        // growth of that pass again; stack/scratch buffers already retain theirs.
        state
            .arena
            .lists
            .reserve_test_growth(state.arena.lists.storage_shape().0 - initial_lists);
        state
            .arena
            .pools
            .js
            .reserve(state.arena.pools.js.len() - initial_js);
        state
            .arena
            .pools
            .property_keys
            .reserve(state.arena.pools.property_keys.len());
        state.free.reserve_repeat();
        let capacities = |s: &State| {
            vec![
                s.arena.nodes.capacity(),
                s.arena.parents.capacity(),
                s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(),
                s.arena.lists.storage_shape().1,
                s.arena.pools.js.capacity(),
                s.arena.pools.property_keys.capacity(),
                s.external_values.capacity(),
                s.external_pending.capacity(),
                s.traversal.work.capacity(),
                s.traversal.values.capacity(),
                s.traversal.children.capacity(),
                s.constant_work.capacity(),
                s.constant_values.capacity(),
                s.argument_outputs.capacity(),
                s.argument_values.capacity(),
                s.ffi_params.capacity(),
                s.ffi_suffix.capacity(),
            ]
        };
        let before = capacities(&state);
        let free_before = state.free.capacities();
        let visits = state.source_steps;
        let steps = state.primitive_steps;
        let allocations = allocation_counter::measure(|| run(&mut state));
        println!("whole external object={object}: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.source_steps - visits, count * (width + 2) - 1);
        assert_eq!(
            state.primitive_steps - steps,
            count * (width * if object { 4 } else { 3 } + 1)
        );
    }

    #[test]
    fn ten_thousand_external_calls_do_not_allocate() {
        allocation_fixture(false);
    }

    #[test]
    fn ten_thousand_external_object_fields_do_not_allocate() {
        allocation_fixture(true);
    }

    #[test]
    fn constant_polyvariant_test_inside_external_argument() {
        let mut a = LamArena::new();
        let value = a.const_(Constant::String("a".into()));
        let test = a.prim_raw(Primitive::PisPolyVarBlock, &[value], LamLoc::NONE);
        let three = a.const_(Constant::Int {
            i: 3,
            comment: None,
        });
        let two = a.const_(Constant::Int {
            i: 2,
            comment: None,
        });
        let arg = a.if_(test, three, two);
        let root = a.prim_raw(
            Primitive::PjsCall(Box::new(JsCall {
                prim_name: "consume".into(),
                arg_types: vec![Param::dummy()],
                ffi: ExternalDecl {
                    kind: DeclKind::DeclVal {
                        name: "consume".into(),
                    },
                    module_: None,
                    scopes: vec![],
                    variadic: false,
                    effective_arity: 1,
                },
            })),
            &[arg],
            LamLoc::NONE,
        );
        oracle_tests::compare(a, root);
    }

    #[test]
    fn module_bindings_scopes_and_attributes_match_legacy() {
        for module_itself in [false, true] {
            for default in [false, true] {
                for attributes in [false, true] {
                    let mut a = LamArena::new();
                    let arg = a.const_(Constant::Int {
                        i: 1,
                        comment: None,
                    });
                    let module_ = if module_itself {
                        ModuleSource::ModuleItself
                    } else {
                        ModuleSource::ModuleNamed(ExternalModuleName {
                            bundle: "example-module".into(),
                            module_bind_name: ModuleBindName::PhintName("hint".into()),
                            import_attributes: attributes
                                .then(|| vec![("type".into(), "json".into())]),
                        })
                    };
                    let root = a.prim_raw(
                        Primitive::PjsCall(Box::new(JsCall {
                            prim_name: "example-module".into(),
                            arg_types: vec![Param::dummy()],
                            ffi: ExternalDecl {
                                kind: DeclKind::DeclVal {
                                    name: "invoke".into(),
                                },
                                module_: Some(module_),
                                scopes: if default {
                                    vec!["default".into(), "nested".into()]
                                } else {
                                    vec![]
                                },
                                variadic: false,
                                effective_arity: 1,
                            },
                        })),
                        &[arg],
                        LamLoc::NONE,
                    );
                    oracle_tests::compare(a, root);
                }
            }
        }
    }

    #[test]
    fn ten_thousand_calls_and_object_fields_have_linear_counts() {
        use crate::lambda::lam_primitive::{Attr, Label, ObjParam};
        assert_eq!(std::mem::size_of::<[Option<VarId>; 2]>(), 16);
        for object in [false, true] {
            let mut a = LamArena::new();
            let args: Vec<_> = (0..10_000)
                .map(|i| a.const_(Constant::Int { i, comment: None }))
                .collect();
            let primitive = if object {
                Primitive::PjsObjectCreate(
                    (0..10_000)
                        .map(|i| ObjParam {
                            obj_arg_type: Attr::Nothing,
                            obj_arg_label: Label::ObjLabel {
                                name: format!("field{i}"),
                            },
                        })
                        .collect(),
                )
            } else {
                Primitive::PjsCall(Box::new(JsCall {
                    prim_name: "invoke".into(),
                    arg_types: vec![Param::dummy(); 10_000],
                    ffi: ExternalDecl {
                        kind: DeclKind::DeclVal {
                            name: "invoke".into(),
                        },
                        module_: None,
                        scopes: vec![],
                        variadic: false,
                        effective_arity: 10_000,
                    },
                }))
            };
            let root = a.prim_raw(primitive, &args, LamLoc::NONE);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let output = state.probe(Cx::value(), root).unwrap();
            assert_eq!(state.source_steps, 10_001);
            assert_eq!(state.primitive_steps, if object { 40_001 } else { 30_001 });
            assert_eq!(state.sequence_steps, 10_000);
            assert_eq!(state.statements.pushed, 0);
            let lowered = state.complete(Cx::value(), output);
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root))
                .unwrap();
        }
    }

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
                        let value = a.const_(Constant::Int {
                            i: 42,
                            comment: None,
                        });
                        a.prim_raw(Primitive::Psome, &[value], LamLoc::NONE)
                    }
                    2 => a.var(Ident::new("opt", 10, crate::ident::IdentFlags::NONE)),
                    _ => a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE),
                };
                let later = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
                let root = a.prim_raw(
                    Primitive::PjsObjectCreate(vec![
                        ObjParam {
                            obj_arg_type: Attr::Nothing,
                            obj_arg_label: Label::ObjOptional {
                                name: "optional".into(),
                                for_sure_no_nested_option: nested,
                            },
                        },
                        ObjParam {
                            obj_arg_type: Attr::Nothing,
                            obj_arg_label: Label::ObjLabel {
                                name: "required".into(),
                            },
                        },
                    ]),
                    &[arg, later],
                    LamLoc::NONE,
                );
                oracle_tests::compare(a, root);
            }
        }
        for primitive in [
            Primitive::PjsObjectGet("field".into()),
            Primitive::PjsObjectSet("field".into()),
            Primitive::PjsFnMethod,
        ] {
            let mut a = LamArena::new();
            let receiver = a.var(Ident::new("obj", 10, crate::ident::IdentFlags::NONE));
            let args = if matches!(primitive, Primitive::PjsObjectSet(_)) {
                vec![
                    receiver,
                    a.const_(Constant::Int {
                        i: 1,
                        comment: None,
                    }),
                ]
            } else {
                vec![receiver]
            };
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
                    let values: Vec<_> = (0..3)
                        .map(|i| a.const_(Constant::Int { i, comment: None }))
                        .collect();
                    a.prim_raw(Primitive::Pmakearray, &values, LamLoc::NONE)
                } else {
                    a.var(Ident::new("args", 10, crate::ident::IdentFlags::NONE))
                };
                let mut specs = vec![Param::dummy()];
                if trailing_constant {
                    specs.push(Param {
                        arg_label: LabelNoname::ArgEmpty,
                        arg_type: Attr::ArgCst(Cst::ArgIntLit(7)),
                    });
                }
                let root = a.prim_raw(
                    Primitive::PjsCall(Box::new(JsCall {
                        prim_name: "invoke".into(),
                        arg_types: specs,
                        ffi: ExternalDecl {
                            kind: DeclKind::DeclVal {
                                name: "invoke".into(),
                            },
                            module_: None,
                            scopes: vec![],
                            variadic: true,
                            effective_arity: 1,
                        },
                    })),
                    &[arg],
                    LamLoc::NONE,
                );
                oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn calls_and_access_match_legacy_in_all_continuations() {
        for (kind, count) in [
            (
                DeclKind::DeclVal {
                    name: "invoke".into(),
                },
                0,
            ),
            (
                DeclKind::DeclVal {
                    name: "invoke".into(),
                },
                2,
            ),
            (
                DeclKind::DeclNew {
                    name: "Class".into(),
                },
                2,
            ),
            (
                DeclKind::DeclSend {
                    name: "method".into(),
                },
                2,
            ),
            (
                DeclKind::DeclGet {
                    name: "field".into(),
                },
                1,
            ),
            (
                DeclKind::DeclSet {
                    name: "field".into(),
                },
                2,
            ),
            (DeclKind::DeclGetIndex, 2),
            (DeclKind::DeclSetIndex, 3),
        ] {
            for scoped in [false, true] {
                let mut a = LamArena::new();
                let args: Vec<_> = (0..count)
                    .map(|i| a.const_(Constant::Int { i, comment: None }))
                    .collect();
                let root = a.prim_raw(
                    Primitive::PjsCall(Box::new(JsCall {
                        prim_name: "invoke".into(),
                        arg_types: vec![Param::dummy(); count as usize],
                        ffi: ExternalDecl {
                            kind: kind.clone(),
                            module_: None,
                            scopes: if scoped { vec!["scope".into()] } else { vec![] },
                            variadic: false,
                            effective_arity: i64::from(count),
                        },
                    })),
                    &args,
                    LamLoc::NONE,
                );
                oracle_tests::compare(a, root);
            }
        }
        let mut a = LamArena::new();
        let func = a.var(Ident::new("f", 10, crate::ident::IdentFlags::NONE));
        let arg = a.const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let root = a.prim_raw(Primitive::PjsApply, &[func, arg], LamLoc::NONE);
        oracle_tests::compare(a, root);
    }
}
