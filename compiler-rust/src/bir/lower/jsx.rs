//! X: compile_jsx / jsx_callee. JSX policy remains in the shared passes/printer.
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{JsPayload, JsxHeader, PropertyKey};
use crate::lambda::lam_primitive::{DeclKind, ExternalDecl, JsxElement, ModuleSource};

impl State {
    /// X: jsx_callee / translate_scoped_module_value / translate_scoped_global_value.
    /// O(module inventory + scopes + spelling bytes). Each scope is built once.
    fn jsx_callee(&mut self, decl: &ExternalDecl) -> NodeId {
        let DeclKind::DeclVal { name } = &decl.kind else {
            unreachable!("JSX external must be a value")
        };
        let (mut value, rest, member) = match &decl.module_ {
            Some(ModuleSource::ModuleNamed(external)) => {
                let (first, rest, member) = match decl.scopes.split_first() {
                    Some((first, rest)) => (first.as_str(), rest, Some(name.as_str())),
                    None => (name.as_str(), &[][..], None),
                };
                let module = self.external_module(external, first == "default", false);
                let member_id = Some(self.arena.intern_text(first));
                (
                    plain::node(
                        &mut self.arena,
                        View::JQualified {
                            module,
                            member: member_id,
                        },
                        0,
                    ),
                    rest,
                    member,
                )
            }
            None => {
                let (first, rest, member) = match decl.scopes.split_first() {
                    Some((first, rest)) => (first.as_str(), rest, Some(name.as_str())),
                    None => (name.as_str(), &[][..], None),
                };
                let var = self.fresh_variable(first);
                self.idents[var.index()] = Ident::create_persistent(first);
                self.arena.mark_js_global(var);
                (self.pure_expression(View::Var { var }, 0), rest, member)
            }
            Some(ModuleSource::ModuleItself) => {
                unreachable!("JSX external cannot be the module itself")
            }
        };
        for scope in rest {
            self.primitive_steps += 1;
            value = self.static_member(value, scope);
        }
        if let Some(member) = member {
            value = self.static_member(value, member);
        }
        value
    }

    /// X: compile_jsx. O(props + children + spelling bytes), after shared
    /// argument sequencing. Optional undefined props are consumed and omitted.
    /// One output vector is extended once per operand, never copied per child.
    pub(super) fn compile_jsx(
        &mut self,
        jsx: &JsxElement,
        args: impl IntoIterator<Item = NodeId>,
    ) -> NodeId {
        let mut args = args.into_iter();
        let tag = args.next().expect("JSX tag");
        let spread = jsx.jsx_spread.then(|| args.next().expect("JSX spread"));
        let mut props = Vec::with_capacity(jsx.jsx_props.len());
        let mut values = Vec::with_capacity(
            2 + usize::from(jsx.jsx_spread)
                + jsx.jsx_props.len()
                + jsx.jsx_children.unwrap_or(0)
                + usize::from(jsx.jsx_key),
        );
        // Reserve the callee slot: its external binding is allocated after the
        // operands and key, matching the legacy temporary-name order.
        values.push(tag);
        values.push(tag);
        if let Some(spread) = spread {
            values.push(spread);
        }
        for (name, optional) in &jsx.jsx_props {
            self.primitive_steps += 1;
            let value = args.next().expect("JSX prop");
            if *optional && matches!(self.arena.view(value), View::JUndefined) {
                self.arena.release(value);
            } else {
                props.push(PropertyKey::Literal(self.arena.intern_text(name)));
                values.push(value);
            }
        }
        for _ in 0..jsx.jsx_children.unwrap_or(0) {
            self.primitive_steps += 1;
            values.push(args.next().expect("JSX child"));
        }
        if jsx.jsx_key {
            let key = self.jsx_key(args.next().expect("JSX key"));
            values.push(key);
        }
        assert!(args.next().is_none(), "JSX argument count");
        values[0] = self.jsx_callee(&jsx.jsx_ffi);
        let info = self.arena.js_info(JsPayload::Jsx(JsxHeader {
            spread: jsx.jsx_spread,
            props,
            children: jsx.jsx_children.unwrap_or(0) as u32,
            key: jsx.jsx_key,
            multi: jsx.jsx_multi,
            fragment: jsx.jsx_fragment,
        }));
        plain::node(
            &mut self.arena,
            View::JJsx {
                values: &values,
                info,
            },
            u16::from(jsx.jsx_children.is_some()),
        )
    }

    /// X: external_optional_to_undefined_expr. O(member-spine depth) for a
    /// duplicable key, O(1) otherwise, plus J-E4/J-E7 constructor work.
    fn jsx_key(&mut self, key: NodeId) -> NodeId {
        match self.arena.view(key) {
            View::JUndefined => {
                self.arena.release(key);
                plain::node(&mut self.arena, View::JUndefined, 0)
            }
            View::JOptional { value } => {
                self.arena.detach(value);
                self.arena.release(key);
                value
            }
            _ => {
                if let Some(copy) = self.duplicate_jsx_key(key) {
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    let test = norm::je4_bin(
                        &mut self.arena,
                        crate::js_ir::BinOp::NotEqEq,
                        key,
                        undefined,
                    );
                    let value =
                        self.primitive_runtime("Primitive_option", "valFromOption", &[copy]);
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    norm::je7_cond(&mut self.arena, test, value, undefined)
                } else {
                    self.primitive_runtime("Primitive_option", "valFromOption", &[key])
                }
            }
        }
    }

    /// A: is_okay_to_duplicate(false), with copying in the same walk. O(d)
    /// for a d-deep member spine; one reusable stack, no per-node allocation.
    /// A failed shape leaves the original key untouched and creates no nodes.
    fn duplicate_jsx_key(&mut self, mut key: NodeId) -> Option<NodeId> {
        let mut spine = smallvec::SmallVec::<[NodeId; 4]>::new();
        loop {
            self.primitive_steps += 1;
            match self.arena.view(key) {
                View::JDot {
                    object, position, ..
                } if position.get().is_some() => {
                    spine.push(key);
                    key = object;
                }
                View::Var { var }
                    if !self
                        .arena
                        .vars
                        .flags(var)
                        .contains(crate::bir::VarFlags::JS_GLOBAL)
                        || !self.arena.vars.name(var).as_str().contains('.') =>
                {
                    break;
                }
                View::JQualified { .. }
                | View::JBool
                | View::JStr { .. }
                | View::JNumber { .. } => break,
                View::JTemplate { .. } if self.arena.node(key).aux() == 1 => break,
                _ => return None,
            }
        }
        let aux = self.arena.node(key).aux();
        let view = match self.arena.view(key) {
            View::Var { var } => View::Var { var },
            View::JQualified { module, member } => View::JQualified { module, member },
            View::JBool => View::JBool,
            View::JStr { text } => View::JStr { text },
            View::JNumber { value } => View::JNumber { value },
            View::JTemplate { info, .. } => View::JTemplate { values: &[], info },
            _ => unreachable!("duplicable leaf"),
        };
        let mut copy = plain::node(&mut self.arena, view, aux);
        self.copy_jsx_key_decoration(key, copy);
        for node in spine.into_iter().rev() {
            let View::JDot {
                property, position, ..
            } = self.arena.view(node)
            else {
                unreachable!()
            };
            let aux = self.arena.node(node).aux();
            copy = plain::node(
                &mut self.arena,
                View::JDot {
                    object: copy,
                    property,
                    position,
                },
                aux,
            );
            self.copy_jsx_key_decoration(node, copy);
        }
        Some(copy)
    }

    /// O(1), copy the cold decoration of a duplicated key node.
    fn copy_jsx_key_decoration(&mut self, from: NodeId, to: NodeId) {
        if let Some(cold) = self.arena.cold(from) {
            self.arena.set_cold(to, cold);
        }
        if let Some(code) = self.arena.node(from).js_char() {
            self.arena.nodes[to.index()].set_js_char(code);
        }
        if self
            .arena
            .node(from)
            .flags()
            .contains(crate::bir::NodeFlags::JS_LOC_PRESENT)
        {
            let mut flags = self.arena.node(to).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[to.index()].set_flags(flags);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{
        LamLoc,
        arena::{Lam, LamArena},
        lam_constant::Constant,
        lam_primitive::Primitive,
    };

    fn element(props: usize, children: Option<usize>, key: bool, spread: bool) -> JsxElement {
        JsxElement {
            jsx_name: "jsx".into(),
            jsx_ffi: ExternalDecl {
                kind: DeclKind::DeclVal { name: "jsx".into() },
                module_: None,
                scopes: vec!["React".into()],
                variadic: false,
                effective_arity: 3,
            },
            jsx_multi: children.is_some_and(|n| n > 1),
            jsx_fragment: false,
            jsx_spread: spread,
            jsx_props: (0..props)
                .map(|i| (format!("prop{i}"), i % 2 == 0))
                .collect(),
            jsx_children: children,
            jsx_key: key,
        }
    }

    fn input(jsx: JsxElement, key_shape: usize, statement_child: bool) -> (LamArena, Lam) {
        let mut a = LamArena::new();
        let mut args = vec![a.const_(Constant::String("div".into()))];
        if jsx.jsx_spread {
            args.push(a.var(Ident::new("props", 10, IdentFlags::NONE)));
        }
        for (_, optional) in &jsx.jsx_props {
            args.push(if *optional {
                a.const_(Constant::JsUndefined { is_unit: false })
            } else {
                a.var(Ident::new("prop", 11, IdentFlags::NONE))
            });
        }
        for i in 0..jsx.jsx_children.unwrap_or(0) {
            let value = a.var(Ident::new("child", 12, IdentFlags::NONE));
            let value = if statement_child && i + 1 == jsx.jsx_children.unwrap_or(0) {
                let debug = a.prim_raw(Primitive::Pdebugger, &[], LamLoc::NONE);
                a.seq_raw(debug, value)
            } else {
                a.prim_raw(Primitive::PinitMod, &[value], LamLoc::NONE)
            };
            args.push(value);
        }
        if jsx.jsx_key {
            let key = match key_shape {
                0 => a.const_(Constant::JsUndefined { is_unit: false }),
                1 => {
                    let key = a.const_(Constant::String("key".into()));
                    a.prim_raw(Primitive::Psome, &[key], LamLoc::NONE)
                }
                2 => a.var(Ident::new("key", 13, IdentFlags::NONE)),
                _ => {
                    let key = a.var(Ident::new("key", 13, IdentFlags::NONE));
                    a.prim_raw(Primitive::PinitMod, &[key], LamLoc::NONE)
                }
            };
            args.push(key);
        }
        let root = a.prim_raw(Primitive::Pjsx(Box::new(jsx)), &args, LamLoc::NONE);
        (a, root)
    }

    #[test]
    fn jsx_shapes_all_continuations_preserved_and_lowered() {
        for children in [None, Some(0), Some(1), Some(3)] {
            for key_shape in 0..4 {
                for spread in [false, true] {
                    let (a, root) = input(element(3, children, true, spread), key_shape, true);
                    super::super::oracle_tests::compare(a, root);
                }
            }
            let (a, root) = input(element(0, children, false, false), 0, false);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_jsx_scopes_and_key_fields_are_linear() {
        for key_fields in [false, true] {
            let mut jsx = element(0, None, key_fields, false);
            if !key_fields {
                jsx.jsx_ffi.scopes = vec!["scope".into(); 10_000];
            }
            let mut a = LamArena::new();
            let mut args = vec![a.const_(Constant::String("div".into()))];
            if key_fields {
                let mut key = a.var(Ident::new("key", 10, IdentFlags::NONE));
                for _ in 0..10_000 {
                    key = a.prim_raw(
                        Primitive::Pfield(
                            0,
                            crate::lambda::FieldDbgInfo::Record {
                                name: crate::name::Name::new("field"),
                            },
                        ),
                        &[key],
                        LamLoc::NONE,
                    );
                }
                args.push(key);
            }
            let root = a.prim_raw(Primitive::Pjsx(Box::new(jsx)), &args, LamLoc::NONE);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let out = state.probe(Cx::value(), root).unwrap();
            let expected = if key_fields {
                (10_003, 30_004)
            } else {
                (2, 10_001)
            };
            eprintln!(
                "JSX key_fields={key_fields}: source={} primitive={}",
                state.source_steps, state.primitive_steps
            );
            assert_eq!((state.source_steps, state.primitive_steps), expected);
            let lowered = state.complete(Cx::value(), out);
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root))
                .unwrap();
        }
    }

    #[test]
    fn ten_thousand_jsx_children_and_props_are_linear() {
        for props in [false, true] {
            let jsx = if props {
                element(10_000, None, false, false)
            } else {
                element(0, Some(10_000), false, false)
            };
            let (a, root) = input(jsx, 0, !props);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let out = state.probe(Cx::value(), root).unwrap();
            let expected = if props {
                (10_002, 10_001, 20_002)
            } else {
                (20_003, 30_000, 40_001)
            };
            eprintln!(
                "JSX props={props}: source={} sequence={} primitive={}",
                state.source_steps, state.sequence_steps, state.primitive_steps
            );
            assert_eq!(
                (
                    state.source_steps,
                    state.sequence_steps,
                    state.primitive_steps
                ),
                expected
            );
            let lowered = state.complete(Cx::value(), out);
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root))
                .unwrap();
        }
    }

    #[test]
    fn jsx_external_module_and_fragment_match_legacy() {
        use crate::lambda::lam_primitive::{ExternalModuleName, ModuleBindName};
        for scopes in [vec![], vec!["default".into(), "nested".into()]] {
            let mut jsx = element(0, Some(1), false, false);
            jsx.jsx_fragment = true;
            jsx.jsx_ffi.scopes = scopes;
            jsx.jsx_ffi.module_ = Some(ModuleSource::ModuleNamed(ExternalModuleName {
                bundle: "react/jsx-runtime".into(),
                module_bind_name: ModuleBindName::PhintNothing,
                import_attributes: None,
            }));
            let (a, root) = input(jsx, 0, false);
            super::super::oracle_tests::compare(a, root);
        }
    }
}
