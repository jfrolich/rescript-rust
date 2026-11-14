//! X: compile_jsx / jsx_callee. JSX policy remains in the shared passes/printer.
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{JsxHeader, PropertyKey, PropertySpan};
use crate::lambda::lam_primitive::{DeclKind, ExternalDecl, JsxElement, ModuleSource};

/// How the printer writes a JSX node of a unit that preserves JSX.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PrintedForm {
    /// A call of the runtime: the callee is printed.
    Runtime,
    /// `<tag ...>`: the callee is not printed.
    Element,
    /// `<></>`: neither the callee nor the tag is printed.
    Fragment,
}

/// The form of the JSX node `jsx` in a unit that preserves JSX
/// (`emit::walk::jsx_form` over `js_ir::printer::jsx_printable`, on the
/// finished node): an element when the tag is one JSX can name, every
/// property key is a JSX attribute name and the children agree with the
/// element's arity; a fragment when it is an empty fragment besides.
/// Cost: one step per property key and per member of the tag's chain, and
/// the bytes of their names; nothing is allocated once `spelling` has its
/// capacity.
pub(super) fn printed_form(bir: &Bir, idents: &[Ident], jsx: NodeId, spelling: &mut String) -> PrintedForm {
    use crate::js_ir::printer::{is_jsx_attribute_name, unwrap_uppercase_exotic};
    let View::JJsx { values, info } = bir.view(jsx) else { unreachable!("a JSX node") };
    let crate::bir::JsPayload::Jsx(header) = bir.javascript(info) else { unreachable!("JSX metadata") };
    let keys = bir.property_keys(header.props);
    let fragment = header.fragment && !header.spread && keys.is_empty() && !header.key;
    let has_children = bir.nodes[jsx.index()].aux() != 0;
    let printable = (fragment || jsx_tag(bir, idents, values[1], spelling))
        && keys.iter().all(|key| match key {
            crate::bir::PropertyKey::Literal(name) => is_jsx_attribute_name(unwrap_uppercase_exotic(bir.text(*name))),
            _ => false,
        })
        && (!has_children || (header.children >= 2) == header.multi);
    match (printable, fragment) {
        (false, _) => PrintedForm::Runtime,
        (true, false) => PrintedForm::Element,
        (true, true) => PrintedForm::Fragment,
    }
}

/// Whether JSX can name `tag` (`js_ir::printer::is_jsx_tag`): an intrinsic
/// element name, a variable or module whose printed name starts as a
/// component's does, or a chain of dotted members over one. Cost: one step
/// per member of the chain and the bytes of the names.
fn jsx_tag(bir: &Bir, idents: &[Ident], tag: NodeId, spelling: &mut String) -> bool {
    use crate::js_ir::printer::{convert_ident_into, is_jsx_name_char, is_jsx_value_name, property_access_uses_dot};
    use crate::js_ir::Kind;
    // `printed_ident_name`: a JavaScript binding prints as it is spelled.
    let mut value_name = |ident: &Ident| {
        if ident.is_js() {
            return is_jsx_value_name(ident.name());
        }
        spelling.clear();
        convert_ident_into(ident.name(), spelling);
        is_jsx_value_name(spelling)
    };
    match bir.view(tag) {
        View::JStr { text } => match bir.text(text).as_bytes() {
            [first, rest @ ..] => first.is_ascii_lowercase() && rest.iter().all(|c| is_jsx_name_char(*c, true)),
            [] => false,
        },
        View::Var { var } => idents.get(bir.vars.j_origin[var.index()].index()).is_some_and(&mut value_name),
        View::JQualified { module, member } => {
            let module = &bir.pools.j_modules[module.index()];
            match member {
                None => value_name(&module.id),
                Some(_) if matches!(module.kind, Kind::External { default: true, .. }) => value_name(&module.id),
                Some(name) => match module.kind {
                    Kind::Ml | Kind::Runtime => true,
                    Kind::External { .. } => property_access_uses_dot(bir.text(name)),
                },
            }
        }
        View::JDot { .. } => {
            // `is_jsx_member_expression`: dotted members down to a
            // variable or a module.
            let mut at = tag;
            loop {
                match bir.view(at) {
                    View::Var { .. } | View::JQualified { .. } => return true,
                    View::JDot { object, property, .. } if bir.nodes[at.index()].aux() == 0 && property_access_uses_dot(bir.text(property)) => at = object,
                    _ => return false,
                }
            }
        }
        _ => false,
    }
}

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
    /// Operands and property keys go directly into unit pools, without vectors.
    pub(super) fn compile_jsx(
        &mut self,
        jsx: &JsxElement,
        args: impl IntoIterator<Item = NodeId>,
    ) -> NodeId {
        let mut args = args.into_iter();
        let tag = args.next().expect("JSX tag");
        let spread = jsx.jsx_spread.then(|| args.next().expect("JSX spread"));
        let mut props = PropertySpan {
            start: crate::bir::pools::index(self.arena.pools.property_keys.len()), len: 0,
        };
        // Reserve stable slots before any key/callee construction can append lists.
        // Optional properties compact this list in place; unused slots stay outside
        // the final length and never acquire ownership of the placeholder tag.
        let count = 2 + usize::from(jsx.jsx_spread) + jsx.jsx_props.len()
            + jsx.jsx_children.unwrap_or(0) + usize::from(jsx.jsx_key);
        let values = self.arena.lists.push_iter(count, std::iter::repeat_n(tag, count));
        let mut at = 2;
        if let Some(spread) = spread {
            self.arena.lists.set(values, at, spread);
            at += 1;
        }
        for (name, optional) in &jsx.jsx_props {
            self.primitive_steps += 1;
            let value = args.next().expect("JSX prop");
            if *optional && matches!(self.arena.view(value), View::JUndefined) {
                self.arena.release(value);
            } else {
                let key = PropertyKey::Literal(self.arena.intern_text(name));
                self.arena.pools.property_keys.push(key);
                props.len += 1;
                self.arena.lists.set(values, at, value);
                at += 1;
            }
        }
        for _ in 0..jsx.jsx_children.unwrap_or(0) {
            self.primitive_steps += 1;
            self.arena.lists.set(values, at, args.next().expect("JSX child"));
            at += 1;
        }
        if jsx.jsx_key {
            let key = self.jsx_key(args.next().expect("JSX key"));
            self.arena.lists.set(values, at, key);
            at += 1;
        }
        assert!(args.next().is_none(), "JSX argument count");
        let callee = self.jsx_callee(&jsx.jsx_ffi);
        self.arena.lists.set(values, 0, callee);
        self.arena.lists.truncate(values, at);
        self.arena.jsx_from_list(values, JsxHeader {
            spread: jsx.jsx_spread,
            props,
            children: jsx.jsx_children.unwrap_or(0) as u32,
            key: jsx.jsx_key,
            multi: jsx.jsx_multi,
            fragment: jsx.jsx_fragment,
        }, jsx.jsx_children.is_some())
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
        let mut spine = std::mem::take(&mut self.scratch);
        debug_assert!(spine.is_empty());
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
                _ => {
                    spine.clear();
                    self.scratch = spine;
                    return None;
                }
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
        for node in spine.drain(..).rev() {
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
        self.scratch = spine;
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
    fn ten_thousand_jsx_operands_scopes_and_key_fields_lower_without_allocations() {
        for shape in 0..4 {
            let (a, root) = if shape < 2 {
                let jsx = if shape == 0 { element(10_000, None, false, false) }
                    else { element(0, Some(10_000), false, false) };
                input(jsx, 0, false)
            } else {
                let mut jsx = element(0, None, shape == 3, false);
                if shape == 2 { jsx.jsx_ffi.scopes = vec!["scope".into(); 10_000]; }
                let mut a = LamArena::new();
                let mut args = vec![a.const_(Constant::String("div".into()))];
                if shape == 3 {
                    let mut key = a.var(Ident::new("key", 10, IdentFlags::NONE));
                    for _ in 0..10_000 {
                        key = a.prim_raw(Primitive::Pfield(0, crate::lambda::FieldDbgInfo::Record {
                            name: crate::name::Name::new("field"),
                        }), &[key], LamLoc::NONE);
                    }
                    args.push(key);
                }
                let root = a.prim_raw(Primitive::Pjsx(Box::new(jsx)), &args, LamLoc::NONE);
                (a, root)
            };
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let run = |s: &mut State| {
                let out = s.probe(Cx::value(), root).unwrap();
                let out = s.realize(Cx::value(), out);
                for node in s.statements.statements(out.stmts) { s.arena.release(node); }
                if let Some(value) = out.value { s.arena.release(value); }
                s.statements.kill(out.stmts);
            };
            let lists = state.arena.lists.storage_shape().0;
            let js = state.arena.pools.js.len();
            let props = state.arena.pools.property_keys.len();
            let vars = state.arena.vars.len();
            run(&mut state);
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.arena.pools.js.reserve(state.arena.pools.js.len() - js);
            state.arena.pools.property_keys.reserve(state.arena.pools.property_keys.len() - props);
            let added = state.arena.vars.len() - vars;
            macro_rules! reserve_vars { ($($field:ident),*) => { $(state.arena.vars.$field.reserve(added);)* }; }
            reserve_vars!(j_origin, name, order, flags, uses, binder, fact, printed);
            state.idents.reserve(added);
            if let Some(scope) = &mut state.arena.js_scope { scope.uses.reserve(added); }
            state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            state.labels.reserve_repeat();
            #[cfg(debug_assertions)]
            state.arena.checked_children.reserve(state.arena.nodes.len() - state.arena.checked_children.len());
            let capacities = |s: &State| [s.scratch.capacity(), s.tail_name.capacity(),
                s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1,
                s.arena.pools.js.capacity(), s.arena.pools.property_keys.capacity(),
                s.arena.vars.j_origin.capacity(), s.arena.vars.name.capacity(), s.arena.vars.order.capacity(),
                s.arena.vars.flags.capacity(), s.arena.vars.uses.capacity(), s.arena.vars.binder.capacity(),
                s.arena.vars.fact.capacity(), s.arena.vars.printed.capacity(), s.idents.capacity(),
                s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity(),
                s.argument_outputs.capacity(), s.argument_values.capacity()];
            let before = (capacities(&state), state.free.capacities(), state.labels.capacities(), state.statements.capacities());
            let visits = state.source_steps;
            let steps = state.primitive_steps;
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            println!("JSX shape={shape}: {allocations:?}, source={}, primitive={}", state.source_steps - visits, state.primitive_steps - steps);
            assert_eq!(allocations.count_total, 0);
            assert_eq!((capacities(&state), state.free.capacities(), state.labels.capacities(), state.statements.capacities()), before);
            let expected = [(10_002, 20_002), (20_002, 40_002), (2, 10_001), (10_003, 30_004)][shape];
            assert_eq!((state.source_steps - visits, state.primitive_steps - steps), expected);
        }
        assert_eq!(std::mem::size_of::<PropertySpan>(), 8);
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
