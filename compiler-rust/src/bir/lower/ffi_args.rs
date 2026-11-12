//! X: external argument holding and effect assembly.
use super::*;
use crate::bir::{JsPayload, NodeFlags};
use crate::bir::j::{norm, plain};
use crate::lambda::lam_primitive::{Attr, Label, LabelNoname, ObjParam, Param};
use smallvec::SmallVec;

/// The two suffix facts required by X:278's object-argument ordering predicate.
/// Stored per argument, not per expression node.
#[derive(Clone, Copy, Default)]
struct LaterLiteral {
    unsafe_value: bool,
    impure_unsafe_value: bool,
}

impl LaterLiteral {
    /// X:278 order_matters. O(1), using facts recorded while lowering values.
    fn add(&mut self, delay_safe: bool, strictly_pure: bool) {
        self.unsafe_value |= !delay_safe;
        self.impure_unsafe_value |= !delay_safe && !strictly_pure;
    }

    /// X:278 order_matters. O(1), equivalent to the existential suffix search.
    fn conflicts(self, strictly_pure: bool) -> bool {
        if strictly_pure { self.impure_unsafe_value } else { self.unsafe_value }
    }
}

impl State {
    /// X:60 duplicable. O(nodes in the owned argument), iterative and with
    /// one work buffer per argument rather than one allocation per visited node.
    fn duplicable(&self, _cx: Cx, root: NodeId) -> bool {
        let mut work: SmallVec<[NodeId; 4]> = smallvec::smallvec![root];
        while let Some(node) = work.pop() {
            match self.arena.view(node) {
                View::JUndefined | View::JBool | View::JNumber { .. }
                | View::JStr { .. } | View::JTemplate { .. }
                | View::JQualified { .. } => {}
                View::Var { var } if !self.arena.vars.flags(var)
                    .contains(crate::bir::VarFlags::JS_GLOBAL) => {}
                View::JDot { object, position, .. } if position.get().is_some() => {
                    work.push(object);
                }
                View::JIndex { object, index } => { work.push(object); work.push(index); }
                View::JCond { condition, then_, else_ } => {
                    work.push(condition); work.push(then_); work.push(else_);
                }
                _ => return false,
            }
        }
        true
    }

    /// X:30 literal_polyvar_block. O(1), borrowing the literal header.
    fn literal_polyvar_block(&self, _cx: Cx, arg: NodeId) -> bool {
        matches!(self.arena.view(arg), View::JBlockLit { values: [key, _], info }
            if matches!(self.arena.javascript(info), JsPayload::Block(crate::lambda::TagInfo::PolyVar(_)))
                && matches!(self.arena.view(*key), View::JStr { .. }))
    }

    /// X:213 hold_external_arg. O(argument nodes) for event duplicability,
    /// O(1) otherwise. A hold occupies the argument's reserved suffix slot.
    pub(super) fn hold_external_arg(
        &mut self, cx: Cx, label: LabelNoname, attr: &Attr, mut arg: Out,
    ) -> Out {
        let value = arg.value.expect("external argument value");
        let target = match (label, self.arena.view(value)) {
            (LabelNoname::ArgOptional, View::JOptional { value }) => value,
            _ => value,
        };
        let hold = match attr {
            Attr::PolyVar { .. } => !self.literal_polyvar_block(cx, target)
                && !self.duplicable(cx, target),
            Attr::PolyVarString { .. } | Attr::Int(_) =>
                !self.arena.node(target).flags().contains(NodeFlags::STRICT),
            Attr::ArgCst(_) | Attr::ExternUnit | Attr::Nothing | Attr::Ignore | Attr::Unwrap => false,
        };
        if !hold { return arg; }
        let aux = self.arena.node(value).aux();
        let cold = self.arena.cold(value);
        let located = self.arena.node(value).flags().contains(NodeFlags::JS_LOC_PRESENT);
        if target != value { self.arena.detach(target); }
        let var = self.fresh_variable("tmp");
        let statement = crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, target);
        self.statements.fill_held(arg.stmts.start + arg.stmts.len - 1, &[statement]);
        let replacement = self.pure_expression(View::Var { var }, 0);
        arg.value = Some(if target == value { replacement } else {
            self.arena.release(value);
            let wrapper = self.pure_expression(View::JOptional { value: replacement }, aux);
            if let Some(cold) = cold { self.arena.set_cold(wrapper, cold); }
            if located {
                let mut flags = self.arena.node(wrapper).flags();
                flags.0 |= NodeFlags::JS_LOC_PRESENT;
                self.arena.nodes[wrapper.index()].set_flags(flags);
            }
            wrapper
        });
        arg
    }

    /// X:254 hold_external_args. O(specs + owned argument nodes); constants
    /// consume no runtime argument, and unmatched arguments retain their order.
    pub(super) fn hold_external_args(
        &mut self, cx: Cx, specs: &[Param], args: SmallVec<[Out; 4]>,
    ) -> SmallVec<[Out; 4]> {
        let mut args = args.into_iter();
        let mut held = SmallVec::with_capacity(args.len());
        for spec in specs {
            self.primitive_steps += 1;
            if matches!(spec.arg_type, Attr::ArgCst(_)) { continue; }
            let Some(arg) = args.next() else { break; };
            held.push(self.hold_external_arg(cx, spec.arg_label, &spec.arg_type, arg));
        }
        held.extend(args);
        held
    }

    /// X:278 hold_external_obj_args. O(specs + arguments + event argument
    /// nodes). One reverse pass records the suffix predicate, then holds are
    /// allocated in source order. No suffix is searched more than once.
    pub(super) fn hold_external_obj_args(
        &mut self, cx: Cx, specs: &[ObjParam], args: SmallVec<[Out; 4]>,
    ) -> SmallVec<[Out; 4]> {
        let params: SmallVec<[&ObjParam; 4]> = specs.iter().filter(|p|
            !matches!((&p.obj_arg_label, &p.obj_arg_type),
                (Label::ObjEmpty | Label::ObjLabel { .. }, Attr::ArgCst(_))))
            .collect();
        let mut suffix: SmallVec<[LaterLiteral; 4]> = SmallVec::with_capacity(args.len());
        let mut later = LaterLiteral::default();
        for (i, arg) in args.iter().enumerate().rev() {
            self.primitive_steps += 1;
            suffix.push(later);
            let value = arg.value.expect("object argument");
            if params.get(i).is_some_and(|p|
                !matches!(p.obj_arg_label, Label::ObjOptional { .. })
                || matches!(self.arena.view(value), View::JUndefined | View::JOptional { .. })) {
                let flags = self.arena.node(value).flags();
                later.add(flags.contains(NodeFlags::DELAY_SAFE), flags.contains(NodeFlags::STRICT));
            }
        }
        let count = args.len();
        args.into_iter().enumerate().map(|(i, arg)| {
            self.primitive_steps += 1;
            let Some(param) = params.get(i) else { return arg; };
            let label = match param.obj_arg_label {
                Label::ObjEmpty => return arg,
                Label::ObjLabel { .. } => LabelNoname::ArgLabel,
                Label::ObjOptional { .. } => LabelNoname::ArgOptional,
            };
            let mut arg = self.hold_external_arg(cx, label, &param.obj_arg_type, arg);
            let value = arg.value.expect("object argument");
            let flags = self.arena.node(value).flags();
            if label == LabelNoname::ArgOptional
                && !matches!(self.arena.view(value), View::JUndefined | View::JOptional { .. })
                && !flags.contains(NodeFlags::DELAY_SAFE)
                && suffix[count - i - 1].conflicts(flags.contains(NodeFlags::STRICT)) {
                let var = self.fresh_variable("tmp");
                let statement = crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, value);
                self.statements.fill_held(arg.stmts.start + arg.stmts.len - 1, &[statement]);
                arg.value = Some(self.pure_expression(View::Var { var }, 0));
            }
            arg
        }).collect()
    }

    /// X:181 external_optional_to_undefined_expr. O(field spine + copied
    /// spine), or one runtime call. Optional payloads move without copying.
    fn external_optional_to_undefined_expr(&mut self, cx: Cx, arg: NodeId) -> NodeId {
        match self.arena.view(arg) {
            View::JUndefined => {
                self.arena.release(arg);
                plain::node(&mut self.arena, View::JUndefined, 0)
            }
            View::JOptional { value } => {
                self.arena.detach(value);
                self.arena.release(arg);
                value
            }
            _ if self.optional_duplicable(cx, arg) => {
                let copy = self.arena.copy_subtree(arg, &[]);
                let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                let test = norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::NotEqEq, copy, undefined);
                let value = self.primitive_runtime("Primitive_option", "valFromOption", &[arg]);
                let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                norm::je7_cond(&mut self.arena, test, value, undefined)
            }
            _ => self.primitive_runtime("Primitive_option", "valFromOption", &[arg]),
        }
    }

    /// A:69 is_okay_to_duplicate(false), used by X:181. O(field spine).
    fn optional_duplicable(&self, _cx: Cx, mut node: NodeId) -> bool {
        loop {
            match self.arena.view(node) {
                View::Var { var } => return !self.arena.vars.flags(var).contains(crate::bir::VarFlags::JS_GLOBAL)
                    || !self.arena.vars.name(var).as_str().contains('.'),
                View::JQualified { .. } | View::JBool | View::JStr { .. }
                | View::JTemplate { .. } | View::JNumber { .. } => return true,
                View::JDot { object, position, .. } if position.get().is_some() => node = object,
                _ => return false,
            }
        }
    }

    /// X:421 external_polyvar_unwrap_expr. O(1) shape inspection plus release
    /// of the unused literal tag, or one J-M11 member construction.
    fn external_polyvar_unwrap_expr(&mut self, _cx: Cx, arg: NodeId) -> NodeId {
        if let View::JBlockLit { values: [first, second], .. } = self.arena.view(arg) {
            if matches!(self.arena.view(*first), View::JNumber { .. }) {
                let value = *second;
                self.arena.detach(value);
                self.arena.release(arg);
                return value;
            }
        }
        norm::jm11_poly_var_access(&mut self.arena, arg, true)
    }

    /// X:197 external_option_unwrap_expr. O(1) apart from releasing a literal.
    fn external_option_unwrap_expr(&mut self, cx: Cx, arg: NodeId) -> NodeId {
        match self.arena.view(arg) {
            View::JUndefined => { self.arena.release(arg); plain::node(&mut self.arena, View::JUndefined, 0) }
            View::JOptional { value } => {
                self.arena.detach(value);
                self.arena.release(arg);
                self.external_polyvar_unwrap_expr(cx, value)
            }
            _ => self.primitive_runtime("Primitive_option", "unwrapPolyVar", &[arg]),
        }
    }

    /// X:344/X:400 dispatch IIFE construction. O(cases + spelling bytes).
    fn external_dispatch(&mut self, _cx: Cx, arg: NodeId, cases: impl Iterator<Item = (String, NodeId)>) -> NodeId {
        let mut keys = Vec::new();
        let mut actions = Vec::new();
        let mut clauses = Vec::new();
        for (key, value) in cases {
            self.primitive_steps += 1;
            keys.push(crate::bir::CaseKey::JavaScript(crate::lambda::SwitchCaseTag::String(key)));
            let ret = plain::node(&mut self.arena, View::SReturn { value }, 0);
            actions.push(plain::list(&mut self.arena, &[ret]));
            clauses.push(crate::bir::ClauseMeta { should_break: false, comment: None, loc: None });
        }
        let header = self.arena.switch_header(crate::bir::SwitchHeader {
            constants: keys.len() as u32, keys, clauses, has_default: false,
            consts_full: false, blocks_full: false, dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let switch = plain::node(&mut self.arena, View::SSwitch { scrutinee: arg, actions: &actions, header }, 1);
        let body = plain::list(&mut self.arena, &[switch]);
        let header = self.arena.function_header(crate::bir::VarSpan { start: 0, len: 0 }, Default::default(), crate::lambda::LamLoc::NONE);
        let callee = self.pure_expression(View::JFun { body, header }, 0);
        self.call_node(callee, &[], Default::default())
    }

    /// X:344 external_polyvar_string_expr. O(dispatch cases + spelling bytes).
    fn external_polyvar_string_expr(&mut self, cx: Cx, arg: NodeId, cases: &[(String, String)]) -> NodeId {
        if matches!(self.arena.view(arg), View::JUndefined) { return arg; }
        if let View::JStr { text } = self.arena.view(arg) {
            let target = &cases.iter().find(|(key, _)| key == self.arena.text(text)).expect("polyvariant string tag").1;
            let result = plain::string(&mut self.arena, target);
            self.arena.release(arg);
            return result;
        }
        let cases: Vec<_> = cases.iter().map(|(key, value)| (key.clone(), plain::string(&mut self.arena, value))).collect();
        self.external_dispatch(cx, arg, cases.into_iter())
    }

    /// X:400 external_polyvar_int_expr. O(dispatch cases + spelling bytes).
    fn external_polyvar_int_expr(&mut self, cx: Cx, arg: NodeId, cases: &[(String, i64)]) -> NodeId {
        if matches!(self.arena.view(arg), View::JUndefined) { return arg; }
        if let View::JStr { text } = self.arena.view(arg) {
            let value = cases.iter().find(|(key, _)| key == self.arena.text(text)).expect("polyvariant integer tag").1;
            self.arena.release(arg);
            return plain::int(&mut self.arena, value as i32);
        }
        let cases: Vec<_> = cases.iter().map(|(key, value)| (key.clone(), plain::int(&mut self.arena, *value as i32))).collect();
        self.external_dispatch(cx, arg, cases.into_iter())
    }

    /// X:374 external_polyvar_event_exprs. O(argument copy + dispatch cases).
    /// The bounded result stays inline; literal operands move to their uses.
    fn external_polyvar_event_exprs(&mut self, cx: Cx, arg: NodeId, cases: Option<&[(String, String)]>) -> SmallVec<[NodeId; 2]> {
        let (tag, value) = if self.literal_polyvar_block(cx, arg) {
            let View::JBlockLit { values: [tag, value], .. } = self.arena.view(arg) else { unreachable!() };
            let (tag, value) = (*tag, *value);
            self.arena.detach(tag); self.arena.detach(value); self.arena.release(arg);
            (tag, value)
        } else {
            let copy = self.arena.copy_subtree(arg, &[]);
            (norm::jm11_poly_var_access(&mut self.arena, arg, false), norm::jm11_poly_var_access(&mut self.arena, copy, true))
        };
        let tag = cases.map_or(tag, |cases| self.external_polyvar_string_expr(cx, tag, cases));
        smallvec::smallvec![tag, value]
    }

    /// X:782 lower_external_arg_values_and_effect. O(argument conversion),
    /// returning zero to two values inline, never a vector allocation per arg.
    pub(super) fn lower_external_arg_values_and_effect(&mut self, cx: Cx, raw: NodeId, label: LabelNoname, attr: &Attr) -> (SmallVec<[NodeId; 2]>, Option<NodeId>) {
        if matches!(attr, Attr::Unwrap) && label == LabelNoname::ArgOptional {
            return (smallvec::smallvec![self.external_option_unwrap_expr(cx, raw)], None);
        }
        let arg = if label == LabelNoname::ArgOptional { self.external_optional_to_undefined_expr(cx, raw) } else { raw };
        let value = match attr {
            Attr::Nothing => arg,
            Attr::ArgCst(_) => { self.arena.release(arg); return (SmallVec::new(), None); }
            Attr::Ignore => return (SmallVec::new(), self.external_arg_effect(cx, arg)),
            Attr::ExternUnit => {
                let effect = self.external_arg_effect(cx, arg);
                let values = if label == LabelNoname::ArgEmpty { SmallVec::new() }
                    else { smallvec::smallvec![plain::node(&mut self.arena, View::JUndefined, 1)] };
                return (values, effect);
            }
            Attr::PolyVarString { descr } => self.external_polyvar_string_expr(cx, arg, descr),
            Attr::PolyVar { descr } => return (self.external_polyvar_event_exprs(cx, arg, descr.as_deref()), None),
            Attr::Int(cases) => self.external_polyvar_int_expr(cx, arg, cases),
            Attr::Unwrap => self.external_polyvar_unwrap_expr(cx, arg),
        };
        (smallvec::smallvec![value], None)
    }

    /// C:6120 compile_external_arg_const. O(literal spelling bytes).
    fn compile_external_arg_const(&mut self, _cx: Cx, cst: &crate::types::external_ffi_types::Cst) -> NodeId {
        use crate::types::external_ffi_types::Cst;
        match cst {
            Cst::ArgIntLit(value) => plain::int(&mut self.arena, *value as i32),
            Cst::ArgStringLit(value) => plain::string(&mut self.arena, value),
            Cst::ArgJsonLit(value) => { let text = self.arena.intern_text(value); plain::node(&mut self.arena, View::JJson { text }, 0) }
        }
    }

    /// X:834 assemble_external_args_no_splice. O(specs + conversions + fused
    /// effects). Trailing trimming zips assembled values with original specs.
    pub(super) fn assemble_external_args_no_splice(&mut self, cx: Cx, specs: &[Param], args: SmallVec<[NodeId; 4]>) -> (SmallVec<[NodeId; 4]>, Option<NodeId>) {
        let mut args = args.into_iter();
        let mut values = SmallVec::with_capacity(specs.len());
        let mut effects: SmallVec<[NodeId; 4]> = SmallVec::new();
        for spec in specs {
            self.primitive_steps += 1;
            if let Attr::ArgCst(cst) = &spec.arg_type {
                values.push(self.compile_external_arg_const(cx, cst));
            } else {
                let arg = args.next().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                let (converted, effect) = self.lower_external_arg_values_and_effect(cx, arg, spec.arg_label, &spec.arg_type);
                values.extend(converted);
                effects.extend(effect);
            }
        }
        debug_assert!(args.next().is_none());
        let trim = specs.iter().rev().zip(values.iter().rev()).take_while(|(spec, value)|
            spec.arg_label == LabelNoname::ArgOptional && matches!(self.arena.view(**value), View::JUndefined)
                && self.arena.node(**value).aux() == 0).count();
        for value in values.drain(values.len() - trim..) { self.arena.release(value); }
        (values, self.fuse_external_effects(cx, effects))
    }

    /// X:741 external_arg_effect. O(1) cached ordinary purity lookup.
    pub(super) fn external_arg_effect(&mut self, _cx: Cx, arg: NodeId) -> Option<NodeId> {
        if self.arena.node(arg).flags().contains(NodeFlags::PURE) {
            self.arena.release(arg);
            None
        } else { Some(arg) }
    }

    /// X:749 fuse_external_effects. O(effects + J-M1 normalisation work).
    pub(super) fn fuse_external_effects(
        &mut self, cx: Cx, effects: impl IntoIterator<Item = NodeId>,
    ) -> Option<NodeId> {
        let mut effects = effects.into_iter();
        let first = effects.next()?;
        Some(effects.fold(first, |first, next| self.add_external_effect(cx, Some(first), next)))
    }

    /// X:755 add_external_effect. The cost is that of J-M1 on the two operands.
    pub(super) fn add_external_effect(&mut self, _cx: Cx, effect: Option<NodeId>, value: NodeId) -> NodeId {
        effect.map_or(value, |effect| norm::jm1_js_seq(&mut self.arena, effect, value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same Lambda operands go through both lowerers before the X helpers.
    fn oracle(mut source: crate::lambda::arena::LamArena, args: &[crate::lambda::arena::Lam], specs: &[Param]) {
        use crate::bir::{bridge, bridge_j};
        use crate::js_ir::{arena::{JsDepsProgram, JsProgram, StmtKind}, build::exp};
        use crate::lambda::{LamLoc, lam_primitive::Primitive, lam_compile::LambdaCompiler};
        let root = source.prim_raw(Primitive::Pmakearray, args, LamLoc::NONE);
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let View::Prim { args: children, .. } = state.source.view(root) else { unreachable!() };
        let children = children.to_vec();
        let mut outputs = SmallVec::new();
        let mut compiler = LambdaCompiler::new();
        let mut expected = crate::lambda::lam_compile_arguments::HeldArgs::new();
        let target = Ident::new("unused", 100, crate::ident::IdentFlags::NONE);
        for (&node, &old) in children.iter().zip(args) {
            let result = state.probe(Cx::value(), node).unwrap();
            let mut out = state.realize(Cx::value(), result);
            state.statements.reserve();
            out.stmts = state.statements.since(Span { start: out.stmts.start, len: 0 });
            outputs.push(out);
            let out = compiler.bir_lower_oracle(&mut source, old, Cx::value().cont, target);
            expected.push((out.prelude, out.expr));
        }
        let held = state.hold_external_args(Cx::value(), specs, outputs);
        let (stmts, args) = state.sequence_arguments(false, held);
        let (args, effect) = state.assemble_external_args_no_splice(Cx::value(), specs, args);
        let value = plain::node(&mut state.arena, View::JArray { values: &args }, 0);
        let value = state.add_external_effect(Cx::value(), effect, value);
        let lowered = state.complete(Cx::value(), Probed::Out(Out { stmts, value: Some(value), finished: Finished::False }));
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
        let actual = bridge_j::export_js(&lowered.program).unwrap();
        let held = compiler.hold_external_args(specs, expected);
        let (mut block, args) = compiler.sequence_arguments(false, held);
        let (args, effect) = compiler.assemble_external_args_no_splice(specs, args.into_vec());
        let value = exp::array(&args, crate::js_ir::op::MutableFlag::Immutable, &mut compiler.j);
        let value = compiler.add_external_effect(effect, value);
        block.push(compiler.j.stmt(StmtKind::Exp(value)));
        let expected = JsDepsProgram { program: JsProgram::new_in(block, vec![], compiler.j), modules: vec![], side_effect: None };
        let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
        assert_eq!(print(&actual), print(&expected), "{specs:?}");
    }

    #[test]
    fn argument_kinds_and_holds_match_legacy() {
        use crate::lambda::{arena::LamArena, lam_constant::Constant, lam_primitive::Primitive, LamLoc};
        use crate::types::external_ffi_types::Cst;
        let attrs = [Attr::Nothing, Attr::Ignore, Attr::ExternUnit,
            Attr::PolyVarString { descr: vec![("tag".into(), "mapped".into())] },
            Attr::PolyVar { descr: None }, Attr::PolyVar { descr: Some(vec![("tag".into(), "mapped".into())]) },
            Attr::Int(vec![("tag".into(), 42)]), Attr::Unwrap];
        for attr in attrs {
            for label in [LabelNoname::ArgEmpty, LabelNoname::ArgLabel, LabelNoname::ArgOptional] {
                for shape in 0..4 {
                    let mut a = LamArena::new();
                    let arg = match shape {
                        0 => a.const_(Constant::String("tag".into())),
                        1 => a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE),
                        2 => a.var(Ident::new("value", 10, crate::ident::IdentFlags::NONE)),
                        _ => {
                            let value = a.const_(Constant::String("tag".into()));
                            a.prim_raw(Primitive::Psome, &[value], LamLoc::NONE)
                        }
                    };
                    oracle(a, &[arg], &[Param { arg_label: label, arg_type: attr.clone() }]);
                }
            }
        }
        for cst in [Cst::ArgIntLit(42), Cst::ArgStringLit("constant".into()), Cst::ArgJsonLit("{}".into())] {
            oracle(LamArena::new(), &[], &[Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::ArgCst(cst) }]);
        }
    }

    #[test]
    fn earlier_argument_is_sequenced_before_later_statements() {
        use crate::lambda::{arena::LamArena, lam_constant::Constant, lam_primitive::Primitive, LamLoc};
        let mut a = LamArena::new();
        let first = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
        let effect = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
        let value = a.const_(Constant::String("tag".into()));
        let later = a.seq_raw(effect, value);
        oracle(a, &[first, later], &[
            Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::PolyVar { descr: None } },
            Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::Nothing },
        ]);
    }

    #[test]
    fn reverse_summary_matches_suffix_predicate() {
        assert_eq!(std::mem::size_of::<LaterLiteral>(), 2);
        for bits in 0..256u32 {
            let facts: Vec<_> = (0..4).map(|i| ((bits >> (2*i)) & 1 != 0, (bits >> (2*i+1)) & 1 != 0)).collect();
            let mut later = LaterLiteral::default();
            for i in (0..facts.len()).rev() {
                for pure in [false, true] {
                    assert_eq!(later.conflicts(pure), facts[i+1..].iter().any(|&(safe, later_pure)| !safe && !(pure && later_pure)));
                }
                later.add(facts[i].0, facts[i].1);
            }
        }
    }

    #[test]
    fn ten_thousand_arguments_take_linear_holder_steps() {
        use crate::bir::bridge;
        use crate::lambda::{arena::LamArena, lam_constant::Constant};
        for objects in [false, true] {
            let mut source = LamArena::new();
            let root = source.const_(Constant::JsNull);
            let mut state = State::new(bridge::import_lambda(&source, root).unwrap());
            let mut args = SmallVec::with_capacity(10_000);
            let mut specs = Vec::new();
            let mut obj_specs = Vec::new();
            for i in 0..10_000 {
                let text = state.arena.intern_text("effect()");
                let value = plain::node(&mut state.arena, View::JRaw { text }, 0);
                let start = state.statements.mark();
                state.statements.reserve();
                args.push(Out { stmts: state.statements.since(start), value: Some(value), finished: Finished::False });
                specs.push(Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::PolyVar { descr: None } });
                obj_specs.push(ObjParam { obj_arg_type: Attr::Nothing, obj_arg_label: if i % 2 == 0 {
                    Label::ObjOptional { name: "optional".into(), for_sure_no_nested_option: false }
                } else { Label::ObjLabel { name: "required".into() } } });
            }
            let held = if objects {
                state.hold_external_obj_args(Cx::value(), &obj_specs, args)
            } else {
                state.hold_external_args(Cx::value(), &specs, args)
            };
            assert_eq!(held.len(), 10_000);
            assert_eq!(state.primitive_steps, if objects { 20_000 } else { 10_000 });
            assert_eq!(state.statements.pushed, if objects { 5_000 } else { 10_000 });
            let (_, values) = state.sequence_arguments(false, held);
            assert_eq!(values.len(), 10_000);
            assert!(state.sequence_steps <= 30_000);
        }
    }
}
