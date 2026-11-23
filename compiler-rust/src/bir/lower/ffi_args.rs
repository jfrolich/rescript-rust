//! X: external argument holding and effect assembly.
use super::*;
use crate::emit::row::{Kind, flag};
use crate::lambda::lam_primitive::{Attr, Label, LabelNoname, ObjParam, Param};

/// The two suffix facts required by X:278's object-argument ordering predicate.
/// Stored per argument, not per expression node.
#[derive(Clone, Copy, Default)]
pub(super) struct LaterLiteral {
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
        if strictly_pure {
            self.impure_unsafe_value
        } else {
            self.unsafe_value
        }
    }
}

impl<B: super::js_stmt::JsStmt> State<'_, B> {
    /// X:30 literal_polyvar_block. O(1), borrowing the literal header.
    fn literal_polyvar_block(&self, _cx: Cx, arg: &B::E) -> bool {
        self.polyvar_literal(B::of(arg))
    }

    /// X:30 literal_polyvar_block of a node read by reference: a block
    /// literal of two operands with a polymorphic variant tag whose first
    /// operand is a string. O(1).
    fn polyvar_literal<'r>(&'r self, r: B::Ref<'r>) -> bool {
        self.js.kind(&self.arena, r) == Kind::BlockLit
            && self.js.arity(&self.arena, r) == 2
            && self.js.info_of(&self.arena, r).is_some_and(|info| {
                matches!(self.arena.block_tag(info), crate::lambda::TagInfo::PolyVar(_))
            })
            && self.js.kind(&self.arena, self.js.operand(&self.arena, r, 0)) == Kind::Str
    }

    /// X:213 hold_external_arg. O(1) cached shape and duplicability decisions. A hold occupies the argument's reserved suffix slot.
    pub(super) fn hold_external_arg(
        &mut self,
        _cx: Cx,
        label: LabelNoname,
        attr: &Attr,
        arg: &mut Out<B>,
    ) {
        let r = B::of(arg.value.as_ref().expect("external argument value"));
        let wrapped =
            label == LabelNoname::ArgOptional && self.js.kind(&self.arena, r) == Kind::Optional;
        let target = if wrapped { self.js.operand(&self.arena, r, 0) } else { r };
        let hold = match attr {
            Attr::PolyVar { .. } => {
                // X:60 duplicable: a dense cached fact.
                !self.polyvar_literal(target)
                    && !self.js.has(&self.arena, target, flag::DUPLICABLE)
            }
            Attr::PolyVarString { .. } | Attr::Int(_) => {
                !self.js.has(&self.arena, target, flag::STRICT)
            }
            Attr::ArgCst(_) | Attr::ExternUnit | Attr::Nothing | Attr::Ignore | Attr::Unwrap => {
                false
            }
        };
        if !hold {
            return;
        }
        let value = arg.value.take().expect("external argument value");
        let held = if wrapped {
            let mut shell = value;
            self.js.take_operands(&mut self.arena, &mut shell);
            let target = self.js.pop();
            let replacement = self.hold_in_variable(arg, target);
            let mark = self.js.mark();
            self.js.push(replacement);
            let mut wrapper = self.js.refill(&mut self.arena, shell, mark);
            self.js.assume_strict(&mut self.arena, &mut wrapper);
            wrapper
        } else {
            self.hold_in_variable(arg, value)
        };
        arg.value = Some(held);
    }

    /// `value` declared in a fresh variable in the argument's reserved
    /// suffix slot; the strictly pure reference to the variable is
    /// returned. O(1).
    fn hold_in_variable(&mut self, arg: &Out<B>, value: B::E) -> B::E {
        let var = self.fresh_variable("tmp");
        let statement = self.js.declare(&mut self.arena, LetKind::Strict, var, Some(value));
        self.statements.fill_held(
            arg.stmts.start + arg.stmts.len - 1,
            [statement],
        );
        self.js.var(&mut self.arena, var)
    }

    /// X:254 hold_external_args. O(specs + arguments); constants
    /// consume no runtime argument, and unmatched arguments retain their order.
    pub(super) fn hold_external_args(&mut self, cx: Cx, specs: &[Param], args: &mut [Out<B>]) {
        let mut args = args.iter_mut();
        for spec in specs {
            self.primitive_steps += 1;
            if matches!(spec.arg_type, Attr::ArgCst(_)) {
                continue;
            }
            let Some(arg) = args.next() else {
                break;
            };
            self.hold_external_arg(cx, spec.arg_label, &spec.arg_type, arg);
        }
    }

    /// X:278 hold_external_obj_args. O(specs + arguments). One reverse pass records the suffix predicate, then holds are
    /// allocated in source order. No suffix is searched more than once.
    pub(super) fn hold_external_obj_args(&mut self, cx: Cx, specs: &[ObjParam], args: &mut [Out<B>]) {
        let mut params = std::mem::take(&mut self.ffi_params);
        params.extend(specs.iter().enumerate().filter_map(|(i, p)| {
            (!matches!(
                (&p.obj_arg_label, &p.obj_arg_type),
                (Label::ObjEmpty | Label::ObjLabel { .. }, Attr::ArgCst(_))
            ))
            .then_some(i)
        }));
        let mut suffix = std::mem::take(&mut self.ffi_suffix);
        let mut later = LaterLiteral::default();
        for (i, arg) in args.iter().enumerate().rev() {
            self.primitive_steps += 1;
            suffix.push(later);
            let value = B::of(arg.value.as_ref().expect("object argument"));
            if params.get(i).is_some_and(|&p| {
                let p = &specs[p];
                !matches!(p.obj_arg_label, Label::ObjOptional { .. })
                    || matches!(
                        self.js.kind(&self.arena, value),
                        Kind::Undefined | Kind::Optional
                    )
            }) {
                let r = value;
                later.add(
                    self.js.has(&self.arena, r, flag::DELAY_SAFE),
                    self.js.has(&self.arena, r, flag::STRICT),
                );
            }
        }
        let count = args.len();
        for (i, arg) in args.iter_mut().enumerate() {
            self.primitive_steps += 1;
            let Some(&param) = params.get(i) else {
                continue;
            };
            let param = &specs[param];
            let label = match param.obj_arg_label {
                Label::ObjEmpty => continue,
                Label::ObjLabel { .. } => LabelNoname::ArgLabel,
                Label::ObjOptional { .. } => LabelNoname::ArgOptional,
            };
            self.hold_external_arg(cx, label, &param.obj_arg_type, arg);
            let r = B::of(arg.value.as_ref().expect("object argument"));
            if label == LabelNoname::ArgOptional
                && !matches!(self.js.kind(&self.arena, r), Kind::Undefined | Kind::Optional)
                && !self.js.has(&self.arena, r, flag::DELAY_SAFE)
                && suffix[count - i - 1].conflicts(self.js.has(&self.arena, r, flag::STRICT))
            {
                let value = arg.value.take().expect("object argument");
                let held = self.hold_in_variable(arg, value);
                arg.value = Some(held);
            }
        }
        params.clear();
        suffix.clear();
        self.ffi_params = params;
        self.ffi_suffix = suffix;
    }

    /// X:181 external_optional_to_undefined_expr. O(field spine + copied
    /// spine), or one runtime call. Optional payloads move without copying.
    fn external_optional_to_undefined_expr(&mut self, cx: Cx, arg: B::E) -> B::E {
        match self.js.kind(&self.arena, B::of(&arg)) {
            Kind::Undefined => {
                self.js.release(&mut self.arena, arg);
                self.js.undefined(&mut self.arena, false)
            }
            Kind::Optional => self.js.keep_operand(&mut self.arena, arg, 0),
            _ if self.optional_duplicable(cx, &arg) => {
                let copy = self.js.copy(&mut self.arena, B::of(&arg));
                let undefined = self.js.undefined(&mut self.arena, false);
                let test = self.js.bin(
                    &mut self.arena,
                    crate::js_ir::BinOp::NotEqEq,
                    copy,
                    undefined,
                );
                let mark = self.js.mark();
                self.js.push(arg);
                let value = self.runtime_call("Primitive_option", "valFromOption", mark);
                let undefined = self.js.undefined(&mut self.arena, false);
                self.js.cond(&mut self.arena, test, value, undefined)
            }
            _ => {
                let mark = self.js.mark();
                self.js.push(arg);
                self.runtime_call("Primitive_option", "valFromOption", mark)
            }
        }
    }

    /// A:69 is_okay_to_duplicate(false), used by X:181. O(field spine).
    /// A reference is read with `var_of` before the kind (THREE_TREES 11.4,
    /// "For T6v: a dotted global").
    pub(super) fn optional_duplicable(&self, _cx: Cx, node: &B::E) -> bool {
        let mut r = B::of(node);
        loop {
            if let Some(var) = self.js.var_of(&self.arena, r) {
                return !self
                    .arena
                    .vars
                    .flags(var)
                    .contains(crate::bir::VarFlags::JS_GLOBAL)
                    || !self.arena.vars.name(var).as_str().contains('.');
            }
            match self.js.kind(&self.arena, r) {
                Kind::Qualified
                | Kind::Bool
                | Kind::Str
                | Kind::Template
                | Kind::Number => return true,
                Kind::Dot
                    if self
                        .js
                        .member_of(&self.arena, r)
                        .is_some_and(|(_, position)| position.get().is_some()) =>
                {
                    r = self.js.operand(&self.arena, r, 0);
                }
                _ => return false,
            }
        }
    }

    /// X:421 external_polyvar_unwrap_expr. O(1) shape inspection plus release
    /// of the unused literal tag, or one J-M11 member construction.
    fn external_polyvar_unwrap_expr(&mut self, _cx: Cx, arg: B::E) -> B::E {
        let r = B::of(&arg);
        if self.js.kind(&self.arena, r) == Kind::BlockLit
            && self.js.arity(&self.arena, r) == 2
            && self.js.kind(&self.arena, self.js.operand(&self.arena, r, 0)) == Kind::Number
        {
            return self.js.keep_operand(&mut self.arena, arg, 1);
        }
        self.js.poly_var(&mut self.arena, arg, true)
    }

    /// X:197 external_option_unwrap_expr. O(1) apart from releasing a literal.
    fn external_option_unwrap_expr(&mut self, cx: Cx, arg: B::E) -> B::E {
        match self.js.kind(&self.arena, B::of(&arg)) {
            Kind::Undefined => {
                self.js.release(&mut self.arena, arg);
                self.js.undefined(&mut self.arena, false)
            }
            Kind::Optional => {
                let value = self.js.keep_operand(&mut self.arena, arg, 0);
                self.external_polyvar_unwrap_expr(cx, value)
            }
            _ => {
                let mark = self.js.mark();
                self.js.push(arg);
                self.runtime_call("Primitive_option", "unwrapPolyVar", mark)
            }
        }
    }

    /// X:344/X:400 dispatch IIFE construction. O(cases + spelling bytes).
    fn external_dispatch<T>(
        &mut self,
        _cx: Cx,
        arg: B::E,
        cases: &[(String, T)],
        value: impl Fn(&mut B, &mut Bir, &T) -> B::E,
    ) -> B::E {
        super::names::open(&mut self.arena);
        let keys = crate::bir::KeySpan {
            start: u32::try_from(self.arena.pools.switch_keys.len()).expect("key pool capacity"),
            len: u32::try_from(cases.len()).expect("switch capacity"),
        };
        let clauses = crate::bir::ClauseSpan {
            start: u32::try_from(self.arena.pools.switch_clauses.len())
                .expect("clause pool capacity"),
            len: keys.len,
        };
        let mark = self.statements.mark();
        for (key, item) in cases {
            self.primitive_steps += 1;
            let text = self.arena.intern_text(key);
            self.arena
                .pools
                .switch_keys
                .push(crate::bir::CaseKey::String(text));
            let value = value(&mut self.js, &mut self.arena, item);
            let ret = self.js.return_(&mut self.arena, value);
            let body = self.js.list(&mut self.arena, 1, std::iter::once(ret));
            let action = self.js.block_of(&mut self.arena, body);
            self.statements.push(action);
            self.arena
                .pools
                .switch_clauses
                .push(crate::bir::ClauseMeta {
                    should_break: false,
                    comment: None,
                    loc: None,
                });
        }
        // The scrutinee was built before the function's scope opened and
        // moves into it (G10). `names::adopt` takes the row, read by its id
        // until T6r.
        let site = NodeId(self.js.id(&self.arena, B::of(&arg)));
        super::names::adopt(&mut self.arena, &self.idents, site);
        let header = self.arena.switch_record(crate::bir::SwitchRecord {
            constants: keys.len,
            keys,
            clauses,
            has_default: false,
            consts_full: false,
            blocks_full: false,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let actions_list = self.statements.take_actions(&mut self.js, &mut self.arena, self.statements.since(mark));
        let switch = self.js.switch(&mut self.arena, arg, actions_list, header, true);
        let body = self.js.list(&mut self.arena, 1, std::iter::once(switch));
        let header = self.arena.function_header(
            crate::bir::VarSpan { start: 0, len: 0 },
            Default::default(),
            crate::lambda::LamLoc::NONE,
        );
        let callee = self.js.function(&mut self.arena, header, body);
        super::names::close(&mut self.arena, &self.idents, header);
        self.call_values(callee, std::iter::empty(), Default::default())
    }

    /// X:344 external_polyvar_string_expr. O(dispatch cases + spelling bytes).
    fn external_polyvar_string_expr(
        &mut self,
        cx: Cx,
        arg: B::E,
        cases: &[(String, String)],
    ) -> B::E {
        let r = B::of(&arg);
        match self.js.kind(&self.arena, r) {
            Kind::Undefined => return arg,
            Kind::Str => {
                let text = self.js.text(&self.arena, r).expect("a string literal's text");
                let target = &cases
                    .iter()
                    .find(|(key, _)| key == text)
                    .expect("polyvariant string tag")
                    .1;
                let result = self.js.string(&mut self.arena, target);
                self.js.release(&mut self.arena, arg);
                return result;
            }
            _ => {}
        }
        self.external_dispatch(cx, arg, cases, |js, arena, value| js.string(arena, value))
    }

    /// X:400 external_polyvar_int_expr. O(dispatch cases + spelling bytes).
    fn external_polyvar_int_expr(
        &mut self,
        cx: Cx,
        arg: B::E,
        cases: &[(String, i64)],
    ) -> B::E {
        let r = B::of(&arg);
        match self.js.kind(&self.arena, r) {
            Kind::Undefined => return arg,
            Kind::Str => {
                let text = self.js.text(&self.arena, r).expect("a string literal's text");
                let value = cases
                    .iter()
                    .find(|(key, _)| key == text)
                    .expect("polyvariant integer tag")
                    .1;
                self.js.release(&mut self.arena, arg);
                return self.js.int_literal(&mut self.arena, value as i32);
            }
            _ => {}
        }
        self.external_dispatch(cx, arg, cases, |js, arena, value| {
            js.int_literal(arena, *value as i32)
        })
    }

    /// X:374 external_polyvar_event_exprs. O(argument copy + dispatch cases).
    /// The bounded result stays inline; literal operands move to their uses.
    fn external_polyvar_event_exprs(
        &mut self,
        cx: Cx,
        arg: B::E,
        cases: Option<&[(String, String)]>,
    ) -> [Option<B::E>; 2] {
        let (tag, value) = if self.literal_polyvar_block(cx, &arg) {
            self.js.unpack_rev(&mut self.arena, arg);
            let tag = self.js.pop();
            let value = self.js.pop();
            (tag, value)
        } else {
            let copy = self.js.copy(&mut self.arena, B::of(&arg));
            (
                self.js.poly_var(&mut self.arena, arg, false),
                self.js.poly_var(&mut self.arena, copy, true),
            )
        };
        let tag = match cases {
            Some(cases) => self.external_polyvar_string_expr(cx, tag, cases),
            None => tag,
        };
        [Some(tag), Some(value)]
    }

    /// X:782 lower_external_arg_values_and_effect. O(argument conversion),
    /// returning zero to two values inline, never a vector allocation per arg.
    pub(super) fn lower_external_arg_values_and_effect(
        &mut self,
        cx: Cx,
        raw: B::E,
        label: LabelNoname,
        attr: &Attr,
    ) -> ([Option<B::E>; 2], Option<B::E>) {
        if matches!(attr, Attr::Unwrap) && label == LabelNoname::ArgOptional {
            return (
                [Some(self.external_option_unwrap_expr(cx, raw)), None],
                None,
            );
        }
        let arg = if label == LabelNoname::ArgOptional {
            self.external_optional_to_undefined_expr(cx, raw)
        } else {
            raw
        };
        let value = match attr {
            Attr::Nothing => arg,
            Attr::ArgCst(_) => {
                self.js.release(&mut self.arena, arg);
                return ([None, None], None);
            }
            Attr::Ignore => return ([None, None], self.external_arg_effect(cx, arg)),
            Attr::ExternUnit => {
                let effect = self.external_arg_effect(cx, arg);
                let values = if label == LabelNoname::ArgEmpty {
                    [None, None]
                } else {
                    [Some(self.js.undefined(&mut self.arena, true)), None]
                };
                return (values, effect);
            }
            Attr::PolyVarString { descr } => self.external_polyvar_string_expr(cx, arg, descr),
            Attr::PolyVar { descr } => {
                return (
                    self.external_polyvar_event_exprs(cx, arg, descr.as_deref()),
                    None,
                );
            }
            Attr::Int(cases) => self.external_polyvar_int_expr(cx, arg, cases),
            Attr::Unwrap => self.external_polyvar_unwrap_expr(cx, arg),
        };
        ([Some(value), None], None)
    }

    /// C:6120 compile_external_arg_const. O(literal spelling bytes).
    pub(super) fn compile_external_arg_const(
        &mut self,
        _cx: Cx,
        cst: &crate::types::external_ffi_types::Cst,
    ) -> B::E {
        use crate::types::external_ffi_types::Cst;
        match cst {
            Cst::ArgIntLit(value) => self.js.int_literal(&mut self.arena, *value as i32),
            Cst::ArgStringLit(value) => self.js.string(&mut self.arena, value),
            Cst::ArgJsonLit(value) => {
                let text = self.arena.intern_text(value);
                self.js.json(&mut self.arena, text)
            }
        }
    }

    /// X:834 assemble_external_args_no_splice. O(specs + conversions + fused
    /// effects). The values are pushed as operands as they are converted
    /// and their number is returned; the caller takes the mark before the
    /// call. Trailing trimming zips the pushed values with the original
    /// specs from the end: one pop per value looked at, the trimmed ones
    /// released in their order; nothing is allocated once
    /// `State::external_values` has its capacity.
    pub(super) fn assemble_external_args_no_splice(
        &mut self,
        cx: Cx,
        specs: &[Param],
        args: crate::bir::ListId,
    ) -> (u32, Option<B::E>) {
        let argc = self.arena.lists.get(args).len();
        let mut at = 0;
        let mut count = 0;
        let mut effect = None;
        for spec in specs {
            self.primitive_steps += 1;
            if let Attr::ArgCst(cst) = &spec.arg_type {
                let value = self.compile_external_arg_const(cx, cst);
                self.js.push(value);
                count += 1;
            } else {
                let arg = if at < argc {
                    // T6x-d: `compile_js_call` is given a pool list of rows.
                    let value = B::from_node(self.arena.lists.get(args)[at]);
                    at += 1;
                    value
                } else {
                    self.js.undefined(&mut self.arena, false)
                };
                let (converted, next_effect) = self.lower_external_arg_values_and_effect(
                    cx,
                    arg,
                    spec.arg_label,
                    &spec.arg_type,
                );
                for value in converted.into_iter().flatten() {
                    self.js.push(value);
                    count += 1;
                }
                if let Some(next) = next_effect {
                    effect = Some(self.add_external_effect(cx, effect, next));
                }
            }
        }
        debug_assert_eq!(at, argc);
        let mut trimmed = std::mem::take(&mut self.external_values);
        debug_assert!(trimmed.is_empty());
        for spec in specs.iter().rev().take(count as usize) {
            let value = self.js.pop();
            let r = B::of(&value);
            if spec.arg_label == LabelNoname::ArgOptional
                && self.js.kind(&self.arena, r) == Kind::Undefined
                && self.js.aux(&self.arena, r) == 0
            {
                trimmed.push(value);
            } else {
                self.js.push(value);
                break;
            }
        }
        count -= trimmed.len() as u32;
        for value in trimmed.drain(..).rev() {
            self.js.release(&mut self.arena, value);
        }
        self.external_values = trimmed;
        (count, effect)
    }

    /// X:894 assemble_external_args_with_splice. O(specs + array elements +
    /// conversion work); the last runtime argument, not last spec, is spliced.
    /// The values are pushed as operands as they are converted and their
    /// number is returned; the caller takes the mark before the call. The
    /// elements of a spliced array literal pass through
    /// `State::external_values` to be pushed in order: two moves each,
    /// nothing allocated once it has its capacity.
    pub(super) fn assemble_external_args_with_splice(
        &mut self,
        cx: Cx,
        specs: &[Param],
        args: crate::bir::ListId,
    ) -> (u32, Option<B::E>) {
        let argc = self.arena.lists.get(args).len();
        let mut at = 0;
        let mut count = 0;
        let mut effect = None;
        let mut spread = false;
        for spec in specs {
            self.primitive_steps += 1;
            if let Attr::ArgCst(cst) = &spec.arg_type {
                let value = self.compile_external_arg_const(cx, cst);
                self.js.push(value);
                count += 1;
                continue;
            }
            let arg = if at < argc {
                // T6x-d: `compile_js_call` is given a pool list of rows.
                let value = B::from_node(self.arena.lists.get(args)[at]);
                at += 1;
                value
            } else {
                self.js.undefined(&mut self.arena, false)
            };
            if at == argc {
                if self.js.kind(&self.arena, B::of(&arg)) == Kind::Array {
                    let elements = self.js.unpack_rev(&mut self.arena, arg);
                    let mut values = std::mem::take(&mut self.external_values);
                    debug_assert!(values.is_empty());
                    for _ in 0..elements {
                        self.primitive_steps += 1;
                        values.push(self.js.pop());
                    }
                    for value in values.drain(..) {
                        self.js.push(value);
                    }
                    self.external_values = values;
                    count += elements;
                    continue;
                }
                spread = true;
            }
            let (converted, next_effect) =
                self.lower_external_arg_values_and_effect(cx, arg, spec.arg_label, &spec.arg_type);
            for value in converted.into_iter().flatten() {
                self.js.push(value);
                count += 1;
            }
            if let Some(next) = next_effect {
                effect = Some(self.add_external_effect(cx, effect, next));
            }
        }
        debug_assert_eq!(at, argc);
        if spread && count > 0 {
            let value = self.js.pop();
            let value = self.js.spread(&mut self.arena, value);
            self.js.push(value);
        }
        (count, effect)
    }

    /// X:959 assemble_external_args. O(specs + selected assembly work): the
    /// values are pushed as operands and their number is returned.
    pub(super) fn assemble_external_args(
        &mut self,
        cx: Cx,
        specs: &[Param],
        args: crate::bir::ListId,
        splice: bool,
    ) -> (u32, Option<B::E>) {
        if splice {
            self.assemble_external_args_with_splice(cx, specs, args)
        } else {
            self.assemble_external_args_no_splice(cx, specs, args)
        }
    }

    /// X:741 external_arg_effect. O(1) cached ordinary purity lookup.
    pub(super) fn external_arg_effect(&mut self, _cx: Cx, arg: B::E) -> Option<B::E> {
        if self.js.has(&self.arena, B::of(&arg), flag::PURE) {
            self.js.release(&mut self.arena, arg);
            None
        } else {
            Some(arg)
        }
    }

    /// X:755 add_external_effect. Cost: O(1), apart from that of J-M1 on the
    /// two operands.
    pub(super) fn add_external_effect(
        &mut self,
        _cx: Cx,
        effect: Option<B::E>,
        value: B::E,
    ) -> B::E {
        match effect {
            Some(effect) => self.js.seq_rule(&mut self.arena, effect, value),
            None => value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::j::plain;
    use smallvec::SmallVec;

    #[test]
    fn ten_thousand_ffi_dispatch_cases_lower_without_allocations() {
        use crate::lambda::{
            LamLoc,
            arena::LamArena,
            lam_primitive::{DeclKind, ExternalDecl, JsCall, Primitive},
        };
        let mut source = LamArena::new();
        let arg = source.var(Ident::new("arg", 1, crate::ident::IdentFlags::NONE));
        let cases = (0..10_000)
            .map(|i| (format!("key{i}"), format!("value{i}")))
            .collect();
        let root = source.prim_raw(
            Primitive::PjsCall(Box::new(JsCall {
                prim_name: "consume".into(),
                arg_types: vec![Param {
                    arg_type: Attr::PolyVarString { descr: cases },
                    arg_label: LabelNoname::ArgEmpty,
                }],
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
        let input = crate::bir::bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |state: &mut State<'_>| {
            let out = state.probe(Cx::value(), root).unwrap();
            let out = state.realize(Cx::value(), out);
            assert!(!state.statements.has_statements(out.stmts));
            state.arena.release(crate::bir::lower::out::row(out.value.unwrap()));
            state.statements.kill(out.stmts);
        };
        let lists_before = state.arena.lists.storage_shape().0;
        run(&mut state);
        let growth = state.arena.lists.storage_shape().0 - lists_before;
        state.arena.lists.reserve_test_growth(growth);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        state
            .arena
            .pools
            .switch_keys
            .reserve(state.arena.pools.switch_keys.len());
        state
            .arena
            .pools
            .switch_clauses
            .reserve(state.arena.pools.switch_clauses.len());
        let capacities = |s: &State<'_>| {
            [
                s.arena.nodes.capacity(),
                s.arena.lists.storage_shape().1,
                s.arena.pools.switch_keys.capacity(),
                s.arena.pools.switch_clauses.capacity(),
                s.arena.pools.switches.capacity(),
                s.arena.vars.funcs.capacity(),
                s.arena.pools.attrs.capacity(),
                s.arena.pools.js.capacity(),
                s.arena.release_stack.capacity(),
                s.arena.free_nodes.capacity(),
                s.argument_outputs.capacity(),
                s.argument_values.capacity(),
                s.external_values.capacity(),
            ]
        };
        let before = capacities(&state);
        let steps = state.primitive_steps;
        let visits = state.source_steps;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("whole FFI dispatch: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.source_steps - visits, 2);
        assert_eq!(state.primitive_steps - steps, 10_004);
        assert_eq!(std::mem::size_of::<[Option<NodeId>; 2]>(), 16);
        assert_eq!(std::mem::size_of::<crate::bir::KeySpan>(), 8);
        assert_eq!(std::mem::size_of::<crate::bir::ClauseSpan>(), 8);
        assert_eq!(std::mem::size_of::<crate::bir::SwitchRecord>(), 96);
        assert_eq!(std::mem::size_of::<crate::bir::SwitchHeader<'_>>(), 48);
        assert_eq!(std::mem::size_of::<crate::bir::SwitchInput>(), 128);
    }

    /// The same Lambda operands go through both lowerers before the X helpers.
    fn oracle(
        mut source: crate::lambda::arena::LamArena,
        args: &[crate::lambda::arena::Lam],
        specs: &[Param],
    ) {
        use crate::bir::{bridge, bridge_j};
        use crate::js_ir::{
            arena::{JsDepsProgram, JsProgram, StmtKind},
            build::exp,
        };
        use crate::lambda::{LamLoc, lam_compile::LambdaCompiler, lam_primitive::Primitive};
        let root = source.prim_raw(Primitive::Pmakearray, args, LamLoc::NONE);
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let View::Prim { args: children, .. } = state.source.view(root) else {
            unreachable!()
        };
        let children = children.to_vec();
        let mut outputs: SmallVec<[Out<_>; 4]> = SmallVec::new();
        let mut compiler = LambdaCompiler::new();
        let mut expected = crate::lambda::lam_compile_arguments::HeldArgs::new();
        let target = Ident::new("unused", 100, crate::ident::IdentFlags::NONE);
        for (&node, &old) in children.iter().zip(args) {
            let result = state.probe(Cx::value(), node).unwrap();
            let mut out = state.realize(Cx::value(), result);
            state.statements.reserve();
            out.stmts = state.statements.since(Span {
                start: out.stmts.start,
                len: 0,
            });
            outputs.push(out);
            let out = compiler.bir_lower_oracle(&mut source, old, Cx::value().cont, target);
            expected.push((out.prelude, out.expr));
        }
        state.hold_external_args(Cx::value(), specs, &mut outputs);
        let mut held = outputs;
        let mut args = Vec::new();
        let stmts = state.sequence_arguments(false, &mut held, &mut args);
        let args: Vec<_> = args.into_iter().map(crate::bir::lower::out::row).collect();
        let args = state.arena.lists.push(&args);
        use crate::bir::lower::js::Js;
        let mark = state.js.mark();
        let (_, effect) = state.assemble_external_args_no_splice(Cx::value(), specs, args);
        let value = state.js.array(&mut state.arena, mark, 0);
        let value = state.add_external_effect(Cx::value(), effect, value);
        let lowered = state.complete(
            Cx::value(),
            Probed::Out(Out {
                stmts,
                value: Some(value),
                finished: Finished::False,
            }),
        );
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
        let actual = bridge_j::export_js(&lowered.program).unwrap();
        let held = compiler.hold_external_args(specs, expected);
        let (mut block, args) = compiler.sequence_arguments(false, held);
        let (args, effect) = compiler.assemble_external_args_no_splice(specs, args.into_vec());
        let value = exp::array(
            &args,
            crate::js_ir::op::MutableFlag::Immutable,
            &mut compiler.j,
        );
        let value = compiler.add_external_effect(effect, value);
        block.push(compiler.j.stmt(StmtKind::Exp(value)));
        let expected = JsDepsProgram {
            program: JsProgram::new_in(block, vec![], compiler.j),
            modules: vec![],
            side_effect: None,
        };
        let print = |p: &JsDepsProgram| {
            crate::js_ir::print_deps_program_with_directives_and_options(
                p,
                None,
                &[],
                false,
                false,
                false,
            )
        };
        assert_eq!(print(&actual), print(&expected), "{specs:?}");
    }

    #[test]
    fn argument_kinds_and_holds_match_legacy() {
        use crate::lambda::{
            LamLoc, arena::LamArena, lam_constant::Constant, lam_primitive::Primitive,
        };
        use crate::types::external_ffi_types::Cst;
        let attrs = [
            Attr::Nothing,
            Attr::Ignore,
            Attr::ExternUnit,
            Attr::PolyVarString {
                descr: vec![("tag".into(), "mapped".into())],
            },
            Attr::PolyVar { descr: None },
            Attr::PolyVar {
                descr: Some(vec![("tag".into(), "mapped".into())]),
            },
            Attr::Int(vec![("tag".into(), 42)]),
            Attr::Unwrap,
        ];
        for attr in attrs {
            for label in [
                LabelNoname::ArgEmpty,
                LabelNoname::ArgLabel,
                LabelNoname::ArgOptional,
            ] {
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
                    oracle(
                        a,
                        &[arg],
                        &[Param {
                            arg_label: label,
                            arg_type: attr.clone(),
                        }],
                    );
                }
            }
        }
        for cst in [
            Cst::ArgIntLit(42),
            Cst::ArgStringLit("constant".into()),
            Cst::ArgJsonLit("{}".into()),
        ] {
            oracle(
                LamArena::new(),
                &[],
                &[Param {
                    arg_label: LabelNoname::ArgEmpty,
                    arg_type: Attr::ArgCst(cst),
                }],
            );
        }
    }

    #[test]
    fn earlier_argument_is_sequenced_before_later_statements() {
        use crate::lambda::{
            LamLoc, arena::LamArena, lam_constant::Constant, lam_primitive::Primitive,
        };
        let mut a = LamArena::new();
        let first = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
        let effect = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
        let value = a.const_(Constant::String("tag".into()));
        let later = a.seq_raw(effect, value);
        oracle(
            a,
            &[first, later],
            &[
                Param {
                    arg_label: LabelNoname::ArgEmpty,
                    arg_type: Attr::PolyVar { descr: None },
                },
                Param {
                    arg_label: LabelNoname::ArgEmpty,
                    arg_type: Attr::Nothing,
                },
            ],
        );
    }

    #[test]
    fn reverse_summary_matches_suffix_predicate() {
        assert_eq!(std::mem::size_of::<LaterLiteral>(), 2);
        for bits in 0..256u32 {
            let facts: Vec<_> = (0..4)
                .map(|i| ((bits >> (2 * i)) & 1 != 0, (bits >> (2 * i + 1)) & 1 != 0))
                .collect();
            let mut later = LaterLiteral::default();
            for i in (0..facts.len()).rev() {
                for pure in [false, true] {
                    assert_eq!(
                        later.conflicts(pure),
                        facts[i + 1..]
                            .iter()
                            .any(|&(safe, later_pure)| !safe && !(pure && later_pure))
                    );
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
            let mut args: SmallVec<[Out<_>; 4]> = SmallVec::with_capacity(10_000);
            let mut specs = Vec::new();
            let mut obj_specs = Vec::new();
            for i in 0..10_000 {
                let text = state.arena.intern_text("effect()");
                let value = plain::node(&mut state.arena, View::JRaw { text }, 0);
                let start = state.statements.mark();
                state.statements.reserve();
                args.push(Out {
                    stmts: state.statements.since(start),
                    value: Some(crate::bir::lower::out::of_row(value)),
                    finished: Finished::False,
                });
                specs.push(Param {
                    arg_label: LabelNoname::ArgEmpty,
                    arg_type: Attr::PolyVar { descr: None },
                });
                obj_specs.push(ObjParam {
                    obj_arg_type: Attr::Nothing,
                    obj_arg_label: if i % 2 == 0 {
                        Label::ObjOptional {
                            name: "optional".into(),
                            for_sure_no_nested_option: false,
                        }
                    } else {
                        Label::ObjLabel {
                            name: "required".into(),
                        }
                    },
                });
            }
            if objects {
                state.hold_external_obj_args(Cx::value(), &obj_specs, &mut args);
            } else {
                state.hold_external_args(Cx::value(), &specs, &mut args);
            }
            let mut held = args;
            assert_eq!(held.len(), 10_000);
            assert_eq!(state.primitive_steps, if objects { 20_000 } else { 10_000 });
            assert_eq!(
                state.statements.pushed,
                if objects { 5_000 } else { 10_000 }
            );
            let mut values = Vec::new();
            state.sequence_arguments(false, &mut held, &mut values);
            assert_eq!(values.len(), 10_000);
            assert!(state.sequence_steps <= 30_000);
        }
    }
}
