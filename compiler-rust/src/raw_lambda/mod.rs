//! Raw Lambda IR - Pre-optimization Lambda representation.
//!
//! This module exists to mirror OCaml's staged pipeline:
//! typedtree -> raw lambda -> lowered lambda -> JS IR.
//!
//! [`convert`] translates the typedtree into [`RawLambda`] (using
//! [`matching`] for pattern matching and [`switch`] for integer switches),
//! [`print`] renders it for `-drawlambda`, and [`lower`] turns it into the
//! lowered [`crate::lambda`] IR that the optimization passes and JS
//! generation consume.

pub mod convert;
pub(crate) mod lambda_scc;
pub mod loc;
pub mod lower;
pub mod matching;
pub mod print;
pub mod switch;
pub(crate) mod typeopt;

use std::cell::{Ref, RefCell};

use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, Node, View};
use crate::lambda::{ApInfo, DirectionFlag, FunctionAttribute, Lambda, LetKind};
use crate::lambda::{Comparison, Constant, Primitive, SwitchDispatch, SwitchKey};

/// A raw Lambda term: a node of the conversion's [`RawArena`].
///
/// Raw Lambda has the node set of the lowered Lambda and the same
/// `Constant`/`Primitive`/`ApInfo` payloads, so translation builds straight
/// into a [`LamArena`] with its non-folding constructors. Terms are
/// immutable and `Copy`: OCaml's physical sharing of match actions and
/// arguments (`Lambda.bind`, `Switch.Store`) is sharing a handle.
pub type RawLambda = Lam;

/// Raw-lambda switch under construction: owned keys and actions, built into
/// a node by [`RawArena::switch`].
#[derive(Debug, Clone)]
pub struct RawLambdaSwitch {
    /// Are all constant cases covered?
    pub sw_consts_full: bool,
    /// Constant case branches.
    pub sw_consts: Vec<(SwitchKey, RawLambda)>,
    /// Are all block cases covered?
    pub sw_blocks_full: bool,
    /// Block case branches.
    pub sw_blocks: Vec<(SwitchKey, RawLambda)>,
    /// Fallback action if no case matches.
    pub sw_failaction: Option<RawLambda>,
    /// Runtime dispatch semantics.
    pub sw_dispatch: SwitchDispatch,
}

/// The arena one typedtree -> raw Lambda conversion builds into.
///
/// Translation builds terms bottom-up through shared references (a
/// constructor's arguments are often built by nested calls), so the arena
/// sits in a `RefCell`; every method borrows it only for its own duration.
/// Reads that hand out references go through [`RawArena::get`]; drop that
/// guard before building. Lowering takes the arena back with
/// [`RawArena::into_inner`] and appends the lowered term to it.
pub struct RawArena {
    a: RefCell<LamArena>,
}

impl Default for RawArena {
    fn default() -> Self {
        Self::new()
    }
}

impl RawArena {
    pub fn new() -> Self {
        Self::with_capacity(1024)
    }

    pub fn with_capacity(nodes: usize) -> Self {
        Self {
            a: RefCell::new(LamArena::with_capacity(nodes)),
        }
    }

    /// The arena, for lowering.
    pub fn into_inner(self) -> LamArena {
        self.a.into_inner()
    }

    /// Read access. Do not build while holding it.
    #[inline]
    pub fn get(&self) -> Ref<'_, LamArena> {
        self.a.borrow()
    }

    #[inline]
    fn with<R>(&self, f: impl FnOnce(&mut LamArena) -> R) -> R {
        f(&mut self.a.borrow_mut())
    }

    /// Mutable access for a rewrite over the arena. Do not touch the
    /// `RawArena` from `f`.
    pub fn with_mut<R>(&self, f: impl FnOnce(&mut LamArena) -> R) -> R {
        self.with(f)
    }

    // ------------------------------------------------------------ reads

    #[inline]
    pub fn node(&self, lam: RawLambda) -> Node {
        self.a.borrow().node(lam)
    }

    pub fn as_var(&self, lam: RawLambda) -> Option<Ident> {
        self.a.borrow().as_var(lam)
    }

    pub fn is_const(&self, lam: RawLambda) -> bool {
        self.a.borrow().is_const(lam)
    }

    /// The constant of a `Lconst` node.
    pub fn const_of(&self, lam: RawLambda) -> Option<Constant> {
        self.a.borrow().as_const(lam).cloned()
    }

    /// Check if this is the unit value.
    pub fn is_unit(&self, lam: RawLambda) -> bool {
        matches!(
            self.a.borrow().as_const(lam),
            Some(Constant::JsUndefined { is_unit: true })
        )
    }

    /// Arity, parameters, body, attributes and location of a function node.
    #[allow(clippy::type_complexity)]
    pub fn function_parts(
        &self,
        lam: RawLambda,
    ) -> Option<(i32, Vec<Ident>, RawLambda, FunctionAttribute, LamLoc)> {
        let a = self.a.borrow();
        match a.node(lam) {
            Node::Function { body, info } => {
                let p = a.func_payload(info);
                Some((
                    p.arity,
                    a.params(info).to_vec(),
                    body,
                    p.attr.clone(),
                    p.loc,
                ))
            }
            _ => None,
        }
    }

    /// The attributes of a function node.
    pub fn function_attr(&self, lam: RawLambda) -> Option<FunctionAttribute> {
        let a = self.a.borrow();
        match a.node(lam) {
            Node::Function { info, .. } => Some(a.func_payload(info).attr.clone()),
            _ => None,
        }
    }

    /// A function node with its attributes changed by `f`; `lam` must be a
    /// function.
    pub fn with_function_attr(
        &self,
        lam: RawLambda,
        f: impl FnOnce(&mut FunctionAttribute),
    ) -> RawLambda {
        self.with(|a| {
            let Node::Function { body, info } = a.node(lam) else {
                unreachable!("with_function_attr on a non-function")
            };
            let p = a.func_payload(info);
            let (arity, params, mut attr, loc) = (p.arity, p.params, p.attr.clone(), p.loc);
            f(&mut attr);
            let info = a.add_func(arity, params, attr, loc);
            a.function_with(info, body)
        })
    }

    /// The list `list` as an owned vector.
    pub fn list(&self, list: crate::lambda::arena::LamList) -> Vec<RawLambda> {
        self.a.borrow().list(list).to_vec()
    }

    /// The scrutinee and owned cases of a switch node.
    pub fn switch_parts(&self, lam: RawLambda) -> Option<(RawLambda, RawLambdaSwitch)> {
        let a = self.a.borrow();
        let View::Switch(scrut, sw) = a.view(lam) else {
            return None;
        };
        Some((
            scrut,
            RawLambdaSwitch {
                sw_consts_full: sw.payload.consts_full,
                sw_consts: sw.consts().map(|(k, l)| (k.clone(), l)).collect(),
                sw_blocks_full: sw.payload.blocks_full,
                sw_blocks: sw.blocks().map(|(k, l)| (k.clone(), l)).collect(),
                sw_failaction: sw.actions.fail,
                sw_dispatch: sw.payload.dispatch.clone(),
            },
        ))
    }

    /// The scrutinee, owned cases and default of a string switch node.
    #[allow(clippy::type_complexity)]
    pub fn string_switch_parts(
        &self,
        lam: RawLambda,
    ) -> Option<(RawLambda, Vec<(String, RawLambda)>, Option<RawLambda>)> {
        let a = self.a.borrow();
        let View::StringSwitch(scrut, sw) = a.view(lam) else {
            return None;
        };
        Some((
            scrut,
            sw.cases().map(|(k, l)| (k.to_string(), l)).collect(),
            sw.default,
        ))
    }

    // ----------------------------------------------------- constructors

    /// Push a node built from existing payload handles.
    pub fn push(&self, node: Node) -> RawLambda {
        self.with(|a| a.push(node))
    }

    /// Create a variable reference.
    pub fn var(&self, id: Ident) -> RawLambda {
        self.with(|a| a.var(id))
    }

    /// Create a global module reference. A predefined exception is its own
    /// name at runtime, so it becomes that string
    /// (`compiler/ml/transl_path.ml` `transl_normal_path`).
    pub fn global_module(&self, id: Ident) -> RawLambda {
        if id.is_predef_exn() {
            self.const_(Constant::String(id.name().to_string()))
        } else {
            self.with(|a| a.global_module(id))
        }
    }

    /// Create a constant.
    pub fn const_(&self, c: Constant) -> RawLambda {
        self.with(|a| a.const_(c))
    }

    /// Unit constant.
    pub fn unit(&self) -> RawLambda {
        self.const_(Constant::JsUndefined { is_unit: true })
    }

    /// Create a function.
    pub fn function_(
        &self,
        arity: i32,
        params: &[Ident],
        body: RawLambda,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> RawLambda {
        self.with(|a| a.function_(arity, params, body, attr, loc))
    }

    /// Create a let binding.
    pub fn let_(&self, kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> RawLambda {
        self.with(|a| a.let_(kind, id, value, body))
    }

    /// Create recursive let bindings.
    pub fn letrec(&self, bindings: &[(Ident, RawLambda)], body: RawLambda) -> RawLambda {
        self.with(|a| a.letrec(bindings, body))
    }

    /// Create a primitive operation.
    pub fn prim(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda {
        self.with(|a| a.prim_raw(primitive, args, loc))
    }

    /// `Lambda.mk_builtin` builds a builtin through the smart `Lambda.prim`
    /// (lambda.ml), whose folds evaluate a primitive over one or two
    /// constant arguments at construction. Those folds read constants only,
    /// so they are taken from [`Lambda::prim`], applied to the constants in
    /// the form OCaml builds them (raw constants keep a few encodings, such
    /// as an int-named polymorphic variant, until they are lowered).
    pub fn prim_folded(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda {
        if matches!(args.len(), 1 | 2) {
            let consts: Option<Vec<Lambda>> = {
                let a = self.a.borrow();
                args.iter()
                    .map(|arg| {
                        a.as_const(*arg).map(|c| {
                            Lambda::Lconst(crate::raw_lambda::lower::lower_constant(c.clone()))
                        })
                    })
                    .collect()
            };
            if let Some(consts) = consts
                && let Lambda::Lconst(c) = Lambda::prim(primitive.clone(), consts, loc)
            {
                return self.const_(c);
            }
        }
        self.prim(primitive, args, loc)
    }

    /// Translcore builds conditionals through the smart `Lambda.if_`
    /// (lambda.ml). Its constant-condition and `assert false` arms decide
    /// which branches the match compiler sees, so they apply here; the arms
    /// that rewrite the condition itself are applied by [`LamArena::if_`]
    /// when the term is lowered.
    pub fn if_(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda {
        let is_assertfalse = |a: &LamArena, lam: RawLambda| {
            matches!(
                a.as_const(lam),
                Some(Constant::Int { comment: Some(info), .. })
                    if matches!(**info, crate::lambda::lam_constant::PointerInfo::AssertFalse)
            )
        };
        enum Shape {
            Const(bool),
            Seq(RawLambda, RawLambda),
            Cond,
            Not(LamLoc),
            Plain,
        }
        let shape = {
            let a = self.a.borrow();
            if let Some(c) = a.as_const(cond) {
                Shape::Const(crate::raw_lambda::lower::lower_constant(c.clone()).eval_as_bool())
            } else if is_assertfalse(&a, else_) {
                Shape::Seq(cond, then_)
            } else if is_assertfalse(&a, then_) {
                Shape::Seq(cond, else_)
            } else {
                // lambda.ml `if_`: `if a then true else false` is `a`, and
                // `if a then false else true` is `not a`, when `a` is boolean.
                match (
                    raw_has_boolean_type(&a, cond),
                    a.as_const(then_),
                    a.as_const(else_),
                ) {
                    (Some(_), Some(Constant::JsTrue), Some(Constant::JsFalse)) => Shape::Cond,
                    (Some(loc), Some(Constant::JsFalse), Some(Constant::JsTrue)) => Shape::Not(loc),
                    _ => Shape::Plain,
                }
            }
        };
        match shape {
            Shape::Const(true) => then_,
            Shape::Const(false) => else_,
            Shape::Seq(first, second) => self.seq(first, second),
            Shape::Cond => cond,
            Shape::Not(loc) => self.with(|a| raw_not(a, loc, cond)),
            Shape::Plain => self.if_raw(cond, then_, else_),
        }
    }

    /// `Lifthenelse` without the smart constructor.
    pub fn if_raw(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda {
        self.with(|a| a.if_raw(cond, then_, else_))
    }

    /// Create a sequence.
    pub fn seq(&self, first: RawLambda, second: RawLambda) -> RawLambda {
        self.with(|a| a.seq_raw(first, second))
    }

    /// Function application.
    pub fn apply(
        &self,
        func: RawLambda,
        args: &[RawLambda],
        info: ApInfo,
        transformed_jsx: bool,
    ) -> RawLambda {
        self.with(|a| a.apply_raw(func, args, info, transformed_jsx))
    }

    /// Switch on integer/block tag.
    pub fn switch(&self, scrut: RawLambda, sw: RawLambdaSwitch) -> RawLambda {
        self.with(|a| {
            let actions = a.add_list_iter(
                sw.sw_consts
                    .iter()
                    .map(|(_, l)| *l)
                    .chain(sw.sw_blocks.iter().map(|(_, l)| *l))
                    .chain(sw.sw_failaction),
            );
            let info = a.add_switch(
                sw.sw_consts_full,
                sw.sw_consts.into_iter().map(|(k, _)| k),
                sw.sw_blocks_full,
                sw.sw_blocks.into_iter().map(|(k, _)| k),
                sw.sw_failaction.is_some(),
                sw.sw_dispatch,
            );
            a.switch_raw(scrut, actions, info)
        })
    }

    /// Switch on string value.
    pub fn string_switch(
        &self,
        scrut: RawLambda,
        cases: &[(String, RawLambda)],
        default: Option<RawLambda>,
    ) -> RawLambda {
        self.with(|a| {
            let actions = a.add_list_iter(cases.iter().map(|(_, l)| *l).chain(default));
            let info = a.add_str_switch(cases.iter().map(|(k, _)| k.as_str()), default.is_some());
            a.string_switch_raw(scrut, actions, info)
        })
    }

    /// Raise a static exception.
    pub fn static_raise(&self, label: i32, args: &[RawLambda]) -> RawLambda {
        self.with(|a| a.static_raise(label, args))
    }

    /// Catch a static exception.
    pub fn static_catch(
        &self,
        body: RawLambda,
        label: i32,
        params: &[Ident],
        handler: RawLambda,
    ) -> RawLambda {
        self.with(|a| a.static_catch(body, label, params, handler))
    }

    /// Try-with exception handling.
    pub fn try_with(&self, body: RawLambda, exn: Ident, handler: RawLambda) -> RawLambda {
        self.with(|a| a.try_(body, exn, handler))
    }

    /// While loop.
    pub fn while_(&self, cond: RawLambda, body: RawLambda) -> RawLambda {
        self.with(|a| a.while_(cond, body))
    }

    /// For loop.
    pub fn for_(
        &self,
        var: Ident,
        start: RawLambda,
        finish: RawLambda,
        dir: DirectionFlag,
        body: RawLambda,
    ) -> RawLambda {
        self.with(|a| a.for_(var, start, finish, dir, body))
    }

    /// For-of loop (upstream #7887).
    pub fn for_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda {
        self.with(|a| a.for_of(var, iterable, body))
    }

    /// For-await-of loop (upstream #7887).
    pub fn for_await_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda {
        self.with(|a| a.for_await_of(var, iterable, body))
    }

    /// Break out of the enclosing loop (port of OCaml `Lbreak`).
    pub fn break_(&self) -> RawLambda {
        self.with(|a| a.break_())
    }

    /// Continue the enclosing loop (port of OCaml `Lcontinue`).
    pub fn continue_(&self) -> RawLambda {
        self.with(|a| a.continue_())
    }

    /// Assignment.
    pub fn assign(&self, id: Ident, value: RawLambda) -> RawLambda {
        self.with(|a| a.assign(id, value))
    }
}

/// `Lambda.has_boolean_type` (`compiler/ml/lambda.ml:1137-1147`).
fn raw_has_boolean_type(a: &LamArena, lam: RawLambda) -> Option<LamLoc> {
    match a.view(lam) {
        View::Prim(primitive, _, loc)
            if matches!(
                primitive,
                Primitive::Pnot
                    | Primitive::Psequand
                    | Primitive::Psequor
                    | Primitive::PisNotNone
                    | Primitive::Pobjcomp(_)
                    | Primitive::Pboolcomp(_)
                    | Primitive::Pintcomp(_)
                    | Primitive::Pfloatcomp(_)
                    | Primitive::Pbigintcomp(_)
                    | Primitive::Pstringcomp(_)
            ) =>
        {
            Some(loc)
        }
        _ => None,
    }
}

/// `Lambda.not_` (`compiler/ml/lambda.ml:1131-1135`).
fn raw_not(a: &mut LamArena, loc: LamLoc, lam: RawLambda) -> RawLambda {
    if let Node::Prim { args, info } = a.node(lam) {
        let payload = a.prim_payload(info);
        if matches!(payload.primitive, Primitive::Pintcomp(Comparison::Neq)) {
            let info = a.add_prim(Primitive::Pintcomp(Comparison::Eq), payload.loc);
            return a.prim_raw_with(info, args);
        }
    }
    a.prim_raw(Primitive::Pnot, &[lam], loc)
}

/// Identifier set used by [`collect_free_variables`].
pub(crate) trait FreeVarSet {
    fn add(&mut self, id: Ident);
    fn discard(&mut self, id: &Ident);
}

impl FreeVarSet for crate::fast_hash::AHashSet<Ident> {
    fn add(&mut self, id: Ident) {
        self.insert(id);
    }
    fn discard(&mut self, id: &Ident) {
        self.remove(id);
    }
}

impl FreeVarSet for std::collections::BTreeSet<Ident> {
    fn add(&mut self, id: Ident) {
        self.insert(id);
    }
    fn discard(&mut self, id: &Ident) {
        self.remove(id);
    }
}

/// Add the free variables of `lam` to `fv`.
///
/// Port of `Lambda_traverse.free_ids` with `free_variables`' getter
/// (`compiler/ml/lambda_traverse.ml:200-231`): children are visited first,
/// then the node's own variable is added or its binders removed.
pub(crate) fn collect_free_variables<S: FreeVarSet>(a: &LamArena, lam: RawLambda, fv: &mut S) {
    let collect = collect_free_variables::<S>;
    match a.view(lam) {
        View::Var(id) => {
            fv.add(id);
        }
        View::GlobalModule(_) | View::Const(_) | View::Break | View::Continue => {}
        View::Apply { func, args, .. } => {
            collect(a, func, fv);
            for arg in args {
                collect(a, *arg, fv);
            }
        }
        View::Function { params, body, .. } => {
            collect(a, body, fv);
            for param in params {
                fv.discard(param);
            }
        }
        View::Let(_, id, arg, body) => {
            collect(a, arg, fv);
            collect(a, body, fv);
            fv.discard(&id);
        }
        View::LetRec(ids, values, body) => {
            collect(a, body, fv);
            for expr in values {
                collect(a, *expr, fv);
            }
            for id in ids {
                fv.discard(id);
            }
        }
        View::Prim(_, args, _) | View::StaticRaise(_, args) => {
            for arg in args {
                collect(a, *arg, fv);
            }
        }
        View::Switch(arg, sw) => {
            collect(a, arg, fv);
            for lam in sw.actions.consts.iter().chain(sw.actions.blocks) {
                collect(a, *lam, fv);
            }
            if let Some(fail) = sw.actions.fail {
                collect(a, fail, fv);
            }
        }
        View::StringSwitch(arg, sw) => {
            collect(a, arg, fv);
            for lam in sw.actions {
                collect(a, *lam, fv);
            }
            if let Some(default) = sw.default {
                collect(a, default, fv);
            }
        }
        View::StaticCatch(body, _, vars, handler) => {
            collect(a, body, fv);
            collect(a, handler, fv);
            for var in vars {
                fv.discard(var);
            }
        }
        View::TryWith(body, exn, handler) => {
            collect(a, body, fv);
            collect(a, handler, fv);
            fv.discard(&exn);
        }
        View::If(cond, ifso, ifnot) => {
            collect(a, cond, fv);
            collect(a, ifso, fv);
            collect(a, ifnot, fv);
        }
        View::Sequence(first, second) | View::While(first, second) => {
            collect(a, first, fv);
            collect(a, second, fv);
        }
        View::For(var, lo, hi, _, body) => {
            collect(a, lo, fv);
            collect(a, hi, fv);
            collect(a, body, fv);
            fv.discard(&var);
        }
        View::ForOf(var, iterable, body) | View::ForAwaitOf(var, iterable, body) => {
            collect(a, iterable, fv);
            collect(a, body, fv);
            fv.discard(&var);
        }
        View::Assign(id, expr) => {
            collect(a, expr, fv);
            fv.add(id);
        }
    }
}
