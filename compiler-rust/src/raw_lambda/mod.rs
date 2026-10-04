//! Raw Lambda IR - Pre-optimization Lambda representation.
//!
//! This module exists to mirror OCaml's staged pipeline:
//! typedtree -> raw lambda -> lowered lambda -> JS IR.
//!
//! The initial scaffolding keeps the raw stage structurally separate
//! from the existing lowered [`crate::lambda`] IR, so `-drawlambda`
//! can evolve independently without perturbing JS generation.

pub mod convert;
pub(crate) mod lambda_scc;
pub mod lower;
pub mod matching;
pub mod print;
pub mod switch;
pub(crate) mod typeopt;

use crate::ident::Ident;
use crate::lambda::{ApInfo, DirectionFlag, FunctionAttribute, Lambda, LetKind};
use crate::lambda::{Comparison, Constant, FieldDbgInfo, Primitive, SetFieldDbgInfo};
use crate::location::Location;

/// Raw-lambda switch construct.
#[derive(Debug, Clone)]
pub struct RawLambdaSwitch {
    /// Are all constant cases covered?
    pub sw_consts_full: bool,
    /// Constant case branches.
    pub sw_consts: Vec<(crate::lambda::SwitchKey, RawLambda)>,
    /// Are all block cases covered?
    pub sw_blocks_full: bool,
    /// Block case branches.
    pub sw_blocks: Vec<(crate::lambda::SwitchKey, RawLambda)>,
    /// Fallback action if no case matches.
    pub sw_failaction: Option<Box<RawLambda>>,
    /// Runtime dispatch semantics.
    pub sw_dispatch: crate::lambda::SwitchDispatch,
}

/// Raw-lambda function definition.
#[derive(Debug, Clone)]
pub struct RawLFunction {
    /// Number of arguments.
    pub arity: i32,
    /// Parameter identifiers.
    pub params: Vec<Ident>,
    /// Function body.
    pub body: Box<RawLambda>,
    /// Function attributes.
    pub attr: FunctionAttribute,
}

/// Raw-lambda primitive operation payload.
#[derive(Debug, Clone)]
pub struct RawPrimInfo {
    /// The primitive operation.
    pub primitive: Primitive,
    /// Arguments to the primitive.
    pub args: Vec<RawLambda>,
    /// Source location.
    pub loc: Location,
}

/// Raw-lambda function application.
#[derive(Debug, Clone)]
pub struct RawApply {
    /// Function being applied.
    pub ap_func: Box<RawLambda>,
    /// Arguments.
    pub ap_args: Vec<RawLambda>,
    /// Application metadata.
    pub ap_info: ApInfo,
    /// Whether this was transformed from JSX.
    pub ap_transformed_jsx: bool,
}

/// Raw Lambda IR expression.
#[derive(Debug, Clone)]
pub enum RawLambda {
    /// Variable reference.
    Lvar(Ident),
    /// Global module reference.
    LglobalModule(Ident),
    /// Constant value.
    Lconst(Constant),
    /// Function application.
    Lapply(Box<RawApply>),
    /// Function definition.
    Lfunction(Box<RawLFunction>),
    /// Let binding.
    Llet(LetKind, Ident, Box<RawLambda>, Box<RawLambda>),
    /// Recursive let bindings.
    Lletrec(Vec<(Ident, RawLambda)>, Box<RawLambda>),
    /// Primitive operation.
    Lprim(Box<RawPrimInfo>),
    /// Switch on integer/block tag.
    Lswitch(Box<RawLambda>, Box<RawLambdaSwitch>),
    /// Switch on string value.
    LstringSwitch(
        Box<RawLambda>,
        Vec<(String, RawLambda)>,
        Option<Box<RawLambda>>,
    ),
    /// Raise a static exception.
    LstaticRaise(i32, Vec<RawLambda>),
    /// Catch a static exception.
    LstaticCatch(Box<RawLambda>, (i32, Vec<Ident>), Box<RawLambda>),
    /// Try-with exception handling.
    LtryWith(Box<RawLambda>, Ident, Box<RawLambda>),
    /// If-then-else.
    LifThenElse(Box<RawLambda>, Box<RawLambda>, Box<RawLambda>),
    /// Sequence of expressions.
    Lsequence(Box<RawLambda>, Box<RawLambda>),
    /// While loop.
    Lwhile(Box<RawLambda>, Box<RawLambda>),
    /// For loop.
    Lfor(
        Ident,
        Box<RawLambda>,
        Box<RawLambda>,
        DirectionFlag,
        Box<RawLambda>,
    ),
    /// For-of loop (upstream #7887).
    Lfor_of(Ident, Box<RawLambda>, Box<RawLambda>),
    /// For-await-of loop (upstream #7887).
    Lfor_await_of(Ident, Box<RawLambda>, Box<RawLambda>),
    /// Break out of the enclosing loop (port of OCaml `Lbreak`).
    Lbreak,
    /// Continue the enclosing loop (port of OCaml `Lcontinue`).
    Lcontinue,
    /// Assignment.
    Lassign(Ident, Box<RawLambda>),
    /// A match action placed in a compiled matching without copying it.
    /// Only the pattern-matching compiler creates this, and its entry points
    /// replace every occurrence (see `matching::resolve_shared_actions`), so
    /// no other pass sees it.
    Lshared(std::sync::Arc<RawLambda>),
}

impl RawLambda {
    /// Look through shared match actions.
    #[inline]
    pub fn peel(&self) -> &RawLambda {
        let mut lam = self;
        while let RawLambda::Lshared(inner) = lam {
            lam = inner;
        }
        lam
    }

    /// Take ownership through shared match actions, copying an action only
    /// while something else still refers to it.
    pub fn unshare(self) -> RawLambda {
        let mut lam = self;
        while let RawLambda::Lshared(inner) = lam {
            lam = std::sync::Arc::unwrap_or_clone(inner);
        }
        lam
    }

    /// Apply `f` to each direct child expression.
    pub fn for_each_child_mut(&mut self, f: &mut impl FnMut(&mut RawLambda)) {
        match self {
            RawLambda::Lvar(_)
            | RawLambda::LglobalModule(_)
            | RawLambda::Lconst(_)
            | RawLambda::Lbreak
            | RawLambda::Lcontinue => {}
            RawLambda::Lapply(apply) => {
                f(&mut apply.ap_func);
                apply.ap_args.iter_mut().for_each(|arg| f(arg));
            }
            RawLambda::Lfunction(func) => f(&mut func.body),
            RawLambda::Llet(_, _, value, body) => {
                f(value);
                f(body);
            }
            RawLambda::Lletrec(bindings, body) => {
                bindings.iter_mut().for_each(|(_, value)| f(value));
                f(body);
            }
            RawLambda::Lprim(info) => info.args.iter_mut().for_each(|arg| f(arg)),
            RawLambda::Lswitch(arg, sw) => {
                f(arg);
                sw.sw_consts.iter_mut().for_each(|(_, act)| f(act));
                sw.sw_blocks.iter_mut().for_each(|(_, act)| f(act));
                if let Some(fail) = &mut sw.sw_failaction {
                    f(fail);
                }
            }
            RawLambda::LstringSwitch(arg, cases, default) => {
                f(arg);
                cases.iter_mut().for_each(|(_, act)| f(act));
                if let Some(default) = default {
                    f(default);
                }
            }
            RawLambda::LstaticRaise(_, args) => args.iter_mut().for_each(|arg| f(arg)),
            RawLambda::LstaticCatch(body, _, handler) | RawLambda::LtryWith(body, _, handler) => {
                f(body);
                f(handler);
            }
            RawLambda::LifThenElse(cond, ifso, ifnot) => {
                f(cond);
                f(ifso);
                f(ifnot);
            }
            RawLambda::Lsequence(first, second) | RawLambda::Lwhile(first, second) => {
                f(first);
                f(second);
            }
            RawLambda::Lfor(_, start, finish, _, body) => {
                f(start);
                f(finish);
                f(body);
            }
            RawLambda::Lfor_of(_, iterable, body) | RawLambda::Lfor_await_of(_, iterable, body) => {
                f(iterable);
                f(body);
            }
            RawLambda::Lassign(_, value) => f(value),
            RawLambda::Lshared(_) => {}
        }
    }

    /// Create a variable reference.
    pub fn var(id: Ident) -> Self {
        RawLambda::Lvar(id)
    }

    /// Create a global module reference.
    pub fn global_module(id: Ident) -> Self {
        RawLambda::LglobalModule(id)
    }

    /// Create a constant.
    pub fn const_(c: Constant) -> Self {
        RawLambda::Lconst(c)
    }

    /// Create a function.
    pub fn function_(
        arity: i32,
        params: Vec<Ident>,
        body: RawLambda,
        attr: FunctionAttribute,
    ) -> Self {
        RawLambda::Lfunction(Box::new(RawLFunction {
            arity,
            params,
            body: Box::new(body),
            attr,
        }))
    }

    /// Create a let binding.
    pub fn let_(kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> Self {
        RawLambda::Llet(kind, id, Box::new(value), Box::new(body))
    }

    /// Create recursive let bindings.
    pub fn letrec(bindings: Vec<(Ident, RawLambda)>, body: RawLambda) -> Self {
        RawLambda::Lletrec(bindings, Box::new(body))
    }

    /// Create a primitive operation.
    pub fn prim(primitive: Primitive, args: Vec<RawLambda>, loc: Location) -> Self {
        RawLambda::Lprim(Box::new(RawPrimInfo {
            primitive,
            args,
            loc,
        }))
    }

    /// `Lambda.mk_builtin` builds a builtin through the smart `Lambda.prim`
    /// (lambda.ml), whose folds evaluate a primitive over one or two
    /// constant arguments at construction. Those folds read constants only,
    /// so they are taken from [`Lambda::prim`], applied to the constants in
    /// the form OCaml builds them (raw constants keep a few encodings, such
    /// as an int-named polymorphic variant, until they are lowered).
    pub fn prim_folded(primitive: Primitive, args: Vec<RawLambda>, loc: Location) -> Self {
        if matches!(args.len(), 1 | 2) && args.iter().all(|arg| matches!(arg, RawLambda::Lconst(_))) {
            let consts = args
                .iter()
                .map(|arg| match arg {
                    RawLambda::Lconst(c) => Lambda::Lconst(crate::raw_lambda::lower::lower_constant(c.clone())),
                    _ => unreachable!(),
                })
                .collect();
            if let Lambda::Lconst(c) = Lambda::prim(primitive.clone(), consts, loc.clone()) {
                return RawLambda::Lconst(c);
            }
        }
        RawLambda::prim(primitive, args, loc)
    }

    /// Translcore builds conditionals through the smart `Lambda.if_`
    /// (lambda.ml). Its constant-condition and `assert false` arms decide
    /// which branches the match compiler sees, so they apply here; the arms
    /// that rewrite the condition itself are applied by [`Lambda::if_`] when
    /// the term is lowered.
    pub fn if_(cond: RawLambda, then_: RawLambda, else_: RawLambda) -> Self {
        let is_assertfalse = |lam: &RawLambda| {
            matches!(
                lam,
                RawLambda::Lconst(Constant::Int { comment: Some(info), .. })
                    if matches!(**info, crate::lambda::lam_constant::PointerInfo::AssertFalse)
            )
        };
        match cond {
            RawLambda::Lconst(c) => {
                if crate::raw_lambda::lower::lower_constant(c).eval_as_bool() {
                    then_
                } else {
                    else_
                }
            }
            cond if is_assertfalse(&else_) => RawLambda::seq(cond, then_),
            cond if is_assertfalse(&then_) => RawLambda::seq(cond, else_),
            cond => RawLambda::LifThenElse(Box::new(cond), Box::new(then_), Box::new(else_)),
        }
    }

    /// Create a sequence.
    pub fn seq(first: RawLambda, second: RawLambda) -> Self {
        RawLambda::Lsequence(Box::new(first), Box::new(second))
    }

    /// Unit constant.
    pub fn unit() -> Self {
        RawLambda::Lconst(Constant::JsUndefined { is_unit: true })
    }

    /// Check if this is the unit value.
    pub fn is_unit(&self) -> bool {
        matches!(
            self,
            RawLambda::Lconst(Constant::JsUndefined { is_unit: true })
        )
    }

    /// Convert the existing lowered Lambda into raw-lambda scaffolding.
    pub fn from_lowered(lowered: Lambda) -> Self {
        match lowered {
            Lambda::Lvar(id) => RawLambda::Lvar(id),
            Lambda::LglobalModule(id) => {
                RawLambda::LglobalModule(id)
            }
            Lambda::Lconst(c) => RawLambda::Lconst(c),
            Lambda::Lapply(apply) => RawLambda::Lapply(Box::new(RawApply {
                ap_func: Box::new(RawLambda::from_lowered(*apply.ap_func)),
                ap_args: apply
                    .ap_args
                    .into_iter()
                    .map(RawLambda::from_lowered)
                    .collect(),
                ap_info: apply.ap_info,
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })),
            Lambda::Lfunction(func) => RawLambda::Lfunction(Box::new(RawLFunction {
                arity: func.arity,
                params: func.params,
                body: Box::new(RawLambda::from_lowered(*func.body)),
                attr: func.attr,
            })),
            Lambda::Llet(kind, id, value, body) => RawLambda::Llet(
                kind,
                id,
                Box::new(RawLambda::from_lowered(*value)),
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lletrec(bindings, body) => RawLambda::Lletrec(
                bindings
                    .into_iter()
                    .map(|(id, lam)| (id, RawLambda::from_lowered(lam)))
                    .collect(),
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lprim(info) => RawLambda::Lprim(Box::new(RawPrimInfo {
                primitive: info.primitive,
                args: info.args.into_iter().map(RawLambda::from_lowered).collect(),
                loc: info.loc,
            })),
            Lambda::Lswitch(arg, sw) => RawLambda::Lswitch(
                Box::new(RawLambda::from_lowered(*arg)),
                Box::new(RawLambdaSwitch {
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: sw
                        .sw_consts
                        .into_iter()
                        .map(|(tag, lam)| (tag, RawLambda::from_lowered(lam)))
                        .collect(),
                    sw_blocks_full: sw.sw_blocks_full,
                    sw_blocks: sw
                        .sw_blocks
                        .into_iter()
                        .map(|(tag, lam)| (tag, RawLambda::from_lowered(lam)))
                        .collect(),
                    sw_failaction: sw
                        .sw_failaction
                        .map(|lam| Box::new(RawLambda::from_lowered(*lam))),
                    sw_dispatch: sw.sw_dispatch,
                }),
            ),
            Lambda::LstringSwitch(arg, cases, default) => RawLambda::LstringSwitch(
                Box::new(RawLambda::from_lowered(*arg)),
                cases
                    .into_iter()
                    .map(|(name, lam)| (name, RawLambda::from_lowered(lam)))
                    .collect(),
                default.map(|lam| Box::new(RawLambda::from_lowered(*lam))),
            ),
            Lambda::LstaticRaise(i, args) => {
                RawLambda::LstaticRaise(i, args.into_iter().map(RawLambda::from_lowered).collect())
            }
            Lambda::LstaticCatch(body, handler, on_raise) => RawLambda::LstaticCatch(
                Box::new(RawLambda::from_lowered(*body)),
                handler,
                Box::new(RawLambda::from_lowered(*on_raise)),
            ),
            Lambda::LtryWith(body, exn, handler) => RawLambda::LtryWith(
                Box::new(RawLambda::from_lowered(*body)),
                exn,
                Box::new(RawLambda::from_lowered(*handler)),
            ),
            Lambda::LifThenElse(cond, then_, else_) => RawLambda::LifThenElse(
                Box::new(RawLambda::from_lowered(*cond)),
                Box::new(RawLambda::from_lowered(*then_)),
                Box::new(RawLambda::from_lowered(*else_)),
            ),
            Lambda::Lsequence(first, second) => RawLambda::Lsequence(
                Box::new(RawLambda::from_lowered(*first)),
                Box::new(RawLambda::from_lowered(*second)),
            ),
            Lambda::Lwhile(cond, body) => RawLambda::Lwhile(
                Box::new(RawLambda::from_lowered(*cond)),
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lfor(var, start, end, dir, body) => RawLambda::Lfor(
                var,
                Box::new(RawLambda::from_lowered(*start)),
                Box::new(RawLambda::from_lowered(*end)),
                dir,
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lfor_of(var, iterable, body) => RawLambda::Lfor_of(
                var,
                Box::new(RawLambda::from_lowered(*iterable)),
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lfor_await_of(var, iterable, body) => RawLambda::Lfor_await_of(
                var,
                Box::new(RawLambda::from_lowered(*iterable)),
                Box::new(RawLambda::from_lowered(*body)),
            ),
            Lambda::Lbreak => RawLambda::Lbreak,
            Lambda::Lcontinue => RawLambda::Lcontinue,
            Lambda::Lassign(id, value) => {
                RawLambda::Lassign(id, Box::new(RawLambda::from_lowered(*value)))
            }
        }
    }

    /// Lower raw lambda back into the existing Lambda IR.
    pub fn into_lowered(self) -> Lambda {
        match self {
            RawLambda::Lshared(inner) => std::sync::Arc::unwrap_or_clone(inner).into_lowered(),
            RawLambda::Lvar(id) => Lambda::Lvar(id),
            RawLambda::LglobalModule(id) => {
                Lambda::LglobalModule(id)
            }
            RawLambda::Lconst(c) => Lambda::Lconst(c),
            RawLambda::Lapply(apply) => Lambda::Lapply(Box::new(crate::lambda::Apply {
                ap_func: Box::new(apply.ap_func.into_lowered()),
                ap_args: apply
                    .ap_args
                    .into_iter()
                    .map(RawLambda::into_lowered)
                    .collect(),
                ap_info: apply.ap_info,
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })),
            RawLambda::Lfunction(func) => Lambda::Lfunction(Box::new(crate::lambda::LFunction {
                arity: func.arity,
                params: func.params,
                body: Box::new(func.body.into_lowered()),
                attr: func.attr,
            })),
            RawLambda::Llet(kind, id, value, body) => Lambda::Llet(
                kind,
                id,
                Box::new(value.into_lowered()),
                Box::new(body.into_lowered()),
            ),
            RawLambda::Lletrec(bindings, body) => Lambda::Lletrec(
                bindings
                    .into_iter()
                    .map(|(id, lam)| (id, lam.into_lowered()))
                    .collect(),
                Box::new(body.into_lowered()),
            ),
            RawLambda::Lprim(info) => Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: info.primitive,
                args: info.args.into_iter().map(RawLambda::into_lowered).collect(),
                loc: info.loc,
            })),
            RawLambda::Lswitch(arg, sw) => Lambda::Lswitch(
                Box::new(arg.into_lowered()),
                Box::new(crate::lambda::LambdaSwitch {
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: sw
                        .sw_consts
                        .into_iter()
                        .map(|(tag, lam)| (tag, lam.into_lowered()))
                        .collect(),
                    sw_blocks_full: sw.sw_blocks_full,
                    sw_blocks: sw
                        .sw_blocks
                        .into_iter()
                        .map(|(tag, lam)| (tag, lam.into_lowered()))
                        .collect(),
                    sw_failaction: sw.sw_failaction.map(|lam| Box::new(lam.into_lowered())),
                    sw_dispatch: sw.sw_dispatch,
                }),
            ),
            RawLambda::LstringSwitch(arg, cases, default) => Lambda::LstringSwitch(
                Box::new(arg.into_lowered()),
                cases
                    .into_iter()
                    .map(|(name, lam)| (name, lam.into_lowered()))
                    .collect(),
                default.map(|lam| Box::new(lam.into_lowered())),
            ),
            RawLambda::LstaticRaise(i, args) => {
                Lambda::LstaticRaise(i, args.into_iter().map(RawLambda::into_lowered).collect())
            }
            RawLambda::LstaticCatch(body, handler, on_raise) => Lambda::LstaticCatch(
                Box::new(body.into_lowered()),
                handler,
                Box::new(on_raise.into_lowered()),
            ),
            RawLambda::LtryWith(body, exn, handler) => Lambda::LtryWith(
                Box::new(body.into_lowered()),
                exn,
                Box::new(handler.into_lowered()),
            ),
            RawLambda::LifThenElse(cond, then_, else_) => Lambda::LifThenElse(
                Box::new(cond.into_lowered()),
                Box::new(then_.into_lowered()),
                Box::new(else_.into_lowered()),
            ),
            RawLambda::Lsequence(first, second) => Lambda::Lsequence(
                Box::new(first.into_lowered()),
                Box::new(second.into_lowered()),
            ),
            RawLambda::Lwhile(cond, body) => {
                Lambda::Lwhile(Box::new(cond.into_lowered()), Box::new(body.into_lowered()))
            }
            RawLambda::Lfor(var, start, end, dir, body) => Lambda::Lfor(
                var,
                Box::new(start.into_lowered()),
                Box::new(end.into_lowered()),
                dir,
                Box::new(body.into_lowered()),
            ),
            RawLambda::Lfor_of(var, iterable, body) => Lambda::Lfor_of(
                var,
                Box::new(iterable.into_lowered()),
                Box::new(body.into_lowered()),
            ),
            RawLambda::Lfor_await_of(var, iterable, body) => Lambda::Lfor_await_of(
                var,
                Box::new(iterable.into_lowered()),
                Box::new(body.into_lowered()),
            ),
            RawLambda::Lbreak => Lambda::Lbreak,
            RawLambda::Lcontinue => Lambda::Lcontinue,
            RawLambda::Lassign(id, value) => Lambda::Lassign(id, Box::new(value.into_lowered())),
        }
    }
}

#[allow(dead_code)]
fn _keep_public_types_used(_cmp: Comparison, _field: FieldDbgInfo, _set_field: SetFieldDbgInfo) {}
