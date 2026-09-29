//! Raw Lambda IR - Pre-optimization Lambda representation.
//!
//! This module exists to mirror OCaml's staged pipeline:
//! typedtree -> raw lambda -> lowered lambda -> JS IR.
//!
//! The initial scaffolding keeps the raw stage structurally separate
//! from the existing lowered [`crate::lambda`] IR, so `-drawlambda`
//! can evolve independently without perturbing JS generation.

pub mod convert;
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
    /// Number of integer cases in the source switch table.
    pub sw_numconsts: usize,
    /// Are all constant cases covered?
    pub sw_consts_full: bool,
    /// Constant case branches.
    pub sw_consts: Vec<(crate::lambda::SwitchKey, RawLambda)>,
    /// Number of block-tag cases in the source switch table.
    pub sw_numblocks: usize,
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
    LglobalModule(Ident, bool),
    /// Constant value.
    Lconst(Constant),
    /// Function application.
    Lapply(RawApply),
    /// Function definition.
    Lfunction(RawLFunction),
    /// Let binding.
    Llet(LetKind, Ident, Box<RawLambda>, Box<RawLambda>),
    /// Recursive let bindings.
    Lletrec(Vec<(Ident, RawLambda)>, Box<RawLambda>),
    /// Primitive operation.
    Lprim(RawPrimInfo),
    /// Switch on integer/block tag.
    Lswitch(Box<RawLambda>, RawLambdaSwitch, Location),
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
    /// Method send.
    Lsend(String, Box<RawLambda>, Location),
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
            | RawLambda::LglobalModule(_, _)
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
            RawLambda::Lswitch(arg, sw, _) => {
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
            RawLambda::Lassign(_, value) | RawLambda::Lsend(_, value, _) => f(value),
            RawLambda::Lshared(_) => {}
        }
    }

    /// Create a variable reference.
    pub fn var(id: Ident) -> Self {
        RawLambda::Lvar(id)
    }

    /// Create a global module reference.
    pub fn global_module(id: Ident, dynamic_import: bool) -> Self {
        RawLambda::LglobalModule(id, dynamic_import)
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
        RawLambda::Lfunction(RawLFunction {
            arity,
            params,
            body: Box::new(body),
            attr,
        })
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
        RawLambda::Lprim(RawPrimInfo {
            primitive,
            args,
            loc,
        })
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
            Lambda::LglobalModule(id, dynamic_import) => {
                RawLambda::LglobalModule(id, dynamic_import)
            }
            Lambda::Lconst(c) => RawLambda::Lconst(c),
            Lambda::Lapply(apply) => RawLambda::Lapply(RawApply {
                ap_func: Box::new(RawLambda::from_lowered(*apply.ap_func)),
                ap_args: apply
                    .ap_args
                    .into_iter()
                    .map(RawLambda::from_lowered)
                    .collect(),
                ap_info: apply.ap_info,
                ap_transformed_jsx: apply.ap_transformed_jsx,
            }),
            Lambda::Lfunction(func) => RawLambda::Lfunction(RawLFunction {
                arity: func.arity,
                params: func.params,
                body: Box::new(RawLambda::from_lowered(*func.body)),
                attr: func.attr,
            }),
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
            Lambda::Lprim(info) => RawLambda::Lprim(RawPrimInfo {
                primitive: info.primitive,
                args: info.args.into_iter().map(RawLambda::from_lowered).collect(),
                loc: info.loc,
            }),
            Lambda::Lswitch(arg, sw) => RawLambda::Lswitch(
                Box::new(RawLambda::from_lowered(*arg)),
                RawLambdaSwitch {
                    sw_numconsts: sw.sw_consts.len(),
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: sw
                        .sw_consts
                        .into_iter()
                        .map(|(tag, lam)| (tag, RawLambda::from_lowered(lam)))
                        .collect(),
                    sw_numblocks: sw.sw_blocks.len(),
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
                },
                Location::none(),
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
            RawLambda::LglobalModule(id, dynamic_import) => {
                Lambda::LglobalModule(id, dynamic_import)
            }
            RawLambda::Lconst(c) => Lambda::Lconst(c),
            RawLambda::Lapply(apply) => Lambda::Lapply(crate::lambda::Apply {
                ap_func: Box::new(apply.ap_func.into_lowered()),
                ap_args: apply
                    .ap_args
                    .into_iter()
                    .map(RawLambda::into_lowered)
                    .collect(),
                ap_info: apply.ap_info,
                ap_transformed_jsx: apply.ap_transformed_jsx,
            }),
            RawLambda::Lfunction(func) => Lambda::Lfunction(crate::lambda::LFunction {
                arity: func.arity,
                params: func.params,
                body: Box::new(func.body.into_lowered()),
                attr: func.attr,
            }),
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
            RawLambda::Lprim(info) => Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: info.primitive,
                args: info.args.into_iter().map(RawLambda::into_lowered).collect(),
                loc: info.loc,
            }),
            RawLambda::Lswitch(arg, sw, _) => Lambda::Lswitch(
                Box::new(arg.into_lowered()),
                crate::lambda::LambdaSwitch {
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
                },
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
            RawLambda::Lsend(name, obj, loc) => Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::PjsCall {
                    prim_name: format!("send{name}"),
                    arg_types: vec![crate::lambda::lam_primitive::ExternalArgSpec::dummy()],
                    ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                        kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper:
                            crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    }),
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                args: vec![obj.into_lowered()],
                loc,
            }),
        }
    }
}

#[allow(dead_code)]
fn _keep_public_types_used(_cmp: Comparison, _field: FieldDbgInfo, _set_field: SetFieldDbgInfo) {}
