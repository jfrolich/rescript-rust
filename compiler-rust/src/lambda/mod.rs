//! Lambda IR - Intermediate representation for ReScript compilation.
//!
//! This module provides the Lambda IR, which sits between the typed AST
//! and the JavaScript IR in the compilation pipeline. The Lambda IR is
//! a simplified, imperative representation that makes code generation
//! and optimization easier.
//!
//! # Architecture
//!
//! The Lambda IR is organized into several submodules:
//!
//! - [`constant`] - Lambda constants (literals, blocks, etc.)
//! - [`primitive`] - Primitive operations (arithmetic, comparisons, etc.)
//! - [`compat`] - Compatibility types (comparison, let_kind, etc.)
//! - [`tag_info`] - Block tag information for variants and records
//! - [`arity`] - Arity tracking for functions
//! - [`free_variables`] - Free variable analysis
//! - [`analysis`] - Side effect and size analysis
//! - [`closure`] - Closure analysis
//! - [`subst`] - Variable substitution
//! - [`beta_reduce`] - Beta reduction (function inlining)
//! - [`print`] - Pretty printing for debugging
//! - [`compile_context`] - Compilation context for Lambda to JS IR

pub mod analysis;
pub mod arity;
pub mod beta_reduce;
pub mod closure;
pub mod compat;
pub mod compile;
pub mod compile_context;
pub mod constant;
pub mod convert;
pub mod free_variables;
pub mod primitive;
pub mod print;
pub mod sexp_lambda;
pub mod simplify;
pub mod subst;
pub mod tag_info;

use crate::ident::Ident;
use crate::location::Location;
pub use compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
pub use constant::Constant;
pub use primitive::Primitive;
pub use tag_info::TagInfo;

/// Application status for function calls
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplyStatus {
    /// No special handling
    Na,
    /// Infer full application
    InferFull,
    /// Uncurried application
    Uncurry,
}

/// Inline attribute for functions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InlineAttribute {
    /// Always inline this function
    Always,
    /// Never inline this function
    Never,
    /// Default inlining behavior
    #[default]
    Default,
}

/// Application info for function calls
#[derive(Debug, Clone)]
pub struct ApInfo {
    /// Source location
    pub loc: Location,
    /// Inline hint
    pub inlined: InlineAttribute,
    /// Application status
    pub status: ApplyStatus,
}

/// Function attributes
#[derive(Debug, Clone)]
pub struct FunctionAttribute {
    /// Inline hint
    pub inline: InlineAttribute,
    /// Is this a functor?
    pub is_a_functor: bool,
    /// Does this function return unit?
    pub return_unit: bool,
    /// Is this an async function?
    pub async_: bool,
    /// Directive (e.g., "use server")
    pub directive: Option<String>,
    /// Does this function take a single unit argument?
    pub one_unit_arg: bool,
}

impl Default for FunctionAttribute {
    fn default() -> Self {
        Self {
            inline: InlineAttribute::Default,
            is_a_functor: false,
            return_unit: false,
            async_: false,
            directive: None,
            one_unit_arg: false,
        }
    }
}

/// Switch construct for pattern matching
#[derive(Debug, Clone)]
pub struct LambdaSwitch {
    /// Are all constant cases covered?
    pub sw_consts_full: bool,
    /// Constant case branches (tag -> lambda)
    pub sw_consts: Vec<(i32, Lambda)>,
    /// Are all block cases covered?
    pub sw_blocks_full: bool,
    /// Block case branches (tag -> lambda)
    pub sw_blocks: Vec<(i32, Lambda)>,
    /// Fallback action if no case matches
    pub sw_failaction: Option<Box<Lambda>>,
    /// Names for switch cases (for untagged variants)
    pub sw_names: Option<SwitchNames>,
}

/// Runtime literal carried by an OCaml/ReScript variant tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchCaseTag {
    String(String),
    Int(i32),
    Float(String),
    BigInt(String),
    Bool(bool),
    Null,
    Undefined,
}

/// Runtime kind used for ReScript's untagged payload cases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchBlockType {
    Int,
    String,
    Float,
    BigInt,
    Boolean,
    Instance(String),
    Function,
    Object,
    Unknown,
}

/// Runtime tag metadata for one constructor case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchTag {
    /// Source constructor name.
    pub name: String,
    /// Optional `@as(...)` runtime literal.
    pub tag_type: Option<SwitchCaseTag>,
}

impl SwitchTag {
    pub fn named(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            tag_type: None,
        }
    }
}

/// Runtime metadata for one payload-carrying constructor case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchBlock {
    /// Constructor tag metadata.
    pub tag: SwitchTag,
    /// Optional custom tag field name from `@tag(...)`.
    pub tag_name: Option<String>,
    /// Optional untagged runtime payload kind.
    pub block_type: Option<SwitchBlockType>,
}

impl SwitchBlock {
    pub fn named(name: impl Into<String>) -> Self {
        Self {
            tag: SwitchTag::named(name),
            tag_name: None,
            block_type: None,
        }
    }
}

/// Switch names and runtime metadata for tagged and untagged variants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchNames {
    /// Nullary constructor names.
    pub consts: Vec<SwitchTag>,
    /// Constructor names for payload-carrying cases.
    pub blocks: Vec<SwitchBlock>,
}

/// Lambda function definition
#[derive(Debug, Clone)]
pub struct LFunction {
    /// Number of arguments (arity)
    pub arity: i32,
    /// Parameter identifiers
    pub params: Vec<Ident>,
    /// Function body
    pub body: Box<Lambda>,
    /// Function attributes
    pub attr: FunctionAttribute,
}

/// Primitive operation info
#[derive(Debug, Clone)]
pub struct PrimInfo {
    /// The primitive operation
    pub primitive: Primitive,
    /// Arguments to the primitive
    pub args: Vec<Lambda>,
    /// Source location
    pub loc: Location,
}

/// Function application
#[derive(Debug, Clone)]
pub struct Apply {
    /// Function being applied
    pub ap_func: Box<Lambda>,
    /// Arguments
    pub ap_args: Vec<Lambda>,
    /// Application info
    pub ap_info: ApInfo,
    /// Was this transformed from JSX?
    pub ap_transformed_jsx: bool,
}

/// Lambda IR expression
///
/// This is the core representation used for code generation and optimization.
#[derive(Debug, Clone)]
pub enum Lambda {
    /// Variable reference
    Lvar(Ident),

    /// Global module reference (with dynamic import flag)
    LglobalModule(Ident, bool),

    /// Constant value
    Lconst(Constant),

    /// Function application
    Lapply(Apply),

    /// Function definition
    Lfunction(LFunction),

    /// Let binding: let kind, identifier, value, body
    Llet(LetKind, Ident, Box<Lambda>, Box<Lambda>),

    /// Recursive let bindings
    Lletrec(Vec<(Ident, Lambda)>, Box<Lambda>),

    /// Primitive operation
    Lprim(PrimInfo),

    /// Switch on integer/block tag
    Lswitch(Box<Lambda>, LambdaSwitch),

    /// Switch on string value
    LstringSwitch(Box<Lambda>, Vec<(String, Lambda)>, Option<Box<Lambda>>),

    /// Raise a static exception
    LstaticRaise(i32, Vec<Lambda>),

    /// Catch a static exception: body, (exception id, params), handler
    LstaticCatch(Box<Lambda>, (i32, Vec<Ident>), Box<Lambda>),

    /// Try-with exception handling
    LtryWith(Box<Lambda>, Ident, Box<Lambda>),

    /// If-then-else
    LifThenElse(Box<Lambda>, Box<Lambda>, Box<Lambda>),

    /// Sequence of expressions
    Lsequence(Box<Lambda>, Box<Lambda>),

    /// While loop
    Lwhile(Box<Lambda>, Box<Lambda>),

    /// For loop: variable, start, end, direction, body
    Lfor(Ident, Box<Lambda>, Box<Lambda>, DirectionFlag, Box<Lambda>),

    /// Assignment to a mutable variable
    Lassign(Ident, Box<Lambda>),
}

/// Direction flag for for loops
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectionFlag {
    /// Ascending (to)
    Upto,
    /// Descending (downto)
    Downto,
}

impl Lambda {
    /// Create a variable reference
    pub fn var(id: Ident) -> Self {
        Lambda::Lvar(id)
    }

    /// Create a global module reference
    pub fn global_module(id: Ident, dynamic_import: bool) -> Self {
        Lambda::LglobalModule(id, dynamic_import)
    }

    /// Create a constant
    pub fn const_(c: Constant) -> Self {
        Lambda::Lconst(c)
    }

    /// Create a function
    pub fn function_(
        arity: i32,
        params: Vec<Ident>,
        body: Lambda,
        attr: FunctionAttribute,
    ) -> Self {
        Lambda::Lfunction(LFunction {
            arity,
            params,
            body: Box::new(body),
            attr,
        })
    }

    /// Create a let binding
    pub fn let_(kind: LetKind, id: Ident, value: Lambda, body: Lambda) -> Self {
        Lambda::Llet(kind, id, Box::new(value), Box::new(body))
    }

    /// Create recursive let bindings
    pub fn letrec(bindings: Vec<(Ident, Lambda)>, body: Lambda) -> Self {
        Lambda::Lletrec(bindings, Box::new(body))
    }

    /// Create a primitive operation
    pub fn prim(primitive: Primitive, args: Vec<Lambda>, loc: Location) -> Self {
        Lambda::Lprim(PrimInfo {
            primitive,
            args,
            loc,
        })
    }

    /// Create a sequence
    pub fn seq(first: Lambda, second: Lambda) -> Self {
        match first {
            Lambda::Lprim(PrimInfo {
                primitive: primitive @ Primitive::Pmakeblock(_, _, _),
                args,
                loc,
            }) => {
                let mut args = args.into_iter();
                let Some(first_arg) = args.next() else {
                    return Lambda::Lsequence(
                        Box::new(Lambda::Lprim(PrimInfo {
                            primitive,
                            args: Vec::new(),
                            loc,
                        })),
                        Box::new(second),
                    );
                };
                Lambda::seq(args.fold(first_arg, Lambda::seq), second)
            }
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                mut args,
                ..
            }) if args.len() == 1 => Lambda::seq(args.remove(0), second),
            first => Lambda::Lsequence(Box::new(first), Box::new(second)),
        }
    }

    /// Create an if-then-else
    pub fn if_(cond: Lambda, then_: Lambda, else_: Lambda) -> Self {
        match cond {
            Lambda::Lconst(constant) => {
                if constant.eval_as_bool() {
                    then_
                } else {
                    else_
                }
            }
            cond => {
                if is_assertfalse(&else_) {
                    return Lambda::seq(cond, then_);
                }
                if is_assertfalse(&then_) {
                    return Lambda::seq(cond, else_);
                }

                if matches!(
                    (&then_, &else_),
                    (
                        Lambda::Lconst(Constant::JsTrue),
                        Lambda::Lconst(Constant::JsFalse)
                    )
                ) {
                    return if has_boolean_type(&cond).is_some() {
                        cond
                    } else {
                        make_if(cond, then_, else_)
                    };
                }

                if matches!(
                    (&then_, &else_),
                    (
                        Lambda::Lconst(Constant::JsFalse),
                        Lambda::Lconst(Constant::JsTrue)
                    )
                ) {
                    return match has_boolean_type(&cond) {
                        Some(loc) => lambda_not(loc, cond),
                        None => make_if(cond, then_, else_),
                    };
                }

                if matches!(
                    &then_,
                    Lambda::Lprim(PrimInfo {
                        primitive: Primitive::Praise,
                        ..
                    })
                ) {
                    return if matches!(&else_, Lambda::Lconst(_)) {
                        make_if(cond, then_, else_)
                    } else {
                        Lambda::seq(make_if(cond, then_, Lambda::unit()), else_)
                    };
                }

                match cond {
                    Lambda::Lprim(prim_info) => match prim_info {
                        PrimInfo {
                            primitive: Primitive::Pisout(offset),
                            args,
                            loc,
                        } => {
                            if let [
                                Lambda::Lconst(Constant::Int { i: range, .. }),
                                Lambda::Lvar(xx),
                            ] = args.as_slice()
                            {
                                if let Lambda::Lswitch(switch_arg, body) = &else_ {
                                    if let Lambda::Lvar(yy) = switch_arg.as_ref() {
                                        if body.sw_blocks.is_empty()
                                            && body.sw_blocks_full
                                            && body.sw_failaction.is_none()
                                            && xx.same(yy)
                                            && complete_range(
                                                &body.sw_consts,
                                                -offset,
                                                *range - offset,
                                            )
                                        {
                                            let mut body = body.clone();
                                            body.sw_failaction = Some(Box::new(then_));
                                            body.sw_consts_full = false;
                                            return Lambda::Lswitch(switch_arg.clone(), body);
                                        }
                                    }
                                }
                            }
                            make_if(
                                Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pisout(offset),
                                    args,
                                    loc,
                                }),
                                then_,
                                else_,
                            )
                        }
                        PrimInfo {
                            primitive: Primitive::Pisint,
                            args,
                            loc,
                        } => {
                            let [Lambda::Lvar(i)] = args.as_slice() else {
                                return make_if(
                                    Lambda::Lprim(PrimInfo {
                                        primitive: Primitive::Pisint,
                                        args,
                                        loc,
                                    }),
                                    then_,
                                    else_,
                                );
                            };

                            if let Lambda::LifThenElse(pred, _, branch_false) = &then_ {
                                if let Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pintcomp(Comparison::Eq),
                                    args: pred_args,
                                    ..
                                }) = pred.as_ref()
                                {
                                    if let [Lambda::Lvar(j), Lambda::Lconst(_)] =
                                        pred_args.as_slice()
                                    {
                                        if i.same(j) && lambda_eq_approx(branch_false, &else_) {
                                            return then_;
                                        }
                                    }
                                }
                            }

                            if let Lambda::Lprim(PrimInfo {
                                primitive: Primitive::Pintcomp(Comparison::Eq),
                                args: pred_args,
                                ..
                            }) = &then_
                            {
                                if let [Lambda::Lvar(j), Lambda::Lconst(_)] = pred_args.as_slice() {
                                    if i.same(j) && lambda_eq_approx(&Lambda::false_(), &else_) {
                                        return then_;
                                    }
                                }
                            }

                            if let Lambda::LifThenElse(pred, branch_true, branch_false) = &then_ {
                                if let Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pintcomp(Comparison::Neq),
                                    args: pred_args,
                                    loc,
                                }) = pred.as_ref()
                                {
                                    if let [Lambda::Lvar(j), Lambda::Lconst(_)] =
                                        pred_args.as_slice()
                                    {
                                        if i.same(j) && lambda_eq_approx(branch_true, &else_) {
                                            return Lambda::LifThenElse(
                                                Box::new(Lambda::Lprim(PrimInfo {
                                                    primitive: Primitive::Pintcomp(Comparison::Eq),
                                                    args: pred_args.clone(),
                                                    loc: loc.clone(),
                                                })),
                                                branch_false.clone(),
                                                branch_true.clone(),
                                            );
                                        }
                                    }
                                }
                            }

                            match &then_ {
                                Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pintcomp(Comparison::Neq),
                                    args: pred_args,
                                    loc,
                                }) => {
                                    if let [Lambda::Lvar(j), Lambda::Lconst(_)] =
                                        pred_args.as_slice()
                                    {
                                        if i.same(j) && lambda_eq_approx(&Lambda::true_(), &else_) {
                                            return Lambda::Lprim(PrimInfo {
                                                primitive: Primitive::Pintcomp(Comparison::Neq),
                                                args: pred_args.clone(),
                                                loc: loc.clone(),
                                            });
                                        }
                                    }
                                }
                                Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pnot,
                                    args: outer_args,
                                    ..
                                }) => {
                                    if let [
                                        Lambda::Lprim(PrimInfo {
                                            primitive: Primitive::Pintcomp(Comparison::Eq),
                                            args: pred_args,
                                            loc,
                                        }),
                                    ] = outer_args.as_slice()
                                    {
                                        if let [Lambda::Lvar(j), Lambda::Lconst(_)] =
                                            pred_args.as_slice()
                                        {
                                            if i.same(j)
                                                && lambda_eq_approx(&Lambda::true_(), &else_)
                                            {
                                                return Lambda::Lprim(PrimInfo {
                                                    primitive: Primitive::Pintcomp(Comparison::Neq),
                                                    args: pred_args.clone(),
                                                    loc: loc.clone(),
                                                });
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }

                            make_if(
                                Lambda::Lprim(PrimInfo {
                                    primitive: Primitive::Pisint,
                                    args,
                                    loc,
                                }),
                                then_,
                                else_,
                            )
                        }
                        prim_info => make_if(Lambda::Lprim(prim_info), then_, else_),
                    },
                    cond => make_if(cond, then_, else_),
                }
            }
        }
    }

    /// Create a while loop
    pub fn while_(cond: Lambda, body: Lambda) -> Self {
        Lambda::Lwhile(Box::new(cond), Box::new(body))
    }

    /// Create a for loop
    pub fn for_(var: Ident, start: Lambda, end: Lambda, dir: DirectionFlag, body: Lambda) -> Self {
        Lambda::Lfor(var, Box::new(start), Box::new(end), dir, Box::new(body))
    }

    /// Create a try-with block
    pub fn try_(body: Lambda, exn: Ident, handler: Lambda) -> Self {
        Lambda::LtryWith(Box::new(body), exn, Box::new(handler))
    }

    /// Create an assignment
    pub fn assign(var: Ident, value: Lambda) -> Self {
        Lambda::Lassign(var, Box::new(value))
    }

    /// Create a static raise
    pub fn static_raise(id: i32, args: Vec<Lambda>) -> Self {
        Lambda::LstaticRaise(id, args)
    }

    /// Create a static catch
    pub fn static_catch(
        body: Lambda,
        handler_id: i32,
        params: Vec<Ident>,
        handler: Lambda,
    ) -> Self {
        Lambda::LstaticCatch(Box::new(body), (handler_id, params), Box::new(handler))
    }

    /// JS true constant
    pub fn true_() -> Self {
        Lambda::Lconst(Constant::JsTrue)
    }

    /// JS false constant
    pub fn false_() -> Self {
        Lambda::Lconst(Constant::JsFalse)
    }

    /// Unit constant
    pub fn unit() -> Self {
        Lambda::Lconst(Constant::JsUndefined { is_unit: true })
    }

    /// Check if this is the unit value (undefined with is_unit=true)
    pub fn is_unit(&self) -> bool {
        matches!(
            self,
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        )
    }
}

fn make_if(cond: Lambda, then_: Lambda, else_: Lambda) -> Lambda {
    Lambda::LifThenElse(Box::new(cond), Box::new(then_), Box::new(else_))
}

fn is_assertfalse(lam: &Lambda) -> bool {
    matches!(
        lam,
        Lambda::Lconst(Constant::Int {
            comment: Some(constant::PointerInfo::AssertFalse),
            ..
        })
    )
}

fn lambda_not(loc: Location, lam: Lambda) -> Lambda {
    match lam {
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Neq),
            args,
            loc,
        }) => Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Eq),
            args,
            loc,
        }),
        lam => Lambda::prim(Primitive::Pnot, vec![lam], loc),
    }
}

fn has_boolean_type(lam: &Lambda) -> Option<Location> {
    match lam {
        Lambda::Lprim(PrimInfo {
            primitive:
                Primitive::Pnot
                | Primitive::Psequand
                | Primitive::Psequor
                | Primitive::Pisout(_)
                | Primitive::PisNotNone
                | Primitive::Pobjcomp(_)
                | Primitive::Pboolcomp(_)
                | Primitive::Pintcomp(_)
                | Primitive::Pfloatcomp(_)
                | Primitive::Pbigintcomp(_)
                | Primitive::Pstringcomp(_),
            loc,
            ..
        }) => Some(loc.clone()),
        _ => None,
    }
}

fn complete_range(sw_consts: &[(i32, Lambda)], start: i32, finish: i32) -> bool {
    match sw_consts.split_first() {
        None => finish < start,
        Some(((i, _), rest)) => {
            start <= finish && *i == start && complete_range(rest, start + 1, finish)
        }
    }
}

fn lambda_eq_approx(lhs: &Lambda, rhs: &Lambda) -> bool {
    match (lhs, rhs) {
        (Lambda::LglobalModule(i1, b1), Lambda::LglobalModule(i2, b2)) => i1.same(i2) && b1 == b2,
        (Lambda::Lvar(i1), Lambda::Lvar(i2)) => i1.same(i2),
        (Lambda::Lconst(c1), Lambda::Lconst(c2)) => c1.eq_approx(c2),
        (Lambda::Lapply(app1), Lambda::Lapply(app2)) => {
            lambda_eq_approx(&app1.ap_func, &app2.ap_func)
                && lambda_list_eq_approx(&app1.ap_args, &app2.ap_args)
        }
        (Lambda::LifThenElse(a1, b1, c1), Lambda::LifThenElse(a2, b2, c2)) => {
            lambda_eq_approx(a1, a2) && lambda_eq_approx(b1, b2) && lambda_eq_approx(c1, c2)
        }
        (Lambda::Lsequence(a1, b1), Lambda::Lsequence(a2, b2))
        | (Lambda::Lwhile(a1, b1), Lambda::Lwhile(a2, b2)) => {
            lambda_eq_approx(a1, a2) && lambda_eq_approx(b1, b2)
        }
        (Lambda::Lassign(v1, l1), Lambda::Lassign(v2, l2)) => {
            v1.same(v2) && lambda_eq_approx(l1, l2)
        }
        (Lambda::LstaticRaise(id1, args1), Lambda::LstaticRaise(id2, args2)) => {
            id1 == id2 && lambda_list_eq_approx(args1, args2)
        }
        (Lambda::Lprim(info1), Lambda::Lprim(info2)) => {
            info1.primitive.eq_approx(&info2.primitive)
                && lambda_list_eq_approx(&info1.args, &info2.args)
        }
        (
            Lambda::LstringSwitch(arg1, cases1, default1),
            Lambda::LstringSwitch(arg2, cases2, default2),
        ) => {
            lambda_eq_approx(arg1, arg2)
                && lambda_option_eq_approx(default1, default2)
                && cases1.len() == cases2.len()
                && cases1
                    .iter()
                    .zip(cases2.iter())
                    .all(|((name1, lam1), (name2, lam2))| {
                        name1 == name2 && lambda_eq_approx(lam1, lam2)
                    })
        }
        _ => false,
    }
}

fn lambda_list_eq_approx(lhs: &[Lambda], rhs: &[Lambda]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs.iter())
            .all(|(lhs, rhs)| lambda_eq_approx(lhs, rhs))
}

fn lambda_option_eq_approx(lhs: &Option<Box<Lambda>>, rhs: &Option<Box<Lambda>>) -> bool {
    match (lhs, rhs) {
        (None, None) => true,
        (Some(lhs), Some(rhs)) => lambda_eq_approx(lhs, rhs),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lambda_creation() {
        let id = Ident::create_local("x");
        let var = Lambda::var(id.clone());

        match var {
            Lambda::Lvar(ref i) => assert_eq!(i.name(), "x"),
            _ => panic!("Expected Lvar"),
        }
    }

    #[test]
    fn test_let_binding() {
        let x = Ident::create_local("x");
        let _y = Ident::create_local("y");

        let binding = Lambda::let_(
            LetKind::Strict,
            x.clone(),
            Lambda::const_(Constant::Int {
                i: 42,
                comment: None,
            }),
            Lambda::var(x.clone()),
        );

        match binding {
            Lambda::Llet(LetKind::Strict, ref id, _, _) => {
                assert_eq!(id.name(), "x");
            }
            _ => panic!("Expected Llet"),
        }
    }

    #[test]
    fn test_function() {
        let x = Ident::create_local("x");
        let func = Lambda::function_(
            1,
            vec![x.clone()],
            Lambda::var(x.clone()),
            FunctionAttribute::default(),
        );

        match func {
            Lambda::Lfunction(ref f) => {
                assert_eq!(f.arity, 1);
                assert_eq!(f.params.len(), 1);
            }
            _ => panic!("Expected Lfunction"),
        }
    }

    #[test]
    fn test_if_then_else() {
        let cond = Lambda::var(Ident::create_local("cond"));
        let then_ = Lambda::const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let else_ = Lambda::const_(Constant::Int {
            i: 0,
            comment: None,
        });

        let if_expr = Lambda::if_(cond, then_, else_);

        match if_expr {
            Lambda::LifThenElse(_, _, _) => {}
            _ => panic!("Expected LifThenElse"),
        }
    }

    #[test]
    fn test_if_then_else_constant_fold() {
        let then_ = Lambda::const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let else_ = Lambda::const_(Constant::Int {
            i: 0,
            comment: None,
        });

        let if_expr = Lambda::if_(Lambda::true_(), then_.clone(), else_);
        match if_expr {
            Lambda::Lconst(Constant::Int {
                i: 1,
                comment: None,
            }) => {}
            _ => panic!("Expected folded then-branch"),
        }

        let if_expr = Lambda::if_(Lambda::false_(), then_, Lambda::unit());
        assert!(matches!(
            if_expr,
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        ));
    }

    #[test]
    fn test_if_then_else_assertfalse_sequences_then_branch() {
        let cond_id = Ident::create_local("cond");
        let cond = Lambda::var(cond_id.clone());
        let then_ = Lambda::const_(Constant::int(1));
        let assertfalse = Lambda::const_(Constant::Int {
            i: 0,
            comment: Some(constant::PointerInfo::AssertFalse),
        });

        let if_expr = Lambda::if_(cond.clone(), then_.clone(), assertfalse);

        match if_expr {
            Lambda::Lsequence(first, second) => {
                assert!(matches!(*first, Lambda::Lvar(ref id) if id.same(&cond_id)));
                assert!(lambda_eq_approx(&second, &then_));
            }
            _ => panic!("Expected assertfalse branch to lower to sequence"),
        }
    }

    #[test]
    fn test_if_then_else_true_false_returns_boolean_condition() {
        let x = Ident::create_local("x");
        let cond = Lambda::prim(
            Primitive::Pintcomp(Comparison::Eq),
            vec![Lambda::var(x.clone()), Lambda::const_(Constant::int(0))],
            Location::none(),
        );

        let if_expr = Lambda::if_(cond.clone(), Lambda::true_(), Lambda::false_());
        assert!(lambda_eq_approx(&if_expr, &cond));
    }

    #[test]
    fn test_if_then_else_false_true_negates_boolean_condition() {
        let x = Ident::create_local("x");
        let if_expr = Lambda::if_(
            Lambda::prim(
                Primitive::Pintcomp(Comparison::Neq),
                vec![Lambda::var(x.clone()), Lambda::const_(Constant::int(0))],
                Location::none(),
            ),
            Lambda::false_(),
            Lambda::true_(),
        );

        match if_expr {
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Eq),
                ..
            }) => {}
            _ => panic!("Expected negated integer comparison"),
        }
    }

    #[test]
    fn test_if_then_else_raise_then_sequences_non_constant_else() {
        let x = Ident::create_local("x");
        let if_expr = Lambda::if_(
            Lambda::prim(
                Primitive::Pintcomp(Comparison::Eq),
                vec![Lambda::var(x.clone()), Lambda::const_(Constant::int(0))],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::var(Ident::create_local("exn"))],
                Location::none(),
            ),
            Lambda::static_raise(1, Vec::new()),
        );

        match if_expr {
            Lambda::Lsequence(first, second) => {
                assert!(matches!(*second, Lambda::LstaticRaise(1, ref args) if args.is_empty()));
                match *first {
                    Lambda::LifThenElse(_, then_, else_) => {
                        assert!(matches!(
                            *then_,
                            Lambda::Lprim(PrimInfo {
                                primitive: Primitive::Praise,
                                ..
                            })
                        ));
                        assert!(matches!(
                            *else_,
                            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
                        ));
                    }
                    _ => panic!("Expected rewritten if inside sequence"),
                }
            }
            _ => panic!("Expected raise-then if to lower to sequence"),
        }
    }

    #[test]
    fn test_if_then_else_pisint_reuses_eq_branch() {
        let value = Ident::create_local("value");
        let inner_if = Lambda::LifThenElse(
            Box::new(Lambda::prim(
                Primitive::Pintcomp(Comparison::Eq),
                vec![Lambda::var(value.clone()), Lambda::const_(Constant::int(0))],
                Location::none(),
            )),
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::false_()),
        );

        let if_expr = Lambda::if_(
            Lambda::prim(
                Primitive::Pisint,
                vec![Lambda::var(value)],
                Location::none(),
            ),
            inner_if.clone(),
            Lambda::false_(),
        );

        assert!(lambda_eq_approx(&if_expr, &inner_if));
    }

    #[test]
    fn test_while_loop() {
        let cond = Lambda::true_();
        let body = Lambda::unit();

        let while_loop = Lambda::while_(cond, body);

        match while_loop {
            Lambda::Lwhile(_, _) => {}
            _ => panic!("Expected Lwhile"),
        }
    }
}
