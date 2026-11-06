//! `Lam_analysis` over the Lambda arena: side effects, size, and inlining
//! profitability.

use crate::binary_ast::ppx::{
    JsExpClassification, JsStmtClassification, classify_js_exp, classify_js_stmt,
};
use crate::ident::Ident;
use crate::lambda::arena::{FuncId, Lam, LamArena, Node, View};
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{InlineAttribute, TagInfo};

/// Check if a primitive operation is pure (no side effects).
pub(crate) fn is_pure_primitive(prim: &Primitive, second_constant: Option<&Constant>) -> bool {
    match prim {
        Primitive::Pidentity | Primitive::Pignore => true,
        // Division can raise division by zero.
        Primitive::Pmodint | Primitive::Pdivint | Primitive::Pdivbigint | Primitive::Pmodbigint => {
            second_constant.is_some_and(not_zero_constant)
        }
        // lam_analysis.ml: raises on a negative exponent, so pure only when
        // the exponent is a nonnegative constant.
        Primitive::Ppowbigint => {
            matches!(second_constant, Some(Constant::BigInt { negative: false, .. }))
        }

        // Creation and type checking primitives
        Primitive::PcreateExtension(_)
        | Primitive::PextensionSlotEq
        | Primitive::Ptypeof
        | Primitive::PisNull
        | Primitive::PisNotNone
        | Primitive::Psome
        | Primitive::PsomeNotNest
        | Primitive::PisUndefined
        | Primitive::PisNullUndefined
        | Primitive::PnullToOpt
        | Primitive::PnullUndefinedToOpt
        | Primitive::PjsObjectCreate(_)
        | Primitive::Pimport(_) => true,

        // Block operations
        Primitive::Pmakeblock(_, _)
        | Primitive::Pfield(_, _)
        | Primitive::PvalFromOption
        | Primitive::PvalFromOptionNotNest
        | Primitive::Pduprecord
        | Primitive::PrecordRest(_) => true,

        // Object primitives
        Primitive::Pobjcomp(_)
        | Primitive::Pobjorder
        | Primitive::Pobjmin
        | Primitive::Pobjmax
        | Primitive::Pobjtag
        | Primitive::Pobjsize => true,

        // Boolean primitives
        Primitive::Psequand
        | Primitive::Psequor
        | Primitive::Pnot
        | Primitive::Pboolcomp(_)
        | Primitive::Pboolorder
        | Primitive::Pboolmin
        | Primitive::Pboolmax => true,

        // Integer primitives
        Primitive::Pnegint
        | Primitive::Paddint
        | Primitive::Psubint
        | Primitive::Pmulint
        | Primitive::Ppowint
        | Primitive::Pnotint
        | Primitive::Pandint
        | Primitive::Porint
        | Primitive::Pxorint
        | Primitive::Plslint
        | Primitive::Plsrint
        | Primitive::Pasrint
        | Primitive::Pintcomp(_)
        | Primitive::Pintorder
        | Primitive::Pintmin
        | Primitive::Pintmax => true,

        // Float primitives
        Primitive::Pintoffloat
        | Primitive::Pfloatofint
        | Primitive::Pnegfloat
        | Primitive::Paddfloat
        | Primitive::Psubfloat
        | Primitive::Pmulfloat
        | Primitive::Ppowfloat
        | Primitive::Pdivfloat
        | Primitive::Pmodfloat
        | Primitive::Pfloatcomp(_)
        | Primitive::Pjscomp(_)
        | Primitive::Pfloatorder
        | Primitive::Pfloatmin
        | Primitive::Pfloatmax => true,

        // BigInt primitives
        Primitive::Pnegbigint
        | Primitive::Paddbigint
        | Primitive::Psubbigint
        | Primitive::Pmulbigint
        | Primitive::Pnotbigint
        | Primitive::Pandbigint
        | Primitive::Porbigint
        | Primitive::Pxorbigint
        | Primitive::Plslbigint
        | Primitive::Pasrbigint
        | Primitive::Pbigintcomp(_)
        | Primitive::Pbigintorder
        | Primitive::Pbigintmin
        | Primitive::Pbigintmax => true,

        // String primitives
        Primitive::Pstringlength
        | Primitive::Pstringcomp(_)
        | Primitive::Pstringorder
        | Primitive::Pstringmin
        | Primitive::Pstringmax => true,

        // Array primitives (read-only)
        Primitive::Pmakearray
        | Primitive::Parraylength
        | Primitive::Parrayrefu => true,

        // List and dict primitives
        Primitive::Pmakelist | Primitive::Pmakedict | Primitive::PdictHas => true,

        // Type testing primitives
        Primitive::Pisint | Primitive::PisPolyVarBlock => true,

        // Offset and misc
        Primitive::Pstringadd
        | Primitive::Ptemplate(_)
        | Primitive::PfnArity
        | Primitive::Phash
        | Primitive::PhashMixstring
        | Primitive::PhashMixint
        | Primitive::PhashFinalmix => true,

        // Raw JS code - check if it's a pure expression
        Primitive::PrawJsCode(info) => raw_js_is_pure(info),

        // Impure primitives
        Primitive::PtaggedTemplate(_)
        | Primitive::PjsApply
        | Primitive::PjsCall(_)
        | Primitive::PinitMod
        | Primitive::PupdateMod
        | Primitive::PjsObjectGet(_)
        | Primitive::PjsObjectSet(_)
        | Primitive::Pdebugger
        | Primitive::PjsFnMethod
        | Primitive::Pawait
        | Primitive::Parraysets
        | Primitive::Parraysetu
        | Primitive::Praise
        | Primitive::Psetfield(_, _)
        // Bounds-checked reads throw when the index is out of range.
        | Primitive::Parrayrefs
        | Primitive::Pstringrefs
        | Primitive::Pstringrefu => false,
    }
}

/// Small inline size threshold.
pub const SMALL_INLINE_SIZE: i32 = 5;

/// Exit inline size threshold (for static raise handlers).
pub const EXIT_INLINE_SIZE: i32 = 7;

/// Compute the size of a constant.
pub(crate) fn size_constant(c: &Constant) -> i32 {
    match c {
        Constant::Int { .. }
        | Constant::Constructor(_)
        | Constant::NativeInt { .. }
        | Constant::Char(_)
        | Constant::Float(_)
        | Constant::BigInt { .. }
        | Constant::Pointer(_)
        | Constant::JsNull
        | Constant::JsUndefined { .. }
        | Constant::ModuleAlias
        | Constant::JsTrue
        | Constant::JsFalse => 1,

        Constant::String(_) => 1,
        Constant::ImmString(_) => 1,

        Constant::Some(inner) => size_constant(inner),

        Constant::Block {
            tag_info, elements, ..
        } => {
            let missing_fields = match &**tag_info {
                TagInfo::Record(_) | TagInfo::RecordInlined(_) => tag_info
                    .logical_field_count()
                    .saturating_sub(elements.len()),
                _ => 0,
            };
            missing_fields as i32 + elements.iter().map(size_constant).sum::<i32>()
        }
    }
}

/// `Lam_analysis.lfunction_can_be_inlined` on a function's attributes.
/// Check if a constant is definitely not zero.
/// Used in side effect analysis to determine safe division.
fn not_zero_constant(c: &Constant) -> bool {
    match c {
        Constant::Int { i, .. } => *i != 0,
        Constant::NativeInt { i, .. } => *i != 0,
        Constant::BigInt { value, .. } => value != "0",
        _ => false,
    }
}

fn raw_js_is_pure(info: &crate::lambda::lam_primitive::JsRawInfo) -> bool {
    if info.is_stmt {
        matches!(
            classify_js_stmt(&info.code),
            JsStmtClassification::JsStmtComment
        )
    } else {
        matches!(
            classify_js_exp(&info.code),
            JsExpClassification::JsFunction { .. } | JsExpClassification::JsLiteral { .. }
        )
    }
}

/// `Lam_analysis.lfunction_can_be_inlined` on a function's attributes.
pub fn attr_can_be_inlined(attr: &crate::lambda::FunctionAttribute) -> bool {
    !attr.async_ && attr.directive.is_none()
}

/// `Lam_analysis.no_side_effects`.
pub fn no_side_effects(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Var(_) | Node::Const(_) | Node::Function { .. } | Node::GlobalModule(_) => true,
        Node::Prim { args, info } => {
            let args = a.list(args);
            if !args.iter().all(|x| no_side_effects(a, *x)) {
                return false;
            }
            is_pure_primitive(
                &a.prim_payload(info).primitive,
                args.get(1).and_then(|x| a.as_const(*x)),
            )
        }
        Node::Let { value, body, .. } => no_side_effects(a, value) && no_side_effects(a, body),
        Node::Switch { .. }
        | Node::StringSwitch { .. }
        | Node::StaticRaise { .. }
        | Node::StaticCatch { .. } => false,
        Node::TryWith { body, handler, .. } => {
            no_side_effects(a, body) && no_side_effects(a, handler)
        }
        Node::If { cond, then_, else_ } => {
            no_side_effects(a, cond) && no_side_effects(a, then_) && no_side_effects(a, else_)
        }
        Node::Sequence(x, y) => no_side_effects(a, x) && no_side_effects(a, y),
        Node::LetRec { values, body, .. } => {
            a.list(values).iter().all(|x| no_side_effects(a, *x)) && no_side_effects(a, body)
        }
        Node::While(..)
        | Node::For { .. }
        | Node::ForOf { .. }
        | Node::ForAwaitOf { .. }
        | Node::Break
        | Node::Continue
        | Node::Assign { .. } => false,
        Node::Apply { func, args, .. } => {
            // `Lazy.from_fun` application.
            if let Some((Primitive::Pfield(_, FieldDbgInfo::Module { name }), _, _)) =
                a.as_prim(func)
                && name == "from_fun"
                && let [arg] = a.list(args)
            {
                return no_side_effects(a, *arg);
            }
            false
        }
    }
}

const TOO_BIG_TO_INLINE: i32 = 1000;

/// `Lam_analysis.size`.
pub fn size(a: &LamArena, lam: Lam) -> i32 {
    size_inner(a, lam).unwrap_or(TOO_BIG_TO_INLINE)
}

fn size_inner(a: &LamArena, lam: Lam) -> Option<i32> {
    match a.node(lam) {
        Node::Var(_) | Node::GlobalModule(_) => Some(1),
        Node::Const(c) => Some(size_constant(a.constant(c))),
        Node::Let { value, body, .. } => Some(1 + size_inner(a, value)? + size_inner(a, body)?),
        Node::LetRec { .. } => None,
        Node::Prim { args, info } => {
            let args = a.list(args);
            match &a.prim_payload(info).primitive {
                Primitive::Pfield(_, FieldDbgInfo::Module { .. }) => {
                    if let [x] = args
                        && matches!(a.node(*x), Node::GlobalModule(_) | Node::Var(_))
                    {
                        return Some(1);
                    }
                }
                Primitive::Praise | Primitive::PisNotNone => {
                    if let [x] = args {
                        return size_inner(a, *x);
                    }
                }
                Primitive::Pmakeblock(
                    tag_info @ (TagInfo::Record(_) | TagInfo::RecordInlined(_)),
                    _,
                ) => {
                    let missing = tag_info.logical_field_count().saturating_sub(args.len());
                    return size_lams(a, 1 + missing as i32, args);
                }
                Primitive::PjsObjectCreate(obj_params) => {
                    let logical = obj_params
                        .iter()
                        .filter(|p| {
                            !matches!(
                                p.obj_arg_type,
                                crate::types::external_ffi_types::Attr::ArgCst(_)
                            )
                        })
                        .count();
                    let missing = logical.saturating_sub(args.len());
                    return size_lams(a, 1 + missing as i32, args);
                }
                Primitive::PrawJsCode(_) => return None,
                _ => {}
            }
            size_lams(a, 1, args)
        }
        Node::Apply { func, args, .. } => {
            let f = size_inner(a, func)?;
            size_lams(a, f, a.list(args))
        }
        Node::Function { body, .. } => size_inner(a, body),
        Node::Switch { .. }
        | Node::StringSwitch { .. }
        | Node::StaticCatch { .. }
        | Node::TryWith { .. }
        | Node::While(..)
        | Node::For { .. }
        | Node::ForOf { .. }
        | Node::ForAwaitOf { .. } => None,
        Node::Break | Node::Continue => Some(1),
        Node::StaticRaise { args, .. } => size_lams(a, 1, a.list(args)),
        Node::If { cond, then_, else_ } => {
            Some(1 + size_inner(a, cond)? + size_inner(a, then_)? + size_inner(a, else_)?)
        }
        Node::Sequence(x, y) => Some(size_inner(a, x)? + size_inner(a, y)?),
        Node::Assign { value, .. } => Some(1 + size_inner(a, value)?),
    }
}

fn size_lams(a: &LamArena, acc: i32, lams: &[Lam]) -> Option<i32> {
    let mut total = acc;
    for x in lams {
        total += size_inner(a, *x)?;
    }
    Some(total)
}

pub fn args_all_const(a: &LamArena, args: &[Lam]) -> bool {
    args.iter().all(|x| a.is_const(*x))
}

/// `Lam_analysis.lfunction_can_be_inlined`.
pub fn lfunction_can_be_inlined(a: &LamArena, func: FuncId) -> bool {
    attr_can_be_inlined(&a.func_payload(func).attr)
}

/// `Lam_analysis.ok_to_inline_fun_when_app`.
pub fn ok_to_inline_fun_when_app(a: &LamArena, func: FuncId, body: Lam, args: &[Lam]) -> bool {
    match a.func_payload(func).attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let s = size(a, body);
            s < SMALL_INLINE_SIZE
                || destruct_pattern(a, body, a.params(func), args)
                || (args_all_const(a, args) && s < 10 && no_side_effects(a, body))
        }
    }
}

/// `Lam_analysis.destruct_pattern`: a switch or conditional on a parameter
/// whose argument is a constant, measured after folding.
pub(crate) fn destruct_pattern(a: &LamArena, body: Lam, params: &[Ident], args: &[Lam]) -> bool {
    let find_arg = |v: &Ident| {
        params
            .iter()
            .position(|p| p == v)
            .and_then(|i| args.get(i).copied())
    };
    match a.node(body) {
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            if let Some(v) = a.as_var(scrut)
                && let Some(arg) = find_arg(&v)
                && a.is_const(arg)
            {
                // `Lam.switch` on the constant picks an action; a switch
                // that stays is too big to inline.
                return match a.decide_switch(arg, actions, info) {
                    Some(action) => size(a, action) < SMALL_INLINE_SIZE,
                    None => false,
                };
            }
            false
        }
        Node::If { cond, then_, else_ } => {
            if let Some(v) = a.as_var(cond)
                && let Some(arg) = find_arg(&v)
                && let Some(c) = a.as_const(arg)
            {
                let branch = if c.eval_as_bool() { then_ } else { else_ };
                return size(a, branch) < SMALL_INLINE_SIZE;
            }
            false
        }
        _ => false,
    }
}

/// `Lam_analysis.safe_to_inline`.
pub fn safe_to_inline(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Function { .. } => true,
        Node::Const(c) => {
            let c = a.constant(c);
            matches!(
                c,
                Constant::Pointer(_)
                    | Constant::JsTrue
                    | Constant::JsFalse
                    | Constant::JsUndefined { .. }
            ) || matches!(
                c,
                Constant::Int { comment: Some(info), .. }
                    if matches!(**info, crate::lambda::lam_constant::PointerInfo::Constructor(_))
            )
        }
        _ => false,
    }
}

/// `Lam_exit_code.has_exit_code` (lam_exit_code.ml:25-33): a static raise
/// to a label satisfying `exits`, not under a function.
pub fn has_exit_code(a: &LamArena, lam: Lam, exits: &impl Fn(i32) -> bool) -> bool {
    match a.node(lam) {
        Node::Function { .. } => false,
        Node::StaticRaise { label, .. } if exits(label) => true,
        _ => {
            let mut found = false;
            a.iter_children(lam, |x| found = found || has_exit_code(a, x, exits));
            found
        }
    }
}

/// `Lambda_traverse.free_ids` (lambda_traverse.ml:200-224): the variables
/// `lam` uses and does not bind. Binders are removed from the one shared
/// set after their children are visited.
pub fn free_variables(a: &LamArena, lam: Lam) -> ahash::AHashSet<Ident> {
    fn go(a: &LamArena, lam: Lam, fv: &mut ahash::AHashSet<Ident>) {
        a.iter_children(lam, |x| go(a, x, fv));
        match a.view(lam) {
            View::Var(id) | View::Assign(id, _) => {
                fv.insert(id);
            }
            View::StaticCatch(_, _, vars, _) => {
                for id in vars {
                    fv.remove(id);
                }
            }
            View::Function { params, .. } => {
                for id in params {
                    fv.remove(id);
                }
            }
            View::LetRec(ids, _, _) => {
                for id in ids {
                    fv.remove(id);
                }
            }
            View::Let(_, id, _, _)
            | View::TryWith(_, id, _)
            | View::For(id, ..)
            | View::ForOf(id, ..)
            | View::ForAwaitOf(id, ..) => {
                fv.remove(&id);
            }
            _ => {}
        }
    }
    let mut fv = ahash::AHashSet::new();
    go(a, lam, &mut fv);
    fv
}
