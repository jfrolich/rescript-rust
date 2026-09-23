//! Lambda IR analysis - Side effect and size analysis.
//!
//! This module provides analysis functions for Lambda expressions:
//! - Side effect analysis: determines if an expression has side effects
//! - Size analysis: estimates the size of an expression for inlining decisions
//! - Inlining hints: determines if a function is safe/profitable to inline

use crate::binary_ast::ppx::{
    JsExpClassification, JsStmtClassification, classify_js_exp, classify_js_stmt,
};
use crate::ident::Ident;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{LFunction, Lambda, TagInfo};

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

/// Check if a Lambda expression has no side effects.
///
/// This is a conservative analysis - it returns `true` only if we can
/// prove the expression is side-effect free. Unknown cases return `false`.
///
/// Side effects include:
/// - Mutable state modifications (assignments, setfield)
/// - Exceptions (raise, division by zero)
/// - I/O operations (debugger, raw JS, etc.)
/// - Non-termination (while loops)
pub fn no_side_effects(lam: &Lambda) -> bool {
    match lam {
        // Variables, constants, and functions are pure
        Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::Lfunction(_) => true,

        // Global module references are pure (side effects tracked at module level)
        Lambda::LglobalModule(_, _) => true,

        // Primitive operations - check if the primitive is pure
        Lambda::Lprim(prim_info) => {
            // First check all arguments are pure
            if !prim_info.args.iter().all(no_side_effects) {
                return false;
            }

            // Then check the primitive itself
            is_pure_primitive(
                &prim_info.primitive,
                prim_info.args.get(1).and_then(|arg| match arg {
                    Lambda::Lconst(constant) => Some(constant),
                    _ => None,
                }),
            )
        }

        // Let bindings are pure if both parts are pure
        Lambda::Llet(_, _, arg, body) => no_side_effects(arg) && no_side_effects(body),

        // Switch is not pure (can have pattern matching side effects)
        Lambda::Lswitch(_, _) => false,

        // String switch is not pure
        Lambda::LstringSwitch(_, _, _) => false,

        // Static raise is not pure (control flow)
        Lambda::LstaticRaise(_, _) => false,

        // Static catch is not pure
        Lambda::LstaticCatch(_, _, _) => false,

        // Try-with is pure if both body and handler are pure
        Lambda::LtryWith(body, _, handler) => no_side_effects(body) && no_side_effects(handler),

        // If-then-else is pure if all branches are pure
        Lambda::LifThenElse(a, b, c) => {
            no_side_effects(a) && no_side_effects(b) && no_side_effects(c)
        }

        // Sequence is pure if both parts are pure
        Lambda::Lsequence(a, b) => no_side_effects(a) && no_side_effects(b),

        // Letrec is pure if all bindings and body are pure
        Lambda::Lletrec(bindings, body) => {
            bindings.iter().all(|(_, expr)| no_side_effects(expr)) && no_side_effects(body)
        }

        // While loops are not pure (may not terminate)
        Lambda::Lwhile(_, _) => false,

        // For loops are not pure
        Lambda::Lfor(_, _, _, _, _) => false,

        // for-of / for-await-of run the iterator protocol; not pure.
        Lambda::Lfor_of(_, _, _) | Lambda::Lfor_await_of(_, _, _) => false,

        // break/continue divert control flow — not pure (matches OCaml
        // `Lam_analysis.no_side_effects` after #8348).
        Lambda::Lbreak | Lambda::Lcontinue => false,

        // Assignments are not pure
        Lambda::Lassign(_, _) => false,

        // Function application - special case for known pure functions
        Lambda::Lapply(apply) => {
            // Special case: Lazy.from_fun application
            if let Lambda::Lprim(prim_info) = &*apply.ap_func {
                if let Primitive::Pfield(_, FieldDbgInfo::Module { name }) = &prim_info.primitive {
                    if name == "from_fun" && apply.ap_args.len() == 1 {
                        return no_side_effects(&apply.ap_args[0]);
                    }
                }
            }
            // General function application is not pure
            false
        }
    }
}

/// Check if a primitive operation is pure (no side effects).
pub(crate) fn is_pure_primitive(prim: &Primitive, second_constant: Option<&Constant>) -> bool {
    match prim {
        Primitive::Pidentity | Primitive::Pignore => true,
        // Division can raise division by zero.
        Primitive::Pmodint | Primitive::Pdivint | Primitive::Pdivbigint | Primitive::Pmodbigint => {
            second_constant.is_some_and(not_zero_constant)
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
        | Primitive::Pimport
        | Primitive::Pnull
        | Primitive::Pundefined => true,

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
        | Primitive::Ppowbigint
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
        | Primitive::Pstringrefu
        | Primitive::Pstringrefs
        | Primitive::Pstringcomp(_)
        | Primitive::Pstringorder
        | Primitive::Pstringmin
        | Primitive::Pstringmax => true,

        // Array primitives (read-only)
        Primitive::Pmakearray
        | Primitive::Parraylength
        | Primitive::Parrayrefu
        | Primitive::Parrayrefs => true,

        // List and dict primitives
        Primitive::Pmakelist | Primitive::Pmakedict | Primitive::PdictHas => true,

        // Type testing primitives
        Primitive::Pisint | Primitive::PisPolyVarBlock | Primitive::Pisout(_) => true,

        // Offset and misc
        Primitive::Poffsetint(_)
        | Primitive::Pstringadd
        | Primitive::PfnArity
        | Primitive::PwrapExn
        | Primitive::Phash
        | Primitive::PhashMixstring
        | Primitive::PhashMixint
        | Primitive::PhashFinalmix => true,

        // Raw JS code - check if it's a pure expression
        Primitive::PrawJsCode(info) => raw_js_is_pure(info),

        // Impure primitives
        Primitive::PtaggedTemplate
        | Primitive::PjsApply
        | Primitive::PjsRuntimeApply
        | Primitive::PjsCall { .. }
        | Primitive::PinitMod
        | Primitive::PupdateMod
        | Primitive::PjsUnsafeDowngrade { .. }
        | Primitive::Pdebugger
        | Primitive::PjsFnMethod
        | Primitive::Pawait
        | Primitive::Parraysets
        | Primitive::Parraysetu
        | Primitive::Poffsetref(_)
        | Primitive::Praise
        | Primitive::Psetfield(_, _) => false,
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

/// Maximum size before we consider something too big to inline.
const TOO_BIG_TO_INLINE: i32 = 1000;

/// Small inline size threshold.
pub const SMALL_INLINE_SIZE: i32 = 5;

/// Exit inline size threshold (for static raise handlers).
pub const EXIT_INLINE_SIZE: i32 = 7;

/// Estimate the size of a Lambda expression for inlining decisions.
///
/// Returns a size estimate where smaller values indicate smaller code.
/// Returns `TOO_BIG_TO_INLINE` for expressions that shouldn't be inlined.
pub fn size(lam: &Lambda) -> i32 {
    size_inner(lam).unwrap_or(TOO_BIG_TO_INLINE)
}

/// Internal size computation that can fail for large expressions.
fn size_inner(lam: &Lambda) -> Option<i32> {
    match lam {
        Lambda::Lvar(_) => Some(1),

        Lambda::Lconst(c) => Some(size_constant(c)),

        Lambda::Llet(_, _, l1, l2) => {
            let s1 = size_inner(l1)?;
            let s2 = size_inner(l2)?;
            Some(1 + s1 + s2)
        }

        // Letrec is too big
        Lambda::Lletrec(_, _) => None,

        // Module field access is small
        Lambda::Lprim(prim_info) => {
            match &prim_info.primitive {
                Primitive::Pfield(_, FieldDbgInfo::Module { .. }) => {
                    if prim_info.args.len() == 1 {
                        match &prim_info.args[0] {
                            Lambda::LglobalModule(_, _) | Lambda::Lvar(_) => return Some(1),
                            _ => {}
                        }
                    }
                }
                Primitive::Praise | Primitive::PisNotNone => {
                    if prim_info.args.len() == 1 {
                        return size_inner(&prim_info.args[0]);
                    }
                }
                Primitive::Pmakeblock(
                    tag_info @ (TagInfo::Record { .. } | TagInfo::RecordInlined { .. }),
                    _,
                ) => {
                    let missing_fields = tag_info
                        .logical_field_count()
                        .saturating_sub(prim_info.args.len());
                    return size_lams(1 + missing_fields as i32, &prim_info.args);
                }
                Primitive::PjsObjectCreate(obj_params) => {
                    let logical_arg_count = obj_params
                        .iter()
                        .filter(|param| {
                            !matches!(
                                param.obj_arg_type,
                                crate::lambda::lam_primitive::ExternalArgAttr::ArgCst(_)
                            )
                        })
                        .count();
                    let missing_args = logical_arg_count.saturating_sub(prim_info.args.len());
                    return size_lams(1 + missing_args as i32, &prim_info.args);
                }
                Primitive::PrawJsCode(_) => return None,
                _ => {}
            }
            size_lams(1, &prim_info.args)
        }

        Lambda::LglobalModule(_, _) => Some(1),

        Lambda::Lapply(apply) => {
            let func_size = size_inner(&apply.ap_func)?;
            size_lams(func_size, &apply.ap_args)
        }

        Lambda::Lfunction(func) => size_inner(&func.body),

        // Complex control flow is too big
        Lambda::Lswitch(_, _) => None,
        Lambda::LstringSwitch(_, _, _) => None,
        Lambda::LstaticCatch(_, _, _) => None,
        Lambda::LtryWith(_, _, _) => None,
        Lambda::Lwhile(_, _) => None,
        Lambda::Lfor(_, _, _, _, _) => None,
        Lambda::Lfor_of(_, _, _) | Lambda::Lfor_await_of(_, _, _) => None,

        // OCaml `Lam_analysis.size`: `Lbreak | Lcontinue -> 1`.
        Lambda::Lbreak | Lambda::Lcontinue => Some(1),

        Lambda::LstaticRaise(_, args) => {
            let mut acc = 1;
            for arg in args {
                acc += size_inner(arg)?;
            }
            Some(acc)
        }

        Lambda::LifThenElse(l1, l2, l3) => {
            let s1 = size_inner(l1)?;
            let s2 = size_inner(l2)?;
            let s3 = size_inner(l3)?;
            Some(1 + s1 + s2 + s3)
        }

        Lambda::Lsequence(l1, l2) => {
            let s1 = size_inner(l1)?;
            let s2 = size_inner(l2)?;
            Some(s1 + s2)
        }

        Lambda::Lassign(_, v) => {
            let s = size_inner(v)?;
            Some(1 + s)
        }
    }
}

/// Compute the size of a constant.
fn size_constant(c: &Constant) -> i32 {
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

        Constant::String { .. } => 1,
        Constant::ImmString(_) => 1,

        Constant::Some(inner) => size_constant(inner),

        Constant::Block {
            tag_info, elements, ..
        } => {
            let missing_fields = match tag_info {
                TagInfo::Record { .. } | TagInfo::RecordInlined { .. } => tag_info
                    .logical_field_count()
                    .saturating_sub(elements.len()),
                _ => 0,
            };
            missing_fields as i32 + elements.iter().map(size_constant).sum::<i32>()
        }
    }
}

/// Compute the size of a list of Lambda expressions.
fn size_lams(acc: i32, lams: &[Lambda]) -> Option<i32> {
    let mut total = acc;
    for lam in lams {
        total += size_inner(lam)?;
    }
    Some(total)
}

/// Check if all arguments are constants.
pub fn args_all_const(args: &[Lambda]) -> bool {
    args.iter().all(|x| matches!(x, Lambda::Lconst(_)))
}

/// Check if a function can be inlined (not async, no directive).
pub fn lfunction_can_be_inlined(func: &LFunction) -> bool {
    !func.attr.async_ && func.attr.directive.is_none()
}

/// Determine if it's profitable to inline a function when applied.
pub fn ok_to_inline_fun_when_app(func: &LFunction, args: &[Lambda]) -> bool {
    match func.attr.inline {
        crate::lambda::InlineAttribute::Always => true,
        crate::lambda::InlineAttribute::Never => false,
        crate::lambda::InlineAttribute::Default => {
            let s = size(&func.body);
            s < SMALL_INLINE_SIZE
                || destruct_pattern(&func.body, &func.params, args)
                || (args_all_const(args) && s < 10 && no_side_effects(&func.body))
        }
    }
}

/// Check if inlining would enable pattern matching optimization.
///
/// This returns true when the function body is a switch/if on one of its
/// parameters and the corresponding argument is a constant.
pub(crate) fn destruct_pattern(body: &Lambda, params: &[Ident], args: &[Lambda]) -> bool {
    use crate::ident::Ident;

    fn find_arg<'a>(v: &Ident, params: &[Ident], args: &'a [Lambda]) -> Option<&'a Lambda> {
        for (i, param) in params.iter().enumerate() {
            if param == v {
                return args.get(i);
            }
        }
        None
    }

    match body {
        Lambda::Lswitch(scrutinee, switch) => {
            if let Lambda::Lvar(v) = &**scrutinee {
                if let Some(Lambda::Lconst(constant)) = find_arg(v, params, args) {
                    // Would need to evaluate the switch to check size
                    return size(&Lambda::switch(
                        Lambda::Lconst(constant.clone()),
                        switch.clone(),
                    )) < SMALL_INLINE_SIZE;
                }
            }
            false
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            if let Lambda::Lvar(v) = &**cond {
                if let Some(Lambda::Lconst(constant)) = find_arg(v, params, args) {
                    // OCaml lam_analysis.ml:238-242 measures the folded branch,
                    // not the original conditional with its parameter scrutinee.
                    return size(&Lambda::if_(
                        Lambda::Lconst(constant.clone()),
                        (**then_).clone(),
                        (**else_).clone(),
                    )) < SMALL_INLINE_SIZE;
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if a Lambda expression is safe to inline (won't duplicate work).
pub fn safe_to_inline(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lfunction(_) => true,
        Lambda::Lconst(c) => matches!(
            c,
            Constant::Pointer(_)
                | Constant::Int {
                    comment: Some(crate::lambda::lam_constant::PointerInfo::Constructor(_)),
                    ..
                }
                | Constant::JsTrue
                | Constant::JsFalse
                | Constant::JsUndefined { .. }
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::Ident;
    use crate::lambda::{FunctionAttribute, LambdaSwitch, LetKind, Primitive};
    use crate::location::Location;

    #[test]
    fn test_no_side_effects_simple() {
        let x = Ident::create_local("x");

        // Variable is pure
        assert!(no_side_effects(&Lambda::var(x)));

        // Constant is pure
        assert!(no_side_effects(&Lambda::const_(Constant::int(42))));

        // Function is pure
        let func = Lambda::function_(
            1,
            vec![Ident::create_local("x")],
            Lambda::const_(Constant::int(1)),
            FunctionAttribute::default(),
        );
        assert!(no_side_effects(&func));
    }

    #[test]
    fn test_no_side_effects_let() {
        let x = Ident::create_local("x");

        // Pure let binding
        let pure_let = Lambda::let_(
            LetKind::Strict,
            x.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::var(x.clone()),
        );
        assert!(no_side_effects(&pure_let));
    }

    #[test]
    fn test_no_side_effects_impure() {
        let x = Ident::create_local("x");

        // Assignment is impure
        let assign = Lambda::assign(x.clone(), Lambda::const_(Constant::int(1)));
        assert!(!no_side_effects(&assign));

        // While loop is impure
        let while_loop = Lambda::while_(Lambda::true_(), Lambda::unit());
        assert!(!no_side_effects(&while_loop));
    }

    #[test]
    fn test_no_side_effects_primitive() {
        // Addition is pure
        let add = Lambda::prim(
            Primitive::Paddint,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(2)),
            ],
            Location::none(),
        );
        assert!(no_side_effects(&add));

        // Division by non-zero constant is pure
        let div = Lambda::prim(
            Primitive::Pdivint,
            vec![
                Lambda::const_(Constant::int(10)),
                Lambda::const_(Constant::int(2)),
            ],
            Location::none(),
        );
        assert!(no_side_effects(&div));

        // Division by zero is impure
        let div_zero = Lambda::prim(
            Primitive::Pdivint,
            vec![
                Lambda::const_(Constant::int(10)),
                Lambda::const_(Constant::int(0)),
            ],
            Location::none(),
        );
        assert!(!no_side_effects(&div_zero));

        // Raise is impure
        let raise = Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::int(1))],
            Location::none(),
        );
        assert!(!no_side_effects(&raise));
    }

    #[test]
    fn test_no_side_effects_raw_js_matches_ocaml_classification() {
        let raw_literal = Lambda::prim(
            Primitive::PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                code: "null".to_string(),
                is_stmt: false,
            }),
            vec![],
            Location::none(),
        );
        assert!(no_side_effects(&raw_literal));

        let raw_unknown = Lambda::prim(
            Primitive::PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                code: "Number.EPSILON ? Number.EPSILON : 2.220446049250313e-16".to_string(),
                is_stmt: false,
            }),
            vec![],
            Location::none(),
        );
        assert!(!no_side_effects(&raw_unknown));

        let raw_comment_stmt = Lambda::prim(
            Primitive::PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                code: "/* comment */".to_string(),
                is_stmt: true,
            }),
            vec![],
            Location::none(),
        );
        assert!(no_side_effects(&raw_comment_stmt));
    }

    #[test]
    fn test_size_simple() {
        // Variable has size 1
        let var = Lambda::var(Ident::create_local("x"));
        assert_eq!(size(&var), 1);

        // Constant has size 1
        let const_ = Lambda::const_(Constant::int(42));
        assert_eq!(size(&const_), 1);
    }

    #[test]
    fn test_size_let() {
        let x = Ident::create_local("x");

        // let x = 1 in x has size 3 (1 for let + 1 for arg + 1 for body)
        let let_expr = Lambda::let_(
            LetKind::Strict,
            x.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::var(x),
        );
        assert_eq!(size(&let_expr), 3);
    }

    #[test]
    fn test_size_big() {
        // Letrec is too big
        let x = Ident::create_local("x");
        let letrec = Lambda::letrec(
            vec![(x.clone(), Lambda::const_(Constant::int(1)))],
            Lambda::var(x),
        );
        assert_eq!(size(&letrec), TOO_BIG_TO_INLINE);

        // Switch is too big
        let switch = Lambda::Lswitch(
            Box::new(Lambda::const_(Constant::int(0))),
            crate::lambda::LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            },
        );
        assert_eq!(size(&switch), TOO_BIG_TO_INLINE);
    }

    #[test]
    fn test_args_all_const() {
        assert!(args_all_const(&[
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(2)),
        ]));

        assert!(!args_all_const(&[
            Lambda::const_(Constant::int(1)),
            Lambda::var(Ident::create_local("x")),
        ]));
    }

    #[test]
    fn test_lfunction_can_be_inlined() {
        // Normal function can be inlined
        let func = LFunction {
            arity: 1,
            params: vec![Ident::create_local("x")],
            body: Box::new(Lambda::const_(Constant::int(1))),
            attr: FunctionAttribute::default(),
        };
        assert!(lfunction_can_be_inlined(&func));

        // Async function cannot be inlined
        let async_func = LFunction {
            arity: 1,
            params: vec![Ident::create_local("x")],
            body: Box::new(Lambda::const_(Constant::int(1))),
            attr: FunctionAttribute {
                async_: true,
                ..FunctionAttribute::default()
            },
        };
        assert!(!lfunction_can_be_inlined(&async_func));

        // Function with directive cannot be inlined
        let directive_func = LFunction {
            arity: 1,
            params: vec![Ident::create_local("x")],
            body: Box::new(Lambda::const_(Constant::int(1))),
            attr: FunctionAttribute {
                directive: Some("use server".to_string()),
                ..FunctionAttribute::default()
            },
        };
        assert!(!lfunction_can_be_inlined(&directive_func));
    }

    #[test]
    fn test_safe_to_inline() {
        // Function is safe
        let func = Lambda::function_(
            1,
            vec![Ident::create_local("x")],
            Lambda::const_(Constant::int(1)),
            FunctionAttribute::default(),
        );
        assert!(safe_to_inline(&func));

        // JS true/false/undefined are safe
        assert!(safe_to_inline(&Lambda::true_()));
        assert!(safe_to_inline(&Lambda::false_()));
        assert!(safe_to_inline(&Lambda::unit()));

        // Variable is not safe (would duplicate evaluation)
        assert!(!safe_to_inline(&Lambda::var(Ident::create_local("x"))));
    }

    #[test]
    fn test_size_constant() {
        assert_eq!(size_constant(&Constant::int(42)), 1);
        assert_eq!(size_constant(&Constant::string("hello")), 1);
        assert_eq!(size_constant(&Constant::JsTrue), 1);

        // Some wraps another constant
        assert_eq!(
            size_constant(&Constant::Some(Box::new(Constant::int(1)))),
            1
        );

        // Block sums up fields
        assert_eq!(
            size_constant(&Constant::Block {
                tag_info: crate::lambda::lam_tag_info::TagInfo::Tuple,
                elements: vec![Constant::int(1), Constant::int(2), Constant::int(3)],
            }),
            3
        );

        assert_eq!(
            size_constant(&Constant::Block {
                tag_info: TagInfo::Record {
                    fields: vec![("className".to_string(), true)],
                    logical_field_count: Some(4),
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                },
                elements: vec![Constant::Some(Box::new(Constant::string("button")))],
            }),
            4
        );
    }

    #[test]
    fn test_ok_to_inline_fun_when_app_measures_folded_if_branch() {
        let checked = Ident::create_local("checked");
        let value = Ident::create_local("value");
        let branch = || {
            Lambda::prim(
                Primitive::Pdebugger,
                vec![Lambda::var(value.clone())],
                crate::location::Location::none(),
            )
        };
        let func = LFunction {
            arity: 1,
            params: vec![checked.clone()],
            body: Box::new(Lambda::if_(Lambda::var(checked), branch(), branch())),
            attr: FunctionAttribute::default(),
        };

        assert!(size(&func.body) >= SMALL_INLINE_SIZE);
        assert!(ok_to_inline_fun_when_app(
            &func,
            &[Lambda::const_(Constant::JsFalse)]
        ));
        assert!(ok_to_inline_fun_when_app(
            &func,
            &[Lambda::const_(Constant::JsTrue)]
        ));
        assert!(!ok_to_inline_fun_when_app(
            &func,
            &[Lambda::var(Ident::create_local("unknown"))]
        ));
    }

    #[test]
    fn test_ok_to_inline_fun_when_app_folds_switch_on_constant_scrutinee_like_ocaml() {
        let x = Ident::create_local("x");
        let func = LFunction {
            arity: 1,
            params: vec![x.clone()],
            body: Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(x)),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (
                            crate::lambda::SwitchKey::Int(0),
                            Lambda::const_(Constant::JsFalse),
                        ),
                        (
                            crate::lambda::SwitchKey::Int(1),
                            Lambda::const_(Constant::JsTrue),
                        ),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Direct,
                },
            )),
            attr: FunctionAttribute::default(),
        };

        assert!(ok_to_inline_fun_when_app(
            &func,
            &[Lambda::const_(Constant::int(1))]
        ));
    }
}

#[cfg(test)]
mod indexed_helper_extraction_tests {
    use super::*;
    use crate::location::Location;

    fn effect() -> Lambda {
        Lambda::prim(Primitive::Pdebugger, vec![], Location::none())
    }

    #[test]
    fn scalar_primitive_helper_keeps_argument_purity_gate() {
        for primitive in [Primitive::Pidentity, Primitive::Pignore] {
            assert!(!no_side_effects(&Lambda::prim(
                primitive,
                vec![effect()],
                Location::none()
            )));
        }
        assert!(!no_side_effects(&Lambda::prim(
            Primitive::Pdivint,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::var(Ident::create_local("d"))
            ],
            Location::none(),
        )));
        assert!(!no_side_effects(&Lambda::prim(
            Primitive::Pdivint,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(0))
            ],
            Location::none(),
        )));
        assert!(no_side_effects(&Lambda::prim(
            Primitive::Pdivint,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(2))
            ],
            Location::none(),
        )));
    }
}
