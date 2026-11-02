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
        Lambda::LglobalModule(_) => true,

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
        Primitive::PisPolyVarBlock => true,

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
        | Primitive::PjsCall { .. }
        | Primitive::Pjsx(_)
        | Primitive::PinitMod
        | Primitive::PupdateMod
        // A spread reads the source's properties, which may run getters or
        // proxy traps.
        | Primitive::PdictSpread
        | Primitive::PjsObjectGet(_)
        | Primitive::PjsObjectSet(_)
        | Primitive::Pdebugger
        | Primitive::PjsFnMethod
        | Primitive::Pawait
        | Primitive::Parraysetu
        | Primitive::Praise
        | Primitive::Psetfield(_, _)
        // Bounds-checked reads throw when the index is out of range.
        | Primitive::Parrayrefs
        | Primitive::Pstringrefs
        | Primitive::Pstringrefu => false,
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

/// The size count reached the limit of `size_upto`.
struct LimitReached;

/// A running size count that stops at `limit`.
struct SizeCounter {
    total: i32,
    limit: i32,
}

impl SizeCounter {
    fn add(&mut self, n: i32) -> Result<(), LimitReached> {
        self.total += n;
        if self.total >= self.limit {
            Err(LimitReached)
        } else {
            Ok(())
        }
    }

    fn lams(&mut self, lams: &[Lambda]) -> Result<(), LimitReached> {
        lams.iter().try_for_each(|lam| self.lam(lam))
    }

    /// Constants count their leaves, and stop at the limit too: a large
    /// constant list or record should not be walked completely.
    fn constant(&mut self, c: &Constant) -> Result<(), LimitReached> {
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
            | Constant::JsFalse
            | Constant::String(_)
            | Constant::ImmString(_) => self.add(1),
            Constant::Some(inner) => self.constant(inner),
            Constant::Block {
                tag_info, elements, ..
            } => {
                // A sparse record block stands for its omitted fields too.
                let missing_fields = match &**tag_info {
                    TagInfo::Record { .. } | TagInfo::RecordInlined { .. } => tag_info
                        .logical_field_count()
                        .saturating_sub(elements.len()),
                    _ => 0,
                };
                self.add(missing_fields as i32)?;
                elements.iter().try_for_each(|c| self.constant(c))
            }
        }
    }

    fn lam(&mut self, lam: &Lambda) -> Result<(), LimitReached> {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lbreak | Lambda::Lcontinue => {
                self.add(1)
            }
            Lambda::Lconst(c) => self.constant(c),
            Lambda::Llet(_, _, l1, l2) => {
                self.add(1)?;
                self.lam(l1)?;
                self.lam(l2)
            }
            Lambda::Lprim(prim_info) => {
                match &prim_info.primitive {
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. })
                        if matches!(
                            prim_info.args.as_slice(),
                            [Lambda::LglobalModule(_) | Lambda::Lvar(_)]
                        ) =>
                    {
                        return self.add(1);
                    }
                    Primitive::Praise | Primitive::PisNotNone if prim_info.args.len() == 1 => {
                        return self.lam(&prim_info.args[0]);
                    }
                    // A sparse record block stands for its omitted fields too.
                    Primitive::Pmakeblock(
                        tag_info @ (TagInfo::Record { .. } | TagInfo::RecordInlined { .. }),
                        _,
                    ) => {
                        let missing_fields = tag_info
                            .logical_field_count()
                            .saturating_sub(prim_info.args.len());
                        self.add(1 + missing_fields as i32)?;
                        return self.lams(&prim_info.args);
                    }
                    Primitive::PjsObjectCreate(obj_params) => {
                        let logical_arg_count = obj_params
                            .iter()
                            .filter(|param| {
                                !matches!(
                                    param.obj_arg_type,
                                    crate::types::external_ffi_types::Attr::ArgCst(_)
                                )
                            })
                            .count();
                        let missing_args = logical_arg_count.saturating_sub(prim_info.args.len());
                        self.add(1 + missing_args as i32)?;
                        return self.lams(&prim_info.args);
                    }
                    Primitive::PrawJsCode(_) => return self.add(TOO_BIG_TO_INLINE),
                    _ => {}
                }
                self.add(1)?;
                self.lams(&prim_info.args)
            }
            Lambda::Lapply(apply) => {
                self.lam(&apply.ap_func)?;
                self.lams(&apply.ap_args)
            }
            Lambda::Lfunction(func) => self.lam(&func.body),
            Lambda::Lletrec(_, _)
            | Lambda::Lswitch(_, _)
            | Lambda::LstringSwitch(_, _, _)
            | Lambda::LstaticCatch(_, _, _)
            | Lambda::LtryWith(_, _, _)
            | Lambda::Lwhile(_, _)
            | Lambda::Lfor(_, _, _, _, _)
            | Lambda::Lfor_of(_, _, _)
            | Lambda::Lfor_await_of(_, _, _) => self.add(TOO_BIG_TO_INLINE),
            Lambda::LstaticRaise(_, args) => {
                self.add(1)?;
                self.lams(args)
            }
            Lambda::LifThenElse(l1, l2, l3) => {
                self.add(1)?;
                self.lam(l1)?;
                self.lam(l2)?;
                self.lam(l3)
            }
            Lambda::Lsequence(l1, l2) => {
                self.lam(l1)?;
                self.lam(l2)
            }
            Lambda::Lassign(_, v) => {
                self.add(1)?;
                self.lam(v)
            }
        }
    }
}

/// `Lam_analysis.size_upto ~limit lam`: the size of a lambda for inlining
/// decisions if it is below `limit`, `limit` otherwise. Callers only compare
/// it with small thresholds, so counting stops once `limit` is reached.
/// `limit` must be at most 1000.
pub fn size_upto(limit: i32, lam: &Lambda) -> i32 {
    debug_assert!(limit <= TOO_BIG_TO_INLINE);
    let mut counter = SizeCounter { total: 0, limit };
    match counter.lam(lam) {
        Ok(()) => counter.total,
        Err(LimitReached) => limit,
    }
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
            let s = size_upto(10, &func.body);
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
                    return size_upto(
                        SMALL_INLINE_SIZE,
                        &Lambda::switch(Lambda::Lconst(constant.clone()), *switch.clone()),
                    ) < SMALL_INLINE_SIZE;
                }
            }
            false
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            if let Lambda::Lvar(v) = &**cond {
                if let Some(Lambda::Lconst(constant)) = find_arg(v, params, args) {
                    // OCaml lam_analysis.ml:238-242 measures the folded branch,
                    // not the original conditional with its parameter scrutinee.
                    return size_upto(
                        SMALL_INLINE_SIZE,
                        &Lambda::if_(
                            Lambda::Lconst(constant.clone()),
                            (**then_).clone(),
                            (**else_).clone(),
                        ),
                    ) < SMALL_INLINE_SIZE;
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
        Lambda::Lconst(c) => {
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
            crate::location::Location::none(),
        );
        assert!(no_side_effects(&func));
    }

    #[test]
    fn test_no_side_effects_let() {
        let x = Ident::create_local("x");

        // Pure let binding
        let pure_let = Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::const_(Constant::int(1)),
            Lambda::var(x),
        );
        assert!(no_side_effects(&pure_let));
    }

    #[test]
    fn test_no_side_effects_impure() {
        let x = Ident::create_local("x");

        // Assignment is impure
        let assign = Lambda::assign(x, Lambda::const_(Constant::int(1)));
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
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &var), 1);

        // Constant has size 1
        let const_ = Lambda::const_(Constant::int(42));
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &const_), 1);
    }

    #[test]
    fn test_size_let() {
        let x = Ident::create_local("x");

        // let x = 1 in x has size 3 (1 for let + 1 for arg + 1 for body)
        let let_expr = Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::const_(Constant::int(1)),
            Lambda::var(x),
        );
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &let_expr), 3);
    }

    #[test]
    fn test_size_big() {
        // Letrec is too big
        let x = Ident::create_local("x");
        let letrec = Lambda::letrec(vec![(x, Lambda::const_(Constant::int(1)))], Lambda::var(x));
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &letrec), TOO_BIG_TO_INLINE);

        // Switch is too big
        let switch = Lambda::Lswitch(
            Box::new(Lambda::const_(Constant::int(0))),
            Box::new(crate::lambda::LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
        );
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &switch), TOO_BIG_TO_INLINE);
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
            loc: crate::location::Location::none(),
            arity: 1,
            params: vec![Ident::create_local("x")],
            body: Box::new(Lambda::const_(Constant::int(1))),
            attr: FunctionAttribute::default(),
        };
        assert!(lfunction_can_be_inlined(&func));

        // Async function cannot be inlined
        let async_func = LFunction {
            loc: crate::location::Location::none(),
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
            loc: crate::location::Location::none(),
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
            crate::location::Location::none(),
        );
        assert!(safe_to_inline(&func));

        // JS true/false/undefined are safe
        assert!(safe_to_inline(&Lambda::true_()));
        assert!(safe_to_inline(&Lambda::false_()));
        assert!(safe_to_inline(&Lambda::unit()));

        // Variable is not safe (would duplicate evaluation)
        assert!(!safe_to_inline(&Lambda::var(Ident::create_local("x"))));
    }

    fn size_constant(c: &Constant) -> i32 {
        size_upto(TOO_BIG_TO_INLINE, &Lambda::Lconst(c.clone()))
    }

    #[test]
    fn test_size_upto_stops_at_the_limit() {
        let block = Constant::Block {
            tag_info: Box::new(crate::lambda::lam_tag_info::TagInfo::Tuple),
            elements: (0..50).map(Constant::int).collect(),
        };
        assert_eq!(size_upto(5, &Lambda::Lconst(block.clone())), 5);
        assert_eq!(size_upto(TOO_BIG_TO_INLINE, &Lambda::Lconst(block)), 50);
        assert_eq!(size_upto(5, &Lambda::Lconst(Constant::int(1))), 1);
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
                tag_info: Box::new(crate::lambda::lam_tag_info::TagInfo::Tuple),
                elements: vec![Constant::int(1), Constant::int(2), Constant::int(3)],
            }),
            3
        );

        assert_eq!(
            size_constant(&Constant::Block {
                tag_info: Box::new(TagInfo::Record {
                    fields: vec![("className".to_string(), true)],
                    logical_field_count: Some(4),
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                }),
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
                vec![Lambda::var(value)],
                crate::location::Location::none(),
            )
        };
        let func = LFunction {
            loc: crate::location::Location::none(),
            arity: 1,
            params: vec![checked],
            body: Box::new(Lambda::if_(Lambda::var(checked), branch(), branch())),
            attr: FunctionAttribute::default(),
        };

        assert!(size_upto(TOO_BIG_TO_INLINE, &func.body) >= SMALL_INLINE_SIZE);
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
            loc: crate::location::Location::none(),
            arity: 1,
            params: vec![x],
            body: Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(x)),
                Box::new(LambdaSwitch {
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
                }),
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
