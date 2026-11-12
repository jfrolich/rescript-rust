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
        | Primitive::PjsCall(_)
        | Primitive::Pjsx(_)
        | Primitive::PinitMod
        | Primitive::PupdateMod
        // A spread reads the source's properties, which may run getters or
        // proxy traps.
        | Primitive::PdictSpread
        | Primitive::PjsObjectGet(_)
        | Primitive::PjsObjectSet(_)
        | Primitive::Pdebugger
        // Runtime calls, like the `Lapply` they were parsed into.
        | Primitive::ParraySpread
        | Primitive::PlistSpread
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

/// Small inline size threshold.
pub const SMALL_INLINE_SIZE: i32 = 5;

/// Exit inline size threshold (for static raise handlers).
pub const EXIT_INLINE_SIZE: i32 = 7;

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

/// `Lambda.lfunction_can_be_inlined` (lambda.ml:1091-1092) on a function's
/// attributes: an async function or one with a directive must stay a
/// function, neither inlined nor replaced by the call it forwards.
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
        Node::TryFinally { body, finally } => {
            no_side_effects(a, body) && no_side_effects(a, finally)
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
        // lam_analysis.ml:137: an application is not known to be pure (we
        // need purity analysis).
        Node::Apply { .. } => false,
    }
}

/// `Lam_analysis.delay_safe` (lam_analysis.ml:141-193), the Lambda
/// counterpart of the JS-level `lam_compile_arguments::delay_safe`: `lam` has
/// no side effects and reads nothing other code can change, so evaluating it
/// later gives the same value. Fields of records, which may be mutable,
/// arrays, dictionaries and the variables in `assignable` can change.
pub fn delay_safe(a: &LamArena, assignable: &ahash::AHashSet<Ident>, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Const(_) | Node::Function { .. } | Node::GlobalModule(_) => true,
        Node::Var(id) => !assignable.contains(&a.ident(id)),
        Node::If { cond, then_, else_ } => {
            delay_safe(a, assignable, cond)
                && delay_safe(a, assignable, then_)
                && delay_safe(a, assignable, else_)
        }
        Node::Prim { args, info } => {
            a.list(args).iter().all(|x| delay_safe(a, assignable, *x))
                && match &a.prim_payload(info).primitive {
                    // They raise unless an operand is a suitable constant.
                    Primitive::Pdivint
                    | Primitive::Pmodint
                    | Primitive::Pdivbigint
                    | Primitive::Pmodbigint
                    | Primitive::Ppowbigint => no_side_effects(a, lam),
                    primitive => primitive_is_delay_safe(primitive),
                }
        }
        Node::Let { .. }
        | Node::LetRec { .. }
        | Node::Apply { .. }
        | Node::Switch { .. }
        | Node::StringSwitch { .. }
        | Node::StaticRaise { .. }
        | Node::StaticCatch { .. }
        | Node::TryWith { .. }
        | Node::TryFinally { .. }
        | Node::Sequence(..)
        | Node::While(..)
        | Node::For { .. }
        | Node::ForOf { .. }
        | Node::ForAwaitOf { .. }
        | Node::Assign { .. }
        | Node::Break
        | Node::Continue => false,
    }
}

/// Whether a primitive other than a division is a value or builds a fresh
/// block from its operands (lam_analysis.ml:157-193), rather than reading
/// the heap or having side effects.
pub(crate) fn primitive_is_delay_safe(primitive: &Primitive) -> bool {
    match primitive {
        Primitive::Pfield(_, field) => match field {
            FieldDbgInfo::Module { .. }
            | FieldDbgInfo::Tuple
            | FieldDbgInfo::PolyVarTag
            | FieldDbgInfo::PolyVarContent
            | FieldDbgInfo::Extension
            | FieldDbgInfo::Variant
            // The tag of a variant block, which is immutable like its fields.
            | FieldDbgInfo::VariantTag
            | FieldDbgInfo::Cons => true,
            FieldDbgInfo::Record { .. }
            | FieldDbgInfo::RecordInline { .. }
            | FieldDbgInfo::RecordExtension { .. } => false,
        },
        // `%identity` is its operand. A function's arity does not change.
        Primitive::Pidentity
        | Primitive::PfnArity
        | Primitive::Ptypeof
        | Primitive::Psome
        | Primitive::PsomeNotNest
        | Primitive::Pmakeblock(..)
        | Primitive::PjsObjectCreate(_)
        | Primitive::Pmakearray
        | Primitive::Pmakelist
        | Primitive::Pmakedict
        | Primitive::Ptemplate(_)
        | Primitive::Pstringadd
        | Primitive::Pstringlength
        | Primitive::Pstringcomp(_)
        | Primitive::Pstringorder
        | Primitive::Pstringmin
        | Primitive::Pstringmax
        | Primitive::Psequand
        | Primitive::Psequor
        | Primitive::Pnot
        | Primitive::Pboolcomp(_)
        | Primitive::Pboolorder
        | Primitive::Pboolmin
        | Primitive::Pboolmax
        | Primitive::Pnegint
        | Primitive::Paddint
        | Primitive::Psubint
        | Primitive::Pmulint
        | Primitive::Ppowint
        | Primitive::Pandint
        | Primitive::Porint
        | Primitive::Pxorint
        | Primitive::Pnotint
        | Primitive::Plslint
        | Primitive::Plsrint
        | Primitive::Pasrint
        | Primitive::Pintcomp(_)
        | Primitive::Pintorder
        | Primitive::Pintmin
        | Primitive::Pintmax
        | Primitive::Pintoffloat
        | Primitive::Pfloatofint
        | Primitive::Pnegfloat
        | Primitive::Pmodfloat
        | Primitive::Paddfloat
        | Primitive::Psubfloat
        | Primitive::Pmulfloat
        | Primitive::Pdivfloat
        | Primitive::Ppowfloat
        | Primitive::Pfloatcomp(_)
        | Primitive::Pfloatorder
        | Primitive::Pfloatmin
        | Primitive::Pfloatmax
        | Primitive::Pnegbigint
        | Primitive::Paddbigint
        | Primitive::Psubbigint
        | Primitive::Pmulbigint
        | Primitive::Pandbigint
        | Primitive::Porbigint
        | Primitive::Pxorbigint
        | Primitive::Pnotbigint
        | Primitive::Plslbigint
        | Primitive::Pasrbigint
        | Primitive::Pbigintcomp(_)
        | Primitive::Pbigintorder
        | Primitive::Pbigintmin
        | Primitive::Pbigintmax
        | Primitive::PhashMixint
        | Primitive::PhashMixstring
        | Primitive::PhashFinalmix
        | Primitive::PisNullUndefined
        | Primitive::Pjscomp(_)
        | Primitive::PnullToOpt
        | Primitive::PnullUndefinedToOpt
        | Primitive::PisNull
        | Primitive::PisUndefined
        | Primitive::PisNotNone
        | Primitive::PvalFromOption
        | Primitive::PvalFromOptionNotNest
        | Primitive::PisPolyVarBlock => true,
        // Reads of the heap, and primitives with side effects. `%ignore`
        // stands for OCaml's `Lsequence (arg, unit)`, and an extension slot
        // test lowers to a read of the exception's id field.
        Primitive::Pignore
        | Primitive::PextensionSlotEq
        | Primitive::PjsApply
        | Primitive::Pdebugger
        | Primitive::Psetfield(..)
        | Primitive::Pduprecord
        | Primitive::PrecordRest(_)
        | Primitive::PjsCall(_)
        | Primitive::Pjsx(_)
        | Primitive::PjsObjectGet(_)
        | Primitive::PjsObjectSet(_)
        | Primitive::Praise
        | Primitive::Pobjcomp(_)
        | Primitive::Pobjorder
        | Primitive::Pobjmin
        | Primitive::Pobjmax
        | Primitive::Pobjtag
        | Primitive::Pobjsize
        | Primitive::Pstringrefu
        | Primitive::Pstringrefs
        | Primitive::Parraylength
        | Primitive::Parrayrefu
        | Primitive::Parraysetu
        | Primitive::Parrayrefs
        | Primitive::PdictHas
        | Primitive::Pawait
        | Primitive::Pimport(_)
        | Primitive::PinitMod
        | Primitive::PupdateMod
        | Primitive::Phash
        | Primitive::PcreateExtension(_)
        | Primitive::PrawJsCode(_)
        | Primitive::PjsFnMethod
        | Primitive::PtaggedTemplate(_)
        | Primitive::PdictSpread
        | Primitive::ParraySpread
        | Primitive::PlistSpread => false,
        Primitive::Pdivint
        | Primitive::Pmodint
        | Primitive::Pdivbigint
        | Primitive::Pmodbigint
        | Primitive::Ppowbigint => false,
    }
}

const TOO_BIG_TO_INLINE: i32 = 1000;

/// The size count reached the limit of `size_upto`.
struct LimitReached;

/// A running size count that stops at `limit`.
struct SizeCounter<'a> {
    arena: &'a LamArena,
    total: i32,
    limit: i32,
}

impl SizeCounter<'_> {
    fn add(&mut self, n: i32) -> Result<(), LimitReached> {
        self.total += n;
        if self.total >= self.limit {
            Err(LimitReached)
        } else {
            Ok(())
        }
    }

    fn lams(&mut self, lams: &[Lam]) -> Result<(), LimitReached> {
        lams.iter().try_for_each(|lam| self.lam(*lam))
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
                    TagInfo::Record(_) | TagInfo::RecordInlined(_) => tag_info
                        .logical_field_count()
                        .saturating_sub(elements.len()),
                    _ => 0,
                };
                self.add(missing_fields as i32)?;
                elements.iter().try_for_each(|c| self.constant(c))
            }
        }
    }

    fn lam(&mut self, lam: Lam) -> Result<(), LimitReached> {
        let a = self.arena;
        match a.node(lam) {
            Node::Var(_) | Node::GlobalModule(_) | Node::Break | Node::Continue => self.add(1),
            Node::Const(c) => self.constant(a.constant(c)),
            Node::Let { value, body, .. } => {
                self.add(1)?;
                self.lam(value)?;
                self.lam(body)
            }
            Node::Prim { args, info } => {
                let args = a.list(args);
                match &a.prim_payload(info).primitive {
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. })
                        if matches!(
                            args,
                            [x] if matches!(a.node(*x), Node::GlobalModule(_) | Node::Var(_))
                        ) =>
                    {
                        return self.add(1);
                    }
                    Primitive::Praise | Primitive::PisNotNone if args.len() == 1 => {
                        return self.lam(args[0]);
                    }
                    // A sparse record block stands for its omitted fields too.
                    Primitive::Pmakeblock(
                        tag_info @ (TagInfo::Record(_) | TagInfo::RecordInlined(_)),
                        _,
                    ) => {
                        let missing = tag_info.logical_field_count().saturating_sub(args.len());
                        self.add(1 + missing as i32)?;
                        return self.lams(args);
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
                        self.add(1 + missing as i32)?;
                        return self.lams(args);
                    }
                    Primitive::PrawJsCode(_) => return self.add(TOO_BIG_TO_INLINE),
                    _ => {}
                }
                self.add(1)?;
                self.lams(args)
            }
            Node::Apply { func, args, .. } => {
                self.lam(func)?;
                self.lams(a.list(args))
            }
            Node::Function { body, .. } => self.lam(body),
            Node::LetRec { .. }
            | Node::Switch { .. }
            | Node::StringSwitch { .. }
            | Node::StaticCatch { .. }
            | Node::TryWith { .. }
            | Node::TryFinally { .. }
            | Node::While(..)
            | Node::For { .. }
            | Node::ForOf { .. }
            | Node::ForAwaitOf { .. } => self.add(TOO_BIG_TO_INLINE),
            Node::StaticRaise { args, .. } => {
                self.add(1)?;
                self.lams(a.list(args))
            }
            Node::If { cond, then_, else_ } => {
                self.add(1)?;
                self.lam(cond)?;
                self.lam(then_)?;
                self.lam(else_)
            }
            Node::Sequence(x, y) => {
                self.lam(x)?;
                self.lam(y)
            }
            Node::Assign { value, .. } => {
                self.add(1)?;
                self.lam(value)
            }
        }
    }
}

/// `Lam_analysis.size_upto ~limit lam`: the size of a lambda for inlining
/// decisions if it is below `limit`, `limit` otherwise. Callers only compare
/// it with small thresholds, so counting stops once `limit` is reached.
/// `limit` must be at most 1000.
pub fn size_upto(a: &LamArena, limit: i32, lam: Lam) -> i32 {
    debug_assert!(limit <= TOO_BIG_TO_INLINE);
    let mut counter = SizeCounter {
        arena: a,
        total: 0,
        limit,
    };
    match counter.lam(lam) {
        Ok(()) => counter.total,
        Err(LimitReached) => limit,
    }
}

/// Whether every argument is a constant node.
pub fn args_all_const(a: &LamArena, args: &[Lam]) -> bool {
    args.iter().all(|x| a.is_const(*x))
}

/// `Lambda.lfunction_can_be_inlined` (lambda.ml:1091-1092).
pub fn lfunction_can_be_inlined(a: &LamArena, func: FuncId) -> bool {
    attr_can_be_inlined(&a.func_payload(func).attr)
}

/// `Lam_analysis.ok_to_inline_fun_when_app`.
pub fn ok_to_inline_fun_when_app(a: &LamArena, func: FuncId, body: Lam, args: &[Lam]) -> bool {
    match a.func_payload(func).attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let s = size_upto(a, 10, body);
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
                    Some(action) => size_upto(a, SMALL_INLINE_SIZE, action) < SMALL_INLINE_SIZE,
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
                return size_upto(a, SMALL_INLINE_SIZE, branch) < SMALL_INLINE_SIZE;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_upto_stops_at_the_limit() {
        let mut a = LamArena::new();
        let block = Constant::Block {
            tag_info: Box::new(TagInfo::Tuple),
            elements: (0..50).map(Constant::int).collect(),
        };
        let block = a.const_(block);
        let one = a.const_(Constant::int(1));
        assert_eq!(size_upto(&a, 5, block), 5);
        assert_eq!(size_upto(&a, TOO_BIG_TO_INLINE, block), 50);
        assert_eq!(size_upto(&a, 5, one), 1);
    }
}
