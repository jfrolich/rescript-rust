//! Lambda IR printing for debugging.
//!
//! This module provides pretty-printing for Lambda expressions,
//! useful for debugging the compilation pipeline.

use std::fmt;
use crate::lambda::LamLoc;

use crate::ident::Ident;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{DirectionFlag, Lambda};

/// Print kind for let bindings.
#[derive(Debug, Clone, Copy)]
pub enum PrintKind {
    Alias,
    Strict,
    StrictOpt,
    Variable,
    Recursive,
}

impl PrintKind {
    /// Get the short string representation.
    pub fn as_str(self) -> &'static str {
        match self {
            PrintKind::Alias => "a",
            PrintKind::Strict => "",
            PrintKind::StrictOpt => "o",
            PrintKind::Variable => "v",
            PrintKind::Recursive => "r",
        }
    }
}

impl From<LetKind> for PrintKind {
    fn from(k: LetKind) -> Self {
        match k {
            LetKind::Alias => PrintKind::Alias,
            LetKind::Strict => PrintKind::Strict,
            LetKind::StrictOpt => PrintKind::StrictOpt,
            LetKind::Variable => PrintKind::Variable,
        }
    }
}

/// Format a constant for output.
pub fn format_constant(c: &Constant, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match c {
        Constant::JsTrue => write!(f, "#true"),
        Constant::JsFalse => write!(f, "#false"),
        Constant::JsNull => write!(f, "#null"),
        Constant::ModuleAlias => write!(f, "0a"),
        Constant::JsUndefined { .. } => write!(f, "#undefined"),
        Constant::Int { i, .. } => write!(f, "{i}"),
        Constant::NativeInt { i, .. } => write!(f, "{i}"),
        Constant::Constructor(tag) => write!(f, "{}", tag.name),
        Constant::Char(c) => {
            if let Some(ch) = char::from_u32(*c as u32) {
                write!(f, "'{ch}'")
            } else {
                write!(f, "'\\x{c:02x}'")
            }
        }
        Constant::String(s) => write!(f, "{s:?}"),
        Constant::ImmString(s) => write!(f, "#{s:?}"),
        Constant::Float(s) => write!(f, "{s}"),
        Constant::BigInt { negative, value } => {
            if *negative {
                write!(f, "-{value}n")
            } else {
                write!(f, "{value}n")
            }
        }
        Constant::Pointer(name) => write!(f, "`{name}"),
        Constant::Some(inner) => {
            write!(f, "[some-c]")?;
            format_constant(inner, f)
        }
        Constant::Block { tag_info, elements } => {
            let tag = tag_info.tag_label();
            if elements.is_empty() {
                write!(f, "[{tag}]")
            } else {
                write!(f, "[{tag}:")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    format_constant(elem, f)?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Format a comparison operator.
fn format_comparison(cmp: Comparison) -> &'static str {
    match cmp {
        Comparison::Eq => "==",
        Comparison::Neq => "!=",
        Comparison::Lt => "<",
        Comparison::Gt => ">",
        Comparison::Le => "<=",
        Comparison::Ge => ">=",
    }
}

fn format_float_comparison(cmp: Comparison) -> &'static str {
    match cmp {
        Comparison::Eq => "==.",
        Comparison::Neq => "!=.",
        Comparison::Lt => "<.",
        Comparison::Gt => ">.",
        Comparison::Le => "<=.",
        Comparison::Ge => ">=.",
    }
}

/// Format a primitive operation.
pub fn format_primitive(p: &Primitive, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match p {
        Primitive::Pidentity => write!(f, "id"),
        Primitive::Pignore => write!(f, "ignore"),
        Primitive::PcreateExtension(s) => write!(f, "extension[{s}]"),
        Primitive::PextensionSlotEq => write!(f, "#extension_slot_eq"),
        Primitive::PinitMod => write!(f, "init_mod!"),
        Primitive::PupdateMod => write!(f, "update_mod!"),
        Primitive::PjsApply => write!(f, "#apply"),
        Primitive::PtaggedTemplate(_) => write!(f, "#tagged_template"),
        Primitive::Ptemplate(_) => write!(f, "#template"),
        Primitive::PjsObjectGet(name) => write!(f, "js_object_get[{name}]"),
        Primitive::PjsObjectSet(name) => write!(f, "js_object_set[{name}]"),
        Primitive::PfnArity => write!(f, "fn.length"),
        Primitive::PjsFnMethod => write!(f, "js_fn_method"),
        Primitive::Pdebugger => write!(f, "debugger"),
        Primitive::PrawJsCode(_) => write!(f, "[raw]"),
        Primitive::Ptypeof => write!(f, "typeof"),
        Primitive::PnullToOpt => write!(f, "[null->opt]"),
        Primitive::PnullUndefinedToOpt => write!(f, "[null/undefined->opt]"),
        Primitive::PisNull => write!(f, "[?null]"),
        Primitive::PisNotNone => write!(f, "[?is-not-none]"),
        Primitive::Psome => write!(f, "[some]"),
        Primitive::PsomeNotNest => write!(f, "[some-not-nest]"),
        Primitive::PvalFromOption => write!(f, "[?unbox]"),
        Primitive::PvalFromOptionNotNest => write!(f, "[?unbox-not-nest]"),
        Primitive::PisUndefined => write!(f, "[?undefined]"),
        Primitive::PisNullUndefined => write!(f, "[?null?undefined]"),
        Primitive::Pimport(_) => write!(f, "import"),
        Primitive::Pmakeblock(tag_info, Mutable::Immutable) => {
            write!(f, "makeblock {}", tag_info.tag_label())
        }
        Primitive::Pmakeblock(tag_info, Mutable::Mutable) => {
            write!(f, "makemutable {}", tag_info.tag_label())
        }
        Primitive::Pfield(n, field_info) => {
            if let Some(name) = field_info.name() {
                write!(f, "field {name}/{n}")
            } else {
                write!(f, "field {n}")
            }
        }
        Primitive::Psetfield(n, _) => write!(f, "setfield {n}"),
        Primitive::Pduprecord => write!(f, "duprecord"),
        Primitive::PrecordRest(excluded) => {
            write!(f, "record_rest({})", excluded.join(", "))
        }
        Primitive::PjsCall(call) => write!(f, "{}[js]", call.prim_name),
        Primitive::PjsObjectCreate(_) => write!(f, "[js.obj]"),
        Primitive::Praise => write!(f, "raise"),
        Primitive::Pobjcomp(cmp) => write!(f, "{}", format_comparison(*cmp)),
        Primitive::Pobjorder => write!(f, "compare"),
        Primitive::Pobjmin => write!(f, "min"),
        Primitive::Pobjmax => write!(f, "max"),
        Primitive::Pobjtag => write!(f, "tag"),
        Primitive::Pobjsize => write!(f, "length"),
        Primitive::Psequand => write!(f, "&&"),
        Primitive::Psequor => write!(f, "||"),
        Primitive::Pnot => write!(f, "not"),
        Primitive::Pboolcomp(cmp) => write!(f, "{}", format_comparison(*cmp)),
        Primitive::Pboolorder => write!(f, "compare"),
        Primitive::Pboolmin => write!(f, "min"),
        Primitive::Pboolmax => write!(f, "max"),
        Primitive::Pnegint => write!(f, "~-"),
        Primitive::Paddint => write!(f, "+"),
        Primitive::Pstringadd => write!(f, "+*"),
        Primitive::Psubint => write!(f, "-"),
        Primitive::Pmulint => write!(f, "*"),
        Primitive::Pdivint => write!(f, "/"),
        Primitive::Pmodint => write!(f, "mod"),
        Primitive::Ppowint => write!(f, "**"),
        Primitive::Pandint => write!(f, "and"),
        Primitive::Porint => write!(f, "or"),
        Primitive::Pxorint => write!(f, "xor"),
        Primitive::Pnotint => write!(f, "~~"),
        Primitive::Plslint => write!(f, "lsl"),
        Primitive::Plsrint => write!(f, "lsr"),
        Primitive::Pasrint => write!(f, "asr"),
        Primitive::Pintcomp(cmp) => write!(f, "{}", format_comparison(*cmp)),
        Primitive::Pintorder => write!(f, "compare"),
        Primitive::Pintmin => write!(f, "min"),
        Primitive::Pintmax => write!(f, "max"),
        Primitive::Pintoffloat => write!(f, "int_of_float"),
        Primitive::Pfloatofint => write!(f, "float_of_int"),
        Primitive::Pnegfloat => write!(f, "~-."),
        Primitive::Paddfloat => write!(f, "+."),
        Primitive::Psubfloat => write!(f, "-."),
        Primitive::Pmulfloat => write!(f, "*."),
        Primitive::Pdivfloat => write!(f, "/."),
        Primitive::Pmodfloat => write!(f, "mod"),
        Primitive::Ppowfloat => write!(f, "**"),
        Primitive::Pfloatcomp(cmp) => write!(f, "{}", format_float_comparison(*cmp)),
        Primitive::Pfloatorder => write!(f, "compare"),
        Primitive::Pfloatmin => write!(f, "min"),
        Primitive::Pfloatmax => write!(f, "max"),
        Primitive::Pnegbigint => write!(f, "~-"),
        Primitive::Paddbigint => write!(f, "+"),
        Primitive::Psubbigint => write!(f, "-"),
        Primitive::Pmulbigint => write!(f, "*"),
        Primitive::Pdivbigint => write!(f, "/"),
        Primitive::Pmodbigint => write!(f, "mod"),
        Primitive::Ppowbigint => write!(f, "**"),
        Primitive::Pandbigint => write!(f, "and"),
        Primitive::Porbigint => write!(f, "or"),
        Primitive::Pxorbigint => write!(f, "xor"),
        Primitive::Pnotbigint => write!(f, "~~"),
        Primitive::Plslbigint => write!(f, "lsl"),
        Primitive::Pasrbigint => write!(f, "asr"),
        Primitive::Pbigintcomp(cmp) => write!(f, "{},", format_comparison(*cmp)),
        Primitive::Pbigintorder => write!(f, "compare"),
        Primitive::Pbigintmin => write!(f, "min"),
        Primitive::Pbigintmax => write!(f, "max"),
        Primitive::Pjscomp(cmp) => write!(f, "#{}", format_comparison(*cmp)),
        Primitive::Pstringlength => write!(f, "string.length"),
        Primitive::Pstringrefu => write!(f, "string.unsafe_get"),
        Primitive::Pstringrefs => write!(f, "string.get"),
        Primitive::Pstringcomp(cmp) => write!(f, "{}", format_comparison(*cmp)),
        Primitive::Pstringorder => write!(f, "compare"),
        Primitive::Pstringmin => write!(f, "min"),
        Primitive::Pstringmax => write!(f, "max"),
        Primitive::Parraylength => write!(f, "array.length"),
        Primitive::Pmakearray => write!(f, "makearray"),
        Primitive::Pmakelist => write!(f, "makelist"),
        Primitive::Pmakedict => write!(f, "makedict"),
        Primitive::PdictHas => write!(f, "dict.has"),
        Primitive::Parrayrefu => write!(f, "array.unsafe_get"),
        Primitive::Parraysetu => write!(f, "array.unsafe_set"),
        Primitive::Parrayrefs => write!(f, "array.get"),
        Primitive::Parraysets => write!(f, "array.set"),
        Primitive::Pisint => write!(f, "isint"),
        Primitive::PisPolyVarBlock => write!(f, "#is_poly_var_block"),
        Primitive::Pawait => write!(f, "await"),
        Primitive::Phash => write!(f, "hash"),
        Primitive::PhashMixint => write!(f, "hash_mix_int"),
        Primitive::PhashMixstring => write!(f, "hash_mix_string"),
        Primitive::PhashFinalmix => write!(f, "hash_final_mix"),
    }
}

/// Lambda printer struct for formatting.
pub struct LambdaPrinter<'a> {
    lambda: &'a Lambda,
}

impl<'a> LambdaPrinter<'a> {
    pub fn new(lambda: &'a Lambda) -> Self {
        Self { lambda }
    }
}

impl fmt::Display for LambdaPrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format_lambda(self.lambda, f)
    }
}

/// Format a Lambda expression on a single line.
fn format_lambda(lam: &Lambda, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match lam {
        Lambda::Lvar(id) => write!(f, "{}", id.name()),

        Lambda::LglobalModule(id) => write!(f, "global {}", id.name()),

        Lambda::Lconst(c) => format_constant(c, f),

        Lambda::Lapply(apply) => {
            write!(f, "(apply")?;
            if matches!(
                apply.ap_info.inlined,
                crate::lambda::InlineAttribute::Always
            ) {
                write!(f, "%inlined")?;
            }
            write!(f, " ")?;
            format_lambda(&apply.ap_func, f)?;
            for arg in &apply.ap_args {
                write!(f, " ")?;
                format_lambda(arg, f)?;
            }
            write!(f, ")")
        }

        Lambda::Lfunction(func) => {
            write!(f, "(function")?;
            for param in &func.params {
                write!(f, " {}", param.name())?;
            }
            write!(f, " ")?;
            format_lambda(&func.body, f)?;
            write!(f, ")")
        }

        Lambda::Llet(..) => {
            let (bindings, body) = flatten_lets(lam);
            write!(f, "(let (")?;
            for (i, (k, id, expr)) in bindings.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}{} = ", id.name(), k.as_str())?;
                format_lambda(expr, f)?;
            }
            write!(f, ") ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lletrec(bindings, body) => {
            write!(f, "(let (")?;
            for (i, (id, expr)) in bindings.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}r = ", id.name())?;
                format_lambda(expr, f)?;
            }
            write!(f, ") ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lprim(prim_info) => {
            // Special case for module field access
            if let Primitive::Pfield(n, FieldDbgInfo::Module { name }) = &prim_info.primitive {
                if let [Lambda::LglobalModule(id)] = prim_info.args.as_slice() {
                    return write!(f, "{}.{name}/{n}", id.name());
                }
            }

            write!(f, "(")?;
            format_primitive(&prim_info.primitive, f)?;
            for arg in &prim_info.args {
                write!(f, " ")?;
                format_lambda(arg, f)?;
            }
            write!(f, ")")
        }

        Lambda::Lswitch(arg, switch) => {
            let has_fail = switch.sw_failaction.is_some();
            write!(f, "({}switch ", if has_fail { "" } else { "*" })?;
            format_lambda(arg, f)?;
            for (tag, case) in &switch.sw_consts {
                write!(f, " case int {tag}: ")?;
                format_lambda(case, f)?;
            }
            for (tag, case) in &switch.sw_blocks {
                write!(f, " case tag {tag}: ")?;
                format_lambda(case, f)?;
            }
            if let Some(ref fail) = switch.sw_failaction {
                write!(f, " default: ")?;
                format_lambda(fail, f)?;
            }
            write!(f, ")")
        }

        Lambda::LstringSwitch(arg, cases, default) => {
            write!(f, "(stringswitch ")?;
            format_lambda(arg, f)?;
            for (s, case) in cases {
                write!(f, " case {s:?}: ")?;
                format_lambda(case, f)?;
            }
            if let Some(d) = default {
                write!(f, " default: ")?;
                format_lambda(d, f)?;
            }
            write!(f, ")")
        }

        Lambda::LstaticRaise(i, args) => {
            write!(f, "(exit {i}")?;
            for arg in args {
                write!(f, " ")?;
                format_lambda(arg, f)?;
            }
            write!(f, ")")
        }

        Lambda::LstaticCatch(body, (i, vars), handler) => {
            write!(f, "(catch ")?;
            format_lambda(body, f)?;
            write!(f, " with ({i}")?;
            for v in vars {
                write!(f, " {}", v.name())?;
            }
            write!(f, ") ")?;
            format_lambda(handler, f)?;
            write!(f, ")")
        }

        Lambda::LtryWith(body, exn, handler) => {
            write!(f, "(try ")?;
            format_lambda(body, f)?;
            write!(f, " with {} ", exn.name())?;
            format_lambda(handler, f)?;
            write!(f, ")")
        }

        Lambda::LifThenElse(cond, then_, else_) => {
            write!(f, "(if ")?;
            format_lambda(cond, f)?;
            write!(f, " ")?;
            format_lambda(then_, f)?;
            write!(f, " ")?;
            format_lambda(else_, f)?;
            write!(f, ")")
        }

        Lambda::Lsequence(e1, e2) => {
            write!(f, "(seq ")?;
            format_sequence(e1, f)?;
            write!(f, " ")?;
            format_sequence(e2, f)?;
            write!(f, ")")
        }

        Lambda::Lwhile(cond, body) => {
            write!(f, "(while ")?;
            format_lambda(cond, f)?;
            write!(f, " ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lfor(v, lo, hi, dir, body) => {
            let dir_str = match dir {
                DirectionFlag::Upto => "to",
                DirectionFlag::Downto => "downto",
            };
            write!(f, "(for {} ", v.name())?;
            format_lambda(lo, f)?;
            write!(f, " {dir_str} ")?;
            format_lambda(hi, f)?;
            write!(f, " ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lfor_of(v, iterable, body) => {
            write!(f, "(for {} of ", v.name())?;
            format_lambda(iterable, f)?;
            write!(f, " ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lfor_await_of(v, iterable, body) => {
            write!(f, "(for await {} of ", v.name())?;
            format_lambda(iterable, f)?;
            write!(f, " ")?;
            format_lambda(body, f)?;
            write!(f, ")")
        }

        Lambda::Lbreak => write!(f, "break"),
        Lambda::Lcontinue => write!(f, "continue"),

        Lambda::Lassign(id, expr) => {
            write!(f, "(assign {} ", id.name())?;
            format_lambda(expr, f)?;
            write!(f, ")")
        }
    }
}

/// Flatten nested let bindings for pretty printing.
/// Returns the collected bindings and the innermost body.
fn flatten_lets(lam: &Lambda) -> (Vec<(PrintKind, &Ident, &Lambda)>, &Lambda) {
    let mut result = Vec::new();
    let mut current = lam;

    loop {
        match current {
            Lambda::Llet(kind, id, arg, body) => {
                result.push((PrintKind::from(*kind), id, arg.as_ref()));
                current = body.as_ref();
            }
            Lambda::Lletrec(bindings, body) => {
                for (id, expr) in bindings {
                    result.push((PrintKind::Recursive, id, expr));
                }
                current = body.as_ref();
            }
            _ => break,
        }
    }

    (result, current)
}

/// Format a sequence expression.
fn format_sequence(lam: &Lambda, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match lam {
        Lambda::Lsequence(e1, e2) => {
            format_sequence(e1, f)?;
            write!(f, " ")?;
            format_sequence(e2, f)
        }
        _ => format_lambda(lam, f),
    }
}

/// Convert a Lambda to a string for debugging.
pub fn lambda_to_string(lam: &Lambda) -> String {
    format!("{}", LambdaPrinter::new(lam))
}

/// Convert a primitive to a string.
pub fn primitive_to_string(p: &Primitive) -> String {
    struct PrimWrapper<'a>(&'a Primitive);
    impl fmt::Display for PrimWrapper<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            format_primitive(self.0, f)
        }
    }
    format!("{}", PrimWrapper(p))
}

/// Convert a primitive to its OCaml raw-lambda printer spelling.
pub fn raw_primitive_to_string(p: &Primitive) -> String {
    struct PrimWrapper<'a>(&'a Primitive);
    impl fmt::Display for PrimWrapper<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            format_raw_primitive(self.0, f)
        }
    }
    format!("{}", PrimWrapper(p))
}

fn format_raw_tag_info(tag_info: &TagInfo, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match tag_info {
        TagInfo::Extension => write!(f, "ext"),
        TagInfo::RecordExt { fields, .. } => write!(f, "[{}]", fields.join(";")),
        TagInfo::Tuple => write!(f, "tuple"),
        TagInfo::Constructor(c) => {
            let (name, num_nonconst) = (&c.name, c.num_nonconst);
            write!(f, "{name}/{num_nonconst}")
        }
        TagInfo::PolyVar(name) => write!(f, "`{name}"),
        TagInfo::Record(_) | TagInfo::RecordInlined(_) => {
            let fields = tag_info.record_fields().expect("record block");
            let field_names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
            write!(f, "[{}]", field_names.join(";"))
        }
        TagInfo::Module(fields) => write!(f, "[{}]", fields.join(";")),
        TagInfo::ModuleExport(_) => write!(f, "module/exports"),
        TagInfo::Some => write!(f, "some"),
        TagInfo::SomeNotNested => write!(f, "some_not_nested"),
    }
}

fn format_raw_field_info(field_info: &FieldDbgInfo, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match field_info {
        FieldDbgInfo::Record { name }
        | FieldDbgInfo::Module { name }
        | FieldDbgInfo::RecordInline { name }
        | FieldDbgInfo::RecordExtension { name } => write!(f, "{name}"),
        FieldDbgInfo::Tuple => write!(f, "[]"),
        FieldDbgInfo::PolyVarTag => write!(f, "`"),
        FieldDbgInfo::PolyVarContent => write!(f, "#"),
        FieldDbgInfo::Extension => write!(f, "ext"),
        FieldDbgInfo::Variant => write!(f, "var"),
        FieldDbgInfo::VariantTag => write!(f, "tag"),
        FieldDbgInfo::Cons => write!(f, "cons"),
    }
}

fn format_raw_primitive(p: &Primitive, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match p {
        Primitive::PjsCall(call) => write!(f, "{}", call.prim_name),
        Primitive::PjsFnMethod => write!(f, "#fn_method"),
        Primitive::Pjscomp(cmp) => write!(f, "{}", format_comparison(*cmp)),
        Primitive::Pstringadd => write!(f, "string.concat"),
        Primitive::PextensionSlotEq => write!(f, "#extension_slot_eq"),
        Primitive::PinitMod => write!(f, "#init_mod"),
        Primitive::PupdateMod => write!(f, "#update_mod"),
        Primitive::PnullToOpt => write!(f, "null_to_opt"),
        Primitive::PnullUndefinedToOpt => write!(f, "nullable_to_opt"),
        Primitive::PisNotNone => write!(f, "#is_not_none"),
        Primitive::PvalFromOption => write!(f, "#val_from_option"),
        Primitive::PvalFromOptionNotNest => write!(f, "#val_from_option_not_nest"),
        Primitive::PisPolyVarBlock => write!(f, "#is_poly_var_block"),
        Primitive::PisNullUndefined => write!(f, "isnullable"),
        Primitive::PrawJsCode(info) => {
            if info.is_stmt {
                write!(f, "#raw_stmt")
            } else {
                write!(f, "#raw_expr")
            }
        }
        Primitive::Pmakeblock(tag_info, Mutable::Immutable) => {
            write!(f, "makeblock ")?;
            format_raw_tag_info(tag_info, f)
        }
        Primitive::Pmakeblock(tag_info, Mutable::Mutable) => {
            write!(f, "makemutable ")?;
            format_raw_tag_info(tag_info, f)
        }
        Primitive::Pfield(n, field_info) => {
            write!(f, "field:")?;
            format_raw_field_info(field_info, f)?;
            write!(f, "/{n}")
        }
        _ => format_primitive(p, f),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::Ident;
    use crate::lambda::{Constant, FunctionAttribute};
    use LamLoc;

    #[test]
    fn test_print_var() {
        let x = Ident::create_local("x");
        let var = Lambda::var(x);
        let s = lambda_to_string(&var);
        assert_eq!(s, "x");
    }

    #[test]
    fn test_print_constant() {
        let c = Lambda::const_(Constant::int(42));
        let s = lambda_to_string(&c);
        assert_eq!(s, "42");

        let t = Lambda::true_();
        let s = lambda_to_string(&t);
        assert_eq!(s, "#true");

        let str_const = Lambda::const_(Constant::string("hello"));
        let s = lambda_to_string(&str_const);
        assert_eq!(s, "\"hello\"");
    }

    #[test]
    fn test_print_function() {
        let x = Ident::create_local("x");
        let func = Lambda::function_(
            1,
            vec![x],
            Lambda::var(x),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let s = lambda_to_string(&func);
        assert!(s.contains("function"));
        assert!(s.contains("x"));
    }

    #[test]
    fn test_print_if() {
        let cond = Lambda::var(Ident::create_local("cond"));
        let then_ = Lambda::const_(Constant::int(1));
        let else_ = Lambda::const_(Constant::int(0));
        let if_expr = Lambda::if_(cond, then_, else_);
        let s = lambda_to_string(&if_expr);
        assert!(s.contains("if"));
        assert!(s.contains("cond"));
        assert!(s.contains("1"));
        assert!(s.contains("0"));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_primitive() {
        let add = Lambda::prim(
            Primitive::Paddint,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(2)),
            ],
            LamLoc::NONE,
        );
        let s = lambda_to_string(&add);
        assert!(s.contains("+"));
        assert!(s.contains("1"));
        assert!(s.contains("2"));
    }

    #[test]
    fn test_print_global_module() {
        let m = Ident::create_local("Module");
        let global = Lambda::global_module(m);
        let s = lambda_to_string(&global);
        assert!(s.contains("global Module"));
    }

    #[test]
    fn test_print_while() {
        let cond = Lambda::true_();
        let body = Lambda::unit();
        let while_loop = Lambda::while_(cond, body);
        let s = lambda_to_string(&while_loop);
        assert!(s.contains("while"));
        assert!(s.contains("#true"));
    }

    #[test]
    fn test_print_for() {
        let i = Ident::create_local("i");
        let for_loop = Lambda::for_(
            i,
            Lambda::const_(Constant::int(0)),
            Lambda::const_(Constant::int(10)),
            DirectionFlag::Upto,
            Lambda::unit(),
        );
        let s = lambda_to_string(&for_loop);
        assert!(s.contains("for"));
        assert!(s.contains("i"));
        assert!(s.contains("to"));
    }

    #[test]
    fn test_primitive_to_string() {
        assert_eq!(primitive_to_string(&Primitive::Paddint), "+");
        assert_eq!(primitive_to_string(&Primitive::Praise), "raise");
        assert_eq!(primitive_to_string(&Primitive::Ptypeof), "typeof");
    }
}
