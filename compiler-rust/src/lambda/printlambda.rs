//! `Printlambda` (compiler/ml/printlambda.ml): the `-drawlambda` printer of
//! the Lambda that `Translmod.transl_implementation` returns, laid out with
//! the same Format boxes.

use std::io::Write;

use crate::ident::Ident;
use crate::lambda::lam_compat::{Comparison, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::{ImportSource, Primitive};
use crate::lambda::{
    DirectionFlag, FieldDbgInfo, FunctionAttribute, InlineAttribute, Lambda, LambdaSwitch,
    SwitchKey, TagInfo,
};
use crate::parser::ast::MutableFlag;
use crate::parser::formatter::{BoxKind, Formatter};
use crate::types::VariantConstructorCase;

/// `Printlambda.lambda` on a fresh formatter (margin 78), flushed.
pub fn print_lambda(lambda: &Lambda, out: &mut impl Write) {
    let mut f = Formatter::new(out);
    lam(&mut f, lambda);
    f.flush();
}

fn ident<W: Write>(f: &mut Formatter<W>, id: &Ident) {
    f.print(format_args!("{id:?}"));
}

/// OCaml `%S`: `String.escaped` in double quotes. Strings hold one char per
/// byte.
fn quoted_string<W: Write>(f: &mut Formatter<W>, s: &str) {
    f.string("\"");
    escaped(f, s);
    f.string("\"");
}

/// OCaml `String.escaped`.
fn escaped<W: Write>(f: &mut Formatter<W>, s: &str) {
    for ch in s.chars() {
        let byte = ch as u32;
        match byte {
            0x22 => f.string("\\\""),
            0x5C => f.string("\\\\"),
            0x0A => f.string("\\n"),
            0x0D => f.string("\\r"),
            0x09 => f.string("\\t"),
            0x08 => f.string("\\b"),
            0x20..=0x7e => f.print(format_args!("{ch}")),
            _ => f.print(format_args!("\\{:03}", byte & 0xFF)),
        }
    }
}

/// `Ext_util.string_of_int_as_char` (compiler/ext/ext_util.ml:36-53).
fn string_of_int_as_char(i: i32) -> String {
    if (0..=255).contains(&i) {
        // `%C`: `Char.escaped` in single quotes.
        let escaped = match i as u8 {
            b'\'' => "\\'".to_string(),
            b'\\' => "\\\\".to_string(),
            b'\n' => "\\n".to_string(),
            b'\t' => "\\t".to_string(),
            b'\r' => "\\r".to_string(),
            8 => "\\b".to_string(),
            c @ b' '..=b'~' => (c as char).to_string(),
            c => format!("\\{c:03}"),
        };
        return format!("'{escaped}'");
    }
    let s = match char::from_u32(i as u32) {
        Some(c) => c.to_string(),
        None => format!("\\u{{{i:X}}}"),
    };
    format!("'{s}'")
}

/// `Lambda.tag_label_of_tag_info`.
fn tag_label(tag_info: &TagInfo) -> &str {
    tag_info.tag_label()
}

/// `struct_const`.
fn struct_const<W: Write>(f: &mut Formatter<W>, cst: &Constant) {
    match cst {
        Constant::Int { i, .. } => f.print(format_args!("{i}")),
        Constant::NativeInt { i, .. } => f.print(format_args!("{i}")),
        Constant::Char(i) => f.string(&string_of_int_as_char(*i)),
        Constant::String(s) | Constant::ImmString(s) => quoted_string(f, s),
        Constant::Float(s) => f.string(s),
        Constant::BigInt { negative, value } => {
            f.print(format_args!("{}{value}n", if *negative { "-" } else { "" }))
        }
        Constant::Constructor(tag) => f.string(&tag.name),
        Constant::Pointer(name) => {
            f.string("`");
            f.string(&crate::source_text::decode_internal_utf8(name));
        }
        Constant::ModuleAlias => f.string("module_alias"),
        Constant::JsNull => f.string("null"),
        Constant::Some(inner) => {
            f.string("some(");
            struct_const(f, inner);
            f.string(")");
        }
        Constant::JsUndefined { is_unit: true } => f.string("unit"),
        Constant::JsUndefined { is_unit: false } => f.string("undefined"),
        Constant::Block { tag_info, elements } => {
            let tag = tag_label(tag_info);
            match elements.split_first() {
                None => f.print(format_args!("[{tag}]")),
                Some((first, rest)) => {
                    f.open_box(BoxKind::Box, 1);
                    f.print(format_args!("[{tag}:"));
                    f.space();
                    f.open_box(BoxKind::Box, 0);
                    struct_const(f, first);
                    for sc in rest {
                        f.space();
                        struct_const(f, sc);
                    }
                    f.close_box();
                    f.string("]");
                    f.close_box();
                }
            }
        }
        Constant::JsFalse => f.string("false"),
        Constant::JsTrue => f.string("true"),
    }
}

/// `str_of_field_info`.
fn str_of_field_info(field: &FieldDbgInfo) -> &str {
    match field {
        FieldDbgInfo::Module { name }
        | FieldDbgInfo::Record { name }
        | FieldDbgInfo::RecordInline { name }
        | FieldDbgInfo::RecordExtension { name } => name,
        FieldDbgInfo::Tuple => "[]",
        FieldDbgInfo::PolyVarTag => "`",
        FieldDbgInfo::PolyVarContent => "#",
        FieldDbgInfo::Extension => "ext",
        FieldDbgInfo::Variant => "var",
        FieldDbgInfo::VariantTag => "tag",
        FieldDbgInfo::Cons => "cons",
    }
}

/// `print_taginfo`.
fn print_taginfo<W: Write>(f: &mut Formatter<W>, tag_info: &TagInfo) {
    match tag_info {
        TagInfo::Extension => f.string("ext"),
        TagInfo::RecordExt { fields, .. } => f.print(format_args!("[{}]", fields.join(";"))),
        TagInfo::Tuple => f.string("tuple"),
        TagInfo::Constructor(c) => {
            let (name, num_nonconst) = (&c.name, c.num_nonconst);
            f.print(format_args!("{name}/{num_nonconst}"))
        }
        TagInfo::PolyVar(_) => f.string("polyvar"),
        TagInfo::Record(_) | TagInfo::RecordInlined(_) => {
            let fields = tag_info.record_fields().expect("record block");
            let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
            f.print(format_args!("[{}]", names.join(";")));
        }
        TagInfo::Module(names) => f.print(format_args!("[{}]", names.join(";"))),
        TagInfo::ModuleExport(_) => f.string("module/exports"),
        TagInfo::Some => f.string("some"),
        TagInfo::SomeNotNested => f.string("some_not_nested"),
    }
}

/// `comparison`.
fn comparison<W: Write>(f: &mut Formatter<W>, kind: &str, cmp: Comparison) {
    let op = match cmp {
        Comparison::Eq => "==",
        Comparison::Neq => "!=",
        Comparison::Lt => "<",
        Comparison::Le => "<=",
        Comparison::Gt => ">",
        Comparison::Ge => ">=",
    };
    f.print(format_args!("{op}[{kind}]"));
}

/// `primitive`.
fn primitive<W: Write>(f: &mut Formatter<W>, prim: &Primitive) {
    let s = |f: &mut Formatter<W>, text: &str| f.string(text);
    match prim {
        Primitive::Pdebugger => s(f, "debugger"),
        Primitive::Ptypeof => s(f, "typeof"),
        Primitive::Psome => s(f, "some"),
        Primitive::PsomeNotNest => s(f, "some_not_nest"),
        Primitive::Pmakeblock(tag_info, _) => {
            let what = if tag_info.mutable_flag() == MutableFlag::Immutable {
                "makeblock"
            } else {
                "makemutable"
            };
            f.print(format_args!("{what} "));
            print_taginfo(f, tag_info);
        }
        Primitive::Pfield(n, field) => {
            f.print(format_args!("field:{}/{n}", str_of_field_info(field)))
        }
        Primitive::Psetfield(n, _) => f.print(format_args!("setfield {n}")),
        Primitive::Pduprecord => s(f, "duprecord"),
        Primitive::PrecordRest(excluded) => {
            f.print(format_args!("record_rest({})", excluded.join(", ")))
        }
        Primitive::PjsCall(call) => f.print(format_args!("js_call[{}]", call.prim_name)),
        Primitive::PjsObjectCreate(_) => s(f, "js_obj_create"),
        Primitive::PjsObjectGet(name) => f.print(format_args!("js_object_get[{name}]")),
        Primitive::PjsObjectSet(name) => f.print(format_args!("js_object_set[{name}]")),
        Primitive::Praise => s(f, "raise"),
        Primitive::Pobjcomp(cmp) => comparison(f, "obj", *cmp),
        Primitive::Pobjorder => s(f, "compare"),
        Primitive::Pobjmin => s(f, "min"),
        Primitive::Pobjmax => s(f, "max"),
        Primitive::Pobjtag => s(f, "tag"),
        Primitive::Pobjsize => s(f, "length"),
        Primitive::Psequand => s(f, "&&"),
        Primitive::Psequor => s(f, "||"),
        Primitive::Pnot => s(f, "not"),
        Primitive::Pboolcomp(cmp) => comparison(f, "bool", *cmp),
        Primitive::Pboolorder => s(f, "compare"),
        Primitive::Pboolmin => s(f, "min"),
        Primitive::Pboolmax => s(f, "max"),
        Primitive::Pnegint => s(f, "~-"),
        Primitive::Paddint => s(f, "+"),
        Primitive::Psubint => s(f, "-"),
        Primitive::Pmulint => s(f, "*"),
        Primitive::Pdivint => s(f, "/"),
        Primitive::Pmodint => s(f, "mod"),
        Primitive::Ppowint => s(f, "**"),
        Primitive::Pandint => s(f, "and"),
        Primitive::Porint => s(f, "or"),
        Primitive::Pxorint => s(f, "xor"),
        Primitive::Pnotint => s(f, "~~"),
        Primitive::Plslint => s(f, "lsl"),
        Primitive::Plsrint => s(f, "lsr"),
        Primitive::Pasrint => s(f, "asr"),
        Primitive::Pintcomp(cmp) => comparison(f, "int", *cmp),
        Primitive::Pintorder => s(f, "compare"),
        Primitive::Pintmin => s(f, "min"),
        Primitive::Pintmax => s(f, "max"),
        Primitive::Pintoffloat => s(f, "int_of_float"),
        Primitive::Pfloatofint => s(f, "float_of_int"),
        Primitive::Pnegfloat => s(f, "~-."),
        Primitive::Paddfloat => s(f, "+."),
        Primitive::Psubfloat => s(f, "-."),
        Primitive::Pmulfloat => s(f, "*."),
        Primitive::Pdivfloat => s(f, "/."),
        Primitive::Pmodfloat => s(f, "mod"),
        Primitive::Ppowfloat => s(f, "**"),
        Primitive::Pfloatcomp(cmp) => comparison(f, "float", *cmp),
        Primitive::Pfloatorder => s(f, "compare"),
        Primitive::Pfloatmin => s(f, "min"),
        Primitive::Pfloatmax => s(f, "max"),
        Primitive::Pnegbigint => s(f, "~-"),
        Primitive::Paddbigint => s(f, "+"),
        Primitive::Psubbigint => s(f, "-"),
        Primitive::Pmulbigint => s(f, "*"),
        Primitive::Ppowbigint => s(f, "**"),
        Primitive::Pandbigint => s(f, "and"),
        Primitive::Porbigint => s(f, "or"),
        Primitive::Pxorbigint => s(f, "xor"),
        Primitive::Pnotbigint => s(f, "~~"),
        Primitive::Plslbigint => s(f, "lsl"),
        Primitive::Pasrbigint => s(f, "asr"),
        Primitive::Pdivbigint => s(f, "/"),
        Primitive::Pmodbigint => s(f, "mod"),
        Primitive::Pbigintcomp(cmp) => comparison(f, "bigint", *cmp),
        Primitive::Pbigintorder => s(f, "compare"),
        Primitive::Pbigintmin => s(f, "min"),
        Primitive::Pbigintmax => s(f, "max"),
        Primitive::Pstringlength => s(f, "string.length"),
        Primitive::Pstringrefu => s(f, "string.unsafe_get"),
        Primitive::Pstringrefs => s(f, "string.get"),
        Primitive::Pstringcomp(cmp) => comparison(f, "string", *cmp),
        Primitive::Pstringorder => s(f, "compare"),
        Primitive::Pstringmin => s(f, "min"),
        Primitive::Pstringmax => s(f, "max"),
        Primitive::Pstringadd => s(f, "string.concat"),
        Primitive::Parraylength => s(f, "array.length"),
        Primitive::Pmakearray => s(f, "makearray"),
        Primitive::Parrayrefu => s(f, "array.unsafe_get"),
        Primitive::Parraysetu => s(f, "array.unsafe_set"),
        Primitive::Parrayrefs => s(f, "array.get"),
        Primitive::Parraysets => s(f, "array.set"),
        Primitive::Pmakelist => s(f, "makelist"),
        Primitive::Pmakedict => s(f, "makedict"),
        Primitive::PdictHas => s(f, "dict.has"),
        Primitive::Pisint => s(f, "isint"),
        Primitive::PisNull => s(f, "is_null"),
        Primitive::PisUndefined => s(f, "is_undefined"),
        Primitive::PisNullUndefined => s(f, "isnullable"),
        Primitive::PcreateExtension(name) => f.print(format_args!("extension[{name}]")),
        Primitive::Pawait => s(f, "await"),
        Primitive::Pimport(source) => match source.as_ref() {
            ImportSource::ImportModule { module_, path } => {
                let mut parts = vec![module_.name().to_string()];
                parts.extend(path.iter().cloned());
                f.print(format_args!("import[{}]", parts.join(".")));
            }
            ImportSource::ImportExternal { module_, path } => {
                let mut parts = vec![module_.bundle.clone()];
                parts.extend(path.iter().cloned());
                f.print(format_args!("import[{}]", parts.join(".")));
            }
        },
        Primitive::PinitMod => s(f, "#init_mod"),
        Primitive::PupdateMod => s(f, "#update_mod"),
        Primitive::Phash => s(f, "hash"),
        Primitive::PhashMixint => s(f, "hash_mix_int"),
        Primitive::PhashMixstring => s(f, "hash_mix_string"),
        Primitive::PhashFinalmix => s(f, "hash_final_mix"),
        Primitive::Pjscomp(cmp) => comparison(f, "js", *cmp),
        Primitive::PnullToOpt => s(f, "null_to_opt"),
        Primitive::PnullUndefinedToOpt => s(f, "nullable_to_opt"),
        Primitive::PisNotNone => s(f, "#is_not_none"),
        Primitive::PvalFromOption => s(f, "#val_from_option"),
        Primitive::PvalFromOptionNotNest => s(f, "#val_from_option_not_nest"),
        Primitive::PisPolyVarBlock => s(f, "#is_poly_var_block"),
        Primitive::PrawJsCode(_) => s(f, "raw_js_code"),
        Primitive::PjsFnMethod => s(f, "#fn_method"),
        Primitive::PtaggedTemplate(_) => s(f, "#tagged_template"),
        Primitive::Ptemplate(_) => s(f, "#template"),
        // Rust-only primitives; OCaml's Lambda has none of these.
        Primitive::Pidentity => s(f, "#identity"),
        Primitive::Pignore => s(f, "#ignore"),
        Primitive::PextensionSlotEq => s(f, "#extension_slot_eq"),
        Primitive::PjsApply => s(f, "#apply"),
        Primitive::PfnArity => s(f, "#fn_arity"),
    }
}

/// `function_attribute`.
fn function_attribute<W: Write>(f: &mut Formatter<W>, attr: &FunctionAttribute) {
    if attr.is_a_functor {
        f.string("is_a_functor");
        f.space();
    }
    if attr.return_unit {
        f.string("void");
        f.space();
    }
    match attr.inline {
        InlineAttribute::Default => {}
        InlineAttribute::Always => {
            f.string("always_inline");
            f.space();
        }
        InlineAttribute::Never => {
            f.string("never_inline");
            f.space();
        }
    }
}

/// `apply_inlined_attribute`.
fn apply_inlined_attribute<W: Write>(f: &mut Formatter<W>, attr: InlineAttribute) {
    match attr {
        InlineAttribute::Default => {}
        InlineAttribute::Always => f.string(" always_inline"),
        InlineAttribute::Never => f.string(" never_inline"),
    }
}

fn let_kind(kind: LetKind) -> &'static str {
    match kind {
        LetKind::Alias => "a",
        LetKind::Strict => "",
        LetKind::StrictOpt => "o",
        LetKind::Variable => "v",
    }
}

/// `@[<2>(<head>@ <a>@ <b>...)@]`.
fn parenthesized<W: Write>(f: &mut Formatter<W>, head: &str, args: &[&Lambda]) {
    f.open_box(BoxKind::Box, 2);
    f.print(format_args!("({head}"));
    for arg in args {
        f.space();
        lam(f, arg);
    }
    f.string(")");
    f.close_box();
}

fn switch_cases<W: Write>(f: &mut Formatter<W>, sw: &LambdaSwitch) {
    let mut spc = false;
    let mut sep = |f: &mut Formatter<W>| {
        if spc {
            f.space();
        } else {
            spc = true;
        }
    };
    for (key, l) in &sw.sw_consts {
        sep(f);
        f.open_box(BoxKind::HV, 1);
        match key {
            SwitchKey::Int(ordinal) => f.print(format_args!("case int {ordinal}:")),
            SwitchKey::Constructor(VariantConstructorCase::Constant(tag)) => {
                f.string("case constructor ");
                quoted_string(f, &tag.name);
                f.string(":");
            }
            SwitchKey::Constructor(VariantConstructorCase::Block(_)) => {
                unreachable!("block key among constant cases")
            }
        }
        f.space();
        lam(f, l);
        f.close_box();
    }
    for (key, l) in &sw.sw_blocks {
        sep(f);
        f.open_box(BoxKind::HV, 1);
        match key {
            SwitchKey::Int(ordinal) => f.print(format_args!("case tag {ordinal}:")),
            SwitchKey::Constructor(VariantConstructorCase::Block(block)) => {
                f.string("case constructor ");
                quoted_string(f, &block.tag().name);
                f.string(":");
            }
            SwitchKey::Constructor(VariantConstructorCase::Constant(_)) => {
                unreachable!("constant key among block cases")
            }
        }
        f.space();
        lam(f, l);
        f.close_box();
    }
    if let Some(fail) = &sw.sw_failaction {
        sep(f);
        f.open_box(BoxKind::HV, 1);
        f.string("default:");
        f.space();
        lam(f, fail);
        f.close_box();
    }
}

/// `lam`.
fn lam<W: Write>(f: &mut Formatter<W>, lambda: &Lambda) {
    match lambda {
        Lambda::Lvar(id) => ident(f, id),
        Lambda::LglobalModule(id) => {
            f.string("global ");
            ident(f, id);
        }
        Lambda::Lconst(cst) => struct_const(f, cst),
        Lambda::Lapply(ap) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(apply");
            f.space();
            lam(f, &ap.ap_func);
            for arg in &ap.ap_args {
                f.space();
                lam(f, arg);
            }
            apply_inlined_attribute(f, ap.ap_info.inlined);
            f.string(")");
            f.close_box();
        }
        Lambda::Lfunction(func) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(function");
            for param in &func.params {
                f.space();
                ident(f, param);
            }
            f.space();
            function_attribute(f, &func.attr);
            lam(f, &func.body);
            f.string(")");
            f.close_box();
        }
        Lambda::Llet(..) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(let");
            f.space();
            f.open_box(BoxKind::HV, 1);
            f.string("(");
            let mut current = lambda;
            let mut first = true;
            while let Lambda::Llet(kind, id, arg, body) = current {
                if !first {
                    f.space();
                }
                first = false;
                f.open_box(BoxKind::Box, 2);
                ident(f, id);
                f.print(format_args!(" ={}", let_kind(*kind)));
                f.space();
                lam(f, arg);
                f.close_box();
                current = body;
            }
            f.string(")");
            f.close_box();
            f.space();
            lam(f, current);
            f.string(")");
            f.close_box();
        }
        Lambda::Lletrec(bindings, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(letrec");
            f.space();
            f.string("(");
            f.open_box(BoxKind::HV, 1);
            let mut first = true;
            for (id, l) in bindings {
                if !first {
                    f.space();
                }
                first = false;
                f.open_box(BoxKind::Box, 2);
                ident(f, id);
                f.space();
                lam(f, l);
                f.close_box();
            }
            f.close_box();
            f.string(")");
            f.space();
            lam(f, body);
            f.string(")");
            f.close_box();
        }
        Lambda::Lprim(prim) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(");
            primitive(f, &prim.primitive);
            for arg in &prim.args {
                f.space();
                lam(f, arg);
            }
            f.string(")");
            f.close_box();
        }
        Lambda::Lswitch(arg, sw) => {
            f.open_box(BoxKind::Box, 1);
            f.string(if sw.sw_failaction.is_none() {
                "(switch* "
            } else {
                "(switch "
            });
            lam(f, arg);
            f.space();
            f.open_vbox(0);
            switch_cases(f, sw);
            f.close_box();
            f.string(")");
            f.close_box();
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            f.open_box(BoxKind::Box, 1);
            f.string("(stringswitch ");
            lam(f, arg);
            f.space();
            f.open_vbox(0);
            let mut first = true;
            for (s, l) in cases {
                if !first {
                    f.space();
                }
                first = false;
                f.open_box(BoxKind::HV, 1);
                f.string("case \"");
                escaped(f, s);
                f.string("\":");
                f.space();
                lam(f, l);
                f.close_box();
            }
            if let Some(default) = default {
                if !first {
                    f.space();
                }
                f.open_box(BoxKind::HV, 1);
                f.string("default:");
                f.space();
                lam(f, default);
                f.close_box();
            }
            f.close_box();
            f.string(")");
            f.close_box();
        }
        Lambda::LstaticRaise(i, args) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(exit");
            f.space();
            f.print(format_args!("{i}"));
            for arg in args {
                f.space();
                lam(f, arg);
            }
            f.string(")");
            f.close_box();
        }
        Lambda::LstaticCatch(body, (i, vars), handler) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(catch");
            f.space();
            lam(f, body);
            f.break_(1, -1);
            f.print(format_args!("with ({i}"));
            for var in vars {
                f.string(" ");
                ident(f, var);
            }
            f.string(")");
            f.space();
            lam(f, handler);
            f.string(")");
            f.close_box();
        }
        Lambda::LtryWith(body, param, handler) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(try");
            f.space();
            lam(f, body);
            f.break_(1, -1);
            f.string("with ");
            ident(f, param);
            f.space();
            lam(f, handler);
            f.string(")");
            f.close_box();
        }
        Lambda::LifThenElse(cond, ifso, ifnot) => parenthesized(f, "if", &[cond, ifso, ifnot]),
        Lambda::Lsequence(first, second) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(seq");
            f.space();
            lam(f, first);
            f.space();
            sequence(f, second);
            f.string(")");
            f.close_box();
        }
        Lambda::Lbreak => f.string("break"),
        Lambda::Lcontinue => f.string("continue"),
        Lambda::Lwhile(cond, body) => parenthesized(f, "while", &[cond, body]),
        Lambda::Lfor(param, lo, hi, dir, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(for ");
            ident(f, param);
            f.space();
            lam(f, lo);
            f.space();
            f.string(match dir {
                DirectionFlag::Upto => "to",
                DirectionFlag::Downto => "downto",
            });
            f.space();
            lam(f, hi);
            f.space();
            lam(f, body);
            f.string(")");
            f.close_box();
        }
        Lambda::Lfor_of(param, iterable, body) => for_of(f, "for_of", param, iterable, body),
        Lambda::Lfor_await_of(param, iterable, body) => {
            for_of(f, "for_await_of", param, iterable, body)
        }
        Lambda::Lassign(id, expr) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(assign");
            f.space();
            ident(f, id);
            f.space();
            lam(f, expr);
            f.string(")");
            f.close_box();
        }
    }
}

fn for_of<W: Write>(
    f: &mut Formatter<W>,
    head: &str,
    param: &Ident,
    iterable: &Lambda,
    body: &Lambda,
) {
    f.open_box(BoxKind::Box, 2);
    f.print(format_args!("({head} "));
    ident(f, param);
    f.space();
    lam(f, iterable);
    f.space();
    lam(f, body);
    f.string(")");
    f.close_box();
}

/// `sequence`.
fn sequence<W: Write>(f: &mut Formatter<W>, lambda: &Lambda) {
    match lambda {
        Lambda::Lsequence(first, second) => {
            sequence(f, first);
            f.space();
            sequence(f, second);
        }
        _ => lam(f, lambda),
    }
}
