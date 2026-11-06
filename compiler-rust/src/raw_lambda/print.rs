//! Raw Lambda printer.

use std::fmt;
use std::io::Write;

use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::{Constant, PointerInfo};
use crate::lambda::lam_primitive::Mutable;
use crate::lambda::lam_print::raw_primitive_to_string;
use crate::lambda::{FieldDbgInfo, FunctionAttribute, InlineAttribute, Primitive, TagInfo};
use crate::parser::formatter::{BoxKind, Formatter};
use crate::raw_lambda::{RawApply, RawLFunction, RawLambda, RawLambdaSwitch, RawPrimInfo};

/// Print a string in OCaml style: escape non-ASCII bytes as \NNN (decimal).
/// Strings are stored as Latin-1 (each char codepoint = original byte value),
/// so we iterate chars and use the codepoint as the byte value.
fn print_ocaml_string<W: Write>(f: &mut Formatter<W>, s: &str) {
    f.string("\"");
    for ch in s.chars() {
        let byte = ch as u32;
        match byte {
            0x22 /* " */ => f.string("\\\""),
            0x5C /* \ */ => f.string("\\\\"),
            0x0A /* \n */ => f.string("\\n"),
            0x0D /* \r */ => f.string("\\r"),
            0x09 /* \t */ => f.string("\\t"),
            0x20..=0x7e => f.print(format_args!("{ch}")),
            // OCaml uses decimal \NNN for non-printable/non-ASCII bytes
            _ if byte <= 0xFF => f.print(format_args!("\\{byte:03}")),
            // Shouldn't happen for Latin-1 strings, but handle gracefully
            _ => f.print(format_args!("\\x{byte:04x}")),
        }
    }
    f.string("\"");
}

/// Pretty-printer for raw lambda.
pub struct RawLambdaPrinter<'a> {
    raw: &'a RawLambda,
}

impl<'a> RawLambdaPrinter<'a> {
    /// Create a new raw-lambda printer.
    pub fn new(raw: &'a RawLambda) -> Self {
        Self { raw }
    }
}

impl fmt::Display for RawLambdaPrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = Vec::new();
        print_raw_lambda(self.raw, &mut out);
        match String::from_utf8(out) {
            Ok(s) => f.write_str(&s),
            Err(err) => f.write_str(&String::from_utf8_lossy(&err.into_bytes())),
        }
    }
}

pub fn print_raw_lambda(raw: &RawLambda, out: &mut impl Write) {
    let mut f = Formatter::new(out);
    lam(&mut f, raw, None);
    f.flush();
}

fn print_ident<W: Write>(f: &mut Formatter<W>, id: &Ident) {
    f.print(format_args!("{id:?}"));
}

fn print_function_attribute<W: Write>(f: &mut Formatter<W>, attr: &FunctionAttribute) {
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

fn let_kind_suffix(kind: LetKind) -> &'static str {
    match kind {
        LetKind::Alias => "a",
        LetKind::Strict => "",
        LetKind::StrictOpt => "o",
        LetKind::Variable => "v",
    }
}

fn print_internal_utf8<W: Write>(f: &mut Formatter<W>, s: &str) {
    f.string(&crate::source_text::decode_internal_utf8(s));
}

fn print_field_info<W: Write>(f: &mut Formatter<W>, field: &FieldDbgInfo) {
    match field {
        FieldDbgInfo::Record { name }
        | FieldDbgInfo::Module { name }
        | FieldDbgInfo::RecordInline { name }
        | FieldDbgInfo::RecordExtension { name } => f.string(name),
        FieldDbgInfo::Tuple => f.string("[]"),
        FieldDbgInfo::PolyVarTag => f.string("`"),
        FieldDbgInfo::PolyVarContent => f.string("#"),
        FieldDbgInfo::Extension => f.string("ext"),
        FieldDbgInfo::Variant => f.string("var"),
        FieldDbgInfo::VariantTag => f.string("tag"),
        FieldDbgInfo::Cons => f.string("cons"),
    }
}

fn print_tag_info<W: Write>(f: &mut Formatter<W>, tag_info: &TagInfo) {
    match tag_info {
        TagInfo::Extension => f.string("ext"),
        TagInfo::RecordExt { fields, .. } => {
            f.string("[");
            f.string(&fields.join(";"));
            f.string("]");
        }
        TagInfo::Tuple => f.string("tuple"),
        TagInfo::Constructor {
            name, num_nonconst, ..
        } => f.print(format_args!("{name}/{num_nonconst}")),
        TagInfo::PolyVar(name) => {
            f.string("`");
            print_internal_utf8(f, name);
        }
        TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. } => {
            let names = fields
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(";");
            f.string("[");
            f.string(&names);
            f.string("]");
        }
        TagInfo::Module(fields) => {
            f.string("[");
            f.string(&fields.join(";"));
            f.string("]");
        }
        TagInfo::Some => f.string("some"),
        TagInfo::SomeNotNested => f.string("some_not_nested"),
        TagInfo::ModuleExport(_) => f.string("module/exports"),
    }
}

fn print_struct_const<W: Write>(f: &mut Formatter<W>, cst: &Constant) {
    match cst {
        Constant::Int { i, comment } => match comment.as_deref() {
            Some(PointerInfo::ShapeNone) => f.string("shape_none"),
            Some(PointerInfo::Constructor(tag)) => f.print(format_args!("`{}", tag.name)),
            Some(PointerInfo::PolyVariant(name)) => {
                f.string("`");
                print_internal_utf8(f, name);
            }
            _ => f.print(format_args!("{i}")),
        },
        Constant::NativeInt { i, .. } => f.print(format_args!("{i}")),
        Constant::Constructor(tag) => f.print(format_args!("`{}", tag.name)),
        Constant::Char(i) => {
            if let Some(ch) = char::from_u32(*i as u32) {
                f.print(format_args!("{ch:?}"));
            } else {
                f.print(format_args!("'\\x{i:02x}'"));
            }
        }
        Constant::String(s) => print_ocaml_string(f, s),
        Constant::ImmString(s) => {
            f.string("#");
            print_ocaml_string(f, s);
        }
        Constant::Float(s) => f.string(s),
        Constant::BigInt { negative, value } => {
            if *negative {
                f.print(format_args!("-{value}n"));
            } else {
                f.print(format_args!("{value}n"));
            }
        }
        Constant::Pointer(name) => print_internal_utf8(f, name),
        Constant::Block { tag_info, elements } if elements.is_empty() => match &**tag_info {
            TagInfo::Constructor { name, .. } | TagInfo::RecordInlined { name, .. } => {
                f.print(format_args!("[{name}]"))
            }
            _ => f.print(format_args!("[{}]", tag_info.tag_label())),
        },
        Constant::Block { tag_info, elements } => {
            f.open_box(BoxKind::Box, 1);
            match &**tag_info {
                TagInfo::Constructor { name, .. } | TagInfo::RecordInlined { name, .. } => {
                    f.print(format_args!("[{name}:"))
                }
                _ => f.print(format_args!("[{}:", tag_info.tag_label())),
            }
            f.space();
            f.open_box(BoxKind::HOV, 0);
            if let Some((first, rest)) = elements.split_first() {
                print_struct_const(f, first);
                for elem in rest {
                    f.space();
                    print_struct_const(f, elem);
                }
            }
            f.close_box();
            f.string("]");
            f.close_box();
        }
        Constant::JsFalse => f.string("false"),
        Constant::JsTrue => f.string("true"),
        Constant::JsUndefined { is_unit: true } => f.string("`()"),
        Constant::JsUndefined { is_unit: false } => f.string("undefined"),
        Constant::JsNull => f.string("null"),
        Constant::Some(inner) => print_struct_const(f, inner),
        Constant::ModuleAlias => f.string("module_alias"),
    }
}

fn print_primitive<W: Write>(f: &mut Formatter<W>, prim: &Primitive) {
    match prim {
        Primitive::PjsCall { prim_name, .. } => f.string(prim_name),
        Primitive::PrawJsCode(info) => {
            if info.is_stmt {
                f.string("#raw_stmt");
            } else {
                f.string("#raw_expr");
            }
        }
        Primitive::PjsFnMethod => f.string("#fn_method"),
        Primitive::PcreateExtension(name) => f.print(format_args!("extension[{name}]")),
        Primitive::Pmakeblock(tag_info, Mutable::Immutable)
        | Primitive::Pmakeblock(tag_info, Mutable::Mutable) => {
            f.string("makeblock ");
            print_tag_info(f, tag_info);
        }
        Primitive::Pfield(n, field_info) => {
            f.string("field:");
            print_field_info(f, field_info);
            f.print(format_args!("/{n}"));
        }
        Primitive::Psetfield(n, _) => f.print(format_args!("setfield {n}")),
        _ => f.string(&raw_primitive_to_string(prim)),
    }
}

fn print_apply<W: Write>(f: &mut Formatter<W>, apply: &RawApply, reraise_exn: Option<&Ident>) {
    f.open_box(BoxKind::Box, 2);
    f.string("(apply");
    f.space();
    lam(f, &apply.ap_func, reraise_exn);
    for arg in &apply.ap_args {
        f.space();
        lam(f, arg, reraise_exn);
    }
    f.string(")");
    f.close_box();
}

fn print_function<W: Write>(
    f: &mut Formatter<W>,
    func: &RawLFunction,
    reraise_exn: Option<&Ident>,
) {
    f.open_box(BoxKind::Box, 2);
    f.string("(function");
    for param in &func.params {
        f.space();
        print_ident(f, param);
    }
    f.space();
    print_function_attribute(f, &func.attr);
    lam(f, &func.body, reraise_exn);
    f.string(")");
    f.close_box();
}

fn print_let_bindings<'a, W: Write>(
    f: &mut Formatter<W>,
    lam0: &'a RawLambda,
    reraise_exn: Option<&Ident>,
) -> &'a RawLambda {
    let mut current = lam0;
    let mut first = true;
    while let RawLambda::Llet(kind, id, arg, body) = current {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::Box, 2);
        print_ident(f, id);
        f.string(" =");
        f.string(let_kind_suffix(*kind));
        f.space();
        lam(f, arg, reraise_exn);
        f.close_box();
        current = body;
        first = false;
    }
    current
}

fn print_switch_cases_with_exn<W: Write>(
    f: &mut Formatter<W>,
    sw: &RawLambdaSwitch,
    reraise_exn: Option<&Ident>,
) {
    let mut first = true;
    for (n, l) in &sw.sw_consts {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::HV, 1);
        match n {
            crate::lambda::SwitchKey::Int(value) => f.print(format_args!("case int {value}:")),
            crate::lambda::SwitchKey::Constructor(
                crate::types::VariantConstructorCase::Constant(tag),
            ) => f.print(format_args!("case constructor {:?}:", tag.name)),
            crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                _,
            )) => unreachable!("block key in constant cases"),
        }
        f.space();
        lam(f, l, reraise_exn);
        f.close_box();
        first = false;
    }
    for (n, l) in &sw.sw_blocks {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::HV, 1);
        match n {
            crate::lambda::SwitchKey::Int(value) => f.print(format_args!("case tag {value}:")),
            crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                block,
            )) => f.print(format_args!("case constructor {:?}:", block.tag().name)),
            crate::lambda::SwitchKey::Constructor(
                crate::types::VariantConstructorCase::Constant(_),
            ) => unreachable!("constant key in block cases"),
        }
        f.space();
        lam(f, l, reraise_exn);
        f.close_box();
        first = false;
    }
    if let Some(fail) = &sw.sw_failaction {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::HV, 1);
        f.string("default:");
        f.space();
        lam(f, fail, reraise_exn);
        f.close_box();
    }
}

fn print_string_switch_cases_with_exn<W: Write>(
    f: &mut Formatter<W>,
    cases: &[(String, RawLambda)],
    default: &Option<Box<RawLambda>>,
    reraise_exn: Option<&Ident>,
) {
    let mut first = true;
    for (s, l) in cases {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::HV, 1);
        f.string("case ");
        print_ocaml_string(f, s);
        f.string(":");
        f.space();
        lam(f, l, reraise_exn);
        f.close_box();
        first = false;
    }
    if let Some(default) = default {
        if !first {
            f.space();
        }
        f.open_box(BoxKind::HV, 1);
        f.string("default:");
        f.space();
        lam(f, default, reraise_exn);
        f.close_box();
    }
}

fn sequence<W: Write>(f: &mut Formatter<W>, lam0: &RawLambda, reraise_exn: Option<&Ident>) {
    match lam0 {
        RawLambda::Lsequence(first, second) => {
            sequence(f, first, reraise_exn);
            f.space();
            sequence(f, second, reraise_exn);
        }
        _ => lam(f, lam0, reraise_exn),
    }
}

fn lam<W: Write>(f: &mut Formatter<W>, lam0: &RawLambda, reraise_exn: Option<&Ident>) {
    match lam0 {
        RawLambda::Lshared(inner) => lam(f, inner, reraise_exn),
        RawLambda::Lvar(id) => print_ident(f, id),
        RawLambda::LglobalModule(id) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(");
            f.string("global ");
            print_ident(f, id);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lconst(cst) => print_struct_const(f, cst),
        RawLambda::Lapply(apply) => print_apply(f, apply, reraise_exn),
        RawLambda::Lfunction(func) => print_function(f, func, reraise_exn),
        RawLambda::Llet(_, _, _, _) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(let");
            f.space();
            f.open_box(BoxKind::HV, 1);
            f.string("(");
            let body = print_let_bindings(f, lam0, reraise_exn);
            f.string(")");
            f.close_box();
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lletrec(bindings, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(letrec");
            f.space();
            f.string("(");
            f.open_box(BoxKind::HV, 1);
            let mut first = true;
            for (id, expr) in bindings {
                if !first {
                    f.space();
                }
                f.open_box(BoxKind::Box, 2);
                print_ident(f, id);
                f.space();
                lam(f, expr, reraise_exn);
                f.close_box();
                first = false;
            }
            f.close_box();
            f.string(")");
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lprim(__prim0) => {
            let RawPrimInfo {
                primitive,
                args,
                loc: _,
            } = __prim0.as_ref();

            if matches!(primitive, Primitive::Praise) {
                if let ([RawLambda::Lvar(id)], Some(exn_id)) = (args.as_slice(), reraise_exn) {
                    if id.same(exn_id) {
                        f.open_box(BoxKind::Box, 2);
                        f.string("(reraise");
                        f.space();
                        print_ident(f, id);
                        f.string(")");
                        f.close_box();
                        return;
                    }
                }
            }
            f.open_box(BoxKind::Box, 2);
            f.string("(");
            print_primitive(f, primitive);
            for arg in args {
                f.space();
                lam(f, arg, reraise_exn);
            }
            f.string(")");
            f.close_box();
        }
        RawLambda::Lswitch(arg, sw) => {
            f.open_box(BoxKind::Box, 1);
            if sw.sw_failaction.is_some() {
                f.string("(switch");
            } else {
                f.string("(switch*");
            }
            // OCaml lam_print.ml keeps the operator and scrutinee on the
            // same line; only the break before the cases is conditional.
            f.string(" ");
            lam(f, arg, reraise_exn);
            f.space();
            f.open_vbox(0);
            print_switch_cases_with_exn(f, sw, reraise_exn);
            f.close_box();
            f.string(")");
            f.close_box();
        }
        RawLambda::LstringSwitch(arg, cases, default) => {
            f.open_box(BoxKind::Box, 1);
            f.string("(stringswitch ");
            lam(f, arg, reraise_exn);
            f.space();
            f.open_vbox(0);
            print_string_switch_cases_with_exn(f, cases, default, reraise_exn);
            f.close_box();
            f.string(")");
            f.close_box();
        }
        RawLambda::LstaticRaise(i, ls) => {
            f.open_box(BoxKind::Box, 2);
            f.print(format_args!("(exit {i}"));
            for l in ls {
                f.space();
                lam(f, l, reraise_exn);
            }
            f.string(")");
            f.close_box();
        }
        RawLambda::LstaticCatch(body, (i, vars), handler) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(catch");
            f.space();
            lam(f, body, reraise_exn);
            f.break_(1, -1);
            f.print(format_args!("with ({i}"));
            for var in vars {
                f.string(" ");
                print_ident(f, var);
            }
            f.string(")");
            f.space();
            lam(f, handler, reraise_exn);
            f.string(")");
            f.close_box();
        }
        // printlambda.ml: "@[<2>(try@ %a@;<1 -1>finally@ %a)@]"
        RawLambda::LtryFinally(body, finally) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(try");
            f.space();
            lam(f, body, None);
            f.break_(1, -1);
            f.string("finally");
            f.space();
            lam(f, finally, None);
            f.string(")");
            f.close_box();
        }
        RawLambda::LtryWith(body, param, handler) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(try");
            f.space();
            lam(f, body, None);
            f.break_(1, -1);
            f.string("with ");
            print_ident(f, param);
            f.space();
            lam(f, handler, Some(param));
            f.string(")");
            f.close_box();
        }
        RawLambda::LifThenElse(cond, ifso, ifnot) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(if");
            f.space();
            lam(f, cond, reraise_exn);
            f.space();
            lam(f, ifso, reraise_exn);
            f.space();
            lam(f, ifnot, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lsequence(first, second) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(seq");
            f.space();
            // OCaml's printlambda uses `lam` for the first element (preserving
            // nested seq structure) and `sequence` for the second (flattening).
            lam(f, first, reraise_exn);
            f.space();
            sequence(f, second, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lwhile(cond, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(while");
            f.space();
            lam(f, cond, reraise_exn);
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lfor(param, lo, hi, dir, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(for ");
            print_ident(f, param);
            f.space();
            lam(f, lo, reraise_exn);
            f.space();
            f.string(match dir {
                crate::lambda::DirectionFlag::Upto => "to",
                crate::lambda::DirectionFlag::Downto => "downto",
            });
            f.space();
            lam(f, hi, reraise_exn);
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lfor_of(param, iterable, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(for_of ");
            print_ident(f, param);
            f.space();
            lam(f, iterable, reraise_exn);
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lfor_await_of(param, iterable, body) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(for_await_of ");
            print_ident(f, param);
            f.space();
            lam(f, iterable, reraise_exn);
            f.space();
            lam(f, body, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lassign(id, expr) => {
            f.open_box(BoxKind::Box, 2);
            f.string("(assign");
            f.space();
            print_ident(f, id);
            f.space();
            lam(f, expr, reraise_exn);
            f.string(")");
            f.close_box();
        }
        RawLambda::Lbreak => f.string("break"),
        RawLambda::Lcontinue => f.string("continue"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn polyvariant_pointer_decodes_internal_utf8_without_changing_ascii() {
        let unicode = crate::source_text::latin1_bytes_to_string("`🚀".as_bytes().to_vec());
        let unicode = RawLambda::const_(Constant::Pointer(unicode));
        let mut unicode_out = Vec::new();
        print_raw_lambda(&unicode, &mut unicode_out);
        assert_eq!(unicode_out, "`🚀".as_bytes());

        let ascii = RawLambda::const_(Constant::Pointer("`Ready".to_string()));
        let mut ascii_out = Vec::new();
        print_raw_lambda(&ascii, &mut ascii_out);
        assert_eq!(ascii_out, b"`Ready");
    }
}
