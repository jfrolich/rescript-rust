//! Marshalling of digested externals into the binary AST.
//!
//! `bsc -bs-ast` writes the AST after the builtin PPX has digested externals
//! (`compiler/core/js_implementation.ml`, `after_parsing_impl`), so a value
//! description's `pval_prim` can be a `Prim_ffi` or `Prim_inline_const`
//! carrying the structured `External_ffi_types` values. The layouts follow the
//! OCaml type definitions in `compiler/ml/external_arg_spec.ml` and
//! `compiler/ml/external_ffi_types.ml`; `crate::cmi::ffi_decode` is the
//! matching reader.

use super::marshal::MarshalWriter;
use crate::types::external_ffi_types::{
    Attr, Cst, DeclKind, ExternalDecl, ExternalFfi, ExternalModuleName, InlineConst, Label,
    LabelNoname, ModuleBindName, ModuleSource, ObjParam, Param, ReturnWrapper,
};

fn list<T>(w: &mut MarshalWriter<'_>, items: &[T], f: impl Fn(&mut MarshalWriter<'_>, &T)) {
    // A cons cell's tail is the next cell, written in place; `[]` is int 0.
    for item in items {
        w.write_block_header(0, 2);
        f(w, item);
    }
    w.write_int(0);
}

fn option<T>(
    w: &mut MarshalWriter<'_>,
    value: &Option<T>,
    f: impl FnOnce(&mut MarshalWriter<'_>, &T),
) {
    match value {
        None => w.write_int(0),
        Some(v) => {
            w.write_block_header(0, 1);
            f(w, v);
        }
    }
}

fn bool_(w: &mut MarshalWriter<'_>, b: bool) {
    w.write_int(i64::from(b));
}

fn string_pairs(w: &mut MarshalWriter<'_>, pairs: &[(String, String)]) {
    list(w, pairs, |w, (a, b)| {
        w.write_block_header(0, 2);
        w.write_str(a);
        w.write_str(b);
    });
}

fn attr(w: &mut MarshalWriter<'_>, a: &Attr) {
    match a {
        Attr::ExternUnit => w.write_int(0),
        Attr::Nothing => w.write_int(1),
        Attr::Ignore => w.write_int(2),
        Attr::Unwrap => w.write_int(3),
        Attr::PolyVarString { descr } => {
            w.write_block_header(0, 1);
            string_pairs(w, descr);
        }
        Attr::PolyVar { descr } => {
            w.write_block_header(1, 1);
            option(w, descr, |w, d| string_pairs(w, d));
        }
        Attr::Int(cases) => {
            w.write_block_header(2, 1);
            list(w, cases, |w, (name, i)| {
                w.write_block_header(0, 2);
                w.write_str(name);
                w.write_int(*i);
            });
        }
        Attr::ArgCst(cst) => {
            w.write_block_header(3, 1);
            match cst {
                Cst::ArgIntLit(i) => {
                    w.write_block_header(0, 1);
                    w.write_int(*i);
                }
                Cst::ArgStringLit(s) => {
                    w.write_block_header(1, 1);
                    w.write_str(s);
                }
                Cst::ArgJsonLit(s) => {
                    w.write_block_header(2, 1);
                    w.write_str(s);
                }
            }
        }
    }
}

fn label_noname(w: &mut MarshalWriter<'_>, l: &LabelNoname) {
    w.write_int(match l {
        LabelNoname::ArgLabel => 0,
        LabelNoname::ArgEmpty => 1,
        LabelNoname::ArgOptional => 2,
    });
}

fn label(w: &mut MarshalWriter<'_>, l: &Label) {
    match l {
        Label::ObjEmpty => w.write_int(0),
        Label::ObjLabel { name } => {
            w.write_block_header(0, 1);
            w.write_str(name);
        }
        Label::ObjOptional {
            name,
            for_sure_no_nested_option,
        } => {
            w.write_block_header(1, 2);
            w.write_str(name);
            bool_(w, *for_sure_no_nested_option);
        }
    }
}

fn params(w: &mut MarshalWriter<'_>, ps: &[Param]) {
    list(w, ps, |w, p| {
        w.write_block_header(0, 2);
        attr(w, &p.arg_type);
        label_noname(w, &p.arg_label);
    });
}

fn obj_params(w: &mut MarshalWriter<'_>, ps: &[ObjParam]) {
    list(w, ps, |w, p| {
        w.write_block_header(0, 2);
        attr(w, &p.obj_arg_type);
        label(w, &p.obj_arg_label);
    });
}

fn external_module_name(w: &mut MarshalWriter<'_>, m: &ExternalModuleName) {
    w.write_block_header(0, 3);
    w.write_str(&m.bundle);
    match &m.module_bind_name {
        ModuleBindName::PhintNothing => w.write_int(0),
        ModuleBindName::PhintName(name) => {
            w.write_block_header(0, 1);
            w.write_str(name);
        }
    }
    option(w, &m.import_attributes, |w, attrs| string_pairs(w, attrs));
}

fn decl_kind(w: &mut MarshalWriter<'_>, k: &DeclKind) {
    let (tag, name) = match k {
        DeclKind::DeclGetIndex => return w.write_int(0),
        DeclKind::DeclSetIndex => return w.write_int(1),
        DeclKind::DeclVal { name } => (0, name),
        DeclKind::DeclSend { name } => (1, name),
        DeclKind::DeclNew { name } => (2, name),
        DeclKind::DeclGet { name } => (3, name),
        DeclKind::DeclSet { name } => (4, name),
    };
    w.write_block_header(tag, 1);
    w.write_str(name);
}

fn external_decl(w: &mut MarshalWriter<'_>, d: &ExternalDecl) {
    w.write_block_header(0, 5);
    decl_kind(w, &d.kind);
    option(w, &d.module_, |w, source| match source {
        ModuleSource::ModuleItself => w.write_int(0),
        ModuleSource::ModuleNamed(emn) => {
            w.write_block_header(0, 1);
            external_module_name(w, emn);
        }
    });
    list(w, &d.scopes, |w, s| w.write_str(s));
    bool_(w, d.variadic);
    w.write_int(d.effective_arity);
}

fn return_wrapper(w: &mut MarshalWriter<'_>, r: &ReturnWrapper) {
    w.write_int(match r {
        ReturnWrapper::ReturnUnset => 0,
        ReturnWrapper::ReturnIdentity => 1,
        ReturnWrapper::ReturnNullToOpt => 2,
        ReturnWrapper::ReturnNullUndefinedToOpt => 3,
    });
}

/// `External_ffi_types.t`.
pub fn marshal_external_ffi(w: &mut MarshalWriter<'_>, ffi: &ExternalFfi) {
    match ffi {
        ExternalFfi::FfiBs(ps, ret, decl) => {
            w.write_block_header(0, 3);
            params(w, ps);
            return_wrapper(w, ret);
            external_decl(w, decl);
        }
        ExternalFfi::FfiObjCreate(ps) => {
            w.write_block_header(1, 1);
            obj_params(w, ps);
        }
    }
}

/// `External_ffi_types.inline_const`.
pub fn marshal_inline_const(w: &mut MarshalWriter<'_>, c: &InlineConst) {
    match c {
        InlineConst::ConstString(s) => {
            w.write_block_header(0, 1);
            w.write_str(s);
        }
        InlineConst::ConstBool(b) => {
            w.write_block_header(1, 1);
            bool_(w, *b);
        }
        InlineConst::ConstInt(i) => {
            w.write_block_header(2, 1);
            w.write_custom_int32(*i);
        }
        InlineConst::ConstBigint { positive, digits } => {
            w.write_block_header(3, 2);
            bool_(w, *positive);
            w.write_str(digits);
        }
        InlineConst::ConstFloat(f) => {
            w.write_block_header(4, 1);
            w.write_str(f);
        }
    }
}
