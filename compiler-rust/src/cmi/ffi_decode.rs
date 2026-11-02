//! Decoding of marshalled `External_ffi_types` values, as the OCaml compiler
//! stores them in `.cmi` primitive descriptions (`Primitive.prim_kind`) and in
//! `.cmj` inlinable lambdas (`Pjs_call`, `Pjs_object_create`, `Pimport`).
//!
//! The layouts follow the OCaml type definitions in
//! `compiler/ml/external_arg_spec.ml` and `compiler/ml/external_ffi_types.ml`.

use super::marshal_reader::OcamlValue;
use crate::types::decl::PrimKind;
use crate::types::external_ffi_types::{
    Attr, Cst, DeclKind, ExternalDecl, ExternalFfi, ExternalModuleName, InlineConst, Label,
    LabelNoname, ModuleBindName, ModuleSource, ObjParam, Param, ReturnWrapper,
};

fn list(value: &OcamlValue) -> Vec<&OcamlValue> {
    let mut items = Vec::new();
    let mut current = value;
    while let Some((0, [head, tail])) = current.as_block_opt() {
        items.push(head);
        current = tail;
    }
    items
}

fn string(value: &OcamlValue) -> Option<String> {
    match value {
        OcamlValue::String(s) => Some(s.clone()),
        _ => None,
    }
}

fn int(value: &OcamlValue) -> Option<i64> {
    match value {
        OcamlValue::Int(i) => Some(*i),
        _ => None,
    }
}

fn strings(value: &OcamlValue) -> Option<Vec<String>> {
    list(value).into_iter().map(string).collect()
}

fn string_pairs(value: &OcamlValue) -> Option<Vec<(String, String)>> {
    list(value)
        .into_iter()
        .map(|pair| match pair.as_block_opt()? {
            (0, [a, b]) => Some((string(a)?, string(b)?)),
            _ => None,
        })
        .collect()
}

fn attr(value: &OcamlValue) -> Option<Attr> {
    match value {
        OcamlValue::Int(0) => Some(Attr::ExternUnit),
        OcamlValue::Int(1) => Some(Attr::Nothing),
        OcamlValue::Int(2) => Some(Attr::Ignore),
        OcamlValue::Int(3) => Some(Attr::Unwrap),
        _ => match value.as_block_opt()? {
            (0, [descr]) => Some(Attr::PolyVarString {
                descr: string_pairs(descr)?,
            }),
            (1, [descr]) => Some(Attr::PolyVar {
                descr: match descr.as_option() {
                    None => None,
                    Some(d) => Some(string_pairs(d)?),
                },
            }),
            (2, [cases]) => Some(Attr::Int(
                list(cases)
                    .into_iter()
                    .map(|pair| match pair.as_block_opt()? {
                        (0, [a, b]) => Some((string(a)?, int(b)?)),
                        _ => None,
                    })
                    .collect::<Option<_>>()?,
            )),
            (3, [cst]) => Some(Attr::ArgCst(match cst.as_block_opt()? {
                (0, [i]) => Cst::ArgIntLit(int(i)?),
                (1, [s]) => Cst::ArgStringLit(string(s)?),
                (2, [s]) => Cst::ArgJsonLit(string(s)?),
                _ => return None,
            })),
            _ => None,
        },
    }
}

fn label_noname(value: &OcamlValue) -> Option<LabelNoname> {
    Some(match int(value)? {
        0 => LabelNoname::ArgLabel,
        1 => LabelNoname::ArgEmpty,
        2 => LabelNoname::ArgOptional,
        _ => return None,
    })
}

fn label(value: &OcamlValue) -> Option<Label> {
    match value {
        OcamlValue::Int(0) => Some(Label::ObjEmpty),
        _ => match value.as_block_opt()? {
            (0, [name]) => Some(Label::ObjLabel {
                name: string(name)?,
            }),
            (1, [name, sure]) => Some(Label::ObjOptional {
                name: string(name)?,
                for_sure_no_nested_option: int(sure)? != 0,
            }),
            _ => None,
        },
    }
}

/// `External_arg_spec.params`.
pub fn params(value: &OcamlValue) -> Option<Vec<Param>> {
    list(value)
        .into_iter()
        .map(|p| match p.as_block_opt()? {
            (0, [arg_type, arg_label]) => Some(Param {
                arg_type: attr(arg_type)?,
                arg_label: label_noname(arg_label)?,
            }),
            _ => None,
        })
        .collect()
}

/// `External_arg_spec.obj_params`.
pub fn obj_params(value: &OcamlValue) -> Option<Vec<ObjParam>> {
    list(value)
        .into_iter()
        .map(|p| match p.as_block_opt()? {
            (0, [obj_arg_type, obj_arg_label]) => Some(ObjParam {
                obj_arg_type: attr(obj_arg_type)?,
                obj_arg_label: label(obj_arg_label)?,
            }),
            _ => None,
        })
        .collect()
}

/// `External_ffi_types.external_module_name`.
pub fn external_module_name(value: &OcamlValue) -> Option<ExternalModuleName> {
    let (0, [bundle, bind, import_attributes]) = value.as_block_opt()? else {
        return None;
    };
    Some(ExternalModuleName {
        bundle: string(bundle)?,
        module_bind_name: match bind {
            OcamlValue::Int(0) => ModuleBindName::PhintNothing,
            _ => match bind.as_block_opt()? {
                (0, [name]) => ModuleBindName::PhintName(string(name)?),
                _ => return None,
            },
        },
        import_attributes: match import_attributes.as_option() {
            None => None,
            Some(attrs) => Some(string_pairs(attrs)?),
        },
    })
}

fn decl_kind(value: &OcamlValue) -> Option<DeclKind> {
    match value {
        OcamlValue::Int(0) => Some(DeclKind::DeclGetIndex),
        OcamlValue::Int(1) => Some(DeclKind::DeclSetIndex),
        _ => {
            let (tag, [name]) = value.as_block_opt()? else {
                return None;
            };
            let name = string(name)?;
            Some(match tag {
                0 => DeclKind::DeclVal { name },
                1 => DeclKind::DeclSend { name },
                2 => DeclKind::DeclNew { name },
                3 => DeclKind::DeclGet { name },
                4 => DeclKind::DeclSet { name },
                _ => return None,
            })
        }
    }
}

/// `External_ffi_types.external_decl`.
pub fn external_decl(value: &OcamlValue) -> Option<ExternalDecl> {
    let (0, [kind, module_, scopes, variadic, effective_arity]) = value.as_block_opt()? else {
        return None;
    };
    Some(ExternalDecl {
        kind: decl_kind(kind)?,
        module_: match module_.as_option() {
            None => None,
            Some(OcamlValue::Int(0)) => Some(ModuleSource::ModuleItself),
            Some(source) => match source.as_block_opt()? {
                (0, [emn]) => Some(ModuleSource::ModuleNamed(external_module_name(emn)?)),
                _ => return None,
            },
        },
        scopes: strings(scopes)?,
        variadic: int(variadic)? != 0,
        effective_arity: int(effective_arity)?,
    })
}

fn return_wrapper(value: &OcamlValue) -> Option<ReturnWrapper> {
    Some(match int(value)? {
        0 => ReturnWrapper::ReturnUnset,
        1 => ReturnWrapper::ReturnIdentity,
        2 => ReturnWrapper::ReturnNullToOpt,
        3 => ReturnWrapper::ReturnNullUndefinedToOpt,
        _ => return None,
    })
}

/// `External_ffi_types.t`.
pub fn external_ffi(value: &OcamlValue) -> Option<ExternalFfi> {
    match value.as_block_opt()? {
        (0, [ps, ret, decl]) => Some(ExternalFfi::FfiBs(
            params(ps)?,
            return_wrapper(ret)?,
            external_decl(decl)?,
        )),
        (1, [ps]) => Some(ExternalFfi::FfiObjCreate(obj_params(ps)?)),
        _ => None,
    }
}

/// `External_ffi_types.inline_const`.
pub fn inline_const(value: &OcamlValue) -> Option<InlineConst> {
    match value.as_block_opt()? {
        (0, [s]) => Some(InlineConst::ConstString(string(s)?)),
        (1, [b]) => Some(InlineConst::ConstBool(int(b)? != 0)),
        (2, [i]) => Some(InlineConst::ConstInt(int(i)? as i32)),
        (3, [positive, digits]) => Some(InlineConst::ConstBigint {
            positive: int(positive)? != 0,
            digits: string(digits)?,
        }),
        (4, [f]) => Some(InlineConst::ConstFloat(string(f)?)),
        _ => None,
    }
}

/// `Primitive.prim_kind`.
pub fn prim_kind(value: &OcamlValue) -> Option<PrimKind> {
    match value {
        OcamlValue::Int(0) => Some(PrimKind::KindIntrinsic),
        _ => match value.as_block_opt()? {
            (0, [spec]) => Some(PrimKind::KindExternal(Box::new(external_ffi(spec)?))),
            (1, [c]) => Some(PrimKind::KindInlineConst(Box::new(inline_const(c)?))),
            _ => None,
        },
    }
}
