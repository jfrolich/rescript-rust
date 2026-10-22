// Port of compiler/gentype/TypeVars.ml:1-108.

use std::collections::BTreeSet;

use crate::gentype::gen_type_common::{ArgType, Field, Function, Ident, Payload, Type, Variant};
use crate::types::context::TypeContext;
use crate::types::type_expr::{TypeDesc, TypeExpr, TypeExprRef};
use crate::types::typedtree::{TypedCoreType, TypedCoreTypeDesc};

pub fn extract_from_type_expr(type_params: &[TypeExpr]) -> Vec<String> {
    let mut so_far = Vec::new();

    for type_expr in type_params {
        match &*type_expr.desc() {
            TypeDesc::Tvar(Some(s)) => {
                let type_name = s.clone();
                so_far.push(type_name);
            }
            TypeDesc::Tlink(_) => {
                // see if we need to collect more type vars here: t as 'a
            }
            _ => panic!("assert false"),
        }
    }

    so_far
}

pub fn extract_from_type_expr_refs(ctx: &TypeContext, type_params: &[TypeExprRef]) -> Vec<String> {
    // Mirrors compiler/gentype/TypeVars.ml:3-13 at the Types.type_expr
    // boundary. Rust reads the descriptor through TypeContext because
    // TypeExprRef is an arena handle rather than the OCaml record itself.
    let mut so_far = Vec::new();
    for type_expr in type_params {
        match &*ctx.get_desc(*type_expr) {
            TypeDesc::Tvar(Some(s)) => {
                so_far.push(s.clone());
            }
            TypeDesc::Tlink(_) => {
                // see if we need to collect more type vars here: t as 'a
            }
            _ => panic!("assert false"),
        }
    }
    so_far
}

pub fn extract_from_core_type(type_params: &[TypedCoreType]) -> Vec<String> {
    let mut so_far = Vec::new();

    for type_expr in type_params {
        if let TypedCoreTypeDesc::Ttyp_var(Some(s)) = &type_expr.ctyp_desc {
            let type_name = s.clone();
            so_far.push(type_name);
        }
    }

    so_far
}

pub fn substitute<F>(type0: &Type, f: &F) -> Type
where
    F: Fn(&str) -> Option<Type>,
{
    match type0 {
        Type::Array(t, array_kind) => Type::Array(Box::new(substitute(t, f)), *array_kind),
        Type::Dict(type_) => Type::Dict(Box::new(substitute(type_, f))),
        Type::Function(function_) => Type::Function(Function {
            arg_types: function_
                .arg_types
                .iter()
                .map(|ArgType { a_name, a_type }| ArgType {
                    a_name: a_name.clone(),
                    a_type: substitute(a_type, f),
                })
                .collect(),
            ret_type: function_.ret_type.clone(),
            type_vars: function_.type_vars.clone(),
        }),
        Type::Ident(Ident { type_args, .. }) if type_args.is_empty() => type0.clone(),
        Type::Ident(ident) => Type::Ident(Ident {
            builtin: ident.builtin,
            name: ident.name.clone(),
            type_args: ident
                .type_args
                .iter()
                .map(|type_arg| substitute(type_arg, f))
                .collect(),
        }),
        Type::Null(type_) => Type::Null(Box::new(substitute(type_, f))),
        Type::Nullable(type_) => Type::Nullable(Box::new(substitute(type_, f))),
        Type::Object(closed_flag, fields) => Type::Object(
            *closed_flag,
            fields
                .iter()
                .map(|field| Field {
                    type_: substitute(&field.type_, f),
                    ..field.clone()
                })
                .collect(),
        ),
        Type::Option(type_) => Type::Option(Box::new(substitute(type_, f))),
        Type::Promise(type_) => Type::Promise(Box::new(substitute(type_, f))),
        Type::Tuple(inner_types) => {
            Type::Tuple(inner_types.iter().map(|t| substitute(t, f)).collect())
        }
        Type::TypeVar(s) => match f(s) {
            None => type0.clone(),
            Some(type1) => type1,
        },
        Type::Variant(variant) => Type::Variant(Variant {
            payloads: variant
                .payloads
                .iter()
                .map(|payload| Payload {
                    t: substitute(&payload.t, f),
                    ..payload.clone()
                })
                .collect(),
            ..variant.clone()
        }),
    }
}

pub fn free_(type0: &Type) -> BTreeSet<String> {
    match type0 {
        Type::Array(t, _) => free_(t),
        Type::Function(Function {
            arg_types,
            ret_type,
            type_vars,
        }) => {
            let mut out = freeOfList_(arg_types);
            out.extend(free_(ret_type));
            for type_var in type_vars {
                out.remove(type_var);
            }
            out
        }
        Type::Object(_, fields) => {
            fields
                .iter()
                .fold(BTreeSet::new(), |mut s, Field { type_, .. }| {
                    s.extend(free_(type_));
                    s
                })
        }
        Type::Ident(Ident { type_args, .. }) => {
            type_args.iter().fold(BTreeSet::new(), |mut s, type_arg| {
                s.extend(free_(type_arg));
                s
            })
        }
        Type::Dict(type_) | Type::Null(type_) | Type::Nullable(type_) => free_(type_),
        Type::Option(type_) | Type::Promise(type_) => free_(type_),
        Type::Tuple(inner_types) => inner_types.iter().fold(BTreeSet::new(), |mut s, type_arg| {
            s.extend(free_(type_arg));
            s
        }),
        Type::TypeVar(s) => BTreeSet::from([s.clone()]),
        Type::Variant(Variant { payloads, .. }) => {
            payloads
                .iter()
                .fold(BTreeSet::new(), |mut s, Payload { t, .. }| {
                    s.extend(free_(t));
                    s
                })
        }
    }
}

#[allow(non_snake_case)]
pub fn freeOfList_(types: &[ArgType]) -> BTreeSet<String> {
    types
        .iter()
        .fold(BTreeSet::new(), |mut s, ArgType { a_type, .. }| {
            s.extend(free_(a_type));
            s
        })
}

pub fn free(type_: &Type) -> Vec<String> {
    free_(type_).into_iter().collect()
}
