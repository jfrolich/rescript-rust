//! Raw-lambda type-based optimizations.
//!
//! This follows the same split as OCaml's `typeopt.ml`, which `translcore.ml`
//! consults when deciding raw-lambda shapes such as `Blk_some_not_nested`.

use std::collections::HashSet;

use crate::types::context::TypeContext;
use crate::types::decl::{
    Attribute, ConstructorArguments, ConstructorDescription, TypeDeclaration, TypeKind,
    INTERNAL_OPTIONAL_ATTR_NAME,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};

const NOT_UNDEFINED_ATTR: &str = "notUndefined";
const UNTAGGED_ATTR: &str = "unboxed";
const JS_DICT_T: &str = "Js.Dict.t";
const JS_DICT_T_LEGACY: &str = "Js_dict.t";

#[derive(Clone, Copy, PartialEq, Eq)]
enum BuiltinPathTest {
    ForSureYes,
    ForSureNo,
    NotApplicable,
}

pub(crate) fn constructor_has_optional_shape(cstr: &ConstructorDescription) -> bool {
    cstr.cstr_attributes
        .iter()
        .any(|attr| attr.attr_name.txt == INTERNAL_OPTIONAL_ATTR_NAME)
}

pub(crate) fn type_cannot_contain_undefined(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
) -> bool {
    let mut seen = HashSet::new();
    type_cannot_contain_undefined_rec(ctx, env, ty, &mut seen)
}

fn type_cannot_contain_undefined_rec(
    ctx: &TypeContext<'_>,
    env: &Env,
    ty: TypeExprRef,
    seen: &mut HashSet<TypeExprRef>,
) -> bool {
    let ty = scrape_ty(ctx, env, ty);
    if !seen.insert(ty) {
        return false;
    }

    match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, .. } => match type_is_builtin_path_but_option(path) {
            BuiltinPathTest::ForSureYes => true,
            BuiltinPathTest::ForSureNo => false,
            BuiltinPathTest::NotApplicable => {
                let Some(decl) = find_type_decl(ctx, env, path) else {
                    return false;
                };
                match &decl.type_kind {
                    TypeKind::TypeAbstract => decl
                        .type_attributes
                        .iter()
                        .any(is_not_undefined_attr),
                    TypeKind::TypeOpen => false,
                    TypeKind::TypeRecord(_, _) => true,
                    TypeKind::TypeVariant(cdecls)
                        if is_option_like_variant(cdecls) || is_unit_like_variant(cdecls) =>
                    {
                        false
                    }
                    TypeKind::TypeVariant(cdecls) => {
                        let untagged = has_untagged(&decl.type_attributes);
                        cdecls.iter().all(|cd| {
                            if has_undefined_literal(&cd.cd_attributes) {
                                false
                            } else if untagged {
                                match &cd.cd_args {
                                    ConstructorArguments::CstrTuple(args) => match args.as_slice() {
                                        [arg] => {
                                            type_is_builtin_object(ctx, env, *arg)
                                                || type_cannot_contain_undefined_rec(
                                                    ctx, env, *arg, seen,
                                                )
                                        }
                                        [] => true,
                                        [_, _, ..] => true,
                                    },
                                    ConstructorArguments::CstrRecord(labels) => {
                                        match labels.as_slice() {
                                            [label] => {
                                                type_is_builtin_object(ctx, env, label.ld_type)
                                                    || type_cannot_contain_undefined_rec(
                                                        ctx,
                                                        env,
                                                        label.ld_type,
                                                        seen,
                                                    )
                                            }
                                            [] | [_, _, ..] => true,
                                        }
                                    }
                                }
                            } else {
                                true
                            }
                        })
                    }
                }
            }
        },
        TypeDesc::Ttuple(_)
        | TypeDesc::Tvariant(_)
        | TypeDesc::Tpackage { .. }
        | TypeDesc::Tarrow { .. } => true,
        TypeDesc::Tfield { .. }
        | TypeDesc::Tpoly { .. }
        | TypeDesc::Tunivar(_)
        | TypeDesc::Tlink(_)
        | TypeDesc::Tsubst(_)
        | TypeDesc::Tnil
        | TypeDesc::Tvar(_)
        | TypeDesc::Tobject { .. } => false,
    }
}

fn scrape_ty(ctx: &TypeContext<'_>, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    crate::types::ctype::expand_head(ctx, env, ty)
}

fn type_is_builtin_path_but_option(path: &Path) -> BuiltinPathTest {
    let Path::Pident(id) = path else {
        return BuiltinPathTest::NotApplicable;
    };
    if !id.is_persistent() {
        return BuiltinPathTest::NotApplicable;
    }
    match id.name() {
        "option" | "unit" => BuiltinPathTest::ForSureNo,
        "int"
        | "char"
        | "float"
        | "bool"
        | "exn"
        | "array"
        | "list"
        | "result"
        | "dict"
        | "bigint"
        | "string"
        | "extension_constructor"
        | "unknown"
        | "promise" => BuiltinPathTest::ForSureYes,
        _ => BuiltinPathTest::NotApplicable,
    }
}

fn find_type_decl(ctx: &TypeContext<'_>, env: &Env, path: &Path) -> Option<TypeDeclaration> {
    match path {
        Path::Pident(id) if !id.is_persistent() && id.stamp() != 0 => {
            ctx.find_type_decl_by_stamp(id.stamp()).map(|decl| decl.clone())
        }
        _ => ctx
            .find_resolved_pdot_type(&path.name())
            .or_else(|| ctx.find_type_decl_by_path(&path.name()).map(|decl| decl.clone()))
            .or_else(|| env.lookup_type(path).ok().cloned()),
    }
}

fn is_not_undefined_attr(attr: &Attribute) -> bool {
    attr.attr_name.txt == NOT_UNDEFINED_ATTR
}

fn has_untagged(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| attr.attr_name.txt == UNTAGGED_ATTR)
}

fn has_undefined_literal(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.attr_name.txt == "as"
            && matches!(
                attr.attr_payload,
                crate::types::decl::AttributePayload::Ident(ref ident)
                    if ident == "undefined"
            )
    })
}

fn type_is_builtin_object(ctx: &TypeContext<'_>, env: &Env, ty: TypeExprRef) -> bool {
    let ty = scrape_ty(ctx, env, ty);
    match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, args, .. } => {
            if matches!(path, Path::Pident(id) if id.name() == "dict") && args.len() == 1 {
                true
            } else {
                let name = path.name();
                name == JS_DICT_T || name == JS_DICT_T_LEGACY
            }
        }
        _ => false,
    }
}

fn is_option_like_variant(cdecls: &[crate::types::decl::ConstructorDeclaration]) -> bool {
    matches!(
        cdecls,
        [
            crate::types::decl::ConstructorDeclaration {
                cd_id,
                cd_args: ConstructorArguments::CstrTuple(args1),
                ..
            },
            crate::types::decl::ConstructorDeclaration {
                cd_id: cd_id2,
                cd_args: ConstructorArguments::CstrTuple(args2),
                ..
            }
        ] if (
            cd_id.name() == "None" && args1.is_empty() && cd_id2.name() == "Some" && args2.len() == 1
        ) || (
            cd_id.name() == "Some" && args1.len() == 1 && cd_id2.name() == "None" && args2.is_empty()
        )
    )
}

fn is_unit_like_variant(cdecls: &[crate::types::decl::ConstructorDeclaration]) -> bool {
    matches!(
        cdecls,
        [crate::types::decl::ConstructorDeclaration {
            cd_id,
            cd_args: ConstructorArguments::CstrTuple(args),
            ..
        }] if cd_id.name() == "()" && args.is_empty()
    )
}
