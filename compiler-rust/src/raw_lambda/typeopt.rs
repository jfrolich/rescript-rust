//! Raw-lambda type-based optimizations.
//!
//! This follows the same split as OCaml's `typeopt.ml`, which `translcore.ml`
//! consults when deciding raw-lambda shapes such as `Blk_some_not_nested`.

use std::collections::HashSet;

use crate::types::context::TypeContext;
use crate::types::decl::{
    Attribute, ConstructorArguments, ConstructorDescription, INTERNAL_OPTIONAL_ATTR_NAME,
    TypeDeclaration, TypeKind,
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

pub(crate) fn constructor_case(
    ctx: &TypeContext,
    cstr: &ConstructorDescription,
) -> Option<crate::types::VariantConstructorCase> {
    match cstr.cstr_kind {
        crate::types::ConstructorKind::Ordinary(reference) => Some(reference.representation(ctx)),
        crate::types::ConstructorKind::Extension(_) => None,
    }
}

pub(crate) fn constructor_payload_is_unboxed(
    ctx: &TypeContext,
    cstr: &ConstructorDescription,
) -> bool {
    matches!(
        constructor_case(ctx, cstr),
        Some(crate::types::VariantConstructorCase::Block(block)) if block.runtime.untagged
    )
}

pub(crate) fn constructor_has_optional_shape(cstr: &ConstructorDescription) -> bool {
    cstr.cstr_attributes
        .iter()
        .any(|attr| attr.attr_name.txt == INTERNAL_OPTIONAL_ATTR_NAME)
}

pub(crate) fn type_cannot_contain_undefined(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    let mut seen = HashSet::new();
    type_cannot_contain_undefined_rec(ctx, env, ty, &mut seen)
}

fn type_cannot_contain_undefined_rec(
    ctx: &TypeContext,
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
                    TypeKind::TypeAbstract => {
                        decl.type_attributes.iter().any(is_not_undefined_attr)
                    }
                    TypeKind::TypeOpen => false,
                    TypeKind::TypeRecord(_, _) => true,
                    TypeKind::TypeVariant(cdecls, _)
                        if is_option_like_variant(cdecls) || is_unit_like_variant(cdecls) =>
                    {
                        false
                    }
                    TypeKind::TypeVariant(cdecls, _) => {
                        let layout = decl.variant_layout_ref().map(|r| ctx.variant_layout(r));
                        cdecls.iter().enumerate().all(|(position, cd)| {
                            let case = layout.as_ref().map(|layout| &layout.constructors[position]);
                            let has_undefined = matches!(
                                case,
                                Some(crate::types::VariantConstructorCase::Constant(
                                    crate::types::VariantTag {
                                        tag_type: Some(crate::types::VariantTagType::Undefined),
                                        ..
                                    }
                                ))
                            ) || case.is_none()
                                && has_undefined_literal(&cd.cd_attributes);
                            let untagged = matches!(
                                case,
                                Some(crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock {
                                        runtime: crate::types::BlockRuntime { untagged: true, .. },
                                        ..
                                    }
                                ))
                            ) || case.is_none()
                                && has_untagged(&decl.type_attributes);
                            if has_undefined {
                                false
                            } else if untagged {
                                match &cd.cd_args {
                                    ConstructorArguments::CstrTuple(args) => {
                                        match args.as_slice() {
                                            [arg] => {
                                                type_is_builtin_object(ctx, env, *arg)
                                                    || type_cannot_contain_undefined_rec(
                                                        ctx, env, *arg, seen,
                                                    )
                                            }
                                            [] => true,
                                            [_, _, ..] => true,
                                        }
                                    }
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

/// Fast path for type_cannot_contain_undefined that doesn't require an env.
/// Checks type descriptor directly for types that are always safe
/// (Ttuple, Tarrow, Tvariant, Tpackage, Tconstr for builtin types).
/// Also tries to expand Tconstr types via type declarations.
pub(crate) fn type_cannot_contain_undefined_no_env(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    fn rec(ctx: &TypeContext, ty: TypeExprRef, seen: &mut HashSet<TypeExprRef>) -> bool {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            return false;
        }
        match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, .. } => match type_is_builtin_path_but_option(path) {
                BuiltinPathTest::ForSureYes => true,
                BuiltinPathTest::ForSureNo => false,
                BuiltinPathTest::NotApplicable => {
                    if let Some(decl) = find_type_decl(ctx, &crate::types::env::Env::empty(), path)
                    {
                        if let Some(manifest) = decl.type_manifest {
                            return rec(ctx, manifest, seen);
                        }
                        match &decl.type_kind {
                            TypeKind::TypeRecord(_, _) => true,
                            TypeKind::TypeAbstract => {
                                decl.type_attributes.iter().any(is_not_undefined_attr)
                            }
                            _ => false,
                        }
                    } else {
                        false
                    }
                }
            },
            TypeDesc::Ttuple(_)
            | TypeDesc::Tvariant(_)
            | TypeDesc::Tpackage { .. }
            | TypeDesc::Tarrow { .. } => true,
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => rec(ctx, *next, seen),
            _ => false,
        }
    }

    let mut seen = HashSet::new();
    rec(ctx, ty, &mut seen)
}

/// Get the unboxed representation of a type, if possible.
/// For an unboxed variant type with a single constructor and single arg,
/// returns the arg type (recursively expanded). Returns None for recursive types.
/// Simplified version of OCaml's Typedecl.get_unboxed_type_representation.
fn get_unboxed_type_representation(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    let mut visited = HashSet::new();
    get_unboxed_repr_rec(ctx, env, ty, &mut visited)
}

fn get_unboxed_repr_rec(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    visited: &mut HashSet<TypeExprRef>,
) -> Option<TypeExprRef> {
    if !visited.insert(ty) {
        return None; // Recursive type
    }
    match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, args, .. } => {
            let decl = find_type_decl(ctx, env, path)?;
            if decl.type_representation != crate::types::TypeRepresentation::Unboxed {
                return Some(ty);
            }
            match &decl.type_kind {
                TypeKind::TypeVariant(cdecls, _) if cdecls.len() == 1 => {
                    match &cdecls[0].cd_args {
                        ConstructorArguments::CstrTuple(tys) if tys.len() == 1 => {
                            let arg_ty = tys[0];
                            // Substitute type parameters if needed
                            // For simple cases (no type params), use arg_ty directly
                            get_unboxed_repr_rec(ctx, env, arg_ty, visited)
                        }
                        ConstructorArguments::CstrRecord(labels) if labels.len() == 1 => {
                            let arg_ty = labels[0].ld_type;
                            get_unboxed_repr_rec(ctx, env, arg_ty, visited)
                        }
                        _ => Some(ty),
                    }
                }
                _ => Some(ty),
            }
        }
        _ => Some(ty),
    }
}

pub(crate) fn scrape_ty(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    // OCaml `Typeopt.scrape_ty` uses `Ctype.expand_head_opt`, then checks
    // unboxed representations (compiler/ml/typeopt.ml:19-31).
    let ty = crate::types::ctype::expand_head_opt(ctx, env, ty);
    match &*ctx.get_desc(ty) {
        TypeDesc::Tconstr { path, .. } => {
            if let Some(decl) = find_type_decl(ctx, env, path) {
                if decl.type_representation == crate::types::TypeRepresentation::Unboxed {
                    // For unboxed types, try to get the representation type.
                    // If the type is recursive (representation returns None),
                    // return the original type without further expansion.
                    // This matches OCaml's scrape_ty behavior.
                    match get_unboxed_type_representation(ctx, env, ty) {
                        Some(repr_ty) => repr_ty,
                        None => ty,
                    }
                } else {
                    ty
                }
            } else {
                ty
            }
        }
        _ => ty,
    }
}

pub(crate) fn is_base_type(ctx: &TypeContext, env: &Env, ty: TypeExprRef, name: &str) -> bool {
    fn visit(
        ctx: &TypeContext,
        env: &Env,
        ty: TypeExprRef,
        name: &str,
        seen: &mut HashSet<TypeExprRef>,
    ) -> bool {
        let ty = scrape_ty(ctx, env, ty);
        if !seen.insert(ty) {
            return false;
        }
        match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, args, .. } => {
                if path.head_name() == name || path.last() == name {
                    return true;
                }
                // Strengthening can give an expression a stamped owner path
                // while its captured module-body Env still contains the local
                // pre-strengthened declaration. Typeopt only needs to inspect
                // the exact nullary representation here; use Path identity and
                // never printed-name or structural lookup.
                if args.is_empty()
                    && let Some(decl) = ctx.find_type_decl_by_exact_path(path)
                    && decl.type_params.is_empty()
                    && let Some(manifest) = decl.type_manifest
                {
                    return visit(ctx, env, manifest, name, seen);
                }
                false
            }
            _ => false,
        }
    }

    // Match OCaml `Typeopt.is_base_type`: inspect `scrape env ty`
    // (compiler/ml/typeopt.ml:99-101).
    visit(ctx, env, ty, name, &mut HashSet::new())
}

fn type_is_builtin_path_but_option(path: &Path) -> BuiltinPathTest {
    let Path::Pident(id) = path else {
        return BuiltinPathTest::NotApplicable;
    };
    // OCaml checks by stamp range (predef stamps are in a known range).
    // We check by name for predef types, which are always top-level Pident.
    if id.stamp() < 0 {
        return BuiltinPathTest::NotApplicable;
    }
    match id.name() {
        "option" | "unit" | "unknown" => BuiltinPathTest::ForSureNo,
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
        | "promise"
        | "iterable"
        | "asyncIterable" => BuiltinPathTest::ForSureYes,
        _ => BuiltinPathTest::NotApplicable,
    }
}

pub(crate) fn find_type_decl_pub(
    ctx: &TypeContext,
    env: &Env,
    path: &Path,
) -> Option<TypeDeclaration> {
    find_type_decl(ctx, env, path)
}

fn find_type_decl(ctx: &TypeContext, env: &Env, path: &Path) -> Option<TypeDeclaration> {
    match path {
        Path::Pident(id) if !id.is_persistent() && id.stamp() != 0 => {
            crate::types::ctype::lookup_type_decl_for_path_pub(ctx, env, path)
                .or_else(|| {
                    ctx.find_type_decl_by_stamp(id.stamp())
                        .map(|decl| decl.clone())
                })
                .or_else(|| {
                    ctx.find_resolved_pdot_type(&path.name())
                        .map(|decl| (*decl).clone())
                })
                .or_else(|| {
                    ctx.find_type_decl_by_path(&path.name())
                        .map(|decl| decl.clone())
                })
                .or_else(|| env.lookup_type(path).ok().cloned())
        }
        _ => crate::types::ctype::lookup_type_decl_for_path_pub(ctx, env, path)
            .or_else(|| {
                ctx.find_resolved_pdot_type(&path.name())
                    .map(|decl| (*decl).clone())
            })
            .or_else(|| {
                ctx.find_type_decl_by_path(&path.name())
                    .map(|decl| decl.clone())
            })
            .or_else(|| env.lookup_type(path).ok().cloned()),
    }
}

fn is_not_undefined_attr(attr: &Attribute) -> bool {
    attr.attr_name.txt == NOT_UNDEFINED_ATTR
}

pub(crate) fn has_untagged(attrs: &[Attribute]) -> bool {
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

pub(crate) fn type_is_builtin_object(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    let ty = scrape_ty(ctx, env, ty);
    match &*ctx.get_desc(ty) {
        TypeDesc::Tobject { .. } => true,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::ident::Ident;
    use crate::location::Location;
    use crate::types::asttypes::PrivateFlag;

    #[test]
    fn builtin_object_recognizes_object_types() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let fields = ctx.new_type(TypeDesc::Tnil);
        let object = ctx.new_type(TypeDesc::Tobject { fields, name: None });

        assert!(type_is_builtin_object(&ctx, &Env::empty(), object));
    }

    #[test]
    fn base_type_expands_strengthened_local_path_by_identity() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let module_id = ctx.create_ident("Dimension");
        let path = Path::pdot(Path::pident(module_id), "t");
        ctx.register_type_decl_by_exact_path(
            path.clone(),
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: TypeKind::TypeAbstract,
                type_private: PrivateFlag::Public,
                type_manifest: Some(ctx.predef_float()),
                type_variance: vec![],
                type_newtype_level: None,
                type_loc: Location::none(),
                type_attributes: vec![],
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_inlined_types: vec![],
                type_path: Some(path.clone()),
            },
        );
        let ty = ctx.new_constr(path, vec![]);

        assert!(is_base_type(&ctx, &Env::empty(), ty, "float"));
    }

    #[test]
    fn base_type_uses_private_manifest_for_optimization() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = crate::types::env::initial_env(&ctx);
        let alias_id = Ident::create_local("private_string_alias");
        env.add_type(
            alias_id.clone(),
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: TypeKind::TypeAbstract,
                type_private: PrivateFlag::Private,
                type_manifest: Some(ctx.predef_string()),
                type_variance: vec![],
                type_newtype_level: None,
                type_loc: Location::none(),
                type_attributes: vec![],
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_inlined_types: vec![],
                type_path: None,
            },
        );

        let alias_ty = ctx.new_constr(Path::Pident(alias_id), vec![]);

        assert!(is_base_type(&ctx, &env, alias_ty, "string"));
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
