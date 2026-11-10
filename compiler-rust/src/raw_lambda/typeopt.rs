//! Raw-lambda type-based optimizations.
//!
//! This follows the same split as OCaml's `typeopt.ml`, which `translcore.ml`
//! consults when deciding raw-lambda shapes such as `Blk_some_not_nested`.

use crate::fast_hash::AHashSet as HashSet;

use crate::types::context::TypeContext;
use crate::types::decl::{
    Attribute, ConstructorArguments, ConstructorDescription, INTERNAL_OPTIONAL_ATTR_NAME, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::{TypeDesc, TypeExprRef};

const UNTAGGED_ATTR: &str = "unboxed";

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
        Some(crate::types::VariantConstructorCase::Block(block)) if block.is_untagged()
    )
}

pub(crate) fn constructor_has_optional_shape(cstr: &ConstructorDescription) -> bool {
    cstr.cstr_attributes
        .iter()
        .any(|attr| attr.attr_name.txt == INTERNAL_OPTIONAL_ATTR_NAME)
}

pub(crate) fn type_cannot_contain_undefined(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    ctx.typeopt_answer(env.id(), ty, TYPEOPT_CANNOT_CONTAIN_UNDEFINED, || {
        type_cannot_contain_undefined_rec(ctx, env, ty, &[])
    })
}

const TYPEOPT_CANNOT_CONTAIN_UNDEFINED: u8 = 0;
const TYPEOPT_BASE_UNIT: u8 = 2;
const TYPEOPT_BASE_BOOL: u8 = 3;

/// typeopt.ml `cannot_contain_undefined ~visiting`: `visiting` holds the
/// variant declarations the walk is in.
fn type_cannot_contain_undefined_rec(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    visiting: &[Path],
) -> bool {
    use crate::types::ValueShape;
    // typeopt.ml `cannot_contain_undefined`: a value declared to be a class
    // instance or to have a `typeof` other than "undefined" is not
    // undefined. The payload of an `@unboxed` wrapper is declared only after
    // scraping.
    if crate::types::variant_layout::value_shape(ctx, env, ty) != ValueShape::Unstated {
        return true;
    }
    let ty = scrape_ty(ctx, env, ty);
    if crate::types::variant_layout::value_shape(ctx, env, ty) != ValueShape::Unstated {
        return true;
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
                    // Its shape was read from the scraped type above.
                    TypeKind::TypeAbstract => false,
                    TypeKind::TypeOpen => false,
                    TypeKind::TypeRecord(_, _) => true,
                    TypeKind::TypeVariant(cdecls, _)
                        if is_option_like_variant(cdecls) || is_unit_like_variant(cdecls) =>
                    {
                        false
                    }
                    // A value reaches `undefined` through finitely many
                    // unboxed payloads, so the cases met again add none:
                    // whether the variant can be `undefined` is decided by
                    // its other cases.
                    TypeKind::TypeVariant(_, _) if visiting.iter().any(|p| p.same(path)) => true,
                    TypeKind::TypeVariant(cdecls, _) => {
                        let visiting: Vec<Path> =
                            std::iter::once(path.clone()).chain(visiting.iter().cloned()).collect();
                        let visiting = visiting.as_slice();
                        let check_case = |cd: &crate::types::ConstructorDeclaration,
                                              case: Option<
                            &crate::types::VariantConstructorCase,
                        >| {
                            let has_undefined = matches!(
                                case,
                                Some(crate::types::VariantConstructorCase::Constant(
                                    crate::types::VariantTag {
                                        literal: crate::types::VariantLiteralTag::Undefined,
                                        ..
                                    }
                                ))
                            ) || case.is_none()
                                && cd.cd_runtime_tag
                                    == Some(crate::types::VariantLiteralTag::Undefined);
                            let untagged = matches!(
                                case,
                                Some(crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock::Untagged { .. }
                                ))
                            ) || case.is_none()
                                && has_untagged(&decl.type_attributes);
                            if has_undefined {
                                false
                            } else if untagged {
                                match &cd.cd_args {
                                    ConstructorArguments::CstrTuple(args) => {
                                        match args.as_slice() {
                                            [arg] => type_cannot_contain_undefined_rec(
                                                ctx, env, *arg, visiting,
                                            ),
                                            [] => true,
                                            [_, _, ..] => true,
                                        }
                                    }
                                    ConstructorArguments::CstrRecord(labels) => {
                                        match labels.as_slice() {
                                            [label] => type_cannot_contain_undefined_rec(
                                                ctx,
                                                env,
                                                label.ld_type,
                                                visiting,
                                            ),
                                            [] | [_, _, ..] => true,
                                        }
                                    }
                                }
                            } else {
                                true
                            }
                        };

                        match decl.variant_layout_ref() {
                            Some(layout_ref) => ctx.with_variant_layout(layout_ref, |layout| {
                                cdecls.iter().enumerate().all(|(position, cd)| {
                                    check_case(cd, Some(&layout.constructors[position]))
                                })
                            }),
                            None => cdecls.iter().all(|cd| check_case(cd, None)),
                        }
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
        | TypeDesc::Tunivar(..)
        | TypeDesc::Tlink(_)
        | TypeDesc::Tsubst(_)
        | TypeDesc::Tnil
        | TypeDesc::Tvar(..)
        | TypeDesc::Tobject { .. } => false,
    }
}

/// Fast path for type_cannot_contain_undefined that doesn't require an env.
/// Checks type descriptor directly for types that are always safe
/// (Ttuple, Tarrow, Tvariant, Tpackage, Tconstr for builtin types).
/// Also tries to expand Tconstr types via type declarations.
/// typeopt.ml `abstractness`: whether a type is an abstract type whose
/// representation the compiler does not see, one that stands for another
/// type (a functor parameter's or a locally abstract type), or neither.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Abstractness {
    Opaque,
    StandsForAnother,
    NotAbstract,
}

/// typeopt.ml `abstractness`.
pub(crate) fn abstractness(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> Abstractness {
    let expanded = crate::types::ctype::expand_head_opt(ctx, env, ty);
    let path = match &*ctx.get_desc(expanded) {
        TypeDesc::Tconstr { path, .. } => path.clone(),
        _ => return Abstractness::NotAbstract,
    };
    match crate::types::ctype::lookup_type_decl_for_path(ctx, env, &path) {
        Some(decl)
            if matches!(decl.type_kind, TypeKind::TypeAbstract) && decl.type_manifest.is_none() =>
        {
            if decl.type_newtype_level.is_some() || env.is_functor_arg_path(&path) {
                Abstractness::StandsForAnother
            } else if crate::types::predef::type_is_builtin_path_but_option(&path).is_some() {
                Abstractness::NotAbstract
            } else {
                Abstractness::Opaque
            }
        }
        _ => Abstractness::NotAbstract,
    }
}

/// typeopt.ml `undefinedness`: whether a type can hold `undefined`, as far
/// as the compiler sees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Undefinedness {
    CannotBeUndefined,
    Unseen,
    StandsForAnother,
    CanBeUndefined,
}

/// typeopt.ml `undefinedness`: an opaque abstract type or a JavaScript
/// object type has a representation the compiler does not see.
pub(crate) fn undefinedness(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> Undefinedness {
    if type_cannot_contain_undefined(ctx, env, ty) {
        return Undefinedness::CannotBeUndefined;
    }
    match abstractness(ctx, env, ty) {
        Abstractness::Opaque => Undefinedness::Unseen,
        Abstractness::StandsForAnother => Undefinedness::StandsForAnother,
        Abstractness::NotAbstract => {
            let expanded = crate::types::ctype::expand_head_opt(ctx, env, ty);
            if matches!(&*ctx.get_desc(expanded), TypeDesc::Tobject { .. }) {
                Undefinedness::Unseen
            } else {
                Undefinedness::CanBeUndefined
            }
        }
    }
}

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
                        if decl.type_shape != crate::types::ValueShape::Unstated {
                            return true;
                        }
                        if let Some(manifest) = decl.type_manifest {
                            return rec(ctx, manifest, seen);
                        }
                        match &decl.type_kind {
                            TypeKind::TypeRecord(_, _) => true,
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

/// OCaml typedecl.ml `get_unboxed_type_representation` with its fuel of 100
/// (PR#7424): expand the head; through an unboxed single-field record or
/// single-constructor variant, continue with the field type applied to the
/// arguments; stop at any other type, and give up (`None`) on an abstract
/// type or when the fuel runs out.
fn get_unboxed_type_representation(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<TypeExprRef> {
    fn go(ctx: &TypeContext, env: &Env, ty: TypeExprRef, fuel: i32) -> Option<TypeExprRef> {
        if fuel < 0 {
            return None;
        }
        let ty = ctx.repr(crate::types::ctype::expand_head_opt(ctx, env, ty));
        let (path, args) = match &*ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
            _ => return Some(ty),
        };
        let Some(decl) = find_type_decl(ctx, env, &path) else {
            return Some(ty);
        };
        if decl.type_representation != crate::types::TypeRepresentation::Unboxed {
            return Some(ty);
        }
        let ty2 = match &decl.type_kind {
            TypeKind::TypeRecord(labels, _) if labels.len() == 1 => labels[0].ld_type,
            TypeKind::TypeVariant(cdecls, _) if cdecls.len() == 1 => match &cdecls[0].cd_args {
                ConstructorArguments::CstrTuple(tys) if tys.len() == 1 => tys[0],
                ConstructorArguments::CstrRecord(labels) if labels.len() == 1 => labels[0].ld_type,
                _ => return Some(ty),
            },
            // A recursive unboxed type declaration being checked.
            TypeKind::TypeAbstract => return None,
            // Only the above can be unboxed (OCaml asserts).
            _ => return Some(ty),
        };
        let applied =
            crate::types::ctype::apply(ctx, env, &decl.type_params, ty2, args.as_slice())?;
        go(ctx, env, applied, fuel - 1)
    }
    go(ctx, env, ty, 100)
}

pub(crate) fn scrape_ty(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> TypeExprRef {
    // OCaml `Typeopt.scrape_ty` uses `Ctype.expand_head_opt`, then checks
    // unboxed representations (compiler/ml/typeopt.ml:19-31).
    // `Ctype.correct_levels ty` is `duplicate_type ty` (ctype.ml:650), so
    // the expansion's unifications mutate a copy, not the typed tree.
    let ty = crate::types::ctype::subst_identity_copy(ctx, ty);
    let ty = crate::types::ctype::expand_head_opt(ctx, env, ty);
    let path = match &*ctx.borrow_desc(ty) {
        TypeDesc::Tconstr { path, .. } => Some(path.clone()),
        _ => None,
    };
    match path {
        Some(path) => {
            if let Some(decl) = find_type_decl(ctx, env, &path) {
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
    // Match OCaml `Typeopt.is_base_type`: inspect `scrape env ty`
    // (compiler/ml/typeopt.ml:99-101).
    let visit = || {
        let ty = scrape_ty(ctx, env, ty);
        // NOTE: OCaml tests `Path.same p Predef.path_*`; this last-component
        // name test is broader and is kept as-is to preserve output.
        matches!(&*ctx.get_desc(ty), TypeDesc::Tconstr { path, .. } if path.last() == name)
    };
    let query = match name {
        "unit" => Some(TYPEOPT_BASE_UNIT),
        "bool" => Some(TYPEOPT_BASE_BOOL),
        _ => None,
    };
    match query {
        Some(query) => ctx.typeopt_answer(env.id(), ty, query, visit),
        None => visit(),
    }
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
        "int" | "char" | "float" | "bool" | "exn" | "array" | "list" | "result" | "dict"
        | "bigint" | "string" | "promise" | "iterable" | "asyncIterable" => {
            BuiltinPathTest::ForSureYes
        }
        _ => BuiltinPathTest::NotApplicable,
    }
}

pub(crate) fn find_type_decl<'a>(
    ctx: &'a TypeContext,
    env: &'a Env,
    path: &Path,
) -> Option<crate::types::decl::TypeDeclarationRef<'a>> {
    use crate::types::decl::TypeDeclarationRef;
    crate::types::ctype::lookup_type_decl_for_path(ctx, env, path)
        .or_else(|| env.lookup_type(path).ok().map(TypeDeclarationRef::Borrowed))
}

pub(crate) fn has_untagged(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| attr.attr_name.txt == UNTAGGED_ATTR)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::ident::Ident;
    use crate::types::asttypes::PrivateFlag;
    use crate::types::decl::TypeDeclaration;

    #[test]
    fn base_type_uses_private_manifest_for_optimization() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = crate::types::env::initial_env(&ctx);
        let alias_id = Ident::create_local("private_string_alias");
        env.add_type(
            alias_id,
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: TypeKind::TypeAbstract,
                type_private: PrivateFlag::Private,
                type_manifest: Some(ctx.predef_string()),
                type_variance: vec![],
                type_newtype_level: None,
                type_loc: crate::types::DeclLoc::none(),
                type_attributes: vec![],
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_shape: crate::types::ValueShape::Unstated,
                type_inlined_types: vec![],
                type_path: None,
            },
        );

        let alias_ty = ctx.new_constr(Path::Pident(alias_id), vec![]);

        assert!(is_base_type(&ctx, &env, alias_ty, "string"));
    }
}
